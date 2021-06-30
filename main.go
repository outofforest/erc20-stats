package stats

import (
	"context"
	"crypto/ecdsa"
	"crypto/rand"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"math/big"
	"os"
	"path/filepath"
	"reflect"
	"sync"
	"sync/atomic"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/forkid"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto/secp256k1"
	"github.com/ethereum/go-ethereum/eth/protocols/eth"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/dnsdisc"
	"github.com/ethereum/go-ethereum/p2p/enode"
	"github.com/ethereum/go-ethereum/p2p/nat"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/ridge/must"
	"github.com/wojciech-malota-wojcik/cms/code/config"
	"github.com/wojciech-malota-wojcik/cms/code/contracts/exw/devexw"
	"github.com/wojciech-malota-wojcik/cms/code/lib/erc20"
	"github.com/wojciech-malota-wojcik/cms/code/lib/logger"
	"github.com/wojciech-malota-wojcik/cms/code/lib/parallel"
	"github.com/wojciech-malota-wojcik/cms/code/lib/run"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

const blocksPerRequest = 10

var (
	exwTokenAddress  = common.HexToAddress(devexw.Address)
	exwTokenTransfer = erc20.ABI.Events[erc20.EventTransfer].ID

	bigZero     = big.NewInt(0)
	bigOne      = big.NewInt(1)
	zeroAddress = common.HexToAddress("0x0")
	today       = uint64(time.Now().UTC().Truncate(24 * time.Hour).Unix())
)

var (
	typeBlockHeadersPacket = reflect.TypeOf(&eth.BlockHeadersPacket{})
	typeReceiptsPacket     = reflect.TypeOf(&eth.ReceiptsPacket{})
)

func newDailySummary(previous *dailySummary) *dailySummary {
	d := &dailySummary{
		TotalSupply:    big.NewInt(0),
		ActiveAccounts: big.NewInt(0),
		Transactions:   big.NewInt(0),
		Volume:         big.NewInt(0),
	}
	if previous != nil {
		d.TotalSupply.Set(previous.TotalSupply)
		d.ActiveAccounts.Set(previous.ActiveAccounts)
	}
	return d
}

type dailySummary struct {
	TotalSupply    *big.Int
	ActiveAccounts *big.Int
	Transactions   *big.Int
	Volume         *big.Int
	Skip           uint
}

func newDailyStats(day time.Time) *dailyStats {
	return &dailyStats{
		day:          day,
		Balances:     map[common.Address]*big.Int{},
		Transactions: big.NewInt(0),
	}
}

type dailyStats struct {
	LastBlock    uint64                      `json:"n"`
	Transactions *big.Int                    `json:"t"`
	Balances     map[common.Address]*big.Int `json:"b"`
	Skip         uint                        `json:"s"`

	day time.Time
}

func (d *dailyStats) Empty() bool {
	return len(d.Balances) == 0
}

type peerInfo struct {
	Version    uint
	Difficulty *big.Int
	Head       string
}

type peerConnection struct {
	Peer   *eth.Peer
	Closed chan struct{}
	Rcv    chan eth.Packet
}

type transfers struct {
	Block     *types.Header
	Transfers []erc20.Transfer
}

func (pc *peerConnection) AwaitMessage(ctx context.Context, t reflect.Type) eth.Packet {
	for {
		select {
		case <-ctx.Done():
			return nil
		case <-pc.Closed:
			return nil
		case msg := <-pc.Rcv:
			if reflect.TypeOf(msg) == t {
				return msg
			}
		}
	}
}

type peerSet struct {
	ch chan struct{}

	mu     sync.RWMutex
	closed bool
	peers  map[string]*peerConnection
	peersP map[*eth.Peer]*peerConnection
}

func (ps *peerSet) Add(peer *eth.Peer) (*peerConnection, error) {
	ps.mu.Lock()
	defer ps.mu.Unlock()

	if ps.closed {
		return nil, errors.New("server is terminating")
	}

	if _, exists := ps.peers[peer.ID()]; exists {
		return nil, errors.New("peer has been already registered")
	}

	conn := &peerConnection{Peer: peer, Closed: make(chan struct{}), Rcv: make(chan eth.Packet)}

	if existingConn := ps.peers[peer.ID()]; existingConn != nil {
		close(existingConn.Closed)
		delete(ps.peersP, existingConn.Peer)
	}

	ps.peers[peer.ID()] = conn
	ps.peersP[peer] = conn
	return conn, nil
}

func (ps *peerSet) Remove(peerID string) {
	ps.mu.Lock()
	defer ps.mu.Unlock()

	peerConn, exists := ps.peers[peerID]
	if !exists {
		return
	}
	peerConn.Peer.Disconnect(p2p.DiscQuitting)

	delete(ps.peers, peerID)
	delete(ps.peersP, peerConn.Peer)
	close(peerConn.Closed)
}

func (ps *peerSet) Get(peerID string) *eth.Peer {
	ps.mu.RLock()
	defer ps.mu.RUnlock()

	return ps.peers[peerID].Peer
}

func (ps *peerSet) GetConn(peer *eth.Peer) *peerConnection {
	ps.mu.RLock()
	defer ps.mu.RUnlock()

	return ps.peersP[peer]
}

func (ps *peerSet) Close() {
	ps.mu.Lock()
	defer ps.mu.Unlock()

	ps.closed = true
	for _, p := range ps.peers {
		p.Peer.Disconnect(p2p.DiscQuitting)
		close(p.Closed)
	}
	ps.peers = nil
	ps.peersP = nil
}

func newRequest(block uint64) *request {
	return &request{
		FromBlock: block,
	}
}

type request struct {
	FromBlock uint64
	LastBlock *types.Header
}

type backend struct {
	network          network
	networkID        config.Blockchain
	fromBlock        uint64
	controlBlock     uint64
	controlBlockHash common.Hash

	chain   *core.BlockChain
	peers   *peerSet
	newPeer chan *peerConnection
}

// Chain retrieves the blockchain object to serve data.
func (b *backend) Chain() *core.BlockChain {
	return b.chain
}

// StateBloom retrieves the bloom filter - if any - for state trie nodes.
func (b *backend) StateBloom() *trie.SyncBloom {
	return nil
}

// TxPool retrieves the transaction pool object to serve data.
func (b *backend) TxPool() eth.TxPool {
	return nil
}

// AcceptTxs retrieves whether transaction processing is enabled on the node
// or if inbound transactions should simply be dropped.
func (b *backend) AcceptTxs() bool {
	return true
}

// RunPeer is invoked when a peer joins on the `eth` protocol. The handler
// should do any peer maintenance work, handshakes and validations. If all
// is passed, control should be given back to the `handler` to process the
// inbound messages going forward.
func (b *backend) RunPeer(peer *eth.Peer, handler eth.Handler) error {
	// Execute the Ethereum handshake
	var (
		genesis = b.chain.Genesis()
		head    = b.chain.CurrentHeader()
		hash    = head.Hash()
		number  = head.Number.Uint64()
		td      = b.chain.GetTd(hash, number)
	)
	forkID := forkid.NewID(b.chain.Config(), b.chain.Genesis().Hash(), number)
	if err := peer.Handshake(b.chain.Config().ChainID.Uint64(), td, hash, genesis.Hash(), forkID, forkid.NewFilter(b.chain)); err != nil {
		peer.Log().Debug("Ethereum handshake failed", "err", err)
		return err
	}
	peer.Log().Debug("Ethereum peer connected", "name", peer.Name())
	conn, err := b.peers.Add(peer)
	if err != nil {
		peer.Log().Warn("Failed to register peer in backend", "err", err)
		return err
	}

	defer b.peers.Remove(peer.ID())

	select {
	case b.newPeer <- conn:
	default:
		return errors.New("failed to enqueue peer connection")
	}

	// Handle incoming messages until the connection is torn down
	return handler(peer)
}

// PeerInfo retrieves all known `eth` information about a peer.
func (b *backend) PeerInfo(id enode.ID) interface{} {
	p := b.peers.Get(id.String())
	if p == nil {
		return nil
	}

	hash, td := p.Head()
	return &peerInfo{
		Version:    p.Version(),
		Difficulty: td,
		Head:       hash.Hex(),
	}
}

func (b *backend) Do(ctx context.Context) error {
	cacheDir := filepath.Join("./cache/exw/", string(b.networkID))
	if err := os.MkdirAll(cacheDir, 0755); err != nil && !os.IsExist(err) {
		return err
	}
	staticNodesFile := filepath.Join(cacheDir, "staticNodes.json")

	var staticNodes []*enode.Node
	staticNodesRaw := map[string]time.Time{}
	staticNodesContent, err := ioutil.ReadFile(staticNodesFile)
	if err == nil {
		must.OK(json.Unmarshal(staticNodesContent, &staticNodesRaw))
		staticNodes = make([]*enode.Node, 0, len(staticNodesRaw))
		for url := range staticNodesRaw {
			node, err := enode.Parse(enode.ValidSchemes, url)
			must.OK(err)
			staticNodes = append(staticNodes, node)
		}
	} else if !os.IsNotExist(err) {
		return err
	}

	b.peers = &peerSet{
		ch:     make(chan struct{}),
		peers:  map[string]*peerConnection{},
		peersP: map[*eth.Peer]*peerConnection{},
	}
	b.newPeer = make(chan *peerConnection, 100)

	db := rawdb.NewMemoryDatabase()
	_, err = b.network.Genesis.Commit(db)
	must.OK(err)

	chain, err := core.NewBlockChain(db,
		&core.CacheConfig{
			TrieCleanLimit: 256,
			TrieDirtyLimit: 256,
			TrieTimeLimit:  5 * time.Minute,
			SnapshotLimit:  256,
			SnapshotWait:   true,
		},
		b.network.ChainConfig,
		ethash.NewFaker(),
		vm.Config{},
		func(block *types.Block) bool { return true },
		nil,
	)
	must.OK(err)
	b.chain = chain

	privKey, err := ecdsa.GenerateKey(secp256k1.S256(), rand.Reader)
	must.OK(err)

	bootNodes := make([]*enode.Node, 0, len(b.network.BootNodes))
	for _, url := range b.network.BootNodes {
		if url != "" {
			node, err := enode.Parse(enode.ValidSchemes, url)
			must.OK(err)
			bootNodes = append(bootNodes, node)
		}
	}
	bootNodesV5 := make([]*enode.Node, 0, len(params.V5Bootnodes))
	for _, url := range params.V5Bootnodes {
		if url != "" {
			node, err := enode.Parse(enode.ValidSchemes, url)
			must.OK(err)
			bootNodesV5 = append(bootNodesV5, node)
		}
	}

	iter, err := dnsdisc.NewClient(dnsdisc.Config{}).NewIterator(params.KnownDNSNetwork(chain.Genesis().Hash(), "all"))
	must.OK(err)

	server := p2p.Server{
		Config: p2p.Config{
			PrivateKey:       privKey,
			Name:             common.MakeName("geth", "1.10.2"),
			MaxPeers:         100,
			MaxPendingPeers:  100,
			DialRatio:        1,
			BootstrapNodes:   bootNodes,
			BootstrapNodesV5: bootNodesV5,
			StaticNodes:      staticNodes,
			Protocols:        eth.MakeProtocols(b, b.network.ChainConfig.ChainID.Uint64(), iter),
			ListenAddr:       ":0",
			NAT:              nat.Any(),
			Logger:           log.Root(),
		},
	}

	goodPeer := make(chan string)
	req := make(chan *request, 100)
	reqPriority := make(chan *request, 100)
	recTransfers := make(chan transfers)
	sortedTransfers := make(chan transfers)
	aggregatedDays := make(chan *dailyStats)
	summarize := make(chan *dailyStats)

	g := parallel.NewGroup(ctx)
	g.Spawn("server", parallel.Fail, func(ctx context.Context) error {
		if err := server.Start(); err != nil {
			return err
		}
		defer server.Stop()
		defer b.peers.Close()
		<-ctx.Done()
		return ctx.Err()
	})

	var lastRequestedBlock uint64
	g.Spawn("peers", parallel.Fail, func(ctx context.Context) error {
		defer func() {
			must.OK(ioutil.WriteFile(staticNodesFile, must.Bytes(json.MarshalIndent(staticNodesRaw, "", "    ")), 0o644))
		}()

		for {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case peerConn := <-b.newPeer:
				g.Spawn("peer-"+peerConn.Peer.ID(), parallel.Continue, b.peer(peerConn, goodPeer, req, reqPriority, recTransfers, &lastRequestedBlock))
			case addr := <-goodPeer:
				if _, exists := staticNodesRaw[addr]; !exists {
					log.Info("Found new good peer", "addr", addr)
				}
				staticNodesRaw[addr] = time.Now().UTC()
			}
		}
	})

	var nextBlock uint64
	g.Spawn("sortTransfers", parallel.Continue, func(ctx context.Context) error {
		defer close(sortedTransfers)

		cache := map[uint64]transfers{}
		var finishBlock uint64
		for {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case t := <-recTransfers:
				block := t.Block.Number.Uint64()
				log.Debug("Received transfers", "block", block, "expected", nextBlock)
				if block < nextBlock {
					panic("this must not happen")
				}
				if _, exists := cache[block]; exists {
					panic("this must not happen")
				}
				if t.Block.Time >= today {
					if block == nextBlock {
						return nil
					}
					if block < finishBlock || finishBlock == 0 {
						finishBlock = block
					}
					continue
				}
				if block == nextBlock {
					sortedTransfers <- t
					nextBlock++
					for i := nextBlock; ; i++ {
						t, exists := cache[i]
						if !exists {
							break
						}
						delete(cache, i)
						sortedTransfers <- t
						nextBlock++
					}
					if nextBlock == finishBlock {
						return nil
					}
				} else {
					cache[block] = t
				}
			}
		}
	})

	var previous *dailyStats
	var current *dailyStats
	var reportBlock uint64
	g.Spawn("aggregateDays", parallel.Continue, func(ctx context.Context) error {
		defer close(aggregatedDays)
		defer func() {
			if previous != nil {
				if current != nil && current.Empty() {
					previous.LastBlock = current.LastBlock
					previous.Skip++
					current = nil
				}
				log.Info("Storing daily stats", "day", previous.day)
				aggregatedDays <- previous
			}
			if current != nil {
				log.Info("Storing daily stats", "day", current.day)
				aggregatedDays <- current
			}
		}()

		var lastReported uint64
		reportInterval := uint64(time.Hour / time.Second)

		for ts := range sortedTransfers {
			if ts.Block.Time >= lastReported {
				block := ts.Block.Number.Uint64()
				lastReported = ts.Block.Time + reportInterval
				log.Info("Blocks processed", "blocks", block-reportBlock+1,
					"time", time.Unix(int64(ts.Block.Time), 0).UTC())
				reportBlock = block
			}

			day := time.Unix(int64(ts.Block.Time), 0).UTC().Truncate(24 * time.Hour)
			if current != nil && day != current.day {
				if previous != nil && current.Empty() {
					previous.LastBlock = current.LastBlock
					previous.Skip++
				} else {
					if previous != nil {
						log.Info("Storing daily stats", "day", previous.day)
						aggregatedDays <- previous
					}
					previous = current
				}
				current = newDailyStats(day)
			} else if current == nil {
				current = newDailyStats(day)
			}
			current.LastBlock = ts.Block.Number.Uint64()
			if len(ts.Transfers) == 0 {
				continue
			}
			log.Info("Aggregating transfers", "block", ts.Block.Number.Uint64())
			for _, t := range ts.Transfers {
				current.Transactions.Add(current.Transactions, bigOne)
				if t.From != zeroAddress {
					balance := current.Balances[t.From]
					if balance == nil {
						current.Balances[t.From] = big.NewInt(0).Mul(t.Value, big.NewInt(-1))
					} else {
						balance.Sub(balance, t.Value)
						if balance.Cmp(bigZero) == 0 {
							delete(current.Balances, t.From)
						}
					}
				}

				if t.To != zeroAddress {
					balance := current.Balances[t.To]
					if balance == nil {
						current.Balances[t.To] = big.NewInt(0).Set(t.Value)
					} else {
						balance.Add(balance, t.Value)
						if balance.Cmp(bigZero) == 0 {
							delete(current.Balances, t.To)
						}
					}
				}
			}
		}
		return nil
	})

	archiveFile := must.OSFile(os.OpenFile(filepath.Join(cacheDir, "archive.json"), os.O_RDWR|os.O_APPEND|os.O_CREATE, 0644))
	defer archiveFile.Close()

	must.Any(archiveFile.Seek(0, io.SeekStart))
	archiveDec := json.NewDecoder(archiveFile)
	archiveEnc := json.NewEncoder(archiveFile)
	g.Spawn("storage", parallel.Continue, func(ctx context.Context) error {
		defer close(summarize)

		fileStat, err := archiveFile.Stat()
		must.OK(err)
		lastPos := fileStat.Size() - 1 // -1 due to \n
		var previousPos int64

		nextBlock = b.fromBlock
		log.Info("Processing archive stats")
		for {
			day := &dailyStats{}
			if err := archiveDec.Decode(day); err != nil {
				if errors.Is(err, io.EOF) {
					log.Info("Finished processing archive stats")
					break
				}
				log.Error("Decoding stats archive failed", "err", err)
				break
			}
			nextBlock = day.LastBlock + 1
			if archiveDec.InputOffset() >= lastPos {
				previous = day
				must.OK(archiveFile.Truncate(previousPos))
				must.OK(archiveFile.Sync())
				if must.Int64(archiveFile.Seek(0, io.SeekEnd)) != 0 {
					must.Any(archiveFile.WriteString("\n"))
				}
				break
			}
			previousPos = archiveDec.InputOffset()
			summarize <- day
		}

		reportBlock = nextBlock
		log.Info("Processing stats downloaded from peers", "block", nextBlock)
		lastRequestedBlock = nextBlock + uint64((cap(req)-1)*blocksPerRequest)
		for i, j := nextBlock, 0; j < cap(req); i, j = i+blocksPerRequest, j+1 {
			log.Debug("Enqueuing block request", "block", i)
			req <- newRequest(i)
		}
		for day := range aggregatedDays {
			must.OK(archiveEnc.Encode(day))
			summarize <- day
		}
		return nil
	})

	var summaries []*dailySummary
	previousSummary := newDailySummary(nil)
	balances := map[common.Address]*big.Int{}
	g.Spawn("summarize", parallel.Exit, func(ctx context.Context) error {
		for day := range summarize {
			current := newDailySummary(previousSummary)
			summaries = append(summaries, current)

			current.Transactions = day.Transactions
			current.Skip = day.Skip

			supply := big.NewInt(0)
			for a, b := range day.Balances {
				supply.Add(supply, b)
				if b.Cmp(bigZero) == 1 {
					current.Volume.Add(current.Volume, b)
				}
				if previousB := balances[a]; previousB != nil {
					previousB.Add(previousB, b)
					if previousB.Cmp(bigZero) == 0 {
						delete(balances, a)
						current.ActiveAccounts.Sub(current.ActiveAccounts, bigOne)
					}
				} else {
					balances[a] = big.NewInt(0).Set(b)
					current.ActiveAccounts.Add(current.ActiveAccounts, bigOne)
				}
			}
			current.TotalSupply.Add(current.TotalSupply, supply)
			if supply.Cmp(bigZero) == 1 {
				current.Volume.Sub(current.Volume, supply)
			}
			previousSummary = current
		}
		must.OK(ioutil.WriteFile(filepath.Join(cacheDir, "stats.json"), must.Bytes(json.MarshalIndent(summaries, "", "    ")), 0o644))
		return nil
	})

	return g.Wait()
}

func (b *backend) peer(conn *peerConnection, goodPeer chan<- string, req chan *request, reqPriority chan *request, tCh chan<- transfers, lastRequestedBlock *uint64) parallel.Task {
	peer := conn.Peer
	log := peer.Log()
	return func(ctx context.Context) error {
		if err := peer.RequestHeadersByNumber(b.controlBlock, 1, 0, false); err != nil {
			log.Warn("Sending request failed")
			return nil
		}

		ctxTest, cancelTest := context.WithTimeout(ctx, 10*time.Second)
		defer cancelTest()
		msg := conn.AwaitMessage(ctxTest, typeBlockHeadersPacket)
		if msg == nil {
			return nil
		}
		blocks := *msg.(*eth.BlockHeadersPacket)
		if len(blocks) != 1 {
			log.Warn("Control block not received")
			return nil
		}
		if blocks[0].Hash() != b.controlBlockHash {
			log.Warn("Invalid control block hash", "received", blocks[0].Hash().String())
			return nil
		}

		select {
		case <-ctx.Done():
			return ctx.Err()
		case goodPeer <- conn.Peer.Info().Enode:
		}

		for {
			var r *request
			select {
			case <-ctx.Done():
				return ctx.Err()
			case <-conn.Closed:
				return nil
			case r = <-reqPriority:
			default:
			}

			if r == nil {
			loop:
				for {
					select {
					case <-ctx.Done():
						return ctx.Err()
					case <-conn.Closed:
						return nil
					case <-conn.Rcv:
					case r = <-req:
						break loop
					}
				}
			}

			log.Debug("Received block request", "block", r.FromBlock)

			err := func() error {
				if err := peer.RequestHeadersByNumber(r.FromBlock, blocksPerRequest, 0, false); err != nil {
					return errors.New("sending request failed")
				}

				ctxReq1, cancelReq1 := context.WithTimeout(ctx, 10*time.Second)
				defer cancelReq1()

				msg := conn.AwaitMessage(ctxReq1, typeBlockHeadersPacket)
				if msg == nil {
					return errors.New("response not received before timeout")
				}
				blocks := *msg.(*eth.BlockHeadersPacket)
				if len(blocks) < blocksPerRequest {
					return errors.New("got less blocks than requested")
				}
				hashes := make([]common.Hash, 0, len(blocks))
				for _, block := range blocks {
					hashes = append(hashes, block.Hash())
				}

				log.Debug("Received block headers, sending receipts request")
				if err := peer.RequestReceipts(hashes); err != nil {
					return fmt.Errorf("sending receipts request failed: %w", err)
				}

				ctxReq2, cancelReq2 := context.WithTimeout(ctx, 10*time.Second)
				defer cancelReq2()

				msg = conn.AwaitMessage(ctxReq2, typeReceiptsPacket)
				if msg == nil {
					return errors.New("response not received before timeout")
				}

				receipts := *msg.(*eth.ReceiptsPacket)
				if len(receipts) < len(blocks) {
					return errors.New("got less receipts than requested")
				}
				r.LastBlock = blocks[len(receipts)-1]
				for i, block := range receipts {
					transfers := transfers{Block: blocks[i]}
					for _, tx := range block {
						for _, l := range tx.Logs {
							if l.Address != exwTokenAddress {
								continue
							}
							if len(l.Topics) > 0 && l.Topics[0] == exwTokenTransfer {
								t, err := erc20.UnpackTransfer(*l)
								if err != nil {
									log.Warn("Transfer parsing failed", "err", err)
									continue
								}
								if t.Value.Cmp(bigZero) == 0 {
									continue
								}
								transfers.Transfers = append(transfers.Transfers, t)
							}
						}
					}
					select {
					case <-ctx.Done():
						return ctx.Err()
					case tCh <- transfers:
						if transfers.Block.Time >= today {
							return nil
						}
					}
				}
				return nil
			}()

			if err != nil {
				log.Debug("Processing error", "err", err)

				select {
				case <-ctx.Done():
					return ctx.Err()
				case reqPriority <- newRequest(r.FromBlock):
					select {
					case <-ctx.Done():
						return ctx.Err()
					case <-time.After(5 * time.Second): // pause peer for a moment
					}
				}
				return nil
			}

			if r.LastBlock.Time >= today {
				return nil
			}

			nextRequestedBlock := atomic.AddUint64(lastRequestedBlock, blocksPerRequest)
			log.Debug("Enqueuing block request", "from", nextRequestedBlock)

			select {
			case <-ctx.Done():
				return ctx.Err()
			case req <- newRequest(nextRequestedBlock):
			}
		}
	}
}

func (b *backend) Handle(peer *eth.Peer, packet eth.Packet) error {
	conn := b.peers.GetConn(peer)
	if conn == nil {
		return errors.New("connection closed")
	}

	select {
	case <-conn.Closed:
		return errors.New("connection closed")
	case conn.Rcv <- packet:
	}

	return nil
}

type network struct {
	ChainConfig *params.ChainConfig
	Genesis     *core.Genesis
	BootNodes   []string
}

var networks = map[config.Blockchain]network{
	config.BlockchainMainnet: {
		ChainConfig: params.MainnetChainConfig,
		Genesis:     core.DefaultGenesisBlock(),
		BootNodes:   params.MainnetBootnodes,
	},
	config.BlockchainRopsten: {
		ChainConfig: params.RopstenChainConfig,
		Genesis:     core.DefaultRopstenGenesisBlock(),
		BootNodes:   params.RopstenBootnodes,
	},
}

type logAdapter struct {
	log zapcore.Core
}

func convertLevel(level log.Lvl) zapcore.Level {
	switch level {
	case log.LvlCrit:
		return zapcore.FatalLevel
	case log.LvlError:
		return zapcore.ErrorLevel
	case log.LvlWarn:
		return zapcore.WarnLevel
	case log.LvlInfo:
		return zapcore.InfoLevel
	case log.LvlDebug:
		return zapcore.DebugLevel
	case log.LvlTrace:
		return zapcore.DebugLevel
	default:
		panic(fmt.Sprintf("unknown level %d", level))
	}
}

func (la *logAdapter) Log(r *log.Record) error {
	frame := r.Call.Frame()
	zapEntry := zapcore.Entry{
		Level:   convertLevel(r.Lvl),
		Time:    r.Time,
		Message: r.Msg,
		Caller: zapcore.EntryCaller{
			Defined: true,
			PC:      frame.PC,
			File:    frame.File,
			Line:    frame.Line,
		},
	}
	fields := make([]zapcore.Field, 0, len(r.Ctx)/2)
	for i := 0; i < len(r.Ctx); i += 2 {
		if len(r.Ctx) == i+1 {
			break
		}
		fields = append(fields, zap.Any(r.Ctx[i].(string), r.Ctx[i+1]))
	}
	return la.log.Write(zapEntry, fields)
}

// Main is an entry point for stats
func Main(cfg config.Config, appRunner run.AppRunner) {
	appRunner(func(ctx context.Context) error {
		log.Root().SetHandler(log.LvlFilterHandler(log.LvlInfo, &logAdapter{log: logger.Get(ctx).Core()}))
		backend := &backend{
			network:          networks[cfg.Blockchain.Network],
			networkID:        cfg.Blockchain.Network,
			fromBlock:        cfg.EXW.FromBlock,
			controlBlock:     cfg.Blockchain.ControlBlock,
			controlBlockHash: common.HexToHash(cfg.Blockchain.ControlBlockHash),
		}

		return backend.Do(ctx)
	})
}
