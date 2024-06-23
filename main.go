package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/rand"
	"crypto/sha256"
	"encoding/csv"
	"encoding/gob"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"image/color"
	"io"
	"io/ioutil"
	"log"
	"math"
	mrand "math/rand"
	"os"
	"os/signal"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/boltdb/bolt"
	"github.com/davecgh/go-spew/spew"
	shell "github.com/ipfs/go-ipfs-api"
	golog "github.com/ipfs/go-log"
	libp2p "github.com/libp2p/go-libp2p"
	dht "github.com/libp2p/go-libp2p-kad-dht"
	pubsub "github.com/libp2p/go-libp2p-pubsub"
	"github.com/libp2p/go-libp2p/core/crypto"
	host "github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/network"
	peer "github.com/libp2p/go-libp2p/core/peer"
	pstore "github.com/libp2p/go-libp2p/core/peerstore"
	"github.com/libp2p/go-libp2p/p2p/discovery/mdns"
	"github.com/muesli/clusters"
	"github.com/muesli/kmeans"
	ma "github.com/multiformats/go-multiaddr"
	gologging "github.com/whyrusleeping/go-logging"
	"gonum.org/v1/plot"
	"gonum.org/v1/plot/plotter"
	"gonum.org/v1/plot/vg"
)

var ps *pubsub.PubSub

type ValidationResult struct {
	NBCluster    int      `json:"nbCluster"`
	MinerResults []Kmeans `json:"minerResults"`
}

type ValidationRequest struct {
	SubgroupName string      `json:"subgroup_name"`
	Centroids    [][]float64 `json:"centroids"`
}
type ClusteringResult struct {
	Data            [][]int     `json:"data"`
	Labels          []int       `json:"labels"`
	Representatives [][]float64 `json:"representatives"`
}

// Global variable to store dataset partitions assigned to miners
var datasetPartitions []DatasetPartition
var startTimeFormatted string

// Define a map to store NBCluster channels for each miner
var minerNBClusterChannels = make(map[string]chan int)

const difficulty = 5

var clusteringResultsCh <-chan clusters.Clusters
var silhouetteScore float64
var silhouetteScores map[peer.ID]float64

type discoveryNotifee struct {
	h host.Host
}

// DataMessage represents the message containing data to be sent
type DataMessage struct {
	Data [][]float64 `json:"data"`
}

const DiscoveryServiceTag = "my-discovery-service"

var peerID peer.ID
var api *shell.Shell

// PerformanceMetrics holds the performance metrics for each clustering approach.
type PerformanceMetrics struct {
	ApproachName string
	MetricValue  float64
}

var NBCluster int
var roleValue string

var err error
var data []int
var Centroidss []float64

var startTime, endTime time.Time

const dbFile = "blockchain.db"
const blocksBucket = "blocks"

type PeerRole struct {
	PeerID peer.ID
	Role   string
}

var PeerRoles []PeerRole

type Configuration struct {
	ConnectedPeers int        `json:"connectedPeers"`
	NumValidators  int        `json:"numValidators"`
	NumMiners      int        `json:"numMiners"`
	PeerRoles      []PeerRole `json:"peerRoles"`
}

// Define a struct to represent dataset partitions
type DatasetPartition struct {
	MinerID      string      // Identifier of the miner
	Partition    [][]float64 // Data partition assigned to the miner
	NBCluster    int         // Number of clusters for clustering
	ClusterID    string      // Identifier for the clustering result
	PartitionCID string
}

var subgroups map[string][]peer.ID
var (
	connectedPeers int // Variable to keep track of the number of connected peers
	numValidators  int // Variable to keep track of the number of Validators
	numMiners      int // Variable to keep track of the number of Miners
	role           string
	peerRoles      = make([]PeerRole, 0)
)

// Block represents each 'item' in the blockchain
type Block struct {
	Index        int
	Timestamp    string
	NBCluster    int
	Data         [][]float64
	PrevHash     string
	Hash         string
	Performance  float64
	KmeansResult Kmeans
}

// Global channel to receive NBCluster from the dataholder
var nbcReceived = make(chan int)

type Task struct {
	Index     int
	Data      [][][]float64
	NBCluster int
}

var isconverged bool

// Blockchain is a series of validated Blocks
var Blockchain []Block

/*
	type Blockchainn struct {
		tip []byte
		db  *bolt.DB
	}
*/
type Vector []float64

var dataPartitions [][][]float64
var Clusters []Convertclusters
var ar Convertclusters
var datas [][]float64
var NodeType string

// bcServer handles incoming concurrent Blocks
var bcServer chan []Block
var mutex = &sync.Mutex{}
var newBlock Block
var db *bolt.DB

type BlockchainIterator struct {
	currentHash []byte
	db          *bolt.DB
}

type Convertclusters struct {
	individu []float64
	cluster  int
}

type Kmeans struct {
	MinerID         string      `json:"minerID"`
	Data            [][]float64 `json:"data"`
	Labels          []int       `json:"labels"`
	Representatives [][]float64 `json:"representatives"`
}

var threshold = 0.0

// SubgroupResult represents the results from a subgroup of Miners.
type SubgroupResult struct {
	Results []ClusteringResult
}

// MinerResults represents the results produced by a Miner.
type MinerResults struct {
	PeerID            peer.ID
	Results           []ClusteringResult
	AggregatedResults AggregatedResult
}

// AggregatedResult represents the aggregated result of clustering.
type AggregatedResult struct {
	AggregatedData string // Define the fields of AggregatedResult as needed.
}

// SHA256 hashing
func calculateHash(block Block) string {
	record := string(block.Index) + block.Timestamp + string(block.NBCluster) + block.PrevHash
	h := sha256.New()
	h.Write([]byte(record))
	hashed := h.Sum(nil)
	return hex.EncodeToString(hashed)
}

// calculateHash takes a string as input and returns its SHA256 hash as a hex string.
// calculateHashData takes a [][]float64 as input and returns its SHA256 hash as a hex string.
func calculateHashData(input [][]float64) string {
	// Create a buffer to hold the byte representation of the input
	var buf bytes.Buffer

	// Create a new encoder that will write to the buffer
	enc := gob.NewEncoder(&buf)

	// Encode the input ([][]float64) into the buffer
	err := enc.Encode(input)
	if err != nil {
		log.Fatalf("Failed to encode input: %v", err)
	}

	// Compute the SHA256 hash of the encoded data
	hash := sha256.Sum256(buf.Bytes())

	// Return the hexadecimal encoding of the hash
	return hex.EncodeToString(hash[:])
}

// create a new block using previous block's hash
func generateBlock(oldBlock Block, NBCluster int, sil float64, kmeansResult Kmeans) (Block, error) {

	var newBlock Block
	t := time.Now()

	newBlock.Index = oldBlock.Index + 1
	newBlock.Timestamp = t.String()
	newBlock.NBCluster = NBCluster
	newBlock.Data = datas
	newBlock.PrevHash = oldBlock.Hash
	newBlock.Performance = sil
	//	newBlock.Centroids = kmeansResult.Representatives
	newBlock.Hash = calculateHash(newBlock)

	fmt.Println("ani dakhal generer block")
	return newBlock, nil
}

// CreateBlockFromResults creates a new block using the previous block's hash and mining results.
func CreateBlockFromResults(oldBlock Block, NBCluster int, sil float64, kmeansResult Kmeans) (Block, error) {
	var newBlock Block
	t := time.Now()

	newBlock.Index = oldBlock.Index + 1
	newBlock.Timestamp = t.String()
	newBlock.NBCluster = NBCluster
	newBlock.Data = kmeansResult.Data // Assuming kmeansResult has a Data field.
	newBlock.PrevHash = oldBlock.Hash
	newBlock.Performance = sil
	newBlock.KmeansResult = kmeansResult
	newBlock.Hash = calculateHash(newBlock)

	return newBlock, nil
}

func PerformKmeansClustering(NBCluster int, datass [][]float64) (clusters.Clusters, error) {

	// Add data points to the slice
	fmt.Println("Proof of Clustering  Consensus:")
	fmt.Println("datas in  KmeansClustering maining partition for miner")

	var d clusters.Observations
	for x := 0; x < 102; x++ {
		d = append(d, clusters.Coordinates{
			mrand.Float64(),
			mrand.Float64(),
		})
	}

	// Partition the data points into NBCluster clusters
	kmm := kmeans.New()
	resultingClusters, err := kmm.Partition(d, NBCluster)
	if err != nil {
		return nil, err
	}

	return resultingClusters, nil
}

// generateComparisonPlot creates a bar chart to compare the performance of different clustering approaches.
func generateComparisonPlot(metrics []PerformanceMetrics, metricName, filename string) {
	p := plot.New()
	if err != nil {
		log.Fatalf("Could not create plot: %v", err)
	}

	p.Title.Text = "Clustering Performance Comparison "
	p.Y.Label.Text = metricName

	// Create bars for the performance metrics
	w := vg.Points(40) // Bar width
	bars := make(plotter.Values, len(metrics))

	for i, metric := range metrics {
		bars[i] = metric.MetricValue
	}

	bar, err := plotter.NewBarChart(bars, w)
	if err != nil {
		log.Fatalf("Could not create bar chart: %v", err)
	}
	bar.LineStyle.Width = vg.Length(0)
	bar.Color = color.RGBA{R: 0, G: 0, B: 255, A: 255} // Set the bar color

	// Add the bar chart to the plot
	p.Add(bar)

	// Set the X-axis labels
	names := make([]string, len(metrics))
	for i, metric := range metrics {
		names[i] = metric.ApproachName
	}
	p.NominalX(names...)

	// Save the plot to a PNG file
	if err := p.Save(6*vg.Inch, 4*vg.Inch, filename); err != nil {
		log.Fatalf("Could not save plot: %v", err)
	}
}
func generateComparisongroupedPlot(metrics1, metrics2 []PerformanceMetrics, metricName1, metricName2, filename string) {
	p := plot.New()
	if err != nil {
		log.Fatalf("Could not create plot: %v", err)
	}

	p.Title.Text = "Clustering Performance Comparison  MallCustomers dataset  "
	p.Y.Label.Text = "Metric Values"

	// Create bars for the first set of performance metrics
	w := vg.Points(20) // Bar width
	bars1 := make(plotter.Values, len(metrics1))
	for i, metric := range metrics1 {
		bars1[i] = metric.MetricValue
	}

	bar1, err := plotter.NewBarChart(bars1, w)
	if err != nil {
		log.Fatalf("Could not create bar chart for metrics1: %v", err)
	}
	bar1.LineStyle.Width = vg.Length(0)

	bar1.Color = color.RGBA{R: 0, G: 0, B: 255, A: 255} // Set the bar color for metrics1

	// Create bars for the second set of performance metrics
	bars2 := make(plotter.Values, len(metrics2))
	for i, metric := range metrics2 {
		bars2[i] = metric.MetricValue
	}

	bar2, err := plotter.NewBarChart(bars2, w)
	if err != nil {
		log.Fatalf("Could not create bar chart for metrics2: %v", err)
	}
	bar2.LineStyle.Width = vg.Length(0)
	bar2.Color = color.RGBA{R: 255, G: 0, B: 0, A: 255} // Set the bar color for metrics2

	// Adjust the positions of the bars
	offset := w / 2
	bar1.Offset = -offset
	bar2.Offset = offset
	// Add legends for each set of bars
	p.Legend.Add(metricName1, bar1)
	p.Legend.Add(metricName2, bar2)
	p.Legend.Top = true
	// Add the bar charts to the plot
	p.Add(bar1, bar2)

	// Set the X-axis labels
	names := make([]string, len(metrics1))
	for i, metric := range metrics1 {
		names[i] = metric.ApproachName
	}
	p.NominalX(names...)

	// Save the plot to a PNG file
	if err := p.Save(10*vg.Inch, 6*vg.Inch, filename); err != nil {
		log.Fatalf("Could not save plot: %v", err)
	}
}
func generateComparisongroupedPlotiris(metrics1, metrics2 []PerformanceMetrics, metricName1, metricName2, filename string) {
	p := plot.New()
	if err != nil {
		log.Fatalf("Could not create plot: %v", err)
	}

	p.Title.Text = "Clustering Performance Comparison  Iris dataset  "
	p.Y.Label.Text = "Metric Values"

	// Create bars for the first set of performance metrics
	w := vg.Points(20) // Bar width
	bars1 := make(plotter.Values, len(metrics1))
	for i, metric := range metrics1 {
		bars1[i] = metric.MetricValue
	}

	bar1, err := plotter.NewBarChart(bars1, w)
	if err != nil {
		log.Fatalf("Could not create bar chart for metrics1: %v", err)
	}
	bar1.LineStyle.Width = vg.Length(0)
	bar1.Color = color.RGBA{R: 0, G: 0, B: 255, A: 255} // Set the bar color for metrics1

	// Create bars for the second set of performance metrics
	bars2 := make(plotter.Values, len(metrics2))
	for i, metric := range metrics2 {
		bars2[i] = metric.MetricValue
	}

	bar2, err := plotter.NewBarChart(bars2, w)
	if err != nil {
		log.Fatalf("Could not create bar chart for metrics2: %v", err)
	}
	bar2.LineStyle.Width = vg.Length(0)
	bar2.Color = color.RGBA{R: 255, G: 0, B: 0, A: 255} // Set the bar color for metrics2

	// Adjust the positions of the bars
	offset := w / 2
	bar1.Offset = -offset
	bar2.Offset = offset
	// Add legends for each set of bars
	p.Legend.Add(metricName1, bar1)
	p.Legend.Add(metricName2, bar2)
	p.Legend.Top = true
	// Add the bar charts to the plot
	p.Add(bar1, bar2)

	// Set the X-axis labels
	names := make([]string, len(metrics1))
	for i, metric := range metrics1 {
		names[i] = metric.ApproachName
	}
	p.NominalX(names...)

	// Save the plot to a PNG file
	if err := p.Save(10*vg.Inch, 6*vg.Inch, filename); err != nil {
		log.Fatalf("Could not save plot: %v", err)
	}
}

func KmeansClustering(data [][]float64, numClusters int) (*Kmeans, error) {
	fmt.Println("Proof of Clustering Consensus:")
	fmt.Println("Data in KmeansClustering for mining partition:")
	fmt.Println(data)
	log.Println("After displaying data")
	log.Println(numClusters)

	// Seed the random number generator
	mrand.Seed(time.Now().UnixNano())

	// Check for invalid inputs
	if numClusters <= 0 {
		return nil, fmt.Errorf("KMeans: Number of clusters (numClusters) cannot be less than or equal to zero")
	}
	if data == nil {
		return nil, fmt.Errorf("KMeans: Data cannot be nil")
	}
	if len(data) == 0 {
		return nil, fmt.Errorf("KMeans: Data cannot be empty")
	}

	// Initialize a Kmeans instance with input data
	km := &Kmeans{
		Data: data,
	}

	// Transpose the input data
	transposedData := Transpose(km.Data)
	log.Println("Transposed Data")
	fmt.Println(transposedData)

	// Calculate the minimum and maximum values for each feature
	var minMax [][]float64
	for _, featureValues := range transposedData {
		min := featureValues[0]
		max := featureValues[0]
		for _, value := range featureValues {
			min = math.Min(min, value)
			max = math.Max(max, value)
		}
		minMax = append(minMax, []float64{min, max})
	}

	// Initialize cluster representatives
	for i := 0; i < numClusters; i++ {
		km.Representatives = append(km.Representatives, make([]float64, len(minMax)))
	}

	// Initialize cluster representatives with random values within the range of feature values
	for i := 0; i < numClusters; i++ {
		for j := 0; j < len(minMax); j++ {
			km.Representatives[i][j] = mrand.Float64()*(minMax[j][1]-minMax[j][0]) + minMax[j][0]
		}
	}
	fmt.Println("km.representatives:")
	for _, r := range km.Representatives {
		fmt.Println(r)
	}

	// Define a maximum number of iterations to avoid infinite loops
	maxIterations := 1000 // You can adjust this value as needed

	// Iteratively update cluster representatives until convergence or reaching the maximum iterations
	for iteration := 0; iteration < maxIterations; iteration++ {
		var tempRepresentatives [][]float64

		// Update cluster representatives based on data points
		for clusterIndex, _ := range km.Representatives {
			var groupedData [][]float64

			for dataPointIndex, dataPoint := range km.Data {
				if dataPointIndex < len(km.Labels) && km.Labels[dataPointIndex] == clusterIndex {
					groupedData = append(groupedData, dataPoint)
				} else {
					fmt.Printf("Invalid dataPointIndex: %d (length of labels: %d)\n", dataPointIndex, len(km.Labels))
				}
			}

			if len(groupedData) != 0 {
				transposedGroup := Transpose(groupedData)
				updated := []float64{}
				for _, featureValues := range transposedGroup {
					sum := 0.0
					for _, value := range featureValues {
						sum += value
					}
					updated = append(updated, sum/float64(len(featureValues)))
				}
				tempRepresentatives = append(tempRepresentatives, updated)
			}
		}

		fmt.Println("km.representatives:")
		for _, r := range km.Representatives {
			fmt.Println(r)
		}

		// Update cluster representatives and labels
		km.Representatives = tempRepresentatives

		tempLabel := []int{}
		for _, dataPoint := range km.Data {
			var distances []float64
			for _, representative := range km.Representatives {
				distances = append(distances, Dist(dataPoint, representative))
			}
			tempLabel = append(tempLabel, ArgMin(distances))
		}

		// Check for convergence
		if reflect.DeepEqual(km.Labels, tempLabel) {
			fmt.Println("**Converged, Work done!!!**")
			break
		}

		km.Labels = tempLabel
	}

	return km, nil
}

func isHashValid(hash string, difficulty int) bool {
	prefix := strings.Repeat("0", difficulty)
	return strings.HasPrefix(hash, prefix)
}

// make sure block is valid by checking index, and comparing the hash of the previous block
func isBlockValid(newBlock, oldBlock Block) bool {
	if oldBlock.Index+1 != newBlock.Index {
		return false
	}

	if oldBlock.Hash != newBlock.PrevHash {
		return false
	}

	if calculateHash(newBlock) != newBlock.Hash {
		return false
	}

	return true
}

// make sure the chain we're checking is longer than the current blockchain
func replaceChain(newBlocks []Block) {
	if len(newBlocks) > len(Blockchain) {
		Blockchain = newBlocks
	}
}

func readNumberOfClusters() int {
	fmt.Println("Enter the Number of Cluster: ")
	stdReader := bufio.NewReader(os.Stdin)

	sendNBCluster, err := stdReader.ReadString('\n')
	if err != nil {
		log.Fatal(err)
	}
	sendNBCluster = strings.Replace(sendNBCluster, "\n", "", -1)
	NBCluster, err := strconv.Atoi(sendNBCluster)
	if err != nil {
		log.Fatal(err)
	}
	return NBCluster
}

// generateSilhouetteScorePlot creates a bar chart of silhouette scores and saves it to a file.
func generateSilhouetteScorePlot(scores map[string]float64, filename string) {
	p := plot.New()
	if err != nil {
		log.Fatalf("Could not create plot: %v", err)
	}

	p.Title.Text = "Silhouette Scores"
	p.Y.Label.Text = "Score"

	// Create bars for the scores
	w := vg.Points(20)
	bars := make(plotter.Values, len(scores))

	i := 0
	for _, score := range scores {
		bars[i] = score
		i++
	}

	bar, err := plotter.NewBarChart(bars, w)
	if err != nil {
		log.Fatalf("Could not create bar chart: %v", err)
	}
	bar.LineStyle.Width = vg.Length(0)
	bar.Color = color.RGBA{R: 0, G: 0, B: 255, A: 255} // Set the bar color to blue

	// Add the bar chart to the plot
	p.Add(bar)

	// Set the X-axis labels
	labels := make([]string, len(scores))
	i = 0
	for label := range scores {
		labels[i] = label
		i++
	}
	p.NominalX(labels...)

	// Save the plot to a PNG file
	if err := p.Save(4*vg.Inch, 4*vg.Inch, filename); err != nil {
		log.Fatalf("Could not save plot: %v", err)
	}
}
func main() {
	// Initialize the IPFS client
	api := shell.NewShell("localhost:5001")

	// Example usage: Fetch the CID of a file from IPFS
	cid, err := api.Add(strings.NewReader("Hello, IPFS!"))
	if err != nil {
		log.Fatal("Error adding file to IPFS:", err)
	}
	log.Println("CID:", cid)

	// Example data: silhouette scores for two clustering algorithms
	scores := map[string][]float64{
		"K-means (ClusterChain)": {0.338, 0.335, 0.476, 0.466, 0.382},
		"K-means (PoC)":          {0.560, 0.605, 0.560, 0.511, 0.429},
	}

	// Example colors for each line
	colors := map[string]color.Color{
		"K-means (ClusterChain)": color.RGBA{R: 0, G: 0, B: 255, A: 255}, // blue
		"K-means (PoC)":          color.RGBA{R: 255, G: 0, B: 0, A: 255}, // red
	}

	filename := "silhouette_scores.png"
	generateSilhouetteScorePlot2(scores, colors, filename)

	// Example performance metrics for silhouette scores
	metrics := []PerformanceMetrics{
		{"K-means (PoC)", 0.56},
		{"K-means (ClusterChain)", 0.87},
		{"Traditional K-means", 0.53},
	}
	generateComparisonPlot(metrics, "Clustering Performance(s) Silhouette K=3", "clustering_performance2.png")

	// Example performance metrics for Davies-Bouldin index
	metrics = []PerformanceMetrics{
		{"K-means (PoC)", 0.56},
		{"K-means (ClusterChain)", 0.476},
		{"Traditional K-means", 0.20},
	}
	generateComparisonPlot(metrics, "Clustering Performance(s) Davies-Bouldin Index K=4", "performancemetricautree.png")

	// Grouped bar chart example
	metric1 := []PerformanceMetrics{
		{"K-means (PoC)", 0.631},
		{"K-means (ClusterChain)", 0.706},
		{"Traditional K-means", 0.685},
	}
	metric2 := []PerformanceMetrics{
		{"K-means (PoC)", 0.327},
		{"K-means (ClusterChain)", 0.217},
		{"Traditional K-means", 0.217},
	}
	generateComparisongroupedPlotiris(metric1, metric2, "Silhouette", "Davies-Bouldin Index", "performancemetrigroupediris.png")

	metric1 = []PerformanceMetrics{
		{"K-means (PoC)", 0.416},
		{"K-means (ClusterChain)", 0.398},
		{"Traditional K-means", 0.356},
	}
	metric2 = []PerformanceMetrics{
		{"K-means (PoC)", 0.241},
		{"K-means (ClusterChain)", 0.312},
		{"Traditional K-means", 0.362},
	}
	generateComparisongroupedPlot(metric1, metric2, "Silhouette", "Davies-Bouldin Index", "performancemetrigroupedmall.png")

	golog.SetAllLoggers(golog.LogLevel(gologging.INFO))

	// Parse command-line flags
	listenF := flag.Int("l", 0, "wait for incoming connections")
	target := flag.String("d", "", "target peer to dial")
	//secio := flag.Bool("secio", false, "enable secio")
	//seed := flag.Int64("seed", 0, "set random seed for id generation")
	role := flag.String("role", "Dataholder", "peer role (Miner, or Validator)")
	flag.Parse()
	config.PeerRoles = make([]PeerRole, 0)
	// Validate command-line arguments
	if *listenF == 0 {
		log.Fatal("Please provide a port to bind on with -l")
	}
	// Initialize the blockchain with the genesis block
	startTime = time.Now()
	log.Println("Start Timeeeee:", startTime)
	startTimeFormatted = startTime.Format("15:04:05.999999999 -0700 MST")

	listenPort := 0 // 0 means to listen on a random port

	discoveryServiceTag := "my-discovery-service"

	ctx := context.Background()
	basicHost, ps, err := makeBasicHost(ctx, listenPort, discoveryServiceTag)
	if err != nil {
		panic(err)
	}

	defer basicHost.Close()

	log.Printf("Role: %s\n", *role) // Log the role here
	topicName := "example-topic"
	//topicResultName := "KM-result"
	//SiltopicName := "topic-silhouette-score"
	topic, sub, err := setupPubSub(ctx, ps, topicName)
	if err != nil {
		panic(err)
	}
	defer sub.Cancel()

	//defer subsil.Cancel()

	roleValue := *role
	peerID := basicHost.ID()
	log.Printf("I am a %s and I have the ID %s", roleValue, peerID)
	newPeerRole := PeerRole{
		PeerID: peerID,
		Role:   roleValue,
	}
	peerRoles = append(peerRoles, newPeerRole)

	var mutex sync.Mutex

	addPeerToRoles := func(peerID peer.ID, role string) {
		mutex.Lock()
		defer mutex.Unlock()
		newPeerRole.PeerID = peerID
		newPeerRole.Role = role
		peerRoles = append(peerRoles, newPeerRole)
	}

	for _, peerID := range basicHost.Network().Peers() {
		role, _ := basicHost.Peerstore().Get(peerID, "Role")
		roleValue, ok := role.(string)
		if !ok {
			fmt.Printf("Error: Role value for peer %s is not a string\n", peerID)
			continue
		}
		addPeerToRoles(peerID, roleValue)
	}

	if *target != "" {
		roleValue = *role

		log.Println("avant connectToPeer ")
		//	err := connectToPeer(basicHost, *target, roleValue)
		log.Println("apres connectToPeer ")
		if err != nil {
			log.Fatal(err)
		}

		// Initialize the blockchain with the genesis block
		startTime = time.Now()
		log.Println("Start Timeeeee:", startTime)
		startTimeFormatted = startTime.Format("15:04:05.999999999 -0700 MST")
		initBlockchain()
		log.Println("listening for connections")
		log.Println("apres initblockchain")
	}

	var wg sync.WaitGroup
	var minerPeerIDs []peer.ID
	for _, peerRole := range peerRoles {
		// Vérifier si le rôle est "Miner"
		fmt.Println("peerRole.Roler", peerRole.Role)
		if peerRole.Role == "Miner" {
			fmt.Println(peerRole.PeerID)
			// Ajouter l'identifiant du pair à la tranche des pairs Miners
			minerPeerIDs = append(minerPeerIDs, peerRole.PeerID)
		}

	}
	log.Println("listes des minerss ", len(minerPeerIDs))
	for {
		// Attendre que le goroutine de connexion se termine
		wg.Wait()
		if roleValue == "Dataholder" {
			log.Println("I am a Dataholder")
			mutex.Lock()
			mutex.Unlock()
			setPeerRole(peerID, "Dataholder")

			NBCluster := readNumberOfClusters()
			log.Println("The number of clusters is:", NBCluster)
			errr := topic.Publish(ctx, []byte(strconv.Itoa(NBCluster)))
			if errr != nil {
				log.Println("Error broadcasting number of clusters:", err)
			}
			log.Println("Transmitted number of clusters")

			// Broadcast NBCluster to all peers
			broadcastNBCluster(basicHost, NBCluster)

		} else if roleValue == "Miner" {
			log.Println("I am a Miner")

			// Step 1: Divide Miners into Subgroups
			subgroups := make(map[string][]PeerRole)
			for _, peerRole := range peerRoles {
				if peerRole.Role == "Miner" {
					subgroups["subgroup1"] = append(subgroups["subgroup1"], peerRole)
				}
			}

			// Step 2: Perform Local Clustering on each miner's data part
			for _, subgroup := range subgroups {
				for _, peerRole := range subgroup {
					wg.Add(1)
					go func(peerRole PeerRole) {
						defer wg.Done()
						msg, err := sub.Next(ctx)
						if err != nil {
							fmt.Println("Error reading message", err)
							return
						}
						fmt.Printf("Miner received message: %s\n", string(msg.Data))

						time.Sleep(3 * time.Second)

						NBClusterReceived, err := strconv.Atoi(string(msg.Data))
						if err != nil {
							log.Println("Error converting message data: ", err)
						}

						fmt.Printf("Miner received NBCluster: %d\n", NBClusterReceived)

						scanner := bufio.NewScanner(os.Stdin)
						fmt.Println("Please enter the path to the CSV file: ")
						scanner.Scan()
						filePath := scanner.Text()

						if strings.TrimSpace(filePath) == "" {
							fmt.Println("File path cannot be empty.")
							return
						}

						if _, err := os.Stat(filePath); os.IsNotExist(err) {
							fmt.Printf("The file '%s' does not exist.\n", filePath)
							return
						}

						fmt.Printf("CSV file path: %s\n", filePath)

						log.Println("Performing clustering operation")
						clusteringResults := performClustering(peerRole.PeerID)
						log.Println("Clustering operation completed")

						subgroupResult := SubgroupResult{}
						for _, result := range clusteringResults {
							subgroupResult.Results = append(subgroupResult.Results, result)
						}

						aggregatedResults := AggregateSubgroupResults(subgroupResult)
						log.Printf("Miner %s received aggregated results: %v\n", peerID, aggregatedResults)
						// Share results with peers
						log.Printf("Aggregated results: %v\n", aggregatedResults)
						minerResults := MinerResults{
							PeerID:            peerID,
							Results:           clusteringResults,
							AggregatedResults: aggregatedResults,
						}
						shareResultsWithPeers(minerResults)
						//	block, err := CreateBlockFromResults(oldBlock Block, NBCluster int, sil float64, kmeansResult Kmeans minerResults)
						if err != nil {
							log.Println("Error converting message data: ", err)
						}
						// Broadcast the block to all peers in the subgroup
						//broadcastBlock(subgroup, block)

						fmt.Printf("Miner %s completed local clustering and block creation\n", peerRole.PeerID)
					}(peerRole)
				}
			}
			wg.Wait()

		} else if roleValue == "Validator" {
			log.Println("I am a Validator")

			mutex.Lock()
			mutex.Unlock()
			setPeerRole(peerID, "Validator")

			wg.Add(1)
			go func() {
				defer wg.Done()
				for {

					/*msg, err := subsil.Next(ctx)
					if err != nil {
						log.Println("Error reading message from PubSub topic:", err)
						return
					}
					log.Println("Received message:", string(msg.Data))

					newBlock, err := CreateBlock([]Transaction{Transaction{}})
					if err != nil {
						log.Println("Error creating new block:", err)
						continue
					}
					isValid := validateBlock(newBlock)
					if isValid {
						blockchain = append(blockchain, newBlock)
						fmt.Println("Block added to the blockchain")
					} else {
						fmt.Println("Invalid block received")
					}*/
				}
			}()
			wg.Wait()
		}
	}
	select {}
}
func AggregateSubgroupResults(subgroupResult SubgroupResult) AggregatedResult {
	var aggregatedData string
	for _, result := range subgroupResult.Results {
		aggregatedData += dataToString(result.Data)
	}

	return AggregatedResult{
		AggregatedData: aggregatedData,
	}
}

// Convert 2D slice of integers to a string representation
func dataToString(data [][]int) string {
	var buffer bytes.Buffer
	for _, row := range data {
		for _, value := range row {
			buffer.WriteString(fmt.Sprintf("%d ", value))
		}
		buffer.WriteString(";")
	}
	return buffer.String()
}

func shareResultsWithPeers(minerResults MinerResults) {
	// Implement the logic to share the results with other peers
	log.Printf("Sharing results with peers: %v\n", minerResults)
	// Example: Publish results to a PubSub topic or send directly to peers
}

func calculateDaviesBouldinIndex(km Kmeans) float64 {
	dbIndex := 0.0
	for i := 0; i < len(km.Representatives); i++ {
		maxDb := 0.0
		for j := 0; j < len(km.Representatives); j++ {
			if i != j {
				dist := calculateEuclideanDistance(km.Representatives[i], km.Representatives[j])
				sigma_i := calculateDispersion(km.Data, km.Labels, km.Representatives, i)
				sigma_j := calculateDispersion(km.Data, km.Labels, km.Representatives, j)
				db := (sigma_i + sigma_j) / dist
				if db > maxDb {
					maxDb = db
				}
			}
		}
		dbIndex += maxDb
	}
	dbIndex /= float64(len(km.Representatives))
	return dbIndex
}
func calculateDispersion(data [][]float64, labels []int, representatives [][]float64, clusterIndex int) float64 {
	var dispersion float64
	for i, d := range data {
		if labels[i] == clusterIndex {
			dist := calculateEuclideanDistance(d, representatives[clusterIndex])
			dispersion += dist
		}
	}
	return dispersion / float64(len(data))
}
func broadcastSilhouetteScore(score float64, topic *pubsub.Topic) error {
	// Convert the score into a string or byte slice for transmission
	scoreBytes := []byte(fmt.Sprintf("%f", score))

	// Publish the score to the given topic
	err := topic.Publish(context.Background(), scoreBytes)
	if err != nil {
		log.Printf("Failed to broadcast silhouette score: %s", err)
		return err
	}

	log.Println("Successfully broadcasted silhouette score")
	return nil
}

func sendBlockToPeer(newBlock Block, peer peer.AddrInfo, basicHost host.Host) error {
	stream, err := basicHost.NewStream(context.Background(), peer.ID, "/p2p/1.0.0")
	if err != nil {
		return err
	}
	defer stream.Close()

	// Serialize the block
	blockBytes, err := json.Marshal(newBlock)
	if err != nil {
		return err
	}

	// Send the serialized block over the stream
	_, err = stream.Write(blockBytes)
	if err != nil {
		return err
	}

	return nil
}

// sendNBClusterToNeighbors sends the NBCluster value to the Miner's neighbors
func sendNBClusterToNeighbors(ha host.Host, NBCluster int) {
	// Iterate over all connected peers
	for _, p := range ha.Network().Peers() {
		// Open a new stream to the peer using the correct protocol string
		stream, err := ha.NewStream(context.Background(), p, "/p2p/1.0.0")
		if err != nil {
			log.Printf("Error opening stream to peer %s: %s\n", p.String(), err)
			continue
		}

		// Create a buffered writer and send the NBCluster value
		rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
		_, err = rw.WriteString(fmt.Sprintf("%d\n", NBCluster))
		if err != nil {
			log.Printf("Error writing NBCluster to peer %s: %s\n", p.String(), err)
		}
		err = rw.Flush()
		if err != nil {
			log.Printf("Error flushing stream to peer %s: %s\n", p.String(), err)
		}

		// Close the stream after sending the NBCluster value
		err = stream.Close()
		if err != nil {
			log.Printf("Error closing stream to peer %s: %s\n", p.String(), err)
		}
	}

	log.Println("NBCluster value sent to all neighbors")
}

/*
// sendStartSignal envoie le signal de démarrage uniquement aux pairs Miner
// sendStartSignal sends the start signal only to peers with the "Miner" role.
// sendStartSignal sends the start signal only to peers with the "Miner" role.
func sendStartSignal(ha host.Host) {
	peers := ha.Network().Peers()

	// Filter peers based on their roles
	minerPeers := make([]peer.ID, 0)
	for _, peerID := range peers {
		// Retrieve the peer's metadata
		roles, err := ha.Peerstore().Get(peerID, "Miner")
		if err == nil {
			if rolesSlice, ok := roles.([]string); ok {
				for _, role := range rolesSlice {
					if role == "Miner" {
						minerPeers = append(minerPeers, peerID)
						break // No need to check further roles
					}
				}
			}
		}
	}
	log.Printf("miner peer that i will send aqqq  LEn Len : %d\n", len(minerPeers))

	// Send start signal to Miner peers
	for _, peerID := range minerPeers {
		log.Printf("  Send start signal to Miner peers miner peer that i will send a  %s: %s\n", peerID.Pretty(), err)
		err := sendStartSignalToPeer(ha, peerID)
		if err != nil {
			log.Printf("Error sending start signal to peer %s: %s\n", peerID.Pretty(), err)
		}
	}
}
*/
//
// sendStartSignal sends the start signal only to peers with the "Miner" role.
func sendStartSignal(ha host.Host) {
	// Filter peers based on their roles
	minerPeers := make([]peer.ID, 0)
	// Charger les données de config.host et mettre à jour peerRoles
	config, err := loadConfigurationFromFile("config.json")
	if err != nil {
		log.Println("Error loading configuration:", err)

	}
	peerRoles = config.PeerRoles

	for _, pr := range peerRoles {
		if pr.Role == "Miner" {
			minerPeers = append(minerPeers, pr.PeerID)
		}
	}

	log.Printf("Number of miner peers to send start signal: %d\n", len(minerPeers))

	// Send start signal to Miner peers
	for _, peerID := range minerPeers {
		err := sendStartSignalToPeer(ha, peerID)
		if err != nil {
			log.Printf("Error sending start signal to peer %s: %s\n", peerID.String(), err)
		}
	}
}

/*
// sendStartSignalToPeer envoie le signal de démarrage à un pair spécifique
func sendStartSignalToPeer(ha host.Host, peerID peer.ID) error {
	stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
	if err != nil {
		return fmt.Errorf("failed to create stream to %s: %s", peerID.Pretty(), err)
	}
	defer stream.Close()

	rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))

	_, err = rw.Write([]byte("start"))
	if err != nil {
		return fmt.Errorf("failed to write start signal to %s: %s", peerID.Pretty(), err)
	}

	err = rw.Flush()
	if err != nil {
		return fmt.Errorf("failed to flush writer to %s: %s", peerID.Pretty(), err)
	}

	err = stream.Close()
	if err != nil {
		return fmt.Errorf("failed to close stream to %s: %s", peerID.Pretty(), err)
	}

	return nil
}*/
// sendStartSignalToPeer envoie le signal de démarrage à un pair spécifique
func sendStartSignalToPeer(ha host.Host, peerID peer.ID) error {
	stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
	if err != nil {
		return fmt.Errorf("failed to create stream to %s: %s", peerID.String(), err)
	}
	defer stream.Close()

	// Écrivez "start" dans le flux pour indiquer le signal de démarrage
	_, err = fmt.Fprintf(stream, "start\n")
	if err != nil {
		return fmt.Errorf("failed to write start signal to %s: %s", peerID.String(), err)
	}

	return nil
}

/*
func waitForStartSignal(startSignal chan<- struct{}) {

	// Prompt l'utilisateur pour démarrer le clustering
	reader := bufio.NewReader(os.Stdin)
	fmt.Println("Tapez 'start' pour démarrer le clustering :")

	go func() {
		defer close(startSignal) // Fermer le canal de signal lorsqu'il n'est plus nécessaire
		for {
			text, _ := reader.ReadString('\n')
			if strings.TrimSpace(text) == "start" {
				// Envoyer le signal pour démarrer le clustering

				startSignal <- struct{}{}
				fmt.Println("Signal de démarrage envoyé.")
				return // Sortir de la goroutine une fois que le signal de démarrage est envoyé

			} else {
				fmt.Println("Tapez 'start' pour démarrer le clustering :")
			}
		}
	}()

}*/

func waitForStartSignal(startSignal chan<- struct{}) {
	reader := bufio.NewReader(os.Stdin)
	fmt.Println("Tapez 'start' pour démarrer le clustering :")

	text, _ := reader.ReadString('\n')
	if strings.TrimSpace(text) == "start" {
		startSignal <- struct{}{}
		fmt.Println("Signal de démarrage envoyéeee.")
	}
}

// generateSilhouetteScorePlot2 creates a line chart of silhouette scores and saves it to a file.
func generateSilhouetteScorePlot2(scores map[string][]float64, colors map[string]color.Color, filename string) {
	p := plot.New()

	p.Title.Text = "Silhouette Scores"
	p.X.Label.Text = "Number of Clusters K"
	p.Y.Label.Text = "Score"

	// Iterate over each set of scores and corresponding color
	for label, scoreSet := range scores {
		pts := make(plotter.XYs, len(scoreSet))

		// Fill pts with scores
		for i, score := range scoreSet {
			pts[i].X = float64(i + 2) // Starting from K=2 for example
			pts[i].Y = score
		}

		line, err := plotter.NewLine(pts)
		if err != nil {
			log.Fatalf("Could not create line: %v", err)
		}

		// Set line style and color
		line.LineStyle.Width = vg.Points(2)
		line.LineStyle.Color = colors[label]

		// Add the line to the plot with label
		p.Add(line)
		p.Legend.Add(label, line)
	}

	// Save the plot to a PNG file
	if err := p.Save(6*vg.Inch, 4*vg.Inch, filename); err != nil {
		log.Fatalf("Could not save plot: %v", err)
	}
}

/*
	func broadcastNBCluster(ha host.Host, NBCluster int) {
		//marshel
		log.Println("je suis dans broadcastNBCluster \n")
		// Convert NBCluster to a string and prepare to send
		NBClusterStr := fmt.Sprintf("%d\n", NBCluster)
		// Get the list of connected peers
		peers := ha.Network().Peers()
		log.Println("all peer are %d\n", peers)
		fmt.Printf("Nombre de pairs connectés : %d\n", len(peers))
		log.Println("config.PeerRoles %s\n", config.PeerRoles)
		log.Println(" peerRoles %s\n", peerRoles)
		// Iterate over all connected peers
		for _, peerID := range ha.Network().Peers() {
			// Check if the peer is a miner
			//if isMinerPeer(peerID) { // Implement this function based on your application logic
			// Open a new stream to the miner using the correct protocol string
			stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
			if err != nil {
				log.Printf("Error opening stream to miner %s: %s\n", peerID.Pretty(), err)
				continue
			}

			// Create a buffered writer and send the NBCluster
			rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
			mutex.Lock()
			_, err = rw.WriteString(NBClusterStr)
			if err != nil {
				log.Printf("Error writing NBCluster to miner %s: %s\n", peerID.Pretty(), err)
				stream.Reset() // Reset the stream on error
				continue
			}

			err = rw.Flush()

			if err != nil {
				log.Printf("Error flushing stream to miner %s: %s\n", peerID.Pretty(), err)
				stream.Reset() // Reset the stream on error
				continue
			}

			mutex.Unlock()
			// Close the stream after sending the NBCluster
			err = stream.Close()
			if err != nil {
				log.Printf("Error closing stream to miner %s: %s\n", peerID.Pretty(), err)
			}
			//}

			log.Println("the peers ID ID ID ID %d\n", peerID)
			d := isMinerPeer(peerID)
			log.Println("the peers ID ID ID ID  is%d\n", d)
		}
	}
*/
/* 1 avril
func broadcastNBCluster(ha host.Host, NBCluster int) {
	// Convert NBCluster to a string and prepare to send
	NBClusterStr := fmt.Sprintf("%d\n", NBCluster)

	// Create a set to keep track of peers that have already received the NBCluster
	receivedPeers := make(map[peer.ID]struct{})

	// Function to recursively broadcast NBCluster to neighbors
	var broadcast func(peerID peer.ID)
	broadcast = func(peerID peer.ID) {
		// Check if the peer has already received the NBCluster
		if _, ok := receivedPeers[peerID]; ok {
			log.Println("peerID a reue le NBCLuster %d\n", peerID)
			return // Exit if the peer has already received the NBCluster
		}

		// Mark the peer as received
		receivedPeers[peerID] = struct{}{}

		// Open a new stream to the peer using the correct protocol string
		stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
		if err != nil {
			log.Printf("Error opening stream to peer %s: %s\n", peerID.Pretty(), err)
			return
		}
		defer stream.Close()

		// Create a buffered writer and send the NBCluster
		rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
		_, err = rw.WriteString(NBClusterStr)
		if err != nil {
			log.Printf("Error writing NBCluster to peer %s: %s\n", peerID.Pretty(), err)
			return
		}
		err = rw.Flush()
		if err != nil {
			log.Printf("Error flushing stream to peer %s: %s\n", peerID.Pretty(), err)
			return
		}

		log.Printf("Broadcasted NBCluster to peer %s\n", peerID.Pretty())

		// Get the list of connected peers of the current peer
		conns := ha.Network().Conns()
		for _, conn := range conns {
			if conn.RemotePeer() != peerID {
				// Recursively broadcast NBCluster to neighbors
				go broadcast(conn.RemotePeer())
			}
		}
	}

	// Get the list of connected peers
	peers := ha.Network().Peers()

	// Broadcast NBCluster to all connected peers
	for _, peerID := range peers {
		go broadcast(peerID)
	}
}
*/

func broadcastNBCluster(ha host.Host, NBCluster int) {
	// Convert NBCluster to a string and prepare to send
	NBClusterStr := fmt.Sprintf("%d\n", NBCluster)

	// Attendre que tous les pairs soient connectés
	for {
		peers := ha.Network().Peers()
		numConnectedPeers := len(peers)

		// Vérifier si tous les pairs sont connectés
		if numConnectedPeers == 0 {
			time.Sleep(1 * time.Second)
			continue
		}

		// Tous les pairs sont connectés, sortir de la boucle
		break
	}

	// Imprimer tous les pairs connectés
	for _, peer := range ha.Network().Peers() {
		log.Printf("Peer  broadcastNBClusterID: %s\n", peer)
	}

	// Diffuser le nombre de clusters à tous les pairs connectés
	for _, peerID := range ha.Network().Peers() {
		log.Printf("Diffuser le nombre de clusters à tous les pairs commencant apr : %s\n", peerID)

		if isMinerPeer(peerID) {
			// Ouvrir un nouveau flux vers le pair
			stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
			if err != nil {
				log.Printf("Error opening stream to peer %s : %s\n", peerID.String(), err)
				continue
			}

			// Envoyer le nombre de clusters via le flux
			rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
			_, err = rw.WriteString(NBClusterStr)
			if err != nil {
				log.Printf("Error writing NBCluster to peer %s: %s\n", peerID.String(), err)
				stream.Reset() // Réinitialiser le flux en cas d'erreur
				continue
			}

			err = rw.Flush()
			if err != nil {
				log.Printf("Error flushing stream to peer %s: %s\n", peerID.String(), err)
				stream.Reset() // Réinitialiser le flux en cas d'erreur
				continue
			}

			// Fermer le flux après l'envoi du nombre de clusters
			err = stream.Close()
			if err != nil {
				log.Printf("Error closing stream to peer %s: %s\n", peerID.String(), err)
			}
		}
	}
}

/* le 14 avril
func broadcastNBCluster(ha host.Host, NBCluster int) {
	// Convert NBCluster to a string and prepare to send
	NBClusterStr := fmt.Sprintf("%d\n", NBCluster)
	// Attendre que tous les pairs soient connectés

	// Maintenant, vous pouvez accéder à la liste complète des pairs connectés
	peers := ha.Network().Peers()
	for _, peer := range peers {
		log.Printf("Peer ID broadcastNBCluster: %s\n", peer)
	}

	log.Printf("Peeeerrrrr %s", peers)
	// Iterate over all connected peers
	for _, peerID := range peers {
		// Open a new stream to the peer using the correct protocol string
		stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
		if err != nil {
			log.Printf("Error opening stream to peer %s: %s\n", peerID.String(), err)
			continue
		}

		// Create a buffered writer and send the NBCluster
		rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
		_, err = rw.WriteString(NBClusterStr)
		if err != nil {
			log.Printf("Error writing NBCluster to peer %s: %s\n", peerID.String(), err)
			stream.Reset() // Reset the stream on error
			continue
		}

		err = rw.Flush()
		if err != nil {
			log.Printf("Error flushing stream to peer %s: %s\n", peerID.String(), err)
			stream.Reset() // Reset the stream on error
			continue
		}

		// Close the stream after sending the NBCluster
		err = stream.Close()
		if err != nil {
			log.Printf("Error closing stream to peer %s: %s\n", peerID.String(), err)
		}
	}
}*/

/*
27 03 2024

	func broadcastNBCluster(ha host.Host, NBCluster int) {
		//marshel
		log.Println("je suis dans broadcastNBCluster \n")
		// Convert NBCluster to a string and prepare to send
		NBClusterStr := fmt.Sprintf("%d\n", NBCluster)
		// Get the list of connected peers
		peers := ha.Network().Peers()
		log.Println("all peer are %d\n", peers)
		fmt.Printf("Nombre de pairs connectés : %d\n", len(peers))
		log.Println("config.PeerRoles %s\n", config.PeerRoles)
		log.Println(" peerRoles %s\n", peerRoles)
		// Iterate over all connected peers

		//for _, peerID := range ha.Network().Peers() {
		for _, peerID := range ha.Network().Peers() {
			// Check if the peer is a miner
			//if isMinerPeer(peerID) { // Implement this function based on your application logic
			// Open a new stream to the miner using the correct protocol string
			stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
			if err != nil {
				log.Printf("Error opening stream to miner %s: %s\n", peerID.Pretty(), err)
				continue
			}

			// Create a buffered writer and send the NBCluster
			rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
			mutex.Lock()
			_, err = rw.WriteString(NBClusterStr)
			if err != nil {
				log.Printf("Error writing NBCluster to miner %s: %s\n", peerID.Pretty(), err)
				stream.Reset() // Reset the stream on error
				continue
			}

			err = rw.Flush()

			if err != nil {
				log.Printf("Error flushing stream to miner %s: %s\n", peerID.Pretty(), err)
				stream.Reset() // Reset the stream on error
				continue
			}

			mutex.Unlock()
			// Close the stream after sending the NBCluster
			err = stream.Close()
			if err != nil {
				log.Printf("Error closing stream to miner %s: %s\n", peerID.Pretty(), err)
			}
			//}

			log.Println("the peers ID ID ID ID %d\n", peerID)
			d := isMinerPeer(peerID)
			log.Println("the peers ID ID ID ID  is%d\n", d)
		}
	}
*/
func handleIncomingBlock(s network.Stream) {
	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the incoming block data from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}

	// If the incoming data is not just a newline character
	if str != "\n" {
		chain := make([]Block, 0)
		if err := json.Unmarshal([]byte(str), &chain); err != nil {
			log.Printf("Error unmarshaling chain: %s", err)
			return
		}

		mutex.Lock()
		// If the incoming chain is longer than the current blockchain, replace it
		if len(chain) > len(Blockchain) {
			Blockchain = chain
			bytes, err := json.MarshalIndent(Blockchain, "", "  ")
			if err != nil {
				log.Printf("Error marshaling blockchain: %s", err)
				mutex.Unlock()
				return
			}
			// Display the updated blockchain in green
			fmt.Printf("\x1b[32m%s\x1b[0m> ", string(bytes))
		}
		mutex.Unlock()
	}
}

func waitForExit() {

	// waitForExit sets up a listener for SIGINT and SIGTERM.
	// Upon receiving one of these signals, it will perform any necessary cleanup before exiting.

	// Create a channel to listen for signals.

	// Block until a signal is received.

	// Perform cleanup here
	// For example, you might want to save the current state of the blockchain to a file or database.

	// Handle program termination to save the configuration before exiting
	sigChan := make(chan os.Signal, 1)
	sig := <-sigChan
	log.Printf("Received %v signal, shutting down...\n", sig)
	signal.Notify(sigChan, syscall.SIGINT, syscall.SIGTERM)
	log.Printf("Received %v signal, shutting down...\n", sig)

	go func() {
		<-sigChan
		// Reset the counters to 0 before exiting
		mutex.Lock()
		connectedPeers = 0
		numValidators = 0
		numMiners = 0
		mutex.Unlock()
		// Save the configuration to the file before exiting
		config := Configuration{
			ConnectedPeers: connectedPeers,
			NumValidators:  numValidators,
			NumMiners:      numMiners,
		}

		if err := saveConfigurationToFile("config.json", config); err != nil {
			log.Println("Error saving configuration:", err)
		}
		os.Exit(0)
	}()

	// Exit the program.
	os.Exit(0)
}

// initBlockchain initializes the blockchain with the genesis block
func initBlockchain() {
	genesisBlock := Block{}
	mutex.Lock()
	defer mutex.Unlock()

	// Check if the genesis block already exists
	if len(Blockchain) == 0 {
		// Create the genesis block
		t := time.Now()
		genesisBlock = Block{0, t.String(), 0, datas, "", calculateHash(genesisBlock), 0.0, Kmeans{}}

		// Set the hash for the genesis block
		genesisBlock.Hash = calculateHash(genesisBlock)

		// Append the genesis block to the blockchain
		Blockchain = append(Blockchain, genesisBlock)

		// Log the genesis block
		spew.Dump(genesisBlock)

		// Save the genesis block to the database (optional)
		db, err := bolt.Open("my.db", 0600, nil)
		if err != nil {
			log.Fatal(err)
		}
		defer db.Close()

		/*err = db.Update(func(tx *bolt.Tx) error {
			b, err := tx.CreateBucketIfNotExists([]byte("BlocksBucket"))
			if err != nil {
				return err
			}
			encodedBlock, err := encodeBlock(genesisBlock)
			if err != nil {
				return err
			}
			return b.Put([]byte(genesisBlock.Hash), encodedBlock)
		})*/

		Blockchain = append(Blockchain, genesisBlock)

		err1 := Save(genesisBlock, db)
		if err1 != nil {
			log.Fatalln(err1)
		}
		db.Close()

		if err != nil {
			log.Fatal(err)
		}
	}
}

func connectToPeer(host host.Host, target string, role string) error {
	// Parse the target multiaddress
	ipfsaddr, err := ma.NewMultiaddr(target)
	if err != nil {
		return err
	}

	// Extract the peer ID from the multiaddress
	pid, err := ipfsaddr.ValueForProtocol(ma.P_IPFS)
	if err != nil {
		return err
	}

	peerid, err := peer.Decode(pid)
	if err != nil {
		return err
	}

	// Extract the target address for the peer
	targetPeerAddr, _ := ma.NewMultiaddr(fmt.Sprintf("/ipfs/%s", peerid.String()))
	targetAddr := ipfsaddr.Decapsulate(targetPeerAddr)

	// Add the peer's address to the peerstore
	host.Peerstore().AddAddr(peerid, targetAddr, pstore.PermanentAddrTTL)
	host.Peerstore().Put(peerid, "roles", []byte(role))

	log.Println("Opening Stream")

	// Connect to the peer
	ctx := context.Background()
	if err := host.Connect(ctx, peer.AddrInfo{ID: peerid, Addrs: []ma.Multiaddr{targetAddr}}); err != nil {
		return err
	}
	peerAddress := peer.AddrInfo{ID: peerid, Addrs: []ma.Multiaddr{targetAddr}}
	// Once the connection is established, announce it
	fmt.Println("Connection established to peer:", peerAddress)
	log.Printf("Connected to %s - %s\n", peerid.String(), targetAddr)
	return nil
}

/*
// connectToPeer handles connecting to a specified multiaddress
func connectToPeer(host host.Host, target string) error {
	// Parse the target multiaddress
	ipfsaddr, err := ma.NewMultiaddr(target)
	if err != nil {
		return err
	}

	// Extract the peer ID from the multiaddress
	pid, err := ipfsaddr.ValueForProtocol(ma.P_IPFS)
	if err != nil {
		return err
	}

	peerid, err := peer.Decode(pid)
	if err != nil {
		return err
	}

	// Extract the target address for the peer
	targetPeerAddr, _ := ma.NewMultiaddr(fmt.Sprintf("/ipfs/%s", peerid.String()))
	targetAddr := ipfsaddr.Decapsulate(targetPeerAddr)

	// Add the peer's address to the peerstore
	host.Peerstore().AddAddr(peerid, targetAddr, pstore.PermanentAddrTTL)

	log.Println("Opening Stream")

	// Connect to the peer
	ctx := context.Background()
	if err := host.Connect(ctx, peer.AddrInfo{ID: peerid, Addrs: []ma.Multiaddr{targetAddr}}); err != nil {
		return err
	}
	peerAddress := peer.AddrInfo{ID: peerid, Addrs: []ma.Multiaddr{targetAddr}}
	// Once the connection is established, announce it
	fmt.Println("Connection established to peer:", peerAddress)
	log.Printf("Connected to %s - %s\n", peerid.Pretty(), targetAddr)
	return nil
}
*/
//********************************* networing part****************************
// makeBasicHost creates a LibP2P host with a random peer ID listening on the

// given multiaddress. It will use secio if secio is true.
func makeBasicHost(ctx context.Context, listenPort int, discoveryServiceTag string) (host.Host, *pubsub.PubSub, error) {
	// Create a new libp2p Host that listens on the specified TCP port
	r := rand.Reader

	// Generate a key pair for this host to obtain a valid host ID.
	priv, _, err := crypto.GenerateKeyPairWithReader(crypto.RSA, 2048, r)
	if err != nil {
		return nil, nil, err
	}

	opts := []libp2p.Option{
		libp2p.ListenAddrStrings(fmt.Sprintf("/ip4/127.0.0.1/tcp/%d", listenPort)),
		libp2p.Identity(priv),
		libp2p.DisableRelay(),
	}

	h, err := libp2p.New(opts...)
	if err != nil {
		return nil, nil, err
	}

	// Create a new PubSub service using the GossipSub router
	ps, err := pubsub.NewGossipSub(ctx, h)
	if err != nil {
		h.Close()
		return nil, nil, err
	}

	// Setup local mDNS discovery
	if err := setupDiscovery(h); err != nil {
		h.Close()
		return nil, nil, err
	}

	// Create an instance of the discoveryNotifee
	notifee := &discoveryNotifee{h: h}

	// Initialize the mDNS discovery service
	ser := mdns.NewMdnsService(h, discoveryServiceTag, notifee)
	if ser == nil {
		h.Close()
		return nil, nil, fmt.Errorf("failed to create mDNS service")
	}

	// The mDNS service should be closed when the context is done/cancelled, not immediately after this function returns
	go func() {
		<-ctx.Done()
		ser.Close()
	}()
	//go run main.go -l 2001 -d /ip4/127.0.0.1/tcp/2000/p2p/QmakuQqYZSgGAqppuTUY93eok1x7VvZuoHyzTK3CfNJV7A -role Miner

	log.Printf("To create a new Miner, run: \"go run main.go -l %d -d /ip4/127.0.0.1/tcp/%d/p2p%s -role Miner\"\n"+
		"To create a new Validator on a different terminal, run: \"go run main.go -l %d -d /ip4/127.0.0.1/tcp/%d/p2p%s -role Validator\"\n",
		listenPort+1, listenPort+1, h.ID(), listenPort+1, listenPort+1, h.ID())

	return h, ps, nil
}

// start publisher to topic
func publish(ctx context.Context, topic *pubsub.Topic) {
	for {
		scanner := bufio.NewScanner(os.Stdin)
		for scanner.Scan() {
			fmt.Printf("enter message to publish: \n")

			msg := scanner.Text()
			if len(msg) != 0 {
				// publish message to topic
				bytes := []byte(msg)
				topic.Publish(ctx, bytes)
			}
		}
	}
}
func publishresultclustering(ctx context.Context, topicresultclustering *pubsub.Topic) {
	for {
		scanner := bufio.NewScanner(os.Stdin)
		for scanner.Scan() {
			fmt.Printf("enter message to publish: \n")

			msg := scanner.Text()
			if len(msg) != 0 {
				// publish message to topic
				bytes := []byte(msg)
				topicresultclustering.Publish(ctx, bytes)
			}
		}
	}
}

// HandlePeerFound connects to peers discovered via mDNS. Once they're connected,
// the PubSub system will automatically start interacting with them if they also
// support PubSub.
func (n *discoveryNotifee) HandlePeerFound(pi peer.AddrInfo) {
	fmt.Printf("discovered new peer %s\n", pi.ID.String())
	err := n.h.Connect(context.Background(), pi)
	if err != nil {
		fmt.Println("error connecting to peer %s: %s\n", pi.ID.String(), err)
	}
}

// setupDiscovery creates an mDNS discovery service and attaches it to the libp2p Host.
// This lets us automatically discover peers on the same LAN and connect to them.
func setupDiscovery(h host.Host) error {
	// setup mDNS discovery to find local peers
	s := mdns.NewMdnsService(h, DiscoveryServiceTag, &discoveryNotifee{h: h})
	return s.Start()
}

// start subsriber to topic
func subscribe(subscriber *pubsub.Subscription, ctx context.Context) {

	for {
		msg, err := subscriber.Next(ctx)
		if err != nil {
			panic(err)
		}

		// Handle the message
		fmt.Printf("Received message: %s\n", string(msg.Data))
		fmt.Printf("got message: %s, from: %s\n", string(msg.Data), msg.ReceivedFrom.String())
	}

}

func setupPubSub(ctx context.Context, ps *pubsub.PubSub, topicName string) (*pubsub.Topic, *pubsub.Subscription, error) {
	// Join the pubsub topic
	topic, err := ps.Join(topicName)
	if err != nil {
		return nil, nil, err
	}

	// Subscribe to the topic
	sub, err := topic.Subscribe()
	if err != nil {
		return nil, nil, err
	}

	return topic, sub, nil
}

// *********************************************************************************************************************
// sendDataToPeer sends data to a specific peer using a LibP2P stream
func sendDataToPeer(host host.Host, peerID peer.ID, data []byte) error {
	// Open a stream to the target peer
	s, err := host.NewStream(context.Background(), peerID, "/p2p/1.0.0")
	if err != nil {
		return err
	}
	defer s.Close()

	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Send the data
	_, err = rw.Write(data)
	if err != nil {
		return err
	}

	// Flush the writer to ensure the data is sent
	if err := rw.Flush(); err != nil {
		return err
	}

	return nil
}

// Split data and send parts to connected peers
func splitAndSendData(data [][]float64, peers []peer.ID, host host.Host) {
	numPeers := len(peers)
	dataSize := len(data)
	partSize := dataSize / numPeers

	for i, peerID := range peers {
		start := i * partSize
		end := start + partSize

		// Ensure the last peer receives any remaining data
		if i == numPeers-1 {
			end = dataSize
		}

		dataPart := data[start:end]

		// Create a data message containing the data part
		dataMessage := DataMessage{Data: dataPart}

		// Serialize the data message to JSON
		jsonMessage, err := json.Marshal(dataMessage)
		if err != nil {
			log.Println(err)
			continue
		}

		// Send the data message to the peer
		if err := sendDataToPeer(host, peerID, jsonMessage); err != nil {
			log.Println(err)
		}
	}
}

func saveConfigurationToFile(filename string, config Configuration) error {
	file, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer file.Close()

	encoder := json.NewEncoder(file)
	return encoder.Encode(config)
}

func loadConfigurationFromFile(filename string) (Configuration, error) {
	file, err := os.Open(filename)
	if err != nil {
		log.Println("error Open Config")
		return Configuration{}, err
	}
	defer file.Close()

	var config Configuration
	decoder := json.NewDecoder(file)
	if err := decoder.Decode(&config); err != nil {
		return Configuration{}, err
	}

	return config, nil

}
func handleMiner(ha host.Host, dataspart [][]float64, NBCluster int) Kmeans {
	fmt.Printf("Miner-specific logic\n")
	fmt.Println(roleValue)
	fmt.Printf("Taille data pour miner: %d\n", len(dataspart))
	//fmt.Println(dataspart)

	// Create a Kmeans instance
	km := Kmeans{}

	// Perform K-means clustering on the miner's data partition
	clusterResults := km.fit(dataspart, NBCluster)

	// Print the clustering results
	fmt.Printf("predict: %v\n", clusterResults)
	fmt.Printf("Clustering results: %v\n", km.Representatives)

	//km.MinerID = minerID

	return km

}

/*
func handleMiner(ha host.Host, roleValue string, dataspart [][]float64, NBCluster int, resultChan chan<- Kmeans) {
	fmt.Printf("Miner-specific logic\n")
	fmt.Println(roleValue)
	fmt.Printf("Taille data pour miner: %d\n", len(dataspart))
	fmt.Println(dataspart)

	for {
		// Perform mining operations
		// ...
		km := Kmeans{}
		// Perform K-means clustering on the miner's data partition
		clusterResults := km.fit(dataspart, NBCluster)

		// Print the clustering results
		fmt.Printf("predict: %v\n", clusterResults)
		//km, err := KmeansClustering(dataspart, NBCluster)
		if err != nil {
			fmt.Println(err)
			// Handle the error, or you can send an error through a separate channel
			continue
		}

		// Send the result to the provided channel
		resultChan <- km
		fmt.Printf("predict2: %v\n", clusterResults)

		time.Sleep(time.Second) // Example: Sleep for 1 second between mining attempts
	}
}*/

func handleValidator(km Kmeans) float64 {
	fmt.Println("Validator-specific logic")
	log.Println("I am a Validator")

	// Calculate silhouette score for the input Kmeans object
	silhouetteScore := calculateSilhouetteScore(km)

	// Print the silhouette score
	fmt.Printf(" Score for the current Kmeans object: %f\n", silhouetteScore)

	// Sleep for a while before the next validation attempt
	time.Sleep(time.Second)
	log.Println("Validator-specific logic at the end of handleValidator")
	return silhouetteScore
}

// Example function to calculate the silhouette score
func calculateSilhouetteScore(km Kmeans) float64 {
	// Number of data points
	n := len(km.Data)

	// Initialize arrays to store a(i) and b(i)
	a := make([]float64, n)
	b := make([]float64, n)

	// Loop through each data point
	for i := 0; i < n; i++ {
		// Calculate a(i) - average distance to other points in the same cluster
		a[i] = averageDistanceToCluster(i, km.Data, km.Labels)

		// Calculate b(i) - smallest average distance to points in a different cluster
		b[i] = smallestAverageDistanceToOtherCluster(i, km.Data, km.Labels)
	}

	// Calculate silhouette score for each data point
	s := make([]float64, n)
	for i := 0; i < n; i++ {
		maxAorB := math.Max(a[i], b[i])
		if maxAorB == 0 {
			s[i] = 0.0 // Avoid division by zero
		} else {
			s[i] = (b[i] - a[i]) / maxAorB
		}
	}

	// Calculate the overall silhouette score (average of all s(i) values)
	averageSilhouette := calculateAverage(s)
	return averageSilhouette
}

func averageDistanceToCluster(pointIndex int, data [][]float64, labels []int) float64 {
	clusterIndex := labels[pointIndex]

	// Extract points in the same cluster
	var clusterPoints [][]float64
	for i, label := range labels {
		if label == clusterIndex {
			clusterPoints = append(clusterPoints, data[i])
		}
	}

	// Calculate average distance to points in the same cluster
	return calculateAverageDistance(data[pointIndex], clusterPoints)
}

func smallestAverageDistanceToOtherCluster(pointIndex int, data [][]float64, labels []int) float64 {
	clusterIndex := labels[pointIndex]

	// Initialize with a large value
	minAverageDistance := math.Inf(1)

	// Loop through each cluster
	for i := 0; i < len(data); i++ {
		if i != clusterIndex {
			// Extract points in the other cluster
			var otherClusterPoints [][]float64
			for j, label := range labels {
				if label == i {
					otherClusterPoints = append(otherClusterPoints, data[j])
				}
			}

			// Calculate average distance to points in the other cluster
			averageDistance := calculateAverageDistance(data[pointIndex], otherClusterPoints)

			// Update minAverageDistance if the new distance is smaller
			if averageDistance < minAverageDistance {
				minAverageDistance = averageDistance
			}
		}
	}

	return minAverageDistance
}

func calculateAverageDistance(point []float64, points [][]float64) float64 {
	// Calculate the average Euclidean distance from a point to a set of points
	sumDistance := 0.0
	for _, p := range points {
		sumDistance += calculateEuclideanDistance(point, p)
	}

	return sumDistance / float64(len(points))
}

func calculateEuclideanDistance(point1, point2 []float64) float64 {
	// Calculate the Euclidean distance between two points
	sum := 0.0
	for i := range point1 {
		sum += math.Pow(point1[i]-point2[i], 2)
	}

	return math.Sqrt(sum)
}

func calculateAverage(slice []float64) float64 {
	// Calculate the average of a slice of float64
	sum := 0.0
	for _, value := range slice {
		sum += value
	}

	return sum / float64(len(slice))
}

/*
func handleStream(s network.Stream, host host.Host, rrole string) {
	log.Println("Got a new stream!")

	// Determine the role of the peer from the peer ID
	peerID := s.Conn().RemotePeer()

	if rrole == "Miner" {

		log.Printf("rani dakhal handelstream darakh if miner \n")
		go handleMinerStream(s)

	} else if rrole == "Validator" {
		log.Printf("rani dakhal handelstream darakh if validator \n")

		go handleValidatorStream(s)
	} else {
		// If the role is unknown or a data holder, you might want to handle differently or log an error
		log.Printf("Unknown role for peer %s\n", peerID.Pretty())

		// You could close the stream or take other appropriate actions
		//s.Reset()
	}

}*/
/*
// handleStream handles the stream for a peer
func handleStream(s network.Stream, host host.Host, rrole string) {
	log.Println("Got a new stream!")

	// Determine the role of the peer from the peer ID
	peerID := s.Conn().RemotePeer()

	if rrole == "Miner" {
		log.Printf("Handling stream for Miner %s\n", peerID)

		// Create a channel for this miner if it doesn't exist
		if _, ok := minerNBClusterChannels[peerID.Pretty()]; !ok {
			minerNBClusterChannels[peerID.Pretty()] = make(chan int)
		}

		// Launch a goroutine to handle the miner stream
		go handleMinerStream(s, peerID.Pretty())
	} else if rrole == "Validator" {
		log.Println("Handling stream for Validator")
		// Implement logic for handling validator stream
	} else {
		log.Printf("Unknown role for peer %s\n", peerID.Pretty())
	}
}
*/
//le 5 avril le soir
func handleStream(s network.Stream, host host.Host, rrole string, nbcReceived chan<- int) {
	log.Println("Got a new stream!")

	// Determine the role of the peer from the peer ID
	peerID := s.Conn().RemotePeer()
	ciid := "QmYs8voZjW7LWhknxF7qEffyVgsfYQBASt94iH37ea8idm"
	if rrole == "Miner" {
		log.Printf("Handling stream for Miner %s\n", peerID)

		// Launch a goroutine to handle the miner stream
		go handleMinerStream(s, host, peerID.String(), ciid)

	} else if rrole == "Validator" {
		log.Println("Handling stream for Validator")
		// Implement logic for handling validator stream
	} else {
		log.Printf("Unknown role for peer %s\n", peerID.String())
	}
}

/*
// le 5 avril handleStream handles the stream for a peer
func handleStream(s network.Stream, host host.Host, rrole string, nbcReceived chan<- int) {
	log.Println("Got a new stream!")

	// Determine the role of the peer from the peer ID
	peerID := s.Conn().RemotePeer()

	if rrole == "Miner" {
		log.Printf("Handling stream for Miner %s\n", peerID)

		// Create a buffer stream for non-blocking read and write
		rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

		// Read the NBCluster value from the stream
		str, err := rw.ReadString('\n')
		if err != nil {
			log.Printf("Error reading from stream: %s", err)
			s.Reset() // Reset the stream on error
			return
		}
		log.Printf("affichage du str le nbcluster recue  %s\n", peerID)

		// Parse the NBCluster value
		NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
		if err != nil {
			log.Printf("Error parsing NBCluster valueee: %s", err)
			return
		}

		// Log the received NBCluster value
		log.Printf("Received NBCluster value: %d\n", NBCluster)

		// Send the NBCluster value to the channel
		nbcReceived <- NBCluster
	} else if rrole == "Validator" {
		log.Println("Handling stream for Validator")
		// Implement logic for handling validator stream
	} else {
		log.Printf("Unknown role for peer %s\n", peerID.Pretty())
	}
}*/

// handleValidatorStream handles the stream for a validator peer
func handleValidatorStream(s network.Stream) {
	// Implement the logic for handling validator stream
	// This could involve reading validation results, writing new blocks, etc.
}

type Peer interface {
	Send(int) error
}

var peers []Peer

/*// handleMinerStream handles the stream for a miner peer
func handleMinerStream(s network.Stream, minerID string) {
	log.Println("Starting handleMinerStream function...")

	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the NBCluster value from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}
	log.Printf("Received string representation of NBCluster: %s\n", str)

	// Parse the NBCluster value
	NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
	if err != nil {
		log.Printf("Error parsing NBCluster value: %s\n", err)
		return
	}

	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)

	// Send the NBCluster value to the channel
	nbcReceived <- NBCluster

	log.Println("NBCluster value sent to the channel.")
}*/
// handleMinerStream handles the stream for a miner peer
// handleMinerStream handles the stream for a miner peer
/*
func handleMinerStream(s network.Stream, ha host.Host) {
	log.Println("Starting handleMinerStream function...")

	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the NBCluster value from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}
	log.Printf("Received string representation of NBCluster: %s\n", str)

	// Parse the NBCluster value
	NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
	if err != nil {
		log.Printf("Error parsing NBCluster value: %s\n", err)
		return
	}

	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)

	// Perform clustering on each partition in parallel

	for i, partition := range dataPartitions {

		// Inside the goroutine, use partitionCID as a string
		go func(i int, partitionCID string) {
			// Fetch dataset partition from IPFS
			partitionData, err := fetchDatasetPartitionFromIPFS(api, partitionCID)
			if err != nil {
				log.Printf("Error fetching dataset partition from IPFS: %v\n", err)
				return
			}

			// Perform clustering on the partition
			km := handleMiner(ha, partitionData.Partition, partitionData.NBCluster)

			// Send clustering results to the Validator
			sendResultsToValidator(ha, partitionData.NBCluster, km)

			log.Println("Miner", i, "finished its work")
		}(i, partitionCID)
	}


}*/
// Fonction pour gérer le traitement des mineurs
// le 16 04  Main function for handling miner stream
/*func handleMinerStream(s network.Stream, ha host.Host) {
	log.Println("Starting handleMinerStream function...")

	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the NBCluster value from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}
	log.Printf("Received string representation of NBCluster: %s\n", str)

	// Parse the NBCluster value
	NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
	if err != nil {
		log.Printf("Error parsing NBCluster value: %s\n", err)
		return
	}

	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)

	// Fetch dataset partition from IPFS for this miner
	partitionData, err := fetchDatasetPartitionFromIPFS(api, cidForThisMiner)
	if err != nil {
		log.Printf("Error fetching dataset partition from IPFS: %v\n", err)
		return
	}

	// Perform clustering on the partition
	km := Kmeans{}
	km = handleMiner(ha, partitionData.Partition, partitionData.NBCluster)

	// Create a Kmeans instance

	// Perform K-means clustering on the miner's data partition
	clusterResults := km.fit(partitionData.Partition, NBCluster)

	// Print the clustering results
	fmt.Printf("predict: %v\n", clusterResults)
	fmt.Printf("Clustering results: %v\n", km.Representatives)

	// Send clustering results to the Validator
	sendResultsToValidator(ha, NBCluster, km)

	log.Println("Miner finished its work")
} */

/*
// handleMinerStream handles the stream for a miner peer
func handleMinerStream(s network.Stream, minerID string) {
	log.Println("Starting handleMinerStream function...")

	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the NBCluster value from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}
	log.Printf("affichage du str le nbcluster recue  %d\n", str)

	// Parse the NBCluster value
	NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
	log.Printf("affichage du str le nbcluster recue  %d\n", NBCluster)
	if err != nil {
		log.Printf("Error parsing NBCluster valueee: %s", err)
		return
	}

	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)

	// Send the NBCluster value to the channel
	nbcReceived <- NBCluster
	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)
} */

/*
// handleMinerStream handles the stream for a miner peer
func handleMinerStream(s network.Stream) {
	// Implement the logic for handling miner stream
	// This could involve reading mining results, sending data for mining, etc.
	// Create a buffer stream for non-blocking read and write.

	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the NBCluster value from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}

	// Parse the NBCluster value
	NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
	if err != nil {
		log.Printf("Error parsing NBCluster value: %s", err)
		return
	}

	mutex.Lock()
	// Send the NBCluster value to the nbcReceived channel
	nbcReceived <- NBCluster
	mutex.Unlock()
	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)

}
*/

/*
	func determineIfValidator(ha host.Host) bool {
		// Check if the role is set to "Validator"
		// Check if the role is set to "Validator"
		isValidator := role == "Validator"
		log.Printf("Is Validator: %v\n", isValidator)
		return isValidator

}
*/
func determineIfValidator(roleValue string) bool {
	// Check if the role is "Validator"
	return roleValue == "Validator"
}
func determineIfMiner(roleValue string) bool {
	return roleValue == "Miner"

}
func addPeer(peer Peer) {
	mutex.Lock()
	peers = append(peers, peer)
	mutex.Unlock()
}

/*
// Function to determine if a peer is a Miner

	func determineIfMiner(ha host.Host) bool {
		// Implement your logic to identify Miners here
		// Return true if it's a Miner, otherwise false
		isMiner := role == "Miner"
		log.Printf("Is Miner: %v\n", isMiner)
		return isMiner

}
*/
func readData(rw *bufio.ReadWriter) {

	for {
		str, err := rw.ReadString('\n') //read a messae
		if err != nil {
			log.Fatal(err)
		}

		if str == "" {
			return
		}
		if str != "\n" {

			chain := make([]Block, 0)
			log.Println("rani dakhal read data avant unmarshal ")
			if err := json.Unmarshal([]byte(str), &chain); err != nil {
				log.Fatal(err)
			}

			mutex.Lock()
			if len(chain) > len(Blockchain) {
				Blockchain = chain
				bytes, err := json.MarshalIndent(Blockchain, "", "  ")
				if err != nil {

					log.Fatal(err)
				}
				// Green console color: 	\x1b[32m
				// Reset console color: 	\x1b[0m

				fmt.Printf("\x1b[32m%s\x1b[0m> ", string(bytes))
			}
			mutex.Unlock()
		}
	}
}

/*
1 4 2024

	func miner(ha host.Host, roleValue string, startSignal <-chan struct{}) {
		var minerResults []Kmeans
		var NBCluster int
		nbcReceived := make(chan int, 1) // Channel to receive NBCluster
		var wg sync.WaitGroup            // WaitGroup to wait for all miners to finish their work

		// Set up a stream handler to receive NBCluster from the dataholder
		if roleValue == "Miner" {
			ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
				rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

				// Read the NBCluster value from the stream
				str, err := rw.ReadString('\n')
				if err != nil {
					log.Printf("Error reading from stream: %s", err)
					s.Reset() // Reset the stream on error
					return
				}

				// Parse the received NBCluster
				NBCluster, err = strconv.Atoi(strings.TrimSpace(str))
				if err != nil {
					log.Printf("Error parsing NBCluster value: %s", err)
					return
				}

				// Print the received Number of Clusters
				fmt.Printf("Received Number of Clusters: %d\n", NBCluster)

				// Send the NBCluster value to the nbcReceived channel
				select {
				case nbcReceived <- NBCluster:
					// NBCluster received successfully
				default:
					// nbcReceived channel already has a value, discard the received NBCluster
					log.Println("Discarding received NBCluster as it is not needed")
				}
			})
		}

		// Wait for NBCluster
		select {
		case NBCluster = <-nbcReceived:
			log.Printf("Received NBCluster: %d, waiting for start signal.\n", NBCluster)
		case <-startSignal:
			log.Println("Received start signal before NBCluster. Exiting...")
			return // Exit the function if start signal is received before NBCluster
		}

		// Wait for start signal
		select {
		case <-startSignal:
			log.Println("Received start signal. Starting clustering process.")
		default:
			log.Println("Waiting for start signal...")
		}

		// Perform clustering process...
		datas := readdataset("iris2.csv")
		dataPartitions, err := splitDataset(datas, connectedPeers)
		if err != nil {
			log.Fatal(err)
		}

		wg.Add(len(dataPartitions)) // Increase WaitGroup count

		// Perform clustering on each partition in parallel
		for i, partition := range dataPartitions {
			go func(i int, partition [][]float64) {
				defer wg.Done()

				// Perform clustering on the partition
				km := handleMiner(ha, partition, NBCluster)

				mutex.Lock()
				minerResults = append(minerResults, km)
				mutex.Unlock()

				log.Println("Miner", i, "finished its work")
			}(i, partition)
		}

		wg.Wait() // Wait for all miners to finish their work

		// Send clustering results to the Validator
		sendResultsToValidator(ha, NBCluster, minerResults)

		// Clear minerResults for the next round
		minerResults = nil
	}
*/
func sendNBClusterToNeighbor(ha host.Host, NBCluster int) {
	// Get direct peers or neighbors
	peers := ha.Network().Peers()

	// Iterate over peers and send NBCluster to each
	for _, peerID := range peers {
		// Skip sending to self
		if peerID == ha.ID() {
			continue
		}

		// Create a new stream to peer
		stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
		if err != nil {
			log.Printf("Error opening stream to %s: %s\n", peerID, err)
			continue
		}

		// Create a buffer writer to write NBCluster to the stream
		w := bufio.NewWriter(stream)
		_, err = w.WriteString(strconv.Itoa(NBCluster))
		if err != nil {
			log.Printf("Error writing NBCluster to stream: %s\n", err)
			continue
		}

		// Flush the writer to ensure data is sent
		err = w.Flush()
		if err != nil {
			log.Printf("Error flushing stream writer: %s\n", err)
		}

		// Close the stream after writing
		stream.Close()
	}
}

/* nahawha kamal
func miner(ha host.Host, roleValue string, nbcReceived <-chan int) {
	var minerResults []Kmeans
	var NBCluster int
	var wg sync.WaitGroup // WaitGroup to wait for all miners to finish their work
	log.Printf("je suis dan miner functionnn.\n")
	// Wait for NBCluster
	select {
	case NBCluster = <-nbcReceived:
		log.Printf("Received NBCluster: %d\n", NBCluster)

	default:
		log.Println("Failed to receive NBCluster")
		return // Exit the function if NBCluster is not received
	}
	// Send NBCluster to direct peer or neighbor
	sendNBClusterToNeighbor(ha, NBCluster)

	// Perform clustering process...
	datas := readdataset("iris2.csv")
	dataPartitions, err := splitDataset(datas, connectedPeers)
	if err != nil {
		log.Fatal(err)
	}

	wg.Add(len(dataPartitions)) // Increase WaitGroup count

	// Perform clustering on each partition in parallel
	for i, partition := range dataPartitions {
		go func(i int, partition [][]float64) {
			defer wg.Done()

			// Perform clustering on the partition
			km := handleMiner(ha, partition, NBCluster)

			mutex.Lock()
			minerResults = append(minerResults, km)
			mutex.Unlock()

			log.Println("Miner", i, "finished its work")
		}(i, partition)
	}

	wg.Wait() // Wait for all miners to finish their work

	// Send clustering results to the Validator
	sendResultsToValidator(ha, NBCluster, minerResults)

	// Clear minerResults for the next round
	minerResults = nil
}
*/
/* 7 4
func miner(ha host.Host, roleValue string, nbcReceived <-chan int) {
	var minerResults []Kmeans
	var NBCluster int
	var wg sync.WaitGroup // WaitGroup to wait for all miners to finish their work

	// Wait for NBCluster
	select {
	case NBCluster = <-nbcReceived:
		log.Printf("Received NBCluster: %d, waiting for start signal.\n", NBCluster)

		return // Exit the function if start signal is received before NBCluster
	}

	// Perform clustering process...
	datas := readdataset("iris2.csv")
	dataPartitions, err := splitDataset(datas, connectedPeers)
	if err != nil {
		log.Fatal(err)
	}

	wg.Add(len(dataPartitions)) // Increase WaitGroup count

	// Perform clustering on each partition in parallel
	for i, partition := range dataPartitions {
		go func(i int, partition [][]float64) {
			defer wg.Done()

			// Perform clustering on the partition
			km := handleMiner(ha, partition, NBCluster)

			mutex.Lock()
			minerResults = append(minerResults, km)
			mutex.Unlock()

			log.Println("Miner", i, "finished its work")
		}(i, partition)
	}

	wg.Wait() // Wait for all miners to finish their work

	// Send clustering results to the Validator
	sendResultsToValidator(ha, NBCluster, minerResults)

	// Clear minerResults for the next round
	minerResults = nil
}*/

/* 25 03 3024
func miner(ha host.Host, roleValue string, startSignal <-chan struct{}) {
	var minerResults []Kmeans
	var NBCluster int
	nbcReceived := make(chan int, 1) // Channel to receive NBCluster
	var wg sync.WaitGroup            // WaitGroup to wait for all miners to finish their work

	// Set up a stream handler to receive NBCluster from the dataholder
	if roleValue == "Miner" {
		ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
			rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

			// Read the NBCluster value from the stream
			str, err := rw.ReadString('\n')
			if err != nil {
				log.Printf("Error reading from stream: %s", err)
				s.Reset() // Reset the stream on error
				return
			}

			// Check if the message is "start"
			if strings.TrimSpace(str) == "start" {
				// If the message is "start", handle the start signal
				log.Println("Received start signal. Starting mining process.")
				// Proceed with clustering process...
				datas := readdataset("iris2.csv")
				dataPartitions, err := splitDataset(datas, connectedPeers)
				if err != nil {
					log.Fatal(err)
				}

				wg.Add(len(dataPartitions)) // Increase WaitGroup count

				// Perform clustering on each partition in parallel
				for i, partition := range dataPartitions {
					go func(i int, partition [][]float64) {
						defer wg.Done()

						// Perform clustering on the partition
						km := handleMiner(ha, partition, NBCluster)

						mutex.Lock()
						minerResults = append(minerResults, km)
						mutex.Unlock()

						log.Println("Miner", i, "finished its work")
					}(i, partition)
				}

				wg.Wait() // Wait for all miners to finish their work

				// Send clustering results to the Validator
				sendResultsToValidator(ha, NBCluster, minerResults)

				// Clear minerResults for the next round
				minerResults = nil

				return // Exit the handler after processing the start signal
			}

			// If the message is not "start", parse it as NBCluster
			NBCluster, err = strconv.Atoi(strings.TrimSpace(str))
			if err != nil {
				log.Printf("Error parsing NBCluster value: %s", err)
				return
			}

			// Print the received Number of Clusters
			fmt.Printf("Received Number of Clusters: %d\n", NBCluster)

			// Send the NBCluster value to the nbcReceived channel
			select {
			case nbcReceived <- NBCluster:
				// NBCluster received successfully
			default:
				// nbcReceived channel already has a value, discard the received NBCluster
				log.Println("Discarding received NBCluster as it is not needed")
			}
		})
	}

	// Wait for either NBCluster or start signal
	for {
		select {
		case NBCluster = <-nbcReceived:
			log.Printf("Received NBCluster: %d, starting mining process.\n", NBCluster)
		case <-startSignal:
			log.Println("Receiveddd start signal. Starting clustering process.")
			// Proceed with clustering process...
			datas := readdataset("iris2.csv")
			dataPartitions, err := splitDataset(datas, connectedPeers)
			if err != nil {
				log.Fatal(err)
			}

			wg.Add(len(dataPartitions)) // Increase WaitGroup count

			// Perform clustering on each partition in parallel
			for i, partition := range dataPartitions {
				go func(i int, partition [][]float64) {
					defer wg.Done()

					// Perform clustering on the partition
					km := handleMiner(ha, partition, NBCluster)

					mutex.Lock()
					minerResults = append(minerResults, km)
					mutex.Unlock()

					log.Println("Miner", i, "finished its work")
				}(i, partition)
			}

			wg.Wait() // Wait for all miners to finish their work

			// Send clustering results to the Validator
			sendResultsToValidator(ha, NBCluster, minerResults)

			// Clear minerResults for the next round
			minerResults = nil

			return // Exit the loop after processing the start signal
		default:
			log.Println("Waiting for NBCluster or start signal...")
			time.Sleep(time.Second)
		}
	}
}*/
/*
func miner(ha host.Host, roleValue string, startSignal <-chan struct{}) {
	var minerResults []Kmeans
	var NBCluster int
	nbcReceived := make(chan int, 1) // Channel to receive NBCluster
	var wg sync.WaitGroup            // WaitGroup to wait for all miners to finish their work

	if roleValue == "Miner" {
		// Set up a stream handler to receive NBCluster from the dataholder
		ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
			rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

			// Read the NBCluster value from the stream
			str, err := rw.ReadString('\n')
			if err != nil {
				log.Printf("Error reading from stream: %s", err)
				s.Reset() // Reset the stream on error
				return
			}

			// Parse the NBCluster value
			NBCluster, err = strconv.Atoi(strings.TrimSpace(str))
			if err != nil {
				log.Printf("Error parsing NBCluster value: %s", err)
				return
			}

			// Print the received Number of Clusters
			fmt.Printf("Received Number of Clusters: %d\n", NBCluster)

			// Send the NBCluster value to the nbcReceived channel
			select {
			case nbcReceived <- NBCluster:
				// NBCluster received successfully
			default:
				// nbcReceived channel already has a value, discard the received NBCluster
				log.Println("Discarding received NBCluster as it is not needed")
			}
		})
	}

	// Continuously perform mining operations
	for {

		// Wait for NBCluster to be received
		if roleValue == "Miner" {
			log.Printf("Received1 .\n")
			if NBCluster == 0 {
				// Wait for NBCluster to be received
				select {
				case NBCluster = <-nbcReceived:
					log.Printf("Received NBCluster: %d, starting mining process.\n", NBCluster)
					log.Println("j'ai reçu le NBCluster, j'attends le signal pour commencer le clustering")
				default:
					log.Println("Waiting to receive the number of clusters...")
					time.Sleep(time.Second)
					continue
				}
			} else {
				log.Printf("Received2 .\n")
				// Wait for start signal
				select {
				case <-startSignal:
					log.Println("Received start signal. Starting mining process.")
				default:
					log.Printf("Received3 .\n")
					log.Println("Waiting for start signal...")
					time.Sleep(time.Second)
					continue
				}
				log.Println("j'ai reçu le signal de start, je vais commencer le clustering")
			}
			datas := readdataset("iris2.csv")
			dataPartitions, err := splitDataset(datas, connectedPeers)
			if err != nil {
				log.Fatal(err)
			}

			wg.Add(len(dataPartitions)) // Increase WaitGroup count

			// Perform clustering on each partition in parallel
			for i, partition := range dataPartitions {
				go func(i int, partition [][]float64) {
					defer wg.Done()

					// Perform clustering on the partition
					km := handleMiner(ha, partition, NBCluster)

					//	log.Println("Displaying NBCluster et nbrecived", NBCluster, NBClusterr)
					log.Println("Displaying km Representatives:", km.Representatives)
					log.Println("Displaying km MinerID:", km.MinerID)

					mutex.Lock()
					minerResults = append(minerResults, km)
					mutex.Unlock()

					log.Println("Miner", i, "finished its work")
				}(i, partition)
			}

			wg.Wait() // Wait for all miners to finish their work

			// Send clustering results to the Validator
			sendResultsToValidator(ha, NBCluster, minerResults)

			// Clear minerResults for the next round
			minerResults = nil

			// Sleep for a while before the next mining operation
			time.Sleep(5 * time.Second)

		} else {
			// If roleValue is not "Miner", exit the loop
			break
		}
	}
}*/

/*
// miner performs the mining operation and sends results to the validator
func miner(ha host.Host) {
	var minerResults []Kmeans
	var NBCluster int
	// Wait for NBCluster to be received

	// Set up a stream handler to receive NBCluster from the dataholder
	ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
		rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

		// Read the NBCluster value from the stream
		str, err := rw.ReadString('\n')
		if err != nil {
			log.Printf("Error reading from stream: %s", err)
			s.Reset() // Reset the stream on error
			return
		}

		// Parse the NBCluster value
		NBCluster, err = strconv.Atoi(strings.TrimSpace(str))
		if err != nil {
			log.Printf("Error parsing NBCluster value: %s", err)
			return
		}

		// Print the received Number of Clusters
		fmt.Printf("Received Number of Clusters: %d\n", NBCluster)

	})

	log.Printf("Received NBCluster: %d, starting mining process.\n", NBCluster)

	// Continuously perform mining operations
	for {

		// Check if NBCluster has been received
		if NBCluster == 0 {
			log.Println("Waiting to receive the number of clusters...")
			time.Sleep(time.Second)
			continue
		}
		fmt.Println(" the recived Number of Cluster: ")

		datas := readdataset("iris2.csv")
		dataPartitions, err := splitDataset(datas, connectedPeers)
		if err != nil {
			log.Fatal(err)
		}

		var wg sync.WaitGroup
		for i, partition := range dataPartitions {
			wg.Add(1)
			go func(i int, partition [][]float64) {
				defer wg.Done()

				// Perform clustering on the partition
				km := handleMiner(ha, partition, NBCluster)
				log.Println("Displaying km Representatives:", km.Representatives)
				log.Println("Displaying km MinerID:", km.MinerID)
				// Calculate silhouette score for the input Kmeans object
				silhouetteScore := calculateSilhouetteScore(km)

				// Print the silhouette score
				fmt.Printf(" Score for the current Kmeans object: %f\n", silhouetteScore)

				mutex.Lock()
				minerResults = append(minerResults, km)
				mutex.Unlock()

				log.Println("Miner", i, "finished its work")
			}(i, partition)
		}

		wg.Wait()

		// Send clustering results to the Validator
		sendResultsToValidator(ha, NBCluster, minerResults)

		// Sleep for a while before the next mining operation
		time.Sleep(5 * time.Second)
	}
}
*/

/*
	func sendResultsToValidator(ha host.Host, minerResults []Kmeans) {
		// Your existing logic to marshal minerResults into JSON...
		// Marshal the minerResults into JSON
		log.Println("je suis dans send result to validatorvoila mineresult")
		bytes, err := json.Marshal(minerResults)
		if err != nil {
			log.Println("Failed to marshal miner results:", err)
			return
		}

		// Convert the JSON bytes to a string and prepare to send
		resultStr := fmt.Sprintf("%s\n", string(bytes))
		log.Println("je suis dans send result to validatorvoila resultSTR %s", resultStr)
		// Iterate over all connected peers
		for _, p := range ha.Network().Peers() {
			// Check if the peer is a validator
			//if isValidatorPeer(p) {
			log.Println("je suis validator avec ID je vais traiter resultSTR", p)

			// Open a new stream to the validator using the correct protocol string
			stream, err := ha.NewStream(context.Background(), p, "/p2p/1.0.0")

			if err != nil {
				log.Printf("Error opening stream to validator %s: %s\n", p.Pretty(), err)
				continue
			}
			// Create a buffered writer and send the results
			rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))

			mutex.Lock()
			_, err = rw.WriteString(resultStr)
			if err != nil {
				log.Printf("Error writing results to validator %s: %s\n", p.Pretty(), err)
				stream.Reset() // ReseSilhouettet the stream on error
				continue
			}
			err = rw.Flush()
			mutex.Unlock()
			if err != nil {
				log.Printf("Error flushing stream to validator %s: %s\n", p.String(), err)
				stream.Reset() // Reset the stream on error
				continue
			}

			// Close the stream after sending the results
			err = stream.Close()
			if err != nil {
				log.Printf("Error closing stream to validator %s: %s\n", p.String(), err)
			}
			//}
		}

		log.Println("Sent results to all validators")
	}
*/
func sendResultsToValidator(ha host.Host, minerID string, NBCluster int, km Kmeans) {
	// Create an instance of ValidationResult with NBCluster and Kmeans
	validationResult := ValidationResult{
		NBCluster: NBCluster,
		MinerResults: []Kmeans{
			km, // Add Kmeans result for the current miner
		},
	}

	// Marshal the ValidationResult into JSON
	bytes, err := json.Marshal(validationResult)
	if err != nil {
		log.Println("Failed to marshal validation results:", err)
		return
	}

	// Convert the JSON bytes to a string and prepare to send
	resultStr := fmt.Sprintf("%s\n", string(bytes))

	// Iterate over all connected validators

	config, err := loadConfigurationFromFile("config.json")
	if err != nil {
		log.Println("Error loading configuration:", err)

	}
	peerRoles = config.PeerRoles

	log.Println("dans isvalidatorpeer, peerRoles:", peerRoles)
	// Obtenez la liste des pairs de votre hôte
	peers := ha.Network().Peers()
	peeers, err := discoverPeers(ha)
	log.Printf("Epeeerreesrrrrrrrrrrrssss : %s\n", peeers)
	log.Printf("Epeeerreesssss : %s\n", peers)
	// Parcourez chaque pair
	for _, peerID := range peers {
		// Obtenez le rôle du pair en utilisant peerID
		role, err := getRoleForPeer(peerID) // Une fonction hypothétique pour obtenir le rôle d'un pair
		if err != nil {
			log.Printf("Error opening stream to validator : %s\n", err)
			continue // Passer au pair suivant si une erreur est survenue
		}

		// Faites ce que vous avez besoin de faire avec le rôle
		log.Println("Peer:", peerID, "Role:", role)

		if role == "Validator" {
			log.Println("PeerID:", peerID, "est un validateur")
			// Faites ce que vous devez faire avec ce peerID ici
			log.Println("Trying to connect to validator:", peerID)
			// Open a new stream to the validator using the correct protocol string
			stream, err := ha.NewStream(context.Background(), peerID, "/p2p/1.0.0")
			if err != nil {
				log.Printf("Error opening stream to validator %s: %s\n", peerID, err)
				continue
			}

			// Create a buffered writer and send the results
			rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))
			_, err = rw.WriteString(resultStr)
			if err != nil {
				log.Printf("Error writing results to validator %s: %s\n", peerID, err)
				stream.Reset() // Reset the stream on error
				continue
			}
			err = rw.Flush()
			if err != nil {
				log.Printf("Error flushing stream to validator %s: %s\n", peerID, err)
				stream.Reset() // Reset the stream on error
				continue
			}

			// Close the stream after sending the results
			err = stream.Close()
			if err != nil {
				log.Printf("Error closing stream to validator %s: %s\n", peerID, err)
			}
			log.Println("Sent results to all validators")

		} else {
			log.Printf("Peer %s is not a validator, skipping...\n", peerID)
		}

	}

}

/*
func sendResultsToValidator(ha host.Host, NBCluster int, minerResults []Kmeans) {
	// Create an instance of ValidationResult with NBCluster and minerResults

	validationResult := ValidationResult{
		NBCluster:    NBCluster,
		MinerResults: minerResults,
	}

	// Marshal the ValidationResult into JSON
	mutex.Lock()
	bytes, err := json.Marshal(validationResult)
	if err != nil {
		log.Println("Failed to marshal validation results:", err)
		return
	}
	mutex.Unlock()

	// Convert the JSON bytes to a string and prepare to send
	resultStr := fmt.Sprintf("%s\n", string(bytes))
	//	log.Println("Sending result to validator:", resultStr)
	//	log.Println("je suis dans send result to validatorvoila resultSTR %s", resultStr)

	// Iterate over all connected peers
	for _, p := range ha.Network().Peers() {
		// Check if the peer is a validator
		if isValidatorPeer(p) {
			log.Println("Sending results to validator with ID:", p)
			log.Println("je suis validator avec ID je vais traiter resultSTR", p)

			// Open a new stream to the validator using the correct protocol string
			stream, err := ha.NewStream(context.Background(), p, "/p2p/1.0.0")
			if err != nil {
				log.Printf("Error opening stream to validator %s: %s\n", p.Pretty(), err)
				continue
			}

			// Create a buffered writer and send the results
			rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))

			mutex.Lock()
			_, err = rw.WriteString(resultStr)
			if err != nil {
				log.Printf("Error writing results to validator %s: %s\n", p.Pretty(), err)
				stream.Reset() // Reset the stream on error

				continue
			}
			err = rw.Flush()
			mutex.Unlock()
			mutex.Lock()
			if err != nil {
				log.Printf("Error flushing stream to validator %s: %s\n", p.Pretty(), err)
				stream.Reset() // Reset the stream on error
				continue
			}
			mutex.Unlock()

			mutex.Lock()

			// Close the stream after sending the results
			err = stream.Close()
			if err != nil {
				log.Printf("Error closing stream to validator %s: %s\n", p.Pretty(), err)
			}
			mutex.Unlock()
		}
	}

	log.Println("Sent results to all validators")
}
*/
// peerRoles maps a peer.ID to a role (e.g., "Validator", "Miner", "Dataholder")
//var peerRoles = make(map[peer.ID]string)

// Update the global variables to use the Configuration struct
var config Configuration

func isValidatorPeer(peerID peer.ID) bool {
	log.Println("dans isvalidatorpeer avec peerID:", peerID)

	// Charger les données de config.host et mettre à jour peerRoles
	config, err := loadConfigurationFromFile("config.json")
	if err != nil {
		log.Println("Error loading configuration:", err)
		return false
	}
	peerRoles = config.PeerRoles

	log.Println("dans isvalidatorpeer, peerRoles:", peerRoles)

	// Imprimer tous les éléments de peerRoles après la mise à jour
	for _, role := range peerRoles {
		log.Printf("Peer ID: %s, Role: %s\n", role.PeerID, role.Role)
	}
	// Vérifier si le peer est un validateur
	for _, pr := range peerRoles {
		log.Println("dans isvalidatorpeer ares for, pr.PeerID:", pr.PeerID)
		log.Println("dans isvalidatorpeer ares for, pr.Role:", pr.Role)

		//		if pr.PeerID == peerID && pr.Role == "Validator" {
		if pr.Role == "Validator" {

			log.Println("dans isvalidatorpeer, il est un validateur:", pr)
			return true
		}
	}
	return false
}

// isMinerPeer checks if a given peer ID corresponds to a miner node.

func isMinerPeer(peerID peer.ID) bool {

	// Charger les données de config.host et mettre à jour peerRoles
	config, err := loadConfigurationFromFile("config.json")
	if err != nil {
		log.Println("Error loading configuration:", err)
		return false
	}
	peerRoles = config.PeerRoles

	log.Println("dans isMinerPeer, peerRoles:", peerRoles)

	// Imprimer tous les éléments de peerRoles après la mise à jour
	for _, role := range peerRoles {
		log.Printf("Peer ID: %s, Role: %s\n", role.PeerID, role.Role)
	}
	// Vérifier si le peer est un validateur
	for _, pr := range peerRoles {
		log.Println("dans isMinerPeer ares for, pr.PeerID:", pr.PeerID)
		log.Println("dans isMinerPeer ares for, pr.Role:", pr.Role)

		return true

	}
	return false
}

// setPeerRole sets the role of a peer by their ID.
func setPeerRole(peerID peer.ID, role string) {
	log.Printf("I am %s and I have the ID %s\n", role, peerID)
	newPeerRole := PeerRole{
		PeerID: peerID,
		Role:   role,
	}
	switch role {
	case "Validator":
		mutex.Lock()
		config.NumValidators++
		config.PeerRoles = append(config.PeerRoles, newPeerRole)
		mutex.Unlock()
	case "Miner":
		mutex.Lock()
		config.NumMiners++
		config.PeerRoles = append(config.PeerRoles, newPeerRole)
		mutex.Unlock()
	case "Dataholder":
		// Assuming "Dataholder" is a role you might have
		// Update any relevant count for Dataholders if needed
		mutex.Lock()
		config.PeerRoles = append(config.PeerRoles, newPeerRole)
		mutex.Unlock()
	default:
		// Handle other roles or display an error message
		log.Printf("Unknown role: %s\n", role)
	}

	// Log the size of peerRoles
	log.Printf("Size of peerRoles: %d\n", len(config.PeerRoles))
	// Print debug information
	log.Printf("Debug: PeerID: %s, Role: %s\n", peerID, role)

	// Update the count of connected peers
	config.ConnectedPeers = len(config.PeerRoles)
}

// removePeerRole removes a peer from the roles map and updates counts.
func removePeerRole(peerID peer.ID) {
	// Find the index of the peer in the PeerRoles slice
	var indexToRemove int
	for i, pr := range config.PeerRoles {
		if pr.PeerID == peerID {
			indexToRemove = i
			break
		}
	}

	// If the peer exists, update counts and remove it
	if indexToRemove < len(config.PeerRoles) {
		switch config.PeerRoles[indexToRemove].Role {
		case "Validator":
			config.NumValidators--
		case "Miner":
			config.NumMiners--
		case "Dataholder":
			// Update any relevant count for Dataholders if needed
		}

		// Remove the peer from the slice
		config.PeerRoles = append(config.PeerRoles[:indexToRemove], config.PeerRoles[indexToRemove+1:]...)
		config.ConnectedPeers = len(config.PeerRoles) // Update the count of connected peers
	}
}

func extractCentroids(peerID string) [][]float64 {
	// Mock implementation
	return [][]float64{{1.0, 2.0}, {3.0, 4.0}}
}

func setupValidatorStreamHandler(ha host.Host) {
	log.Println("Setting up stream handler for the validator...")

	ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
		log.Println("Validator: Received a new stream from a miner.")

		// Create a buffer stream for non-blocking read and write.
		rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

		// Read data from the stream
		rawData, err := rw.ReadString('\n')
		log.Println("I am validator rawData is :", rawData)
		if err != nil {
			log.Printf("Validator: Error reading from stream - %s", err)
			s.Reset() // Reset the stream on error
			return
		}

		// Log the raw data received for debugging
		log.Printf("VVVVVVValidator: Raw data received from miner - %s", rawData)

		// Process the received data
		// Adjusted to remove the rw parameter
	})

	log.Println("Stream handler for the validator is now set.")
}

func validator(ha host.Host, roleValue string) {
	log.Println("Starting Validator...")
	log.Println("ammm a ", ha.ID())
	if roleValue == "Validator" {
		log.Println("Validator has started and is entering the listening state.")
		// Set up a stream listener for incoming data from miners
		ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
			// Get the peer ID of the remote peer
			peerID := s.Conn().RemotePeer()

			// Check if the remote peer is a miner
			if isMinerPeer(peerID) {
				log.Println("Validator: Received a new stream from a miner.")

				// Create a buffer stream for non-blocking read and write.
				rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

				// Read data from the stream
				rawData, err := rw.ReadString('\n')
				log.Println("Validator received data: ", rawData)

				if err != nil {
					log.Printf("Validator: Error reading from stream - %s", err)
					s.Reset() // Reset the stream on error
					return
				}

				// Log the raw data received for debugging
				log.Printf("Validator: Raw data received from miner - %s", rawData)
				if len(rawData) > 2 {
					// Process the received data
					done := make(chan struct{})
					processMinerData(rw, rawData, done)
					<-done // Wait for processing to finish
				}
			} else {
				// If the remote peer is not a miner, close the stream
				log.Println("Validator: Received a stream from a non-miner or is an NBCluster. Closing the stream.")
				s.Close()
			}
		})
	}
}

/*
func validator(ha host.Host, rolevalue string) {
	log.Println("Starting Validator...")
	log.Println("ammm a ", ha.ID())
	if roleValue == "Validator" {
		log.Println("Validator has started and is entering the listening state.")

		// Set up a stream listener for incoming data from miners
		ha.SetStreamHandler("/p2p/1.0.0", func(s network.Stream) {
			log.Println("Validator: Received a new stream from a miner.")

			// Create a buffer stream for non-blocking read and write.
			rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

			// Read data from the stream
			rawData, err := rw.ReadString('\n')
			log.Println("am am validator recevived  data is %s ", rawData)

			if err != nil {
				log.Printf("Validator: Error reading from stream - %s", err)
				s.Reset() // Reset the stream on error
				return
			}

			// Log the raw data received for debugging
			log.Printf("Validator: Raw data received from miner - %s", rawData)

			// Process the received data
			processMinerData(rw, rawData)
		})
		log.Println("Validator is now listening for incoming streams.")
	}

}
*/

func handleBlockchainSync(s network.Stream) {
	// Create a buffer stream for non-blocking read and write.
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the incoming blockchain data from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}

	// Check if the received data is not just a newline character
	if str != "\n" {
		chain := make([]Block, 0)
		if err := json.Unmarshal([]byte(str), &chain); err != nil {
			log.Fatal(err)
		}

		mutex.Lock()
		// If the received chain is longer than the current blockchain, replace it
		if len(chain) > len(Blockchain) {
			Blockchain = chain
			bytes, err := json.MarshalIndent(Blockchain, "", "  ")
			if err != nil {
				log.Fatal(err)
			}
			// Print the updated blockchain in green color
			fmt.Printf("\x1b[32m%s\x1b[0m> ", string(bytes))
		}
		mutex.Unlock()
	}
}

// saveBlockAndBroadcast saves the block to the database and broadcasts it to the network
func saveBlockAndBroadcast(rw *bufio.ReadWriter, block Block) {

	// Save the block to the database
	db, err := bolt.Open("my.db", 0600, nil)
	if err != nil {
		log.Fatal(err)
		return
	}
	defer db.Close()

	err = Save(block, db)
	if err != nil {
		log.Fatalln(err)
		return
	}

	// Serialize the blockchain and send it to the network
	bytes, err := json.Marshal(Blockchain)
	if err != nil {
		log.Println(err)
		return
	}
	spew.Dump(Blockchain)

	mutex.Lock()
	_, err = rw.WriteString(fmt.Sprintf("%s\n", string(bytes)))

	rw.WriteString(fmt.Sprintf("%s\n", string(bytes)))

	if err != nil {
		log.Println("Error sending blockchain to network:", err)
	} else {
		err = rw.Flush()
		if err != nil {
			log.Println("Error flushing stream:", err)
		}
	}
	mutex.Unlock()
}

var receivedMiners = make(map[string]bool)

func receivedFromAllMiners() bool {
	// Implement your logic to check if you have received from all miners
	return len(receivedMiners) == numMiners
}

// AggregateCentroids takes multiple sets of centroids and aggregates them by computing the mean.
func AggregateCentroids(centroidsSets [][][]float64) [][]float64 {
	if len(centroidsSets) == 0 {
		return nil
	}

	// Initialize the aggregated centroids with the first set of centroids
	numCentroids := len(centroidsSets[0])
	numDimensions := len(centroidsSets[0][0])
	aggregatedCentroids := make([][]float64, numCentroids)

	for i := range aggregatedCentroids {
		aggregatedCentroids[i] = make([]float64, numDimensions)
	}

	// Sum up the centroids
	for _, centroids := range centroidsSets {
		for i, centroid := range centroids {
			for j, coord := range centroid {
				aggregatedCentroids[i][j] += coord
			}
		}
	}

	// Calculate the mean by dividing each coordinate sum by the number of sets
	numSets := float64(len(centroidsSets))
	for i := range aggregatedCentroids {
		for j := range aggregatedCentroids[i] {
			aggregatedCentroids[i][j] /= numSets
		}
	}

	return aggregatedCentroids
}

// / splitDataset splits the dataset into parts for peers.

func splitDataset(dataset [][]float64, numPeers int) ([][][]float64, error) {

	if numPeers == 0 {
		return nil, fmt.Errorf("Number of miners should be greater than 0")
	}
	if len(dataset) == 0 {
		return nil, fmt.Errorf("Data cannot be empty")
	}

	numDataPoints := len(dataset)
	//fmt.Println("numDataPoints")
	//fmt.Println(numPeers)
	dataPerMiner := numDataPoints / numPeers
	//fmt.Println(dataPerMiner)
	//fmt.Println(dataPerMiner)
	partitions := make([][][]float64, numPeers)
	for i := 0; i < numPeers; i++ {
		start := i * dataPerMiner

		end := (i + 1) * dataPerMiner

		if i == numPeers-1 {
			end = numDataPoints // Last miner takes any remaining data points

		}

		partitions[i] = dataset[start:end]
	}

	return partitions, nil

}

// Euclidean distance
func Euclidean(p []float64, q []float64) (d float64, err error) {
	//if err = validateInputs(p, q); err != nil {
	//	return
	//}
	for i, pi := range p {
		d += (pi - q[i]) * (pi - q[i])
	}
	return math.Sqrt(d), nil
}

// Serialize serializes the block
func (b *Block) Serialize() []byte {
	var result bytes.Buffer
	encoder := gob.NewEncoder(&result)

	err := encoder.Encode(b)
	if err != nil {
		log.Panic(err)
	}

	return result.Bytes()
}

// DeserializeBlock deserializes a block
func DeserializeBlock(d []byte) Block {
	var block Block

	decoder := gob.NewDecoder(bytes.NewReader(d))
	err := decoder.Decode(&block)
	if err != nil {
		log.Panic(err)
	}

	return block
}

func Save(block Block, db *bolt.DB) error {

	//log.Println("in the save")
	err = db.Update(func(tx *bolt.Tx) error {
		b := tx.Bucket([]byte(blocksBucket))

		if b == nil {
			fmt.Println("No existing blockchain found. Creating a new one...")

			b, err := tx.CreateBucket([]byte(blocksBucket))
			if err != nil {
				log.Panic(err)
			}

			err = b.Put([]byte(calculateHash(block)), block.Serialize())
			if err != nil {
				log.Panic(err)
			}

			err = b.Put([]byte("l"), []byte(calculateHash(block)))
			if err != nil {
				log.Panic(err)
			}
			//tip = genesisBlock.Hash
		} else {
			//tip = b.Get([]byte("l"))
		}

		return nil
	})

	if err != nil {
		log.Panic(err)
	}

	/*
		err1 := db.View(func(tx *bolt.Tx) error {
			// Assume bucket exists and has keys
			c := tx.Bucket([]byte("blocksBucket")).Cursor()

			prefix := []byte("1234")
			for k, v := c.Seek(prefix); k != nil && bytes.HasPrefix(k, prefix); k, v = c.Next() {
				fmt.Printf("key=%s, value=%s\n", k, v)
			}

			return nil
		})
		if err1 != nil {
			log.Panic(err)
		}
	*/
	//log.Println("avant e view in the save")

	db.View(func(tx *bolt.Tx) error {
		// Assume bucket exists and has keys

		bb := tx.Bucket([]byte(blocksBucket))

		bb.ForEach(func(k, v []byte) error {

			//fmt.Printf("key=%s, value=%s\n", k, string(v))
			return nil
		})
		return nil
	})
	//log.Println("apres e view in the save")
	return nil
}

// Loop output block
func ShowBlockChain() {
	//log.Println("ShowBlockChain")

	//log.Println("apres logShowBlockChain")
	db.View(func(tx *bolt.Tx) error {
		//log.Println("ininview")
		bucket := tx.Bucket([]byte(blocksBucket))

		if bucket != nil {
			lastblockhash := bucket.Get([]byte("LastBlockHash"))

			if lastblockhash == nil {
				panic("lastblock is not exist !")
			} else {
				lastblock := bucket.Get([]byte(lastblockhash))
				toBlock := DeserializeBlock(lastblock)

				fmt.Println()
				fmt.Println(toBlock)

				for {
					hash := toBlock.PrevHash
					get := bucket.Get([]byte(hash))
					toBlock := DeserializeBlock(get)
					fmt.Println(toBlock)
					if toBlock.PrevHash == "" {
						break
					}

				}
			}

		} else {
			panic("bucket is not exist !")
		}
		return nil
	})

}

func Equal(a, b []float64) bool {
	if len(a) != len(b) {
		return false
	}
	for i, v := range a {
		if v != b[i] {
			return false
		}
	}
	return true
}

func readdataset(filePath string) [][]float64 {
	irisMatrix := [][]string{}
	//fmt.Println("filePath")
	//fmt.Println(filePath)

	f, err := os.Open(filePath)
	if err != nil {
		log.Fatal("Unable to read input file "+filePath, err)
	}
	defer f.Close()

	reader := csv.NewReader(f)
	reader.Comma = ','
	reader.LazyQuotes = true
	_, err = reader.Read() // skip first line
	if err != nil {
		fmt.Println("kayan erreur")
		if err != io.EOF {
			log.Fatalln(err)
		}
	}
	for {
		record, err := reader.Read()
		if err == io.EOF {
			break
		} else if err != nil {
			panic(err)
		}
		irisMatrix = append(irisMatrix, record)

	}

	X := [][]float64{}
	Y := []string{}
	for _, data := range irisMatrix {
		//convert str-slice into float-slice
		temp := []float64{}
		for _, i := range data[:4] {
			parsedValue, err := strconv.ParseFloat(i, 64)
			if err != nil {
				panic(err)
			}
			temp = append(temp, parsedValue)
		}
		//to explaining variables
		X = append(X, temp)
		//fmt.Println(X)
		//to explained variable
		Y = append(Y, data[4])
	}

	return X
}
func (km *Kmeans) fit(X [][]float64, k int) []int {
	//set random number seeds
	mrand.Seed(time.Now().UnixNano())
	//store data into structure
	km.Data = X

	//initialize representative vectors
	//to define the random number range for initialization of representative point, check the max and minimum values of each explaining variables
	transposedData := Transpose(km.Data)
	var minMax [][]float64
	for _, d := range transposedData {
		var (
			min float64
			max float64
		)
		for _, n := range d {
			min = math.Min(min, n)
			max = math.Max(max, n)
		}
		minMax = append(minMax, []float64{min, max})
	}
	//set initital values of representative points
	for i := 0; i <= k; i++ {
		km.Representatives = append(km.Representatives, make([]float64, len(minMax)))
		log.Println("km.Representatives", i)
	}
	log.Println("km.Representatives", len(km.Representatives))
	for i := 0; i <= k; i++ {
		for j := 0; j < len(minMax); j++ {
			km.Representatives[i][j] = mrand.Float64()*(minMax[j][1]-minMax[j][0]) + minMax[j][0]
		}
	}
	log.Println("km.Representatives", len(km.Representatives))
	//initialize label
	//calclate distance between each data and representative point and give label
	for _, d := range km.Data {
		var distance []float64
		for _, r := range km.Representatives {
			distance = append(distance, Dist(d, r))
		}
		km.Labels = append(km.Labels, ArgMin(distance))
	}
	for {
		//update representative point
		//set the centroid of the data which belong to the representative point as updated representative point
		//index i means the label
		var tempRepresentatives [][]float64
		for i, _ := range km.Representatives {
			var grouped [][]float64
			for j, d := range km.Data {
				if km.Labels[j] == i {
					grouped = append(grouped, d)
				}
			}
			if len(grouped) != 0 {

				transposedGroup := Transpose(grouped)
				updated := []float64{}
				for _, vectors := range transposedGroup {

					value := 0.0
					for _, v := range vectors {
						value += v
					}
					//store mean of each explaining variables
					updated = append(updated, value/float64(len(vectors)))
				}
				tempRepresentatives = append(tempRepresentatives, updated)
			}
		}
		km.Representatives = tempRepresentatives

		//update labels
		tempLabel := []int{}
		for _, d := range km.Data {
			var distance []float64
			for _, r := range km.Representatives {
				distance = append(distance, Dist(d, r))
			}
			tempLabel = append(tempLabel, ArgMin(distance))
		}
		if reflect.DeepEqual(km.Labels, tempLabel) {
			break
		} else {
			km.Labels = tempLabel
		}
	}
	return km.Labels
}
func convertFloat64ToInt(data [][]float64) [][]int {
	intData := make([][]int, len(data))
	for i := range data {
		intData[i] = make([]int, len(data[i]))
		for j := range data[i] {
			intData[i][j] = int(data[i][j])
		}
	}
	return intData
}

func performClustering(peerID peer.ID) []ClusteringResult {
	// Retrieve the dataset partition assigned to the miner identified by peerID
	datasetPartition := getDatasetPartition(peerID)

	// Perform clustering using the Kmeans algorithm
	var km Kmeans
	labels := km.fit(datasetPartition.Partition, datasetPartition.NBCluster)

	// Prepare the clustering result
	clusteringResult := ClusteringResult{
		Data:            convertFloat64ToInt(datasetPartition.Partition),
		Labels:          labels,
		Representatives: km.Representatives,
	}

	return []ClusteringResult{clusteringResult}
}

func publishCentroidsForValidation(ctx context.Context, ps *pubsub.PubSub, topicName string, subgroupName string, centroids [][]float64) error {
	// Create the request payload
	validationRequest := ValidationRequest{
		SubgroupName: subgroupName,
		Centroids:    centroids,
	}

	// Convert the request payload to JSON
	jsonData, err := json.Marshal(validationRequest)
	if err != nil {
		return err
	}

	// Get the pubsub topic
	topic, err := ps.Join(topicName)
	if err != nil {
		return err
	}

	// Publish the data to the topic
	err = topic.Publish(ctx, jsonData)
	if err != nil {
		return err
	}

	log.Println("Centroids published to pubsub topic successfully.")
	return nil
}
func storeAggregatedCentroids(subgroupName string, centroids [][]float64) {
	// Mock implementation for storing aggregated centroids
	log.Println("Stored aggregated centroids for subgroup:", subgroupName)
}

// Helper function to retrieve the dataset partition assigned to a miner
func getDatasetPartition(peerID peer.ID) DatasetPartition {
	for _, partition := range datasetPartitions {
		if partition.MinerID == peerID.String() {
			return partition
		}
	}
	return DatasetPartition{} // Return an empty partition if not found
}

// Transpose convertir forme des donne a un format bien prési
func Transpose(source [][]float64) [][]float64 {
	var dest [][]float64
	for i := 0; i < len(source[0]); i++ {
		var temp []float64
		for j := 0; j < len(source); j++ {
			temp = append(temp, 0.0)
		}
		dest = append(dest, temp)
	}

	for i := 0; i < len(source); i++ {
		for j := 0; j < len(source[0]); j++ {
			dest[j][i] = source[i][j]
		}
	}
	//fmt.Println("dest")
	//fmt.Println(dest)
	return dest
}

// calculate the distance between two points.Euclidean
func Dist(source, dest []float64) float64 {
	var dist float64
	for i, _ := range source {
		dist += math.Pow(source[i]-dest[i], 2)
	}
	//fmt.Println("am in dist")
	//fmt.Println(dist)
	return math.Sqrt(dist)
}

// return index at the point whose value is the smallest on the slice
func ArgMin(target []float64) int {
	var (
		index int
		base  float64
	)
	for i, d := range target {
		if i == 0 {
			index = i
			base = d
		} else {
			if d < base {
				index = i
				base = d
			}
		}

	}
	return index
}

// Fonction pour ajouter des données à IPFS et retourner le CID de la nouvelle entrée
func addDataToIPFS(data [][]float64) (string, error) {
	// Initialiser le client IPFS
	api := shell.NewShell("localhost:5001")

	// Convertir les données en JSON
	dataJSON, err := json.Marshal(data)
	if err != nil {
		return "", err
	}

	// Ajouter les données JSON à IPFS
	cid, err := api.Add(bytes.NewReader(dataJSON))
	if err != nil {
		return "", err
	}

	return cid, nil
}

/*// Function to add dataset partition to IPFS and return its CID
func addDatasetPartitionToIPFS(api *shell.Shell, partition DatasetPartition) (string, error) {
	// Convert DatasetPartition to JSON
	partitionJSON, err := json.Marshal(partition)
	if err != nil {
		return "", err
	}

	// Add JSON data to IPFS
	cid, err := api.Add(strings.NewReader(string(partitionJSON)))
	if err != nil {
		return "", err
	}

	return cid, nil
}
*/
// Function to fetch dataset partition from IPFS using its CID
// Fetch dataset partition from IPFS using the provided CID
// Fetch dataset partition from IPFS using the provided CID
// Fetch dataset partition from IPFS using the provided CID
func fetchDatasetPartitionFromIPFS(api *shell.Shell, cid string) ([][]float64, error) {
	// Retrieve data from IPFS
	resp, err := api.Cat(cid)
	if err != nil {
		return nil, err
	}
	defer resp.Close()

	// Read data from response
	data, err := ioutil.ReadAll(resp)
	if err != nil {
		return nil, err
	}

	// Parse CSV data
	r := csv.NewReader(bytes.NewReader(data))
	records, err := r.ReadAll()
	if err != nil {
		return nil, err
	}

	// Convert string records to float64 values
	var partition [][]float64
	for i, record := range records {
		if i == 0 {
			// Skip header row
			continue
		}
		var row []float64
		for _, value := range record {
			// Attempt to convert string value to float64
			v, err := strconv.ParseFloat(value, 64)
			if err != nil {
				// If conversion fails, skip this value
				continue
			}
			row = append(row, v)
		}
		// Append the row to the partition if it's not empty
		if len(row) > 0 {
			partition = append(partition, row)
		}
	}

	return partition, nil
}

// Function to add dataset partition to IPFS and update its CID
func addDatasetPartitionToIPFSAndUpdateCID(api *shell.Shell, partition *DatasetPartition) error {
	// Convert DatasetPartition to JSON
	partitionJSON, err := json.Marshal(partition)
	if err != nil {
		return err
	}

	// Add JSON data to IPFS
	cid, err := api.Add(strings.NewReader(string(partitionJSON)))
	if err != nil {
		return err
	}

	// Update PartitionCID field
	partition.PartitionCID = cid

	return nil
}

// Function to get CID of dataset partition
func partitionCID(partition [][]float64) (string, error) {
	// Create DatasetPartition struct
	partitionData := &DatasetPartition{
		Partition: partition,
	}

	// Add dataset partition to IPFS and get CID
	err := addDatasetPartitionToIPFSAndUpdateCID(api, partitionData)
	if err != nil {
		return "", err
	}

	// Return the CID
	return partitionData.PartitionCID, nil
}

// Function to retrieve CID for a miner from the dataset partitions
func getCIDForMiner(minerID string) (string, bool) {
	// Iterate over dataset partitions to find the partition for the given miner
	for _, partition := range datasetPartitions {
		if partition.MinerID == minerID {
			// Return the PartitionCID for the matching miner
			return partition.PartitionCID, true
		}
	}
	// If no matching partition is found, return false
	return "", false
}

func handleMinerStream(s network.Stream, ha host.Host, minerID string, partitionCID string) {
	log.Println("Starting handleMinerStream function...")

	// Create a buffer stream for non-blocking read and write
	rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

	// Read the NBCluster value from the stream
	str, err := rw.ReadString('\n')
	if err != nil {
		log.Printf("Error reading from stream: %s", err)
		s.Reset() // Reset the stream on error
		return
	}
	log.Printf("Received string representation of NBCluster: %s\n", str)

	// Parse the NBCluster value
	NBCluster, err := strconv.Atoi(strings.TrimSpace(str))
	if err != nil {
		log.Printf("Error parsing NBCluster value: %s\n", err)
		return
	}

	// Log the received NBCluster value
	log.Printf("Received NBCluster value: %d\n", NBCluster)

	// Fetch dataset partition from IPFS using the provided CID
	partitionData, err := fetchDatasetPartitionFromIPFS(api, partitionCID)
	//log.Printf("partitionDatapartitionDatapartitionData partitionDatavalue: %s\n", partitionData)
	if err != nil {
		log.Printf("Error fetching dataset partition from IPFS: %v\n", err)
		return
	}

	// Perform clustering on the partition
	km := Kmeans{}
	km = handleMiner(ha, partitionData, NBCluster)

	// Perform K-means clustering on the miner's data partition
	clusterResults := km.fit(partitionData, NBCluster)

	// Print the clustering results
	fmt.Printf("predict: %v\n", clusterResults)
	fmt.Printf("Clustering results: %v\n", km.Representatives)

	// Send clustering results to the Validator
	sendResultsToValidator(ha, minerID, NBCluster, km)

	log.Println("Miner finished its work")
}
func processMinerData(rw *bufio.ReadWriter, rawData string, done chan struct{}) {
	log.Println("Validator: Received data from Miner -", rawData)

	// Unmarshal the JSON data into a ValidationResult struct
	var validationResult ValidationResult
	err := json.Unmarshal([]byte(rawData), &validationResult)
	if err != nil {
		log.Println("Validator: Error unmarshaling miner data -", err)
		return
	}

	var allCentroids [][][]float64
	// Example: Print the number of clusters and miner results
	log.Printf("Number of clusters: %d", validationResult.NBCluster)
	for _, minerResult := range validationResult.MinerResults {
		log.Printf("Miner ID: %s, Representatives: %v", minerResult.MinerID, minerResult.Representatives)
	}

	// Process each Kmeans object as needed
	for _, km := range validationResult.MinerResults {
		log.Println("Validator: Processed Kmeans ", km)
		silhouetteScore := handleValidator(km)
		log.Println("Validator: Silhouette Score ", silhouetteScore)

		// Check if the silhouette score is above the threshold
		if silhouetteScore >= threshold {
			// Aggregate centroids
			allCentroids = append(allCentroids, km.Representatives)
		}
	}

	// Other parts of the function...

	// Notify that processing is done
	done <- struct{}{}
}

// getRoleForPeer recherche le rôle d'un pair en fonction de son ID
func getRoleForPeer(peerID peer.ID) (string, error) {
	// Parcourez la liste des rôles des pairs
	for _, role := range peerRoles {
		// Si le peerID correspond, retournez son rôle
		if role.PeerID == peerID {
			return role.Role, nil
		}
	}
	// Si aucun rôle n'est trouvé pour ce peerID, retournez une erreur
	return "", fmt.Errorf("no role found for peer %s", peerID)
}
func discoverPeers(ha host.Host) ([]peer.ID, error) {
	// Initialiser le protocole DHT
	dht, err := dht.New(context.Background(), ha)
	if err != nil {
		return nil, err
	}

	// Joindre le réseau DHT
	if err := dht.Bootstrap(context.Background()); err != nil {
		return nil, err
	}

	// Requêtez la DHT pour récupérer la liste des pairs
	peers := dht.RoutingTable().ListPeers()
	return peers, nil
}

func hasHighestSilhouetteScore(scores map[peer.ID]float64, myPeerID peer.ID) bool {
	highestScore := -1.0
	for _, score := range scores {
		if score > highestScore {
			highestScore = score
		}
	}
	// Return true if the current miner's score is the highest
	return scores[myPeerID] == highestScore
}
func broadcastBlock(ctx context.Context, h host.Host, topic *pubsub.Topic, block Block, peers []peer.ID) error {
	// Serialize the block to JSON
	blockBytes, err := json.Marshal(block)
	if err != nil {
		return err
	}

	// Publish the serialized block to the given topic
	errr := topic.Publish(context.Background(), blockBytes)

	if errr != nil {
		log.Printf("Failed to broadcast block: %s", err)
		return err
	}
	log.Println("Successfully broadcasted block")
	// Iterate over all peers and send them the new block
	for _, peerID := range peers {
		// Skip sending the block to ourselves
		if peerID == h.ID() {
			continue
		}

		// Open a new stream to the peer
		stream, err := h.NewStream(context.Background(), peerID, "/p2p/1.0.0")
		if err != nil {
			log.Printf("Error opening stream to peer %s: %s", peerID, err)
			continue
		}

		// Create a buffered writer for the stream
		rw := bufio.NewReadWriter(bufio.NewReader(stream), bufio.NewWriter(stream))

		// Send the block to the peer
		_, err = rw.Write(blockBytes)
		if err != nil {
			log.Printf("Error sending block to peer %s: %s", peerID, err)
			stream.Reset()
			continue
		}
		err = rw.Flush()
		if err != nil {
			log.Printf("Error flushing stream to peer %s: %s", peerID, err)
			stream.Reset()
			continue
		}

		// Close the stream after sending the block
		stream.Close()
	}

	// Print the new block
	printBlockchain([]Block{newBlock})

	return nil
}

func printBlockchain(chain []Block) {
	bytes, err := json.MarshalIndent(chain, "", "  ")
	if err != nil {
		log.Printf("Error marshaling blockchain: %s", err)
		return
	}
	// Display the blockchain in green
	fmt.Printf("\x1b[32m%s\x1b[0m\n", string(bytes))
}
func getNumberOfMinerPeers(ha host.Host, peerRoles map[peer.ID]string) int {
	minerCount := 0
	peers := ha.Network().Peers()
	for _, peerID := range peers {
		if role, ok := peerRoles[peerID]; ok && role == "Miner" {
			minerCount++
		}
	}
	return minerCount
}

// Function to get the number and IDs of Miner peers
func preprocess(filePath string) [][]float64 {
	// Open the CSV file
	f, err := os.Open(filePath)
	if err != nil {
		log.Fatal("Unable to read input file "+filePath, err)
	}
	defer f.Close()

	// Create a CSV reader
	reader := csv.NewReader(f)
	reader.Comma = ','

	// Initialize the preprocessed data slice
	preprocessedData := [][]float64{}

	// Read the header line (to skip it)
	_, err = reader.Read()
	if err != nil {
		log.Fatal("Error reading header", err)
	}

	// Read all records from the CSV file
	for {
		record, err := reader.Read()
		if err == io.EOF {
			break
		}
		if err != nil {
			log.Fatal(err)
		}

		// Convert the "Gender" column to a numeric representation (0 for Female, 1 for Male)
		genderValue := 0.0 // Assume Female by default
		if record[1] == "Male" {
			genderValue = 1.0
		}

		// Convert the other numeric columns to float64
		numericValues := []float64{}
		for i := 2; i < len(record); i++ {
			value, err := strconv.ParseFloat(record[i], 64)
			if err != nil {
				log.Fatalf("Error parsing value %s: %v", record[i], err)
			}
			numericValues = append(numericValues, value)
		}

		// Append the one-hot encoded gender value and numeric values to the preprocessed data
		preprocessedRecord := append([]float64{genderValue}, numericValues...)
		preprocessedData = append(preprocessedData, preprocessedRecord)
	}

	// Return the preprocessed data
	return preprocessedData
}
