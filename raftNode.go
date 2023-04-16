package main

import (
	"bufio"
	"fmt"
	"log"
	"math/rand"
	"net/http"
	"net/rpc"
	"os"
	"strconv"
	"sync"
	"time"
)

type RaftNode int

// input for RequestVote RPC
// not using lastLogIndex; lastLogTerm
type VoteArguments struct {
	Term        int // candidate's term
	CandidateID int // candidate requesting vote
}

// output for RequestVote RPC
type VoteReply struct {
	Term       int  // current term, for candidate to update itself
	ResultVote bool // true if candidate recieved vote
}

// input for AppendEntries RPC
// prevLogIndex, prevLogTerm, entries[],and leaderCommit all refer to logs and will not be used here
type AppendEntryArgument struct {
	Term         int // leader's term
	LeaderID     int // so follower can redirect clients
	prevLogIndex int
	prevLogTerm  int
	entries      []LogEntry
	leaderCommit int
}

// output for AppendEntries RPC
type AppendEntryReply struct {
	Term    int  // current term, allowing leader to update itself
	Success bool // true if term >= currentTerm; normally: true if follower contained entry matching prevLogIndex and prevLogTerm
}

type ServerConnection struct {
	serverID      int
	Address       string
	rpcConnection *rpc.Client
}

type LogEntry struct {
	Index int
	Term  int
}

var selfID int
var serverNodes []ServerConnection
var currentTerm int
var votedFor int
var electionTimeout *time.Timer
var isLeader bool
var timerDuration time.Duration

// from Raft paper
var prevLogIndex int
var prevLogTerm int
var leaderCommit int

// state variables
var commitIndex int

// provided by Christine
var lastApplied int

var logEntries []LogEntry

var wg sync.WaitGroup

// The RequestVote RPC as defined in Raft
// Hint 1: Use the description in Figure 2 of the paper
// Hint 2: Only focus on the details related to leader election and majority votes
func (*RaftNode) RequestVote(arguments VoteArguments, reply *VoteReply) error {
	//all RPCs function as heartbeats
	//this should not print
	fmt.Printf("Candidate %d is requesting a vote from Follower %d\n", arguments.CandidateID, selfID)
	//clear the votedFor if we are in a new election
	if arguments.Term > currentTerm {
		votedFor = -1
	}

	//if this machine hasn't voted yet in this term, voted for will be -1
	if votedFor == -1 {
		//if the request is coming from a lesser term, then don't vote for it
		if arguments.Term < currentTerm {
			reply.ResultVote = false
			//tell the candidate our term?
			reply.Term = currentTerm
			fmt.Printf("Server %d (term #%d) REJECTED Candidate %d (term #%d) because we are in higher term\n", selfID, currentTerm, arguments.CandidateID, arguments.Term)
		} else { //otherwise if the candidate is higher term (or same term?) as us, we can vote for it
			fmt.Println("---->I GOT TO WHERE I AM GOING TO VOTE")
			reply.ResultVote = true
			currentTerm = arguments.Term //update term
			if isLeader {
				isLeader = false //no longer leader (if previously leader)
				fmt.Printf("I was leader, but now I am not\n")
			}
			votedFor = arguments.CandidateID
			fmt.Printf("VOTED FOR Candidate %d in term #%d\n", arguments.CandidateID, currentTerm)
		} /*else {
			fmt.Println("--->FIGURE OUT WHAT TO DO IN THIS SCENARIO")
		}*/
	} else if votedFor == arguments.CandidateID {
		fmt.Println("---->I GET TO WHERE I AM GOING TO VOTE")
		reply.ResultVote = true
		currentTerm = arguments.Term //update term
		if isLeader {
			isLeader = false //no longer leader (if previously leader)
			fmt.Printf("I was leader, but now I am not\n")
		}
		votedFor = arguments.CandidateID
		fmt.Printf("VOTED FOR Candidate %d in term #%d\n", arguments.CandidateID, currentTerm)
	} else {
		fmt.Printf("I already voted for %d in this term #%d\n", votedFor, currentTerm)
		reply.ResultVote = false
		reply.Term = currentTerm
	}
	return nil

}

// The AppendEntry RPC as defined in Raft
// Hint 1: Use the description in Figure 2 of the paper
// Hint 2: Only focus on the details related to leader election and heartbeats
func (*RaftNode) AppendEntry(arguments AppendEntryArgument, reply *AppendEntryReply) error {
	fmt.Printf("Got RPC from Leader %d in term #%d\n", arguments.LeaderID, arguments.Term)
	stopped := restartTimer() //returns true if timer was going
	//if recieves a heartbeat, we must be a follower
	if isLeader {
		isLeader = false //no longer leader (if previously leader)
		fmt.Printf("I was leader, but now I am not (found out when receiving a heartbeat)")
	}

	//might need to update our term
	if arguments.Term != currentTerm {
		if arguments.Term < currentTerm {
			fmt.Printf("-- entry not appended because leader is out of sync!!")
			reply.Success = false //don't want to append entry in this scenario because the leader is out of sync
		} else {
			fmt.Printf("-- heartbeat CHANGED term from %d to %d", currentTerm, arguments.Term)
			currentTerm = arguments.Term
		}
	}

	//NEW
	//logEntry: index , term
	if logEntries[prevLogIndex].Term != prevLogTerm {
		fmt.Printf("-- entry not appended because the terms are out of sync!!")
		reply.Success = false
	}

	// if an existing entry conflicts with a new one (same index but diff. terms), delete existing entry and all that follow it
	for entryIndex := range logEntries {
		// check if any existing entries have the same index but diff. terms compared to new one
		if logEntries[entryIndex].Index == arguments.entries[entryIndex].Index && logEntries[entryIndex].Term != arguments.Term {
			// if there is a conflict:
			// update prevLogIndex and set it to the previous index, then delete all entries following that index.
			prevLogIndex = logEntries[entryIndex].Index - 1
			fmt.Printf("-- updated prevLogIndex to %d!", prevLogIndex)
			for i := logEntries[entryIndex].Index; i < len(logEntries); i++ {
				logEntries[i].Term = -1
				logEntries[i].Index = -1
			}
		} else {
			// iterate through sender's log. if any entries in sender's log do not match receiver's log (ie: different index/term combos), append to receiver's log.
			// start from receiver's prevLogIndex, don't look back (assume all correct)
			// sender's log, start at receiver's prevLogIndex
			for i := arguments.prevLogIndex; i < len(arguments.entries); i++ {
				if arguments.Term != logEntries[i].Term && arguments.entries[i].Index != logEntries[i].Index {
					newEntry := arguments.entries[i]
					logEntries[i] = newEntry
					prevLogIndex++
				}
			}
		}
	}

	if !stopped {
		fmt.Printf("leader %d's heartbeat recieved AFTER server %d's timer stopped'\n", arguments.LeaderID, selfID)
	}

	// if leader commit is greater than commit index, set commit index equal to minimum between leadercommit and prevlogindex
	if leaderCommit > commitIndex {
		if leaderCommit < prevLogIndex {
			commitIndex = leaderCommit
		} else {
			commitIndex = prevLogIndex
		}
	}

	//if the candidate's term is less than global currentTerm, reply.Success = FALSE
	return nil
}

// generate random duration
func randomTime() time.Duration {
	rand.Seed(time.Now().UnixNano())
	min := 1500  //ms
	max := 10000 //ms
	t := rand.Intn(max-min+1) + min
	//fmt.Printf("Server %d is using a %d ms timer\n", selfID, t)
	return time.Duration(t)
}

func StartTimer(t time.Duration) {
	//defer wg.Done()
	//start as a follower
	//fmt.Printf("Follfower %d is HERE\n", selfID)
	electionTimeout = time.NewTimer(t * time.Millisecond)
	wg.Add(1)
	go func() {
		<-electionTimeout.C //.C is a channel time object
		//become a candidate by starting leader election
		fmt.Printf("\nElection Timeout: %d is initating elections in term #%d\n", selfID, currentTerm+1)
		LeaderElection()
		wg.Done()
	}()
	wg.Wait()
	// if we get an RPC, restart the timer
}

func restartTimer() bool {
	//stop timer
	timer_was_going := electionTimeout.Stop()
	if timer_was_going {
		fmt.Println("Heartbeat recieved; timer was stopped")
	}
	//restart timer
	StartTimer(timerDuration)
	return timer_was_going
}

// You may use this function to help with handling the election time out
// Hint: It may be helpful to call this method every time the node wants to start an election
func LeaderElection() {
	currentTerm += 1 // increment current term
	//vote for self
	votedFor = selfID
	voteCounts := 1
	fmt.Printf(">> Recieved VOTE: self -> %d\n", selfID)
	//reset election timer (didn't we just do this?)
	//send RequestVote RPC to all other servers
	voteArgs := new(VoteArguments)
	voteArgs.Term = currentTerm
	voteArgs.CandidateID = selfID
	//var voteResult *VoteReply //NEED TO CREATE A NEW VOTEREPLY OBJECT FOR EACH CALL (I THINK PUT INSIDE THE FOR LOOP)
	//voteResult = new(VoteReply)
	for _, node := range serverNodes {
		fmt.Printf("requesting vote from: ")
		fmt.Println(node)
		//var voteResult *VoteReply //NEED TO CREATE A NEW VOTEREPLY OBJECT FOR EACH CALL (I THINK PUT INSIDE THE FOR LOOP)
		voteResult := new(VoteReply)

		serverCall := node.rpcConnection.Go("RaftNode.RequestVote", voteArgs, voteResult, nil)
		<-serverCall.Done
		if voteResult.ResultVote {
			voteCounts += 1 //recieved a vote
			fmt.Printf(">> Recieved VOTE: %d -> %d\n", node.serverID, selfID)
		} else {
			fmt.Printf(">> %d REJECTED %d \n", node.serverID, selfID)
			if voteResult.Term > currentTerm {
				currentTerm = voteResult.Term //catch up to current term
			}
		}
	}

	//if recieved majority of votes, become leader
	voteProportion := float64(voteCounts) / (float64(len(serverNodes) + 1))
	if voteProportion >= 0.5 {
		fmt.Printf("Elected LEADER %d with %d out of %d of the vote in TERM #%d\n", selfID, voteCounts, len(serverNodes)+1, currentTerm)
		electionTimeout.Stop()
		isLeader = true
		Heartbeat() //Make this continue until RequestVote is recieved
	} else {
		fmt.Printf("Server %d Lost election with %d of %d of the vote in TERM %d\n", selfID, voteCounts, len(serverNodes)+1, currentTerm)
		//restartTimer() //try to get elected again if no heartbeats are recieved
	}
	// if AppendEntries RPC recieved from new leader, convert to follower

	// if election timeout elapses, start a new election
}

// You may use this function to help with handling the periodic heartbeats
// Hint: Use this only if the node is a leader
func Heartbeat() {
	arg := new(AppendEntryArgument)
	arg.Term = currentTerm
	arg.LeaderID = selfID
	for isLeader {
		fmt.Printf("heartbeat - leader %d is pinging all servers!\n", selfID)
		reply := new(AppendEntryReply)
		for _, node := range serverNodes {
			node.rpcConnection.Go("RaftNode.AppendEntry", arg, &reply, nil)
		}
		time.Sleep(1 * time.Second) //pause
		//if you want to introduce failures, randomly break in that loop
		// if rand.Intn(10) > 8 {
		// 	break //pretend to fail
		// }
		//alternatively, could set up one of the machines to have a really short timeout and all the others have a really long timeout to mimic a failure
	}
}

// This function is designed to emulate a client reaching out to the
// server. Note that many of the realistic details are removed, for
// simplicity
func ClientAddToLog() {
	// In a realistic scenario, the client will find the leader node and
	//communicate with it
	// In this implementation, we are pretending that the client reached
	//out to the server somehow
	// But any new log entries will not be created unless the server /
	//node is a leader
	// isLeader here is a boolean to indicate whether the node is a leader
	//or not
	if isLeader {
		// lastAppliedIndex here is an int variable that is needed by a node
		//to store the value of the last index it used in the log
		entry := LogEntry{lastAppliedIndex, currentTerm}
		log.Println("Client communication created the new log entry at index " + strconv.Itoa(entry.Index))
		// Add rest of logic here
		// HINT 1: using the AppendEntry RPC might happen here
	}
	// HINT 2: force the thread to sleep for a good amount of time (less
	//than that of the leader election timer) and then repeat the actions above.
	//You may use an endless loop here or recursively call the function
	// HINT 3: you don’t need to add to the logic of creating new log
	//entries, just handle the replication
}

func main() {
	//var wg sync.WaitGroup
	// The assumption here is that the command line arguments will contain:
	// This server's ID (zero-based), location and name of the cluster configuration file
	arguments := os.Args
	if len(arguments) == 1 {
		fmt.Println("Please provide cluster information.")
		return
	}

	// Read the values sent in the command line

	// Get this sever's ID (same as its index for simplicity)
	myID, err := strconv.Atoi(arguments[1])
	if err != nil {
		log.Fatal(err)
	}
	selfID = myID //define raftNode's ID
	// Get the information of the cluster configuration file containing information on other servers
	file, err := os.Open(arguments[2])
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()

	myPort := "localhost"

	// Read the IP:port info from the cluster configuration file
	scanner := bufio.NewScanner(file)
	lines := make([]string, 0)
	index := 0
	offset := 0
	for scanner.Scan() {
		// Get server IP:port
		text := scanner.Text()
		log.Printf(text, index)
		if index == myID {
			myPort = text
			index++
			continue
		}
		// Save that information as a string for now
		lines = append(lines, text)
		index++
	}
	// If anything wrong happens with readin the file, simply exit
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	// Following lines are to register the RPCs of this object of type RaftNode
	api := new(RaftNode)
	err = rpc.Register(api)
	if err != nil {
		log.Fatal("error registering the RPCs", err)
	}
	rpc.HandleHTTP()
	go http.ListenAndServe(myPort, nil)
	log.Printf("serving rpc on port" + myPort)

	for index, element := range lines {
		// Attempt to connect to the other server node
		client, err := rpc.DialHTTP("tcp", element)
		// If connection is not established
		for err != nil {
			// Record it in log
			log.Println("Trying again. Connection error: ", err)
			// Try again!
			client, err = rpc.DialHTTP("tcp", element)
		}
		// Once connection is finally established
		// Save that connection information in the servers list
		if index == myID {
			offset = 1
		}
		serverNodes = append(serverNodes, ServerConnection{index + offset, element, client})
		// Record that in log
		fmt.Println("Connected to " + element)
	}

	// Once all the connections are established, we can start the typical operations within Raft
	// Leader election and heartbeats are concurrent and non-stop in Raft
	fmt.Printf("Creating Follower %d\n", selfID)
	timerDuration = randomTime()
	isLeader = false
	wg.Add(1)
	go StartTimer(timerDuration) //go
	wg.Wait()
}
