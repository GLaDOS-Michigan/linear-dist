include "../../lib/UtilitiesLibrary.dfy"

/* The Toy Leader Election Protocol, sourced from "Modularity for Decidability of
   Deductive Verification with Applications to Distributed Systems" (PLDI'18)
   1. Client broadcasts StartElection
   2. A node receiving client request broadcasts Vote-Req, if it has not already voted
   3. A node receiving Vote-Req broadcasts a Vote for the sender, if it has not already voted
   4. A node receiving a quorum of Votes declares itself the leader, broadcasts Leader message
*/

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message =
    StartElection | VoteReq(candidate: HostId) | Vote(voter: HostId, candidate: HostId) | Leader(src: HostId)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

module Host {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, clusterSize: nat)

  predicate ConstantsValidForGroup(c: Constants, hostId: HostId, clusterSize: nat)
  {
    && c.hostId == hostId
    && c.clusterSize == clusterSize
  }

  datatype Variables = Variables(
    // Apply monotonic transformation here. Rather than a single boolean "voted" flag, 
    // keep track of all candidates I voted for. There should be at most one.
    voted: seq<HostId>,  
    receivedVotes: set<HostId>
  )

  predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForGroup(grp_c[idx], idx, |grp_c|))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.voted == []
    && v.receivedVotes == {}
  }

  datatype Step =
    ReceiveStep() | VictoryStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case VictoryStep => NextVictoryStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && match msgOps.recv.value
        case StartElection =>
          if 0 < |v.voted| then 
            && msgOps.send == None
            && v == v'
          else
            // Nominate myself as leader
            && msgOps.send == Some(VoteReq(c.hostId))
            && v == v'
        case VoteReq(candidate) => 
          if 0 < |v.voted| then
            // Stutter
            && msgOps.send == None
            && v == v'
          else
            // Vote for candidate
            && msgOps.send == Some(Vote(c.hostId, candidate))
            && v' == v.(voted := v.voted + [candidate])  // record the candidate I voted for
        case Vote(voter, candidate) =>
          if candidate == c.hostId then
            // I received a vote
            && msgOps.send == None
            && v' == v.(receivedVotes := v.receivedVotes + {voter})
          else
            // Stutter
            && msgOps.send == None
            && v == v'
        case Leader(_) =>
            // Stutter
            && msgOps.send == None
            && v == v'
  }

  predicate NextVictoryStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && SetIsQuorum(c.clusterSize, v.receivedVotes)
    && msgOps.send == Some(Leader(c.hostId))
    && v == v'
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}


module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  predicate Init(v: Variables)
  {
    && v.sentMsgs == {StartElection}
  }

  predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
} // end module Network


module DistributedSystem {
  import opened Types
  import Network
  import Host

  datatype Constants = Constants(hostConstants: seq<Host.Constants>)
  {
    predicate ValidIdx(id: int) {
      0 <= id < |hostConstants|
    }

    predicate UniqueIds() {
      forall i, j | ValidIdx(i) && ValidIdx(j) && hostConstants[i].hostId == hostConstants[j].hostId :: i == j
    }

    predicate WF() {
      && 0 < |hostConstants|
      && UniqueIds()
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hostConstants, hosts)
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hostConstants, v.hosts)
    && Network.Init(v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, actorIdx: int, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidIdx(actorIdx)
    && Host.Next(c.hostConstants[actorIdx], v.hosts[actorIdx], v'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHostIdx | c.ValidIdx(otherHostIdx) && otherHostIdx != actorIdx :: v'.hosts[otherHostIdx] == v.hosts[otherHostIdx])
  }

  datatype Step = HostActionStep(actorIdx: int, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.actorIdx, step.msgOps)
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}  // end module DistributedSystem