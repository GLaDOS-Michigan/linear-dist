include "../../lib/UtilitiesLibrary.dfy"

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
    voted: seq<HostId>,             // monotonic seq
    receivedVotes: set<HostId>      // monotonic set
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
} // end module Host
