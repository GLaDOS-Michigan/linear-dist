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

  ghost predicate ConstantsValidForGroup(c: Constants, hostId: HostId, clusterSize: nat)
  {
    && c.hostId == hostId
    && c.clusterSize == clusterSize
  }

  datatype Variables = Variables(
    // Apply monotonic transformation here. Rather than a single boolean "voted" flag, 
    // keep track of all candidates I voted for. There should be at most one.
    voted: seq<HostId>,               // monotonic seq
    receivedVotes: set<HostId>,       // monotonic set
    pending: Option<Message>          // received message buffer
  )

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForGroup(grp_c[idx], idx, |grp_c|))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.voted == []
    && v.receivedVotes == {}
  }

  datatype Step =
    ReceiveStep() | ProcessStep() | VictoryStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case ProcessStep => NextProcessStep(c, v, v', msgOps)
      case VictoryStep => NextVictoryStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && v.pending.None?
    && match msgOps.recv.value
        case Vote(voter, candidate) =>
          if candidate == c.hostId then
            // I received a vote
            && v' == v.(receivedVotes := v.receivedVotes + {voter})
          else
            // Stutter
            && v == v'
        case _ =>
          // Store message to pending buffer
          v' == v.(pending := Some(msgOps.recv.value))
  }

  ghost predicate NextProcessStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && v.pending.Some?
    && match v.pending.value
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
          // This case is unreachable based on NextReceiveStep
          && false
        case Leader(_) =>
            // Stutter
            && msgOps.send == None
            && v == v'
  }

  ghost predicate NextVictoryStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && SetIsQuorum(c.clusterSize, v.receivedVotes)
    && msgOps.send == Some(Leader(c.hostId))
    && v == v'
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module Host
