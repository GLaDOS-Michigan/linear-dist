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
    receivedVotes: set<HostId>,   // monotonic seq
    nominee: Option<HostId>       // monotonic option
  ) {
    ghost predicate HasVoteFrom(voter: HostId) 
    {
      voter in receivedVotes
    }

    ghost predicate Nominates(h: HostId) 
    {
      nominee == Some(h)
    }
  }

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
    && v.receivedVotes == {}
    && v.nominee == None
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
    && match msgOps.recv.value
        case StartElection =>
          if v.nominee.None? then
            // Nominate myself as leader
            && v' == v.(nominee := Some(c.hostId))
          else
            // Stutter
            && v' == v
        case VoteReq(candidate) => 
          if v.nominee.None? then
            // Save candidate as nominee
            && v' == v.(nominee := Some(candidate))
          else
            // Stutter
            && v' == v
        case Vote(voter, candidate) =>
          if candidate == c.hostId then
            // I received a vote
            && v' == v.(receivedVotes := v.receivedVotes + {voter})
          else
            // Stutter
            && v' == v
        case Leader(_) =>
            // Stutter
            && v' == v
  }

  ghost predicate NextProcessStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && v.nominee.Some?
    // Vote for nominee
    && msgOps.send == Some(Vote(c.hostId, v.nominee.value))
    && v' == v
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
