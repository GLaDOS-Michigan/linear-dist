include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

} // end module Types


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
    receivedVotes: set<HostId>,   // monotonic set
    nominee: Option<HostId>,      // monotonic option
    isLeader: bool                // am I the leader?
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
    && v.receivedVotes == {}
    && v.nominee == None
    && v.isLeader == false
  }

  datatype TransitionLabel =
    | SendVoteReqLbl(nominee: HostId)
    | RecvVoteReqLbl(nominee: HostId)
    | SendVoteLbl(voter: HostId, nominee: HostId) 
    | RecvVoteLbl(voter: HostId, nominee: HostId) 
    | InternalLbl()

  datatype Step =
    HostStep() | VictoryStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case HostStep => NextHostStep(c, v, v', lbl)
      case VictoryStep => NextVictoryStep(c, v, v', lbl)
      case StutterStep => 
          && v == v'
          && lbl.InternalLbl?
  }

  ghost predicate NextHostStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && match lbl
        case InternalLbl() =>
            && v.nominee.None?
            && v' == v.(
                  nominee := Some(c.hostId),
                  receivedVotes := v.receivedVotes + {c.hostId}
                )
        case SendVoteReqLbl(nominee) =>
            && v.nominee.Some?
            && nominee == v.nominee.value == c.hostId
            && v' == v
        case RecvVoteReqLbl(nominee) =>
            if v.nominee.None? then
              v' == v.(nominee := Some(nominee))
            else 
              v' == v
        case SendVoteLbl(voter: HostId, nominee: HostId) => 
          && voter == c.hostId
          && v.nominee.Some?
          && nominee == v.nominee.value
          && v' == v
        case RecvVoteLbl(voter, nominee) =>
          // I received a vote
          && nominee == c.hostId
          && v' == v.(receivedVotes := v.receivedVotes + {voter})
  }

  ghost predicate NextVictoryStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && SetIsQuorum(c.clusterSize, v.receivedVotes)
    && v' == v.(isLeader := true)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
  }
} // end module Hosts