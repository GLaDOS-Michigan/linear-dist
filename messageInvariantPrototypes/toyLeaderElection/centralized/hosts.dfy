include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message =
    StartElection | VoteReq(candidate: HostId) | Vote(voter: HostId, candidate: HostId) | Leader(src: HostId)

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
    | NominateLbl(candidate: HostId) 
    | SendVoteReqLbl(candidate: HostId)
    | RecvVoteReqLbl(candidate: HostId)
    | SendVoteLbl(voter: HostId, candidate: HostId) 
    | RecvVoteLbl(voter: HostId, candidate: HostId) 
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
        case NominateLbl(candidate) =>
            && v.nominee.None?
            && v' == v.(
                  nominee := Some(c.hostId),
                  receivedVotes := v.receivedVotes + {c.hostId}
                )
        case SendVoteReqLbl(candidate) =>
            && v.nominee.Some?
            && candidate == v.nominee.value == c.hostId
            && v' == v
        case RecvVoteReqLbl(candidate) =>
            if v.nominee.None? then
              v' == v.(nominee := Some(candidate))
            else 
              v' == v
        case SendVoteLbl(voter: HostId, candidate: HostId) => 
          && voter == c.hostId
          && v.nominee.Some?
          && candidate == v.nominee.value
          && v' == v
        case RecvVoteLbl(voter, candidate) =>
          // I received a vote
          && candidate == c.hostId
          && v' == v.(receivedVotes := v.receivedVotes + {voter})
        case InternalLbl() =>
            // Stutter
            && v' == v
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