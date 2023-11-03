include "../types.dfy"

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
    && v.isLeader == false
  }

  datatype TransitionLabel =
    | SendVoteReqLbl(nominee: HostId)
    | RecvVoteReqLbl(nominee: HostId)
    | SendVoteLbl(voter: HostId, nominee: HostId) 
    | RecvVoteLbl(voter: HostId, nominee: HostId) 
    | InternalLbl()

  datatype Step =
    NominateSelfStep() 
    | SendVoteReqStep()
    | RecvVoteReqStep() 
    | SendVoteStep()
    | RecvVoteStep()
    | VictoryStep() 
    | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case NominateSelfStep => NextHostNominateSelfStep(c, v, v', lbl)
      case SendVoteReqStep => NextHostSendVoteReqStep(c, v, v', lbl)
      case RecvVoteReqStep => NextHostRecvVoteReqStep(c, v, v', lbl)
      case SendVoteStep => NextHostSendVoteStep(c, v, v', lbl)
      case RecvVoteStep => NextHostRecvVoteStep(c, v, v', lbl)
      case VictoryStep => NextVictoryStep(c, v, v', lbl)
      case StutterStep => 
          && v == v'
          && lbl.InternalLbl?
  }

  ghost predicate NextHostNominateSelfStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v.nominee.None?
    && v' == v.(
        nominee := Some(c.hostId),
        receivedVotes := v.receivedVotes + {c.hostId}
      )
  }

  ghost predicate NextHostSendVoteReqStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.SendVoteReqLbl?
    && v.nominee.Some?
    && lbl.nominee == v.nominee.value == c.hostId
    && v' == v
  }

  ghost predicate NextHostRecvVoteReqStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.RecvVoteReqLbl?
    && v.nominee.None?
    && v' == v.(nominee := Some(lbl.nominee))
  }

  ghost predicate NextHostSendVoteStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.SendVoteLbl?
    && lbl.voter == c.hostId
    && v.nominee.Some?
    && lbl.nominee == v.nominee.value
    && v' == v
  }

  ghost predicate NextHostRecvVoteStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.RecvVoteLbl?
    && lbl.nominee == c.hostId
    && v' == v.(receivedVotes := v.receivedVotes + {lbl.voter})
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