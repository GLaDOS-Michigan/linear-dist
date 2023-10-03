include "../types.dfy"

module CoordinatorHost {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(numParticipants: nat)

  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat)
  {
    c.numParticipants == participantCount
  }

  datatype Variables = Variables(
    decision: Option<Decision>, 
    yesVotes: set<HostId>,
    noVotes: set<HostId>
  )
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.decision.None?
    && v.yesVotes == {}
    && v.noVotes == {}
  }

  datatype TransitionLabel =
    VoteReqLbl() | ReceiveVoteLbl(vote: Vote, src: HostId) | DecideLbl(decision: Decision) | InternalLbl()

  datatype Step =
    VoteReqStep() | ReceiveStep() | DecisionStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case VoteReqStep => NextVoteReqStep(v, v', lbl)
      case ReceiveStep => NextReceiveStep(v, v', lbl)
      case DecisionStep => NextDecisionStep(c, v, v', lbl)
      case StutterStep => && v == v'
                          && lbl.InternalLbl?
  }

  ghost predicate NextVoteReqStep(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.VoteReqLbl?
    && v' == v  // coordinator local state unchanged
  }

  ghost predicate NextReceiveStep(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceiveVoteLbl?
    &&  if lbl.vote == Yes then 
        v' == v.(
          yesVotes := v.yesVotes + {lbl.src}
        )
      else
        v' == v.(
          noVotes := v.noVotes + {lbl.src}
        )
  }

  ghost predicate NextDecisionStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.DecideLbl?
    && v.decision.None?  // enabling condition
    && (|v.noVotes| > 0 || |v.yesVotes| == c.numParticipants)
    && if |v.noVotes| > 0 then
        && v' == v.(decision := Some(Abort))
        && lbl.decision == Abort
      else if |v.yesVotes| == c.numParticipants then
        && v' == v.(decision := Some(Commit))
        && lbl.decision == Commit
      else
        && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
  }
} // end module CoordinatorHost


module ParticipantHost {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  ghost predicate ConstantsValidForGroup(c: Constants, hostId: HostId)
  {
    c.hostId == hostId
  }

  datatype Variables = Variables(
    // Boolean flag that acts as enabling condition for sending VoteMsg, introduced to make
    // receiving voteReq and sending vote two distinct steps.
    sendVote: bool,
    decision: Option<Decision>
  )
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sendVote == false
    && v.decision == None
  }

  datatype TransitionLabel =
    VoteReqLbl() | SendVoteLbl(vote: Vote) | DecideLbl(decision: Decision) | InternalLbl()

  datatype Step =
    ReceiveStep() | SendVoteStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', lbl)
      case SendVoteStep => NextSendVoteStep(c, v, v', lbl)
      case StutterStep => 
          && v == v'
          && lbl.InternalLbl?
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && match lbl
        case VoteReqLbl =>
          && v == v'.(sendVote := true)
        case DecideLbl(d) =>
          && lbl.DecideLbl?
          && v' == v.(decision := Some(d))
        case _ => 
          false
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && v.sendVote == true
    && lbl.SendVoteLbl?
    && lbl.vote == c.preference
    && v' == v.(sendVote := false)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
  }
} // end module ParticipantHost



module Host {
  import opened UtilitiesLibrary
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Constants =
    | CoordinatorConstants(coordinator: CoordinatorHost.Constants)
    | ParticipantConstants(participant: ParticipantHost.Constants)

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    ghost predicate WF(c: Constants) {
      && (CoordinatorVariables? <==> c.CoordinatorConstants?) // types of c & v agree
      && (match c
            case CoordinatorConstants(_) => coordinator.WF(c.coordinator)
            case ParticipantConstants(_) => participant.WF(c.participant)
          )
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There must at least be a coordinator
    && 0 < |grp_c|
    // Last host is a coordinator
    && Last(grp_c).CoordinatorConstants?
    // All the others are participants
    && (forall hostid:HostId | hostid < |grp_c|-1 :: grp_c[hostid].ParticipantConstants?)
    // The coordinator's constants must correctly account for the number of participants
    && CoordinatorHost.ConstantsValidForGroup(Last(grp_c).coordinator, |grp_c|-1)
    // The participants's constants must match their group positions.
    // (Actually, they just need to be distinct from one another so we get
    // non-conflicting votes, but this is an easy way to express that property.)
    && (forall hostid:HostId | hostid < |grp_c|-1
        :: ParticipantHost.ConstantsValidForGroup(grp_c[hostid].participant, hostid))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_c, grp_v)
    // Coordinator is initialized to know about the N-1 participants.
    && CoordinatorHost.Init(Last(grp_c).coordinator, Last(grp_v).coordinator)
    // Participants initted with their ids.
    && (forall hostid:HostId | hostid < |grp_c|-1 ::
        ParticipantHost.Init(grp_c[hostid].participant, grp_v[hostid].participant)
      )
  }

  datatype TransitionLabel = 
    | CL(c: CoordinatorHost.TransitionLabel)
    | PL(p: ParticipantHost.TransitionLabel)

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case CoordinatorConstants(_) => 
          && lbl.CL?
          && CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, lbl.c)
      case ParticipantConstants(_) => 
          && lbl.PL?
          && ParticipantHost.Next(c.participant, v.participant, v'.participant, lbl.p)
      )
  }
} // end module Host
