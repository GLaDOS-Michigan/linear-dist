include "types.dfy"

module CoordinatorHost {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(numParticipants: nat)

  predicate ConstantsValidForGroup(c: Constants, participantCount: nat)
  {
    c.numParticipants == participantCount
  }

  datatype Variables = Variables(
    decision: Option<Decision>, 
    yesVotes: set<HostId>,
    noVotes: set<HostId>
  )
  {
    predicate WF(c: Constants) {
      true
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.decision.None?
    && v.yesVotes == {}
    && v.noVotes == {}
  }

  datatype TransitionLabel =
    VoteReqLbl() | ProcessLbl(r: Request) | InternalLbl()

  datatype Step =
    VoteReqStep() | ReceiveLbl(vote: Vote, src: src) | DecideLbl() | InternalLbl()


  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case VoteReqStep => NextVoteReqStep(v, v', msgOps)
      case ReceiveStep => NextReceiveStep(v, v', msgOps)
      case DecisionStep => NextDecisionStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && lbl.InternalLbl?
  }

  predicate NextVoteReqStep(v: Variables, v': Variables, lbl: TransitionLabel) {
    && v' == v  // coordinator local state unchanged
    && lbl.VoteReqLbl?
  }

  // TODO: WORK IN PROGRESS
  // Asynchronous 2PC has receiving and sending on same step, and that needs to be fixed

  predicate NextReceiveStep(v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
        case VoteMsg(vote, src) =>
          if vote == Yes then 
            v' == v.(
              yesVotes := v.yesVotes + {src}
            )
          else
            v' == v.(
              noVotes := v.noVotes + {src}
            )
        case _ => v' == v //stutter
  } 

  // This step doubles as a stutter step
  predicate NextDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && v.decision.None?  // enabling condition
    && if |v.noVotes| > 0 then
        && v' == v.(decision := Some(Abort))
        && msgOps.send == Some(DecideMsg(Abort))
      else if |v.yesVotes| == c.numParticipants then
        && v' == v.(decision := Some(Commit))
        && msgOps.send == Some(DecideMsg(Commit))
      else
        && v' == v
        && msgOps.send.None?
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}


module ParticipantHost {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  predicate ConstantsValidForGroup(c: Constants, hostId: HostId)
  {
    c.hostId == hostId
  }

  datatype Variables = Variables(decision: Option<Decision>)
  {
    predicate WF(c: Constants) {
      true
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    v.decision == None
  }

  datatype Step =
    ReceiveStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && match msgOps.recv.value
        case VoteReqMsg =>
          && v == v' 
          && msgOps.send == Some(VoteMsg(c.preference, c.hostId))
        case VoteMsg(_, _) => 
          && v' == v
          && msgOps.send.None?
        case DecideMsg(d) =>
          && v' == v.(decision := Some(d))
          && msgOps.send.None?
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
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
    predicate WF(c: Constants) {
      && (CoordinatorVariables? <==> c.CoordinatorConstants?) // types of c & v agree
      // subtype WF satisfied
      && (match c
            case CoordinatorConstants(_) => coordinator.WF(c.coordinator)
            case ParticipantConstants(_) => participant.WF(c.participant)
          )
    }
  }


  predicate GroupWFConstants(grp_c: seq<Constants>)
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

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
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

  // Dispatch Next to appropriate underlying implementation.
  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
      case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
      )
  }
} // end module Host
