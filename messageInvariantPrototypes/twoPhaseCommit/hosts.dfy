include "types.dfy"

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

  datatype Step =
    VoteReqStep() | ReceiveStep() | DecisionStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case VoteReqStep => NextVoteReqStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case DecisionStep => NextDecisionStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && NextVoteReqStepSendFunc(c, v, msgOps.send.value)
    && v' == v 
  }

  // Send predicate
  ghost predicate NextVoteReqStepSendFunc(c: Constants, v: Variables, msg: Message) {
    msg == VoteReqMsg
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && NextReceiveStepRecvFunc(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate NextReceiveStepRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.VoteMsg?
    && var vote, src := msg.v, msg.src;
    // update v'
    && if vote == Yes then 
        v' == v.(
          yesVotes := v.yesVotes + {src}
        )
      else
        v' == v.(
          noVotes := v.noVotes + {src}
        )
  }

  ghost predicate NextDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && (|v.noVotes| > 0 || |v.yesVotes| == c.numParticipants)
    && NextDecisionStepSendFunc(c, v, msgOps.send.value)
    && if |v.noVotes| > 0 then
        v' == v.(decision := Some(Abort))
      else if |v.yesVotes| == c.numParticipants then
        v' == v.(decision := Some(Commit))
      else
        false
  }

  // Send predicate
  ghost predicate NextDecisionStepSendFunc(c: Constants, v: Variables, msg: Message) {
    // enabling conditions
    && v.decision.None?
    && (|v.noVotes| > 0 || |v.yesVotes| == c.numParticipants)
    // send message
    && if |v.noVotes| > 0 then
        msg == DecideMsg(Abort)
    else if |v.yesVotes| == c.numParticipants then
        msg == DecideMsg(Commit)
    else
      false
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
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

  datatype Step =
    ReceiveVoteReqStep() | ReceiveDecisionStep() | SendVoteStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveVoteReqStep => NextReceiveVoteReqStep(c, v, v', msgOps)
      case ReceiveDecisionStep => NextReceiveDecisionStep(c, v, v', msgOps)
      case SendVoteStep => NextSendVoteStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextReceiveVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && msgOps.recv.value.VoteReqMsg?
    && v == v'.(sendVote := true)
  }

  ghost predicate NextReceiveDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && msgOps.recv.value.DecideMsg?
    && v' == v.(decision := Some(msgOps.recv.value.decision))
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && v.sendVote == true
    && v' == v.(sendVote := false)
    && msgOps.send == Some(VoteMsg(c.preference, c.hostId))
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
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

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
      case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
      )
  }
} // end module Host