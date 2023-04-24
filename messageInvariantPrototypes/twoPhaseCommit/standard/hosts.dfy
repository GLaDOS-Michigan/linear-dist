include "types.dfy"

// There are two host roles in 2PC, Coordinator and Participant. We'll define
// separate state machines for each.
// This state machine defines how a coordinator host should behave: what state
// it records, and what actions it's allowed to take in response to incoming
// messages (or spontaneously by thinking about its existing state).
module CoordinatorHost {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(numParticipants: nat)

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? It needs to have a correct
  // count of the number of participants.
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
    // WF is for a simple condition that relates every valid Variables state
    // to the Constants.
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

  // Protocol steps. Define an action predicate for each step of the protocol
  // that the coordinator is involved in.
  // Hint: it's probably easiest to separate the receipt and recording of
  // incoming votes from detecting that all have arrived and making a decision.

  // JayNF
  datatype Step =
    VoteReqStep() | ReceiveStep() | DecisionStep() | StutterStep()


  // msgOps is a "binding variable" -- the host and the network have to agree
  // on its assignment to make a valid transition. So the host explains what
  // would happen if it could receive a particular message, and the network
  // decides whether such a message is available for receipt.
  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case VoteReqStep => NextVoteReqStep(v, v', msgOps)
      case ReceiveStep => NextReceiveStep(v, v', msgOps)
      case DecisionStep => NextDecisionStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  predicate NextVoteReqStep(v: Variables, v': Variables, msgOps: MessageOps) {
    && v' == v  // coordinator local state unchanged
    && msgOps.recv.None?
    && msgOps.send == Some(VoteReqMsg)
  }

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
} // end module CoordinatorHost


module ParticipantHost {
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? It needs to know its hostId.
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

  // Protocol steps. Define an action predicate for each step of the protocol
  // that participant can take.

  // JayNF
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

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
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

  // What property must be true of any group of hosts to run the protocol?
  // Generic DistributedSystem module calls back into this predicate to ensure
  // that it has a well-formed *group* of hosts.
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

  // Generic DistributedSystem module calls back into this predicate to give
  // the protocol an opportunity to set up constraints across the various
  // hosts.  Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know
  // own ids.
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
