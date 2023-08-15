
include "hosts.dfy"

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
  import opened Types

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(
    hosts: seq<Host.Constants>,
    network: Network.Constants)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(c.network, v.network)
  }

  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.hostid, step.msgOps)
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }

  function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
      case CoordinatorVariables(coordinator) => coordinator.decision
      case ParticipantVariables(participant) => participant.decision
  }

  // Convince us that your model does something
  lemma PseudoLiveness(c: Constants) returns (behavior: seq<Variables>)
    requires c.WF()
    requires |c.hosts| == 2 // There's exactly one voting participant...
    requires c.hosts[0].participant.preference.Yes? // ... who wants a Yes.
    // Exhibit a behavior that satisfies your state machine...
    ensures 0 < |behavior|
    ensures Init(c, behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
    // ...and all the participants arrive at a decision.
    ensures Last(behavior).WF(c)
    ensures forall hostid:HostId | c.ValidHostId(hostid)
      :: GetDecisionForHost(Last(behavior).hosts[hostid]) == Some(Commit)
  {


    // Initial state
    var network := Network.Variables({});
    var group := InitGroup(c);
    assert Host.GroupInit(c.hosts, group);
    behavior := [Variables(group, network)];
    assert Init(c, behavior[0]);

    // Leader sends vote req
    network := Network.Variables(network.sentMsgs + {VoteReqMsg});
    behavior := behavior + [Variables(group, network)];
    var l, l' := behavior[0].hosts[1].coordinator, behavior[1].hosts[1].coordinator;
    var coordStep := CoordinatorHost.VoteReqStep();  // witnesses and triggers
    var msgOps := MessageOps(None, Some(VoteReqMsg));
    var dsStep := HostActionStep(1, msgOps); 
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, l, l', coordStep, msgOps);
    assert NextStep(c, behavior[0], behavior[1], dsStep);
    assert Next(c, behavior[0], behavior[1]);

    // Participant sends yes vote
    network := Network.Variables(network.sentMsgs + {VoteMsg(Yes, 0)});
    behavior := behavior + [Variables(group, network)];
    var p, p' := behavior[1].hosts[0].participant, behavior[2].hosts[0].participant;
    var partStep := ParticipantHost.ReceiveStep();  // witnesses and triggers
    msgOps := MessageOps(Some(VoteReqMsg), Some(VoteMsg(Yes, 0)));
    dsStep := HostActionStep(0, msgOps); 
    assert ParticipantHost.NextStep(c.hosts[0].participant, p, p', partStep, msgOps);
    assert NextStep(c, behavior[1], behavior[2], dsStep);
    assert Next(c, behavior[1], behavior[2]);

    // Leader receive yes vote, network unchanged
    group := [group[0], Host.CoordinatorVariables(CoordinatorHost.Variables(None, {0}, {}))];
    behavior := behavior + [Variables(group, network)];
    l, l' := behavior[2].hosts[1].coordinator, behavior[3].hosts[1].coordinator;
    coordStep := CoordinatorHost.ReceiveStep();  // witnesses and triggers
    msgOps := MessageOps(Some(VoteMsg(Yes, 0)), None);
    dsStep := HostActionStep(1, msgOps); 
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, l, l', coordStep, msgOps);
    assert NextStep(c, behavior[2], behavior[3], dsStep);
    assert Next(c, behavior[2], behavior[3]);

    // Leader decides and sends commit
    network := Network.Variables(network.sentMsgs + {DecideMsg(Commit)});
    group := [group[0], Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), {0}, {}))];
    behavior := behavior + [Variables(group, network)];
    l, l' := behavior[3].hosts[1].coordinator, behavior[4].hosts[1].coordinator;
    coordStep := CoordinatorHost.DecisionStep();  // witnesses and triggers
    msgOps := MessageOps(None, Some(DecideMsg(Commit)));
    dsStep := HostActionStep(1, msgOps); 
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, l, l', coordStep, msgOps);
    assert NextStep(c, behavior[3], behavior[4], dsStep);
    assert Next(c, behavior[3], behavior[4]);

    // Participant receives commit and decides, network unchanged
    group := [Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))), group[1]];
    behavior := behavior + [Variables(group, network)];
    p, p' := behavior[4].hosts[0].participant, behavior[5].hosts[0].participant;
    partStep := ParticipantHost.ReceiveStep();  // witnesses and triggers
    msgOps := MessageOps(Some(DecideMsg(Commit)), None);
    dsStep := HostActionStep(0, msgOps); 
    assert ParticipantHost.NextStep(c.hosts[0].participant, p, p', partStep, msgOps);
    assert NextStep(c, behavior[4], behavior[5], dsStep);
    assert Next(c, behavior[4], behavior[5]);

  }


  function InitGroup(c: Constants) : (group: seq<Host.Variables>) 
    requires c.WF()
    requires |c.hosts| == 2 // There's exactly one voting participant...
    requires c.hosts[0].participant.preference.Yes? // ... who wants a Yes.
    ensures Host.GroupInit(c.hosts, group)
  {
    var initNetwork := Network.Variables({});
    var initCoord := CoordinatorHost.Variables(None, {}, {});
    var initPart := ParticipantHost.Variables(None);
    [Host.ParticipantVariables(initPart), Host.CoordinatorVariables(initCoord)]
  }
}


