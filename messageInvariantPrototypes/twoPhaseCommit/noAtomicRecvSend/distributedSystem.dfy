
include "hosts.dfy"


module Network {
  import opened Types

  datatype Constants = Constants  // no constants for network

  datatype Variables = Variables(sentMsgs:set<Message>)

  predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

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
    predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(c.network, v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.hostid, step.msgOps)
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }

  function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
      case CoordinatorVariables(coordinator) => coordinator.decision
      case ParticipantVariables(participant) => participant.decision
  }
}


