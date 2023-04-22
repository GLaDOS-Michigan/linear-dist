include "hosts.dfy"

module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  predicate Init(v: Variables) {
    && v.sentMsgs == {}
  }

  predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}  // end module Network


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host
  import ServerHost
  import ClientHost

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    predicate ValidActorIdx(idx: nat) {
      idx < |hosts|
    }
    predicate ValidClientIdx(idx: nat) {
      idx < |hosts|-1
    }

    predicate ValidServerIdx(idx: nat) {
      idx == |hosts|-1
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
    && Network.Init(v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, actorIdx: nat, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidActorIdx(actorIdx)
    && Host.Next(c.hosts[actorIdx], v.hosts[actorIdx], v'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherIdx:nat | c.ValidActorIdx(otherIdx) && otherIdx != actorIdx :: v'.hosts[otherIdx] == v.hosts[otherIdx])
  }

  datatype Step =
    | HostActionStep(actorIdx: nat, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.actorIdx, step.msgOps)
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}  // end module Distributed System
