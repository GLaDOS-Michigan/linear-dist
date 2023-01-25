include "UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message = Msg(val: int, src: HostId)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types


module Host {
  import opened Types

  datatype Constants = Constants(hostId: HostId)

  datatype Variables = Variables(
    highest_heard: int
  )
  {
    predicate WF(c: Constants) {
      highest_heard >= -1  // not really useful, but just for fun :)
    }
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.highest_heard == 0
  }

  datatype Step =
    TransmissionStep() | ReceiveStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case TransmissionStep => NextTransmissionStep(v, v', msgOps)
      case ReceiveStep => NextReceiveStep(v, v', msgOps)
  }

  predicate NextTransmissionStep(v: Variables, v': Variables, msgOps: MessageOps) {
    false // TODO
  }

  predicate NextReceiveStep(v: Variables, v': Variables, msgOps: MessageOps) {
    false  // TODO
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host

module Network {
  import opened Types

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
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
} // end module Network


module DistributedSystem {
  import opened Types
  import Network
  import Host

  datatype Constants = Constants(
    host_constants: seq<Host.Constants>,
    network: Network.Constants)
  {
    predicate ValidHostIdx(id: int) {
      0 <= id < |host_constants|
    }

    predicate UniqueIds() {
      forall i, j | ValidHostIdx(i) && ValidHostIdx(j) && host_constants[i] == host_constants[j] :: i == j
    }

    predicate WF() {
      && 0 < |host_constants|
      && UniqueIds()
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.host_constants, hosts)
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.host_constants, v.hosts)
    && Network.Init(c.network, v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, actorIdx: int, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostIdx(actorIdx)
    && Host.Next(c.host_constants[actorIdx], v.hosts[actorIdx], v'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHostIdx | c.ValidHostIdx(otherHostIdx) && otherHostIdx != actorIdx :: v'.hosts[otherHostIdx] == v.hosts[otherHostIdx])
  }

  datatype Step = HostActionStep(actorIdx: int, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.actorIdx, step.msgOps)
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}  // end module DistributedSystem


