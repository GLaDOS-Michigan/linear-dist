include "../hosts.dfy"

module Network {
  import opened Types

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
} // end module Network


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  datatype Constants = Constants(
    hostConstants: seq<Host.Constants>)
  {
    ghost predicate ValidIdx(id: int) {
      0 <= id < |hostConstants|
    }

    ghost predicate UniqueIds() {
      forall i, j | ValidIdx(i) && ValidIdx(j) && hostConstants[i].hostId == hostConstants[j].hostId :: i == j
    }

    ghost predicate WF() {
      && 0 < |hostConstants|
      && UniqueIds()
    }
  }
  
  datatype Hosts = Hosts(
    hosts: seq<Host.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hostConstants, hosts)
    }
  }

  datatype Variables = Variables(
    history: seq<Hosts>,
    network: Network.Variables)
  {
    ghost predicate ValidHistoryIdx(i: int) {
      0 <= i < |history|
    }

    ghost predicate WF(c: Constants) {
      && c.WF()
      && 0 < |history|
      && (forall i | ValidHistoryIdx(i) :: history[i].WF(c))
    }

    ghost function History(i: int) : (h: Hosts)
      requires ValidHistoryIdx(i)
      ensures h == history[i]
    {
      history[i]
    }

    ghost function Last() : (h: Hosts) 
      requires 0 < |history|
      ensures h == history[|history|-1]
    {
      UtilitiesLibrary.Last(history)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && Host.GroupInit(c.hostConstants, v.History(0).hosts)
    && Network.Init(v.network)
  }

  ghost predicate HostAction(c: Constants, h: Hosts, h': Hosts, actorIdx: int, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidIdx(actorIdx)
    && Host.Next(c.hostConstants[actorIdx], h.hosts[actorIdx], h'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHostIdx | c.ValidIdx(otherHostIdx) && otherHostIdx != actorIdx :: h'.hosts[otherHostIdx] == h.hosts[otherHostIdx])
  }

  datatype Step = HostActionStep(actorIdx: int, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && HostAction(c, h, h', step.actorIdx, step.msgOps)
    && Network.Next(n, n', step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && IsSeqExtension(v.history, v'.history)
    && exists step :: NextStep(c, v.Last(), v'.Last(), v.network, v'.network, step)
  }
}  // end module DistributedSystem


