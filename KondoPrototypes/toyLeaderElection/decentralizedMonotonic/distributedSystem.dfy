include "../hosts.dfy"

module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables) {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
} // end module Network


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    ghost predicate ValidHostId(id: int) {
      0 <= id < |hosts|
    }

    ghost predicate UniqueIds() {
      forall i, j | ValidHostId(i) && ValidHostId(j) && hosts[i].hostId == hosts[j].hostId :: i == j
    }

    ghost predicate WF() {
      && 0 < |hosts|
      && UniqueIds()
    }
  }

  datatype Hosts = Hosts(
    hosts: seq<Host.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }

    ghost predicate IsLeader(c: Constants, h: HostId) 
      requires WF(c)
      requires c.ValidHostId(h)
    {
      hosts[h].isLeader
    }
  } // end datatype Hosts

  datatype Variables = Variables(
    history: seq<Hosts>,
    network: Network.Variables)
  {
    ghost predicate ValidHistoryIdx(i: int) {
      0 <= i < |history|
    }

    ghost predicate ValidHistoryIdxStrict(i: int) {
      0 <= i < |history|-1
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
  } // end datatype Variables

  ghost predicate InitHosts(c: Constants, h: Hosts)
  {
    Host.GroupInit(c.hosts, h.hosts)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  ghost predicate HostAction(c: Constants, h: Hosts, h': Hosts, actorIdx: int, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidHostId(actorIdx)
    && Host.Next(c.hosts[actorIdx], h.hosts[actorIdx], h'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHostIdx | c.ValidHostId(otherHostIdx) && otherHostIdx != actorIdx :: h'.hosts[otherHostIdx] == h.hosts[otherHostIdx])
  }

  datatype Step = HostActionStep(actor: int, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && HostAction(c, h, h', step.actor, step.msgOps)
    && Network.Next(n, n', step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && IsSeqExtension(v.history, v'.history)
    && exists step :: NextStep(c, v.Last(), v'.Last(), v.network, v'.network, step)
  }


/***************************************************************************************
*                                 History properties                                   *
***************************************************************************************/

  ghost predicate {:opaque} ValidHistory(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && InitHosts(c, v.History(0))
  }

  lemma InitImpliesValidHistory(c: Constants, v: Variables)
    requires Init(c, v)
    ensures ValidHistory(c, v)
  {
    reveal_ValidHistory();
  }


  lemma InvNextValidHistory(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires ValidHistory(c, v)
    requires Next(c, v, v')
    ensures ValidHistory(c, v')
  {
    reveal_ValidHistory();
    VariableNextProperties(c, v, v');
  }

  lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires Next(c, v, v')
    ensures 1 < |v'.history|
    ensures |v.history| == |v'.history| - 1
    ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)
    ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)
  {
    assert 0 < |v.history|;
    assert 1 < |v'.history|;
  }
}  // end module DistributedSystem