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

    ghost function Truncate(c: Constants, i: int) : (v : Variables)
      requires WF(c)
      requires 0 < i <= |history|
      ensures v.WF(c)
      ensures v.Last() == History(i-1)
    {
      Variables.Variables(history[..i], network)
    }
  } // end datatype Variables

  ghost predicate InitHosts(c: Constants, h: Hosts)
  {
    Host.GroupInit(c.hostConstants, h.hosts)
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


/***************************************************************************************
*                                 History properties                                   *
***************************************************************************************/

  ghost predicate {:opaque} ValidHistory(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && InitHosts(c, v.History(0))
    && forall i | 
      && 1 <= i < |v.history|
    ::
    Next(c, v.Truncate(c, i), v.Truncate(c, i+1))
  }

  ghost predicate IsReceiveStepByActor(c: Constants, v: Variables, i:int, actor: int)
    requires v.WF(c)
    requires 1 <= i < |v.history|
    requires Next(c, v.Truncate(c, i), v.Truncate(c, i+1))
  {
    var step :| NextStep(c, v.Truncate(c, i).Last(), v.Truncate(c, i+1).Last(), v.network, v.network, step);
    && step.msgOps.recv.Some?
    && step.actorIdx == actor
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
    forall i | 1 <= i < |v'.history|
    ensures Next(c, v'.Truncate(c, i), v'.Truncate(c, i+1))
    {
      if i == |v'.history| - 1 {
        MessageContainmentPreservesNext(c, v, v', v'.Truncate(c, i), v'.Truncate(c, i+1));
        assert Next(c, v'.Truncate(c, i), v'.Truncate(c, i+1));
      } else {
        assert Next(c, v.Truncate(c, i), v.Truncate(c, i+1));
        assert v.Truncate(c, i).network.sentMsgs <= v'.Truncate(c, i).network.sentMsgs;
        MessageContainmentPreservesNext(c, v.Truncate(c, i), v.Truncate(c, i+1), v'.Truncate(c, i), v'.Truncate(c, i+1));
        assert Next(c, v'.Truncate(c, i), v'.Truncate(c, i+1));
      }
    }
  }

  lemma MessageContainmentPreservesNext(c: Constants, v: Variables, v': Variables, s: Variables, s': Variables)
    requires v.WF(c)
    requires s.WF(c)
    requires Next(c, v, v')
    requires v.history == s.history
    requires v'.history == s'.history
    requires v'.network.sentMsgs <= s'.network.sentMsgs
    requires s.network.sentMsgs == s'.network.sentMsgs
    ensures Next(c, s, s')
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    assert NextStep(c, s.Last(), s'.Last(), s.network, s'.network, dsStep); // trigger
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


