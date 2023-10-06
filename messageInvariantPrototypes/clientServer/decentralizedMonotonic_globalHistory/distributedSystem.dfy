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
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidActorIdx(idx: int) {
      0 <= idx < |hosts|
    }
    ghost predicate ValidClientIdx(idx: int) {
      0 <= idx < |hosts|-1
    }

    ghost predicate ValidServerIdx(idx: int) {
      idx == |hosts|-1
    }

    ghost function GetClient(idx: int) : ClientHost.Constants
      requires WF()
      requires ValidClientIdx(idx)
    {
      hosts[idx].client
    }

    ghost function GetServer() : ServerHost.Constants
      requires WF()
    {
      Last(hosts).server
    }
  }

  datatype Hosts = Hosts(
    hosts: seq<Host.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }

    ghost function GetClient(c: Constants, idx: int) : ClientHost.Variables
      requires WF(c)
      requires c.ValidClientIdx(idx)
    {
      hosts[idx].client
    }

    ghost function GetServer(c: Constants) : ServerHost.Variables
      requires WF(c)
    {
      Last(hosts).server
    }
  }

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

    ghost function Truncate(c: Constants, i: int) : (v : Variables)
      requires WF(c)
      requires 0 < i <= |history|
      ensures v.WF(c)
      ensures v.Last() == History(i-1)
    {
      Variables.Variables(history[..i], network)
    }
  }

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

  ghost predicate HostAction(c: Constants, h: Hosts, h': Hosts, actorIdx: nat, msgOps: MessageOps)
  {
    && h.WF(c)
    && h'.WF(c)
    && c.ValidActorIdx(actorIdx)
    && Host.Next(c.hosts[actorIdx], h.hosts[actorIdx], h'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherIdx:nat | c.ValidActorIdx(otherIdx) && otherIdx != actorIdx :: h'.hosts[otherIdx] == h.hosts[otherIdx])
  }

  datatype Step =
    | HostActionStep(actorIdx: nat, msgOps: MessageOps)

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

  ghost predicate IsReceiveStepByActor(c: Constants, v: Variables, i:int, actor: int, msg: Message)
    requires v.WF(c)
    requires 1 <= i < |v.history|
    requires Next(c, v.Truncate(c, i), v.Truncate(c, i+1))
  {
    var step :| NextStep(c, v.Truncate(c, i).Last(), v.Truncate(c, i+1).Last(), v.network, v.network, step);
    && step.msgOps.recv == Some(msg)
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
