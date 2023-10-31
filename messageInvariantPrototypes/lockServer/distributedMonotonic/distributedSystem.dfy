include "../hosts.dfy"


module Network {
  import opened Types
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
  {
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
  import ClientHost
  import ServerHost

  datatype Constants = Constants(
    clients: seq<ClientHost.Constants>,
    server: seq<ServerHost.Constants>
    )
  {
    ghost predicate ValidClientIdx(id: int) {
      0 <= id < |clients|
    }

    ghost predicate UniqueIds() {
      forall i, j | ValidClientIdx(i) && ValidClientIdx(j) && clients[i].myId == clients[j].myId :: i == j
    }

    ghost predicate WF() {
      && 0 < |clients|
      && UniqueIds()
      && |server| == 1
    }
  }

  datatype Hosts = Hosts(
    clients: seq<ClientHost.Variables>,
    server: seq<ServerHost.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && ClientHost.GroupWF(c.clients, clients)
      && var allClients := (set x | 0 <= x < |c.clients| :: c.clients[x].myId);
      && ServerHost.GroupWF(c.server, server, allClients)
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
  } // end datatype Variables

  ghost predicate InitHosts(c: Constants, h: Hosts)
  {
    && var allClients := (set x | 0 <= x < |c.clients| :: c.clients[x].myId);
    && ClientHost.GroupInit(c.clients, h.clients)
    && ServerHost.GroupInit(c.server, h.server, allClients)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  ghost predicate NextClientStep(c: Constants, h: Hosts, h': Hosts, actor: int, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidClientIdx(actor)
    && ClientHost.Next(c.clients[actor], h.clients[actor], h'.clients[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall otherClientIdx | c.ValidClientIdx(otherClientIdx) && otherClientIdx != actor :: h'.clients[otherClientIdx] == h.clients[otherClientIdx])
    && h'.server == h.server
  }

  ghost predicate NextServerStep(c: Constants, h: Hosts, h': Hosts, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && ServerHost.Next(c.server[0], h.server[0], h'.server[0], msgOps)
    // all other hosts UNCHANGED
    && h'.clients == h.clients
    && |h'.server| == 1
  }

  datatype Step = 
    | ServerStep(msgOps: MessageOps)
    | ClientStep(actor: int, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step 
      case ClientStep(actor, msgOps) => NextClientStep(c, h, h', actor, msgOps)
      case ServerStep(msgOps) => NextServerStep(c, h, h', msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && IsSeqExtension(v.history, v'.history)
    && exists step :: NextStep(c, v.Last(), v'.Last(), v.network, v'.network, step)
  }

/***************************************************************************************
*                                Variable properties                                   *
***************************************************************************************/

  // All msg have a valid source
  ghost predicate ValidMessages(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs
    :: && (if msg.Release? then c.ValidClientIdx(msg.Src()) else msg.Src() == 0)
       && (if msg.Grant? then c.ValidClientIdx(msg.Dst()) else msg.Dst() == 0)
  }

  ghost predicate {:opaque} ValidHistory(c: Constants, v: Variables)
    requires v.WF(c)
  {
    InitHosts(c, v.History(0))
  }
  
  ghost predicate ValidVariables(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    && ValidMessages(c, v)
    && ValidHistory(c, v)
  }

  lemma InitImpliesValidVariables(c: Constants, v: Variables)
    requires Init(c, v)
    ensures ValidHistory(c, v)
  {
    reveal_ValidHistory();
  }


  lemma InvNextValidVariables(c: Constants, v: Variables, v': Variables)
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