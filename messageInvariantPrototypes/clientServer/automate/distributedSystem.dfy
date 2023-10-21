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
  import ServerHost
  import ClientHost

  datatype Constants = Constants(
    clients: seq<ClientHost.Constants>,
    servers: seq<ServerHost.Constants>)
  {
    ghost predicate WF() {
      && ClientHost.GroupWFConstants(clients)
      && ServerHost.GroupWFConstants(servers)
    }
    
    ghost predicate ValidClientIdx(idx: int) {
      0 <= idx < |clients|
    }

    ghost function GetServer() : ServerHost.Constants 
      requires WF()
    {
      servers[0]
    }

    ghost function GetClient(idx: int) : ClientHost.Constants
      requires WF()
      requires ValidClientIdx(idx)
    {
      clients[idx]
    }
  }

  datatype Hosts = Hosts(
    clients: seq<ClientHost.Variables>,
    servers: seq<ServerHost.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && ClientHost.GroupWF(c.clients, clients)
      && ServerHost.GroupWF(c.servers, servers)
    }

    ghost function GetServer(c: Constants) : ServerHost.Variables 
      requires WF(c)
    {
      servers[0]
    }

    ghost function GetClient(c: Constants, idx: int) : ClientHost.Variables
      requires WF(c)
      requires c.ValidClientIdx(idx)
    {
      clients[idx]
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
  }

  ghost predicate InitHosts(c: Constants, h: Hosts)
  {
    && ClientHost.GroupInit(c.clients, h.clients)
    && ServerHost.GroupInit(c.servers, h.servers)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  ghost predicate ClientAction(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidClientIdx(actor)
    && ClientHost.Next(c.clients[actor], h.clients[actor], h'.clients[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != actor :: h'.clients[otherIdx] == h.clients[otherIdx])
    && h.servers == h'.servers
  }

  ghost predicate ServerAction(c: Constants, h: Hosts, h': Hosts, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && ServerHost.Next(c.GetServer(), h.GetServer(c), h'.GetServer(c), msgOps)
    // all other hosts UNCHANGED
    && h.clients == h'.clients
  }

  datatype Step =
    | ClientStep(actorIdx: nat, msgOps: MessageOps)
    | ServerStep(msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step
      case ClientStep(actor, msgOps) => ClientAction(c, h, h', actor, msgOps)
      case ServerStep(msgOps) => ServerAction(c, h, h', msgOps)
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
    forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: c.ValidClientIdx(req.r.clientId)
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
