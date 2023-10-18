
include "../hosts.dfy"


module Network {
  import opened Types

  datatype Constants = Constants  // no constants for network

  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
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

    ghost predicate ValidHostId(id: int) {
      0 <= id < |hosts|
    }

    ghost predicate ValidParticipantId(id: int) {
      0 <= id < |hosts|-1
    }

    ghost predicate ValidCoordinatorId(id: int) {
      id == |hosts|-1
    }
    
    ghost function GetCoordinator() : CoordinatorHost.Constants
      requires WF()
    {
      Last(hosts).coordinator
    }

    ghost function GetParticipant(idx: int) : ParticipantHost.Constants
      requires WF()
      requires ValidParticipantId(idx)
    {
      hosts[idx].participant
    }
  }

  datatype Hosts = Hosts(
    hosts: seq<Host.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }

    ghost function GetCoordinator(c: Constants) : CoordinatorHost.Variables
      requires WF(c)
    {
      Last(hosts).coordinator
    }

    ghost function GetParticipant(c: Constants, i: int) : ParticipantHost.Variables
      requires WF(c)
      requires c.ValidParticipantId(i)
    {
      hosts[i].participant
    }

    ghost function GetParticipantPreference(c: Constants, i: int) : Vote
      requires c.WF()
      requires c.ValidParticipantId(i)
    {
      c.hosts[i].participant.preference
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
    Host.GroupInit(c.hosts, h.hosts)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  ghost predicate HostAction(c: Constants, h: Hosts, h': Hosts, hostid: HostId, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], h.hosts[hostid], h'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: h'.hosts[otherHost] == h.hosts[otherHost])
  }

  datatype Step =
    | HostActionStep(actor: HostId, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && HostAction(c, h, h', step.actor, step.msgOps)
    && Network.Next(c.network, n, n', step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && IsSeqExtension(v.history, v'.history)
    && exists step :: NextStep(c, v.Last(), v'.Last(), v.network, v'.network, step)
  }

  ghost function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
      case CoordinatorVariables(coordinator) => coordinator.decision
      case ParticipantVariables(participant) => participant.decision
  }

/***************************************************************************************
*                                Variable properties                                   *
***************************************************************************************/

  ghost predicate ValidMessages(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
    :: c.ValidParticipantId(msg.src)
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
} // end module Distributed System


