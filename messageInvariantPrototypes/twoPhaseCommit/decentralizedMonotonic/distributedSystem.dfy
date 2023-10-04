
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
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Hosts = Hosts(
    hosts: seq<Host.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
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
    && Host.GroupInit(c.hosts, v.History(0).hosts)
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
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && HostAction(c, h, h', step.hostid, step.msgOps)
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
}


