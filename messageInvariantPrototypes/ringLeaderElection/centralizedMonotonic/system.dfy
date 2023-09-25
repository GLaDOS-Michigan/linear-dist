include "hosts.dfy"

module System {
import opened UtilitiesLibrary
import opened Types
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
  history: seq<Hosts>)
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

  ghost function Last() : Hosts 
    requires 0 < |history|
    ensures Last() == history[|history|-1]
  {
    UtilitiesLibrary.Last(history)
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && |v.history| == 1
  && Host.GroupInit(c.hostConstants, v.history[0].hosts)
}

ghost predicate Transmission(c: Constants, h: Hosts, h': Hosts, actor: nat, payload: int)
  requires h.WF(c) && h'.WF(c)
{
  var senderLbl := Host.SendLbl(payload);
  var receiverLbl := Host.ReceiveLbl(payload);
  && c.ValidIdx(actor)
  && var succ := Successor(|c.hostConstants|, actor);
  && Host.Next(c.hostConstants[actor], h.hosts[actor], h'.hosts[actor], senderLbl)    // step sender
  && Host.Next(c.hostConstants[succ], h.hosts[succ], h'.hosts[succ], receiverLbl)     // step receiver
  && forall idx:nat | 
      && c.ValidIdx(idx) 
      && idx != actor
      && idx != succ
      :: 
      h'.hosts[idx] == h.hosts[idx]
}

datatype Step = TransmissionStep(actor: nat, payload: int)

ghost predicate NextStep(c:Constants, h: Hosts, h': Hosts, step: Step) 
  requires h.WF(c) && h'.WF(c)
{
  match step {
      case TransmissionStep(actor, payload) => Transmission(c, h, h', actor, payload)
  }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && IsSeqExtension(v.history, v'.history)
  && exists step :: NextStep(c, v.Last(), v'.Last(), step)
}

}  // end module DistributedSystem
