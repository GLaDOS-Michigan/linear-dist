include "../CentralizedHosts.dfy"

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

datatype Variables = Variables(
  hosts: seq<Host.Variables>)
{
  ghost predicate WF(c: Constants) {
    && c.WF()
    && Host.GroupWF(c.hostConstants, hosts)
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && Host.GroupInit(c.hostConstants, v.hosts)
}

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, actor: nat, payload: int)
  requires v.WF(c) && v'.WF(c)
{
  var senderLbl := Host.SendLbl(payload);
  var receiverLbl := Host.ReceiveLbl(payload);
  && c.ValidIdx(actor)
  && var succ := Successor(|c.hostConstants|, actor);
  && Host.Next(c.hostConstants[actor], v.hosts[actor], v'.hosts[actor], senderLbl)    // step sender
  && Host.Next(c.hostConstants[succ], v.hosts[succ], v'.hosts[succ], receiverLbl)     // step receiver
  && forall idx:nat | 
      && c.ValidIdx(idx) 
      && idx != actor
      && idx != succ
      :: 
      v'.hosts[idx] == v.hosts[idx]
}

datatype Step = TransmissionStep(actor: nat, payload: int)

ghost predicate NextStep(c:Constants, v: Variables, v': Variables, step: Step) 
  requires v.WF(c) && v'.WF(c)
{
  match step {
      case TransmissionStep(actor, payload) => Transmission(c, v, v', actor, payload)
  }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && exists step :: NextStep(c, v, v', step)
}

}  // end module DistributedSystem
