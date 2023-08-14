include "hosts.dfy"

module System {
import opened UtilitiesLibrary
import opened Types
import Host
import ServerHost
import ClientHost

datatype Constants = Constants(hosts: seq<Host.Constants>)
{
  ghost predicate WF() {
    Host.GroupWFConstants(hosts)
  }
  ghost predicate ValidActorIdx(idx: nat) {
    idx < |hosts|
  }
  ghost predicate ValidClientIdx(idx: nat) {
    idx < |hosts|-1
  }

  ghost predicate ValidServerIdx(idx: nat) {
    idx == |hosts|-1
  }

  ghost function GetServer() : Host.Constants
    requires WF()
  {
    Last(hosts)
  }
}

datatype Variables = Variables(hosts: seq<Host.Variables>)
{
  ghost predicate WF(c: Constants) {
    && c.WF()
    && Host.GroupWF(c.hosts, hosts)
  }

  ghost function GetServer(c: Constants) : Host.Variables
    requires WF(c)
  {
    Last(hosts)
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && Host.GroupInit(c.hosts, v.hosts)
}

ghost predicate NextClientRequestStep(c: Constants, v: Variables, v': Variables, cidx: nat, reqId: nat)
  requires v.WF(c) && v'.WF(c)
{
  var req := Req(cidx, reqId);
  var clientLbl := ClientHost.RequestLbl(req);
  var serverLbl := ServerHost.ReceiveLbl(req);
  && c.ValidClientIdx(cidx)
  && Host.Next(c.hosts[cidx], v.hosts[cidx], v'.hosts[cidx], Host.CL(clientLbl))    // step client
  && Host.Next(c.GetServer(), v.GetServer(c), v'.GetServer(c), Host.SL(serverLbl))  // step server
  && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx :: v'.hosts[otherIdx] == v.hosts[otherIdx])
}

ghost predicate NextServerProcessStep(c: Constants, v: Variables, v': Variables, req: Request)
  requires v.WF(c) && v'.WF(c)
{
  && var serverLbl := ServerHost.ProcessLbl(req);
  && var clientLbl := ClientHost.ReceiveLbl(req);
  && var cidx := req.clientId;
  && c.ValidClientIdx(cidx)
  && Host.Next(c.GetServer(), v.GetServer(c), v'.GetServer(c), Host.SL(serverLbl))  // step server
  && Host.Next(c.hosts[cidx], v.hosts[cidx], v'.hosts[cidx], Host.CL(clientLbl))    // step client
  && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx :: v'.hosts[otherIdx] == v.hosts[otherIdx])
}

datatype Step =
  | ClientRequestStep(clientIdx: nat, reqId: nat) // step where client initializes a request
  | ServerProcessStep(r: Request)                 // step where server processes a request
  | StutterStep()

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
      case ClientRequestStep(idx, reqId) => NextClientRequestStep(c, v, v', idx, reqId)
      case ServerProcessStep(req) => NextServerProcessStep(c, v, v', req)
      case StutterStep => && v == v'
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && exists step :: NextStep(c, v, v', step)
}
}  // end module System
