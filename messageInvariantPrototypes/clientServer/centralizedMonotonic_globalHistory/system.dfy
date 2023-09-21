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

datatype Hosts = Hosts(
  hosts: seq<Host.Variables>
) {
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

datatype Variables = Variables(history: seq<Hosts>)
{
  ghost predicate ValidHistoryIdx(i: int) {
    0 <= i < |history|
  }

  ghost predicate WF(c: Constants) {
    && c.WF()
    && 0 < |history|
    && (forall i | ValidHistoryIdx(i) :: history[i].WF(c))
  }

  ghost function Last() : Hosts 
    requires 0 < |history|
  {
    UtilitiesLibrary.Last(history)
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && |v.history| == 1
  && Host.GroupInit(c.hosts, v.history[0].hosts)
}

ghost predicate NextClientRequestStep(c: Constants, h: Hosts, h': Hosts, cidx: nat, req: Request)
  requires h.WF(c) && h'.WF(c)
{
  var clientLbl := ClientHost.RequestLbl(req);
  var serverLbl := ServerHost.ReceiveLbl(req);
  && c.ValidClientIdx(cidx)
  && Host.Next(c.hosts[cidx], h.hosts[cidx], h'.hosts[cidx], Host.CL(clientLbl))    // step client
  && Host.Next(c.GetServer(), h.GetServer(c), h'.GetServer(c), Host.SL(serverLbl))  // step server
  && ClientsUnchangedExcept(c, h, h', cidx)
}

ghost predicate NextServerProcessStep(c: Constants, h: Hosts, h': Hosts, req: Request)
  requires h.WF(c) && h'.WF(c)
{
  && var serverLbl := ServerHost.ProcessLbl(req);
  && var clientLbl := ClientHost.ReceiveLbl(req);
  && var cidx := req.clientId;
  && c.ValidClientIdx(cidx)
  && Host.Next(c.GetServer(), h.GetServer(c), h'.GetServer(c), Host.SL(serverLbl))  // step server
  && Host.Next(c.hosts[cidx], h.hosts[cidx], h'.hosts[cidx], Host.CL(clientLbl))    // step client
  && ClientsUnchangedExcept(c, h, h', cidx)
}

datatype Step =
  | ClientRequestStep(clientIdx: nat, req: Request) // step where client initializes a request
  | ServerProcessStep(r: Request)                 // step where server processes a request
  | StutterStep()

ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, step: Step)
  requires h.WF(c) && h'.WF(c)
{
  match step
      case ClientRequestStep(idx, req) => NextClientRequestStep(c, h, h', idx, req)
      case ServerProcessStep(req) => NextServerProcessStep(c, h, h', req)
      case StutterStep => && h == h'
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && IsSeqExtension(v.history, v'.history)
  && exists step :: NextStep(c, v.Last(), v'.Last(), step)
}

//// Helper Functions ////

ghost predicate ClientsUnchangedExcept(c: Constants, h: Hosts, h': Hosts, cidx: nat)
  requires h.WF(c) && h'.WF(c)
  requires c.ValidClientIdx(cidx)
{
  forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx
  :: h'.hosts[otherIdx] == h.hosts[otherIdx]
}

}  // end module System
