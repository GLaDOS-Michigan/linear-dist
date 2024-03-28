include "centralizedHosts.dfy"

module System {
import opened UtilitiesLibrary
import opened Types
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
  
  ghost predicate ValidClientIdx(idx: nat) {
    idx < |clients|
  }

  ghost function GetServer() : ServerHost.Constants 
    requires WF()
  {
    servers[0]
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

  ghost function History(i: int) : (h: Hosts)
    requires ValidHistoryIdx(i)
    ensures h == history[i]
  {
    history[i]
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
  && ClientHost.GroupInit(c.clients, v.History(0).clients)
  && ServerHost.GroupInit(c.servers, v.History(0).servers)
}

ghost predicate NextClientRequestStep(c: Constants, h: Hosts, h': Hosts, cidx: nat, req: Request)
  requires h.WF(c) && h'.WF(c)
{
  var clientLbl := ClientHost.RequestLbl(req);
  var serverLbl := ServerHost.ReceiveLbl(req);
  && c.ValidClientIdx(cidx)
  && ClientHost.Next(c.clients[cidx], h.clients[cidx], h'.clients[cidx], clientLbl)    // step client
  && ServerHost.Next(c.GetServer(), h.GetServer(c), h'.GetServer(c), serverLbl)  // step server
  && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx :: h'.clients[otherIdx] == h.clients[otherIdx])
}

ghost predicate NextServerProcessStep(c: Constants, h: Hosts, h': Hosts, req: Request)
  requires h.WF(c) && h'.WF(c)
{
  && var serverLbl := ServerHost.ProcessLbl(req);
  && var clientLbl := ClientHost.ReceiveLbl(req);
  && var cidx := req.clientId;
  && c.ValidClientIdx(cidx)
  && ServerHost.Next(c.GetServer(), h.GetServer(c), h'.GetServer(c), serverLbl)  // step server
  && ClientHost.Next(c.clients[cidx], h.clients[cidx], h'.clients[cidx], clientLbl)    // step client
  && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx :: h'.clients[otherIdx] == h.clients[otherIdx])
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

}  // end module System
