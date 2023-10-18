include "../centralizedHosts.dfy"

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

datatype Variables = Variables(
  clients: seq<ClientHost.Variables>,
  servers: seq<ServerHost.Variables>)
{
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

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && ClientHost.GroupInit(c.clients, v.clients)
  && ServerHost.GroupInit(c.servers, v.servers)
}

ghost predicate NextClientRequestStep(c: Constants, v: Variables, v': Variables, cidx: nat, req: Request)
  requires v.WF(c) && v'.WF(c)
{
  var clientLbl := ClientHost.RequestLbl(req);
  var serverLbl := ServerHost.ReceiveLbl(req);
  && c.ValidClientIdx(cidx)
  && ClientHost.Next(c.clients[cidx], v.clients[cidx], v'.clients[cidx], clientLbl)    // step client
  && ServerHost.Next(c.GetServer(), v.GetServer(c), v'.GetServer(c), serverLbl)  // step server
  && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx :: v'.clients[otherIdx] == v.clients[otherIdx])
}

ghost predicate NextServerProcessStep(c: Constants, v: Variables, v': Variables, req: Request)
  requires v.WF(c) && v'.WF(c)
{
  && var serverLbl := ServerHost.ProcessLbl(req);
  && var clientLbl := ClientHost.ReceiveLbl(req);
  && var cidx := req.clientId;
  && c.ValidClientIdx(cidx)
  && ServerHost.Next(c.GetServer(), v.GetServer(c), v'.GetServer(c), serverLbl)  // step server
  && ClientHost.Next(c.clients[cidx], v.clients[cidx], v'.clients[cidx], clientLbl)    // step client
  && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != cidx :: v'.clients[otherIdx] == v.clients[otherIdx])
}

datatype Step =
  | ClientRequestStep(clientIdx: nat, req: Request) // step where client initializes a request
  | ServerProcessStep(r: Request)                 // step where server processes a request
  | StutterStep()

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
      case ClientRequestStep(idx, req) => NextClientRequestStep(c, v, v', idx, req)
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
