include "../lib/UtilitiesLibrary.dfy"

/* The "client_server_ae protocol sourced from DuoAI (OSDI'22) 
 * Multiple clients can send requests to a server. The server processes each request 
 * and returns a response to the respective client. The server may process the 
 * requests out-of-order.*/

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Message =
    Request(clientId: ClientId, reqId: nat) | Response(clientId: ClientId, reqId: nat)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types


module ServerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants

  // Server is stateless
  datatype Variables = Variables
  {
    predicate WF(c: Constants) {
      true
    }
  }

  predicate Init(c: Constants, v: Variables) {
    v.WF(c)
  }

  datatype Step =
    ReceiveStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  predicate NextReceiveStep(v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && match msgOps.recv.value
        case Request(clientId, reqId) =>
          && v' == v
          && msgOps.send == Some(Response(clientId, reqId))
        case _ => 
          && v' == v //stutter
          && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module ServerHost


module ClientHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(clientId: ClientId)

  predicate ConstantsValidForGroup(c: Constants, clientId: ClientId) {
    c.clientId == clientId
  }

  datatype Variables = Variables(requests: set<nat>, responses: set<nat>)
  {
    predicate WF(c: Constants) {
      true
    }
  }

  predicate Init(c: Constants, v: Variables) {
    && v.requests == {}
    && v.responses == {}
  }

  datatype Step =
    RequestStep(reqId: nat)  // non-deterministic id for the new request
    | ReceiveStep() 
    | StutterStep

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps) {
    match step
      case RequestStep(reqId) => NextRequestStep(c, v, v', msgOps, reqId)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  predicate NextRequestStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, reqId: nat) {
    && msgOps.recv.None?
    && reqId !in v.requests  // reqId must be fresh
    && msgOps.send == Some(Request(c.clientId, reqId))
    && v' == v.(requests := v.requests + {reqId})
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
        case Response(clientId, reqId) =>
          if clientId == c.clientId then 
            v' == v.(responses := v.responses + {reqId})
          else 
            v' == v 
        case _ => 
          && v' == v
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module ClientHost


module Host {
  import opened UtilitiesLibrary
  import opened Types
  import ServerHost
  import ClientHost

  datatype Constants =
    | ServerConstants(server: ServerHost.Constants)
    | ClientConstants(client: ClientHost.Constants)

  datatype Variables =
    | ServerVariables(server: ServerHost.Variables)
    | ClientVariables(client: ClientHost.Variables)
  {
    predicate WF(c: Constants) {
      && (ServerVariables? <==> c.ServerConstants?) // types of c & v agree
      && (match c
            case ServerConstants(_) => server.WF(c.server)
            case ClientConstants(_) => client.WF(c.client)
          )
    }
  }

  predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There must at least be a server
    && 0 < |grp_c|
    // Last host is a server
    && Last(grp_c).ServerConstants?
    // All the others are clients
    && (forall clientId:ClientId | clientId < |grp_c|-1 :: grp_c[clientId].ClientConstants?)
    // The client's constants must match their group positions.
    && (forall clientId:ClientId | clientId < |grp_c|-1
        :: ClientHost.ConstantsValidForGroup(grp_c[clientId].client, clientId))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c|
    && (forall idx:nat | idx < |grp_c| :: grp_v[idx].WF(grp_c[idx]))
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWF(grp_c, grp_v)
    && ServerHost.Init(Last(grp_c).server, Last(grp_v).server)
    && (forall clientId:ClientId | clientId < |grp_c|-1 ::
        ClientHost.Init(grp_c[clientId].client, grp_v[clientId].client)
      )
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case ServerConstants(_) => ServerHost.Next(c.server, v.server, v'.server, msgOps)
      case ClientConstants(_) => ClientHost.Next(c.client, v.client, v'.client, msgOps)
      )
  }
}  // end module Host


module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  predicate Init(v: Variables) {
    && v.sentMsgs == {}
  }

  predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host
  import ServerHost
  import ClientHost

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    predicate ValidActorIdx(idx: nat) {
      idx < |hosts|
    }
    predicate ValidClientIdx(idx: nat) {
      idx < |hosts|-1
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, actorIdx: nat, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidActorIdx(actorIdx)
    && Host.Next(c.hosts[actorIdx], v.hosts[actorIdx], v'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherIdx:nat | c.ValidActorIdx(otherIdx) && otherIdx != actorIdx :: v'.hosts[otherIdx] == v.hosts[otherIdx])
  }

  datatype Step =
    | HostActionStep(actorIdx: nat, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.actorIdx, step.msgOps)
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}  // end module Distributed System
