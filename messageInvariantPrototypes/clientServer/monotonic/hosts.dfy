include "types.dfy"

/* The "client_server_ae protocol sourced from DuoAI (OSDI'22) 
 * Multiple clients can send requests to a server. The server processes each request 
 * and returns a response to the respective client. The server may process the 
 * requests out-of-order.*/

/***************************************************************************************
*                                      Server Host                                     *
***************************************************************************************/

module ServerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants

  datatype Variables = Variables(
    requests: seq<Request>,     // monotonic seq
    currRequestServiced: bool
  )
  {
    predicate WF(c: Constants) {
      true
    }
  }

  predicate Init(c: Constants, v: Variables) {
    && v.requests == []
    && v.currRequestServiced == true
  }

  datatype Step =
    ReceiveStep() | ProcessStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(v, v', msgOps)
      case ProcessStep => NextProcessStep(v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  predicate NextReceiveStep(v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send == None
    && v.currRequestServiced
    && match msgOps.recv.value
        case RequestMsg(r) =>
          && v' == v.(
            requests := v.requests + [r],
            currRequestServiced := false)
        case _ =>
          && v' == v //stutter
  }

  predicate NextProcessStep(v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && 0 < |v.requests|
    && !v.currRequestServiced
    && v' == v.(currRequestServiced := true)
    && msgOps.send == Some(ResponseMsg(Last(v.requests)))
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module ServerHost


/***************************************************************************************
*                                      Client Host                                     *
***************************************************************************************/

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
    && msgOps.send == Some(RequestMsg(Req(c.clientId, reqId)))
    && v' == v.(requests := v.requests + {reqId})
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
        case ResponseMsg(r) =>
          if r.clientId == c.clientId then 
            v' == v.(responses := v.responses + {r.reqId})
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


/***************************************************************************************
*                                     Generic Host                                     *
***************************************************************************************/

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
