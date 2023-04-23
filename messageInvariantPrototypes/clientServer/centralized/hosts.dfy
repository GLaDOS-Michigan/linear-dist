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
    currentRequest: Option<Request>
  )
  {
    predicate WF(c: Constants) {
      true
    }
  }

  predicate Init(c: Constants, v: Variables) {
    v.currentRequest == None
  }

  datatype TransitionLabel =
    ReceiveLbl(r: Request) | ProcessLbl() | InternalLbl()

  datatype Step =
    ReceiveStep() | ProcessStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case ReceiveStep => NextReceiveStep(v, v', lbl)
      case ProcessStep => NextProcessStep(v, v', lbl)
      case StutterStep => && v == v'
                          && lbl.InternalLbl?
  }

  predicate NextReceiveStep(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceiveLbl?
    && v.currentRequest.None?
    && v' == v.(currentRequest := Some(lbl.r))
  }

  predicate NextProcessStep(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ProcessLbl?
    && v.currentRequest.Some?
    && v' == v.(currentRequest := None)
  }

  predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
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

  datatype TransitionLabel =
    RequestLbl(r: Request) | ReceiveLbl(r: Request) | InternalLbl()

  datatype Step =
      RequestStep()
    | ReceiveStep()
    | StutterStep

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel) {
    match step
      case RequestStep => NextRequestStep(c, v, v', lbl)
      case ReceiveStep => NextReceiveStep(c, v, v', lbl)
      case StutterStep => && v == v'
                          && lbl.InternalLbl?

  }

  predicate NextRequestStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.RequestLbl?
    && lbl.r.clientId == c.clientId   // label id must match
    && lbl.r.reqId !in v.requests     // reqId must be fresh
    && v' == v.(requests := v.requests + {lbl.r.reqId})
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables,lbl: TransitionLabel) {
    && lbl.ReceiveLbl?
    && lbl.r.clientId == c.clientId   // label id must match
    && v' == v.(responses := v.responses + {lbl.r.reqId})
  }

  predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
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

  datatype TransitionLabel =
    | ServerLabel(s: ServerHost.TransitionLabel)
    | ClientLabel(c: ClientHost.TransitionLabel)

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

  predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case ServerConstants(_) => 
            && lbl.ServerLabel?
            && ServerHost.Next(c.server, v.server, v'.server, lbl.s)
      case ClientConstants(_) => 
            && lbl.ClientLabel?
            && ClientHost.Next(c.client, v.client, v'.client, lbl.c)
      )
  }
}  // end module Host
