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
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate Init(c: Constants, v: Variables) {
    v.currentRequest == None
  }

  datatype Step =
    ReceiveStep() | ProcessStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case ProcessStep => NextProcessStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && NextReceiveStepRecvFunc(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate NextReceiveStepRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.currentRequest.None?
    && msg.RequestMsg?
    // update v'
    && v' == v.(currentRequest := Some(msg.r))
  }

  ghost predicate NextProcessStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && NextProcessStepSendFunc(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate NextProcessStepSendFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.currentRequest.Some?
    // send message and update v'
    && v' == v.(currentRequest := None)
    && msg == ResponseMsg(v.currentRequest.value)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
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

  ghost predicate ConstantsValidForGroup(c: Constants, clientId: ClientId) {
    c.clientId == clientId
  }

  datatype Variables = Variables(requests: set<nat>, responses: set<nat>)
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && 0 < |v.requests|  // non-deterministic set
    && v.responses == {}
  }

  datatype Step =
      RequestStep()
    | ReceiveStep() 
    | StutterStep

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps) {
    match step
      case RequestStep() => NextRequestStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextRequestStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && NextRequestStepSendFunc(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate NextRequestStepSendFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // send message and update v'
    && msg.RequestMsg?
    && msg.r.clientId == c.clientId
    && msg.r.reqId in v.requests
    && v' == v
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && NextReceiveRespStepRecvFunc(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate NextReceiveRespStepRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.ResponseMsg?
    && msg.r.clientId == c.clientId
    // update v'
    && v' == v.(responses := v.responses + {msg.r.reqId})
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
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
    ghost predicate WF(c: Constants) {
      && (ServerVariables? <==> c.ServerConstants?) // types of c & v agree
      && (match c
            case ServerConstants(_) => server.WF(c.server)
            case ClientConstants(_) => client.WF(c.client)
          )
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
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

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c|
    && (forall idx:nat | idx < |grp_c| :: grp_v[idx].WF(grp_c[idx]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWF(grp_c, grp_v)
    && ServerHost.Init(Last(grp_c).server, Last(grp_v).server)
    && (forall clientId:ClientId | clientId < |grp_c|-1 ::
        ClientHost.Init(grp_c[clientId].client, grp_v[clientId].client)
      )
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case ServerConstants(_) => ServerHost.Next(c.server, v.server, v'.server, msgOps)
      case ClientConstants(_) => ClientHost.Next(c.client, v.client, v'.client, msgOps)
      )
  }
}  // end module Host
