include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Request = Req(clientId: ClientId, reqId: nat)

  datatype Message =
    RequestMsg(r: Request) | ResponseMsg(r: Request)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types