include "../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Message =
    Request(clientId: ClientId, reqId: nat) | Response(clientId: ClientId, reqId: nat)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types