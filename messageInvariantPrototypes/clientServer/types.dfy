include "../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Request = Req(clientId: ClientId, reqId: nat)

  datatype Message =
    RequestMsg(r: Request) | ResponseMsg(r: Request)
  {
    ghost function Src() : nat {
      if this.RequestMsg? then r.clientId else 0
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types