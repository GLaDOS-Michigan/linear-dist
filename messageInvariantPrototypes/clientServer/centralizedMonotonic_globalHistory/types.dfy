include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Request = Req(clientId: ClientId, reqId: nat)
} // end module Types