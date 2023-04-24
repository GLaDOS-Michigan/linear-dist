include "spec.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations
  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/


// The server's requests must have come from sender client
predicate ServerRequestsValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  v.GetServer(c).server.currentRequest.Some?
  ==> 
  && var req := v.GetServer(c).server.currentRequest.value;
  && c.ValidClientIdx(req.clientId)
  && req.reqId in v.hosts[req.clientId].client.requests
}


predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ServerRequestsValid(c, v)
  && Safety(c, v)
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{}
}  // end module ClientServerProof
