include "messageInvariants.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MessageInvariants
import opened Obligations
  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

ghost predicate ClientRequestsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, idx:nat |
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && c.ValidClientIdx(idx) 
  :: 
    && v.History(i).hosts[idx].client.requests <= 
        v.History(j).hosts[idx].client.requests
}

ghost predicate MonotonicityInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  ClientRequestsMonotonic(c, v)
}


// The server's requests must have come from sender client
ghost predicate ServerRequestsValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i| 
    && v.ValidHistoryIdx(i)
    && v.History(i).GetServer(c).server.currentRequest.Some?
  ::
    && var req := v.History(i).GetServer(c).server.currentRequest.value;
    && c.ValidClientIdx(req.clientId)
    && req.reqId in v.History(i).hosts[req.clientId].client.requests
}

ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  ServerRequestsValid(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ApplicationInv(c, v)
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
{
  VariableNextProperties(c, v, v');
  MessageInvInductive(c, v, v');
  InvNextServerRequestsValid(c, v, v');
}

lemma InvNextServerRequestsValid(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerRequestsValid(c, v')
{
  VariableNextProperties(c, v, v');
}

}  // end module ClientServerProof

