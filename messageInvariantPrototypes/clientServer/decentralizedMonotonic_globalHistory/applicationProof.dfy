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
    && v.History(i).clients[idx].requests <= 
        v.History(j).clients[idx].requests
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
    && v.History(i).GetServer(c).currentRequest.Some?
  ::
    && var req := v.History(i).GetServer(c).currentRequest.value;
    && c.ValidClientIdx(req.clientId)
    && req.reqId in v.History(i).clients[req.clientId].requests
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

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  VariableNextProperties(c, v, v');
  MessageInvInductive(c, v, v');
  InvNextClientRequestsMonotonic(c, v, v');
  InvNextServerRequestsValid(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvNextClientRequestsMonotonic(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ClientRequestsMonotonic(c, v)
  requires Next(c, v, v')
  ensures ClientRequestsMonotonic(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextServerRequestsValid(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerRequestsValid(c, v')
{
  VariableNextProperties(c, v, v');
  forall i| 
    && v'.ValidHistoryIdx(i)
    && v'.History(i).GetServer(c).currentRequest.Some?
  ensures
    && var req := v'.History(i).GetServer(c).currentRequest.value;
    && c.ValidClientIdx(req.clientId)
    && req.reqId in v'.History(i).clients[req.clientId].requests
  {}
}

}  // end module ClientServerProof

