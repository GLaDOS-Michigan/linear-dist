include "monotonicityInvariants.dfy"
include "messageInvariants.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations


/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/


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
    && req.reqId in v.History(i).clients[req.clientId].requests.s
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
  InitImpliesMonotonicityInv(c, v);
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  VariableNextProperties(c, v, v');
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  InvNextServerRequestsValid(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

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
    && req.reqId in v'.History(i).clients[req.clientId].requests.s
  {}
}

}  // end module ClientServerProof

