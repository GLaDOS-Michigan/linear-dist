include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations

// The server's requests must have come from sender client
ghost predicate ServerRequestsValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i| 
    && v.ValidHistoryIdx(i)
    && v.History(i).GetServer(c).currentRequest.Some?
    && c.ValidClientIdx(v.History(i).GetServer(c).currentRequest.value.clientId)
  ::
    && var req := v.History(i).GetServer(c).currentRequest.value;
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
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

}  // end module ClientServerProof

