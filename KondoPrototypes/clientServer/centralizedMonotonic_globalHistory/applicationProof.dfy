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

ghost predicate Inv(c: Constants, v: Variables)
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
{
  InvNextServerRequestsValid(c, v, v');
}

lemma InvNextServerRequestsValid(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerRequestsValid(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  ensures 1 < |v'.history|
  ensures |v.history| == |v'.history| - 1
  ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)
  ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)
{
  assert 0 < |v.history|;
  assert 1 < |v'.history|;
}

}  // end module ClientServerProof

