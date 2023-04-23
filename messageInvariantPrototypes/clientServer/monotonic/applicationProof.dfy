include "spec.dfy"
include "messageInvariants.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants
  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Application bundle
predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  true
}

predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
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
{
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
}
}  // end module ClientServerProof

