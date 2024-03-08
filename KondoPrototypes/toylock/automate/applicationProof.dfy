include "messageInvariantsAutogen.dfy"
include "ownershipInvariantsAutogen.dfy"

module ToylockProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants
import opened OwnershipInvariants

ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  true
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && OwnershipInv(c, v)
  && ApplicationInv(c, v)
  && Safety(c, v)
}


/***************************************************************************************
*                                Top-level Obligations                                 *
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
  OwnershipInvInductive(c, v, v');
  AtMostOwnerPerKeyImpliesSafety(c, v');
}

/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma AtMostOwnerPerKeyImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneOwnerPerKeyHost(c, v)
  ensures Safety(c, v)
{
  forall idx1, idx2, k: UniqueKey| 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && HoldsLock(c, v, idx1)
    && HoldsLock(c, v, idx2)
  ensures
     idx1 == idx2
  {
    // triggers
    assert Host.HostOwnsUniqueKey(c.hosts[idx1], v.Last().hosts[idx1], k);
    assert Host.HostOwnsUniqueKey(c.hosts[idx1], v.Last().hosts[idx1], k);
  }
}

}

