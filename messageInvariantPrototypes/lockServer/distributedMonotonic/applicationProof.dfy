include "messageInvariants.dfy"
include "ownershipInvariants.dfy"

module LockServerProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations
  import opened MessageInvariants
  import opened OwnershipInvariants

  
  ghost predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && true
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && MessageInv(c, v)
    && OwnershipInv(c, v)
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
    InitImpliesOwnershipInv(c, v);
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
  requires AtMostOwnerPerKeyClients(c, v)
  requires AtMostOwnerPerKeyServers(c, v)
  ensures Safety(c, v)
{
  forall idx1, idx2 | 
    && c.ValidClientIdx(idx1) 
    && c.ValidClientIdx(idx2) 
    && HoldsLock(c, v, idx1)
    && HoldsLock(c, v, idx2)
  ensures
   idx1 == idx2
  {
    // triggers
    assert ClientHost.HostOwnsUniqueKey(c.clients[idx1], v.Last().clients[idx1], 0);
    assert ClientHost.HostOwnsUniqueKey(c.clients[idx1], v.Last().clients[idx1], 0);
  }
}
} // end module LockServerProof