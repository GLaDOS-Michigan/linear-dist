include "messageInvariantsAutogen.dfy"
include "ownershipInvariantsAutogen.dfy"

module ShardedKVProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations
  import opened MessageInvariants
  import opened OwnershipInvariants


  ghost predicate HostsCompleteKeys(c: Constants, v: Variables)
   requires v.WF(c)
  {
    forall i:int, idx, k: UniqueKey | 
      && v.ValidHistoryIdx(i)
      && c.ValidIdx(idx)
    :: v.History(i).hosts[idx].HasKey(k)
  }
  
  ghost predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    // && HostsCompleteKeys (c, v)
    && true
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && MessageInv(c, v)
    && OwnershipInv(c, v)
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
    MessageInvInductive(c, v, v');
    OwnershipInvInductive(c, v, v');
    // InvNextHostsCompleteKeys(c, v, v');
    AtMostOwnerPerKeyImpliesSafety(c, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

// lemma InvNextHostsCompleteKeys(c: Constants, v: Variables, v': Variables)
//   requires v'.WF(c)
//   requires Inv(c, v)
//   requires Next(c, v, v')
//   ensures HostsCompleteKeys(c, v')
// {
//   forall i:int, idx, k: UniqueKey | 
//     && v'.ValidHistoryIdx(i)
//     && c.ValidIdx(idx)
//   ensures v'.History(i).hosts[idx].HasKey(k)
//   {

//     VariableNextProperties(c, v, v');
//     if i == |v'.history| - 1 {
//       var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
//       var actor, msgOps := dsStep.actor, dsStep.msgOps;
//       if actor == idx {
//         assert v.Last().hosts[idx].HasKey(k);  // trigger
//       }
//     }
//   }
// }

lemma AtMostOwnerPerKeyImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOwnerPerKey(c, v)
  ensures Safety(c, v)
{
  forall idx1, idx2, k: UniqueKey | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && v.Last().hosts[idx1].HasLiveKey(k)
    && v.Last().hosts[idx2].HasLiveKey(k)
  ensures
     idx1 == idx2
  {
    // triggers
    assert Host.HostOwnsUniqueKey(c.hosts[idx1], v.Last().hosts[idx1], k);
    assert Host.HostOwnsUniqueKey(c.hosts[idx1], v.Last().hosts[idx1], k);
  }
}
} // end module ShardedKVProof