include "messageInvariants.dfy"
include "ownershipInvariants.dfy"

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
    && HostsCompleteKeys (c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
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
    InitImpliesOwnershipInv(c, v);
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    MessageInvInductive(c, v, v');
    OwnershipInvInductive(c, v, v');
    InvNextHostsCompleteKeys(c, v, v');
    InvNextSafety(c, v, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextHostsCompleteKeys(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures HostsCompleteKeys(c, v')
{
  forall i:int, idx, k: UniqueKey | 
    && v'.ValidHistoryIdx(i)
    && c.ValidIdx(idx)
  ensures v'.History(i).hosts[idx].HasKey(k)
  {

    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if actor == idx {
        assert v.Last().hosts[idx].HasKey(k);  // trigger
      }
    }
  }
}

lemma InvNextSafety(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Safety(c, v')
{
  forall idx1, idx2, k: UniqueKey | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && v'.Last().hosts[idx1].HasLiveKey(k)
    && v'.Last().hosts[idx2].HasLiveKey(k)
  ensures
     idx1 == idx2
  {
    if idx1 != idx2 {
      if v.Last().hosts[idx1].HasLiveKey(k) {
        AtMostOneHostHasLiveKey(c, v, v', k, idx1, idx2);
      } else if v.Last().hosts[idx2].HasLiveKey(k) {
        AtMostOneHostHasLiveKey(c, v, v', k, idx2, idx1);
      }
    }
  }
}

lemma AtMostOneHostHasLiveKey(c: Constants, v: Variables, v': Variables, k: UniqueKey, idx: HostId, other: HostId)
  requires v.WF(c) && v'.WF(c)
  requires Inv(c, v)
  requires c.ValidIdx(idx)
  requires c.ValidIdx(other)
  requires idx != other
  requires v.Last().hosts[idx].HasLiveKey(k)
  requires !v.Last().hosts[other].HasLiveKey(k)
  requires Next(c, v, v')
  ensures !v'.Last().hosts[other].HasLiveKey(k)
{
  var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
  var actor, msgOps := dsStep.actor, dsStep.msgOps;
  if actor == other {
    var cs, s, s' := c.hosts[other], v.Last().hosts[other], v'.Last().hosts[other];
    var step :| Host.NextStep(cs, s, s', step, msgOps);
    if step.ReceiveStep? && v'.Last().hosts[other].HasLiveKey(k) {
      // triggers
      assert KeyInFlightByMessage(c, v, msgOps.recv.value, k);  
      assert KeyInFlight(c, v, k);
      assert false;
    }    
  }
}

} // end module ShardedKVProof