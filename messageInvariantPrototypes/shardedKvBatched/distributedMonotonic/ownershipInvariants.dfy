include "spec.dfy"

module OwnershipInvariants {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  ghost predicate KeyInFlight(c: Constants, v: Variables, k: OwnedKey) 
    requires v.WF(c)
  {
    exists msg :: KeyInFlightByMessage(c, v, msg, k)
  }

  ghost predicate KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: OwnedKey) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && (0 <= msg.Dst() < |c.hosts| ==>
      Host.OwnedKeyInFlight(c.hosts[msg.Dst()], v.Last().hosts[msg.Dst()], k, msg)
    )
  }

  ghost predicate AtMostOneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k) 
    :: m1 == m2
  }

  ghost predicate NoHostOwnsKey(c: Constants, v: Variables, k: OwnedKey) 
    requires v.WF(c)
  {
    forall idx | c.ValidIdx(idx) :: !Host.HostOwnsKey(c.hosts[idx], v.Last().hosts[idx], k)
  }

  ghost predicate HostOwnsKeyImpliesNoneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoHostOwnsKey(c, v, k)
    ::
    !KeyInFlight(c, v, k)
  }

  
  ghost predicate OwnershipInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && AtMostOneInFlight(c, v)
    && HostOwnsKeyImpliesNoneInFlight(c, v)
  }

  lemma InitImpliesOwnershipInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures OwnershipInv(c, v)
  {}

  lemma OwnershipInvInductive(c: Constants, v: Variables, v': Variables)
    requires OwnershipInv(c, v)
    requires Next(c, v, v')
    ensures OwnershipInv(c, v')
  {
    InvNextAtMostOneInFlight(c, v, v');
    InvNextLiveKeyImpliesNoneInFlight(c, v, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


lemma InvNextAtMostOneInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneInFlight(c, v')
{
  forall k, m1, m2 | KeyInFlightByMessage(c, v', m1, k) && KeyInFlightByMessage(c, v', m2, k) 
  ensures m1 == m2
  {
    if m1 != m2 {
      if KeyInFlightByMessage(c, v, m1, k) {
        InvNextAtMostOneInFlightHelper(c, v, v', m1, m2, k);
      } else {
        InvNextAtMostOneInFlightHelper(c, v, v', m2, m1, k);
      }
    }
  }
}

lemma InvNextAtMostOneInFlightHelper(c: Constants, v: Variables, v': Variables, m1: Message, m2: Message, k: OwnedKey)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  // input constraints
  requires m1 != m2
  requires KeyInFlightByMessage(c, v, m1, k)
  requires !KeyInFlightByMessage(c, v, m2, k)
  // postcondition
  ensures !KeyInFlightByMessage(c, v', m2, k)
{
  assert KeyInFlight(c, v, k);
}


// TODO: Something is wrong here. This proof should not pass
lemma InvNextLiveKeyImpliesNoneInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsKeyImpliesNoneInFlight(c, v')
{
  forall k | !NoHostOwnsKey(c, v', k)
  ensures !KeyInFlight(c, v', k)
  {
    forall msg | msg in v'.network.sentMsgs
    ensures !KeyInFlightByMessage(c, v', msg, k) {
      var idx :| c.ValidIdx(idx) && Host.HostOwnsKey(c.hosts[idx], v'.Last().hosts[idx], k);
      if Host.HostOwnsKey(c.hosts[idx], v.Last().hosts[idx], k){
        // triggers
        assert !KeyInFlight(c, v, k);
        assert !KeyInFlightByMessage(c, v, msg, k);
      } else {
        if msg in v.network.sentMsgs && KeyInFlightByMessage(c, v, msg, k){
          var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
          // triggers
          assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
          assert KeyInFlight(c, v, k);
        }
      }
    }
  }
}
} // end module ShardedKVProof