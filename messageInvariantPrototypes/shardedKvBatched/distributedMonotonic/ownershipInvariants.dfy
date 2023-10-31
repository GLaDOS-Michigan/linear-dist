include "spec.dfy"

module OwnershipInvariants {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

/***************************************************************************************
*                                   Definitions                                        *
***************************************************************************************/

  ghost predicate UniqueKeyInFlight(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    exists msg :: KeyInFlightByMessage(c, v, msg, k)
  }

  ghost predicate KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: UniqueKey) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && (0 <= msg.Dst() < |c.hosts| ==>
      Host.UniqueKeyInFlightForHost(c.hosts[msg.Dst()], v.Last().hosts[msg.Dst()], k, msg)
    )
  }

  ghost predicate NoHostOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    forall idx | c.ValidIdx(idx) :: !Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k)
  }


/***************************************************************************************
*                                    Invariants                                        *
***************************************************************************************/

  ghost predicate AtMostOwnerPerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && c.ValidIdx(h1) 
      && c.ValidIdx(h2)
      && Host.HostOwnsUniqueKey(c.hosts[h1], v.Last().hosts[h1], k) 
      && Host.HostOwnsUniqueKey(c.hosts[h2], v.Last().hosts[h2], k) 
    ::
     h1 == h2
  }

  ghost predicate HostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoHostOwnsKey(c, v, k)
    ::
    !UniqueKeyInFlight(c, v, k)
  }

  ghost predicate AtMostOneInFlightMessagePerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k) 
    :: m1 == m2
  }
  
  ghost predicate OwnershipInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && AtMostOwnerPerKey(c, v)
    && HostOwnsKeyImpliesNotInFlight(c, v)
    && AtMostOneInFlightMessagePerKey(c, v)
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
    InvNextAtMostOwnerPerKey(c, v, v');
    InvNextHostOwnsKeyImpliesNotInFlight(c, v, v');
    InvNextAtMostOneInFlightMessagePerKey(c, v, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


lemma InvNextAtMostOwnerPerKey(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOwnerPerKey(c, v')
{
  forall h1, h2, k | 
      && c.ValidIdx(h1) 
      && c.ValidIdx(h2)
      && Host.HostOwnsUniqueKey(c.hosts[h1], v'.Last().hosts[h1], k) 
      && Host.HostOwnsUniqueKey(c.hosts[h2], v'.Last().hosts[h2], k) 
  ensures
     h1 == h2
  {
    if h1 != h2 {
      if Host.HostOwnsUniqueKey(c.hosts[h1], v.Last().hosts[h1], k) {
        AtMostOneHostOwnsKey(c, v, v', k, h1, h2);
      } else if Host.HostOwnsUniqueKey(c.hosts[h2], v.Last().hosts[h2], k) {
        AtMostOneHostOwnsKey(c, v, v', k, h2, h1);
      }
    }
  }
}

lemma AtMostOneHostOwnsKey(c: Constants, v: Variables, v': Variables, k: UniqueKey, idx: HostId, other: HostId)
  requires v.WF(c) && v'.WF(c)
  requires OwnershipInv(c, v)
  requires c.ValidIdx(idx)
  requires c.ValidIdx(other)
  requires idx != other
  requires Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k) 
  requires !Host.HostOwnsUniqueKey(c.hosts[other], v.Last().hosts[other], k) 
  requires Next(c, v, v')
  ensures !Host.HostOwnsUniqueKey(c.hosts[other], v'.Last().hosts[other], k) 
{
  var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
  var actor, msgOps := dsStep.actor, dsStep.msgOps;
  if actor == other {
    var cs, s, s' := c.hosts[other], v.Last().hosts[other], v'.Last().hosts[other];
    var step :| Host.NextStep(cs, s, s', step, msgOps);
    if step.ReceiveStep? && Host.HostOwnsUniqueKey(c.hosts[other], v'.Last().hosts[other], k) {
      // triggers
      assert KeyInFlightByMessage(c, v, msgOps.recv.value, k);  
      assert UniqueKeyInFlight(c, v, k);
      assert false;
    }    
  }
}

lemma InvNextHostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsKeyImpliesNotInFlight(c, v')
{
  forall k | !NoHostOwnsKey(c, v', k)
  ensures !UniqueKeyInFlight(c, v', k)
  {
    forall msg | msg in v'.network.sentMsgs
    ensures !KeyInFlightByMessage(c, v', msg, k) {
      var idx :| c.ValidIdx(idx) && Host.HostOwnsUniqueKey(c.hosts[idx], v'.Last().hosts[idx], k);
      if Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k) {
        // triggers
        assert !UniqueKeyInFlight(c, v, k);
        assert !KeyInFlightByMessage(c, v, msg, k);
      } else {
        if msg in v.network.sentMsgs && KeyInFlightByMessage(c, v, msg, k){
          var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
          // triggers
          assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
          assert UniqueKeyInFlight(c, v, k);
        }
      }
    }
  }
}

lemma InvNextAtMostOneInFlightMessagePerKey(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneInFlightMessagePerKey(c, v')
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

lemma InvNextAtMostOneInFlightHelper(c: Constants, v: Variables, v': Variables, m1: Message, m2: Message, k: UniqueKey)
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
  assert UniqueKeyInFlight(c, v, k);
}
} // end module ShardedKVProof