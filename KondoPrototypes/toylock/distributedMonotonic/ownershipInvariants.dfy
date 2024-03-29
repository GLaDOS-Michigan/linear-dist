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
    forall idx | 0 <= idx < |c.hosts|  :: !Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k)
  }

/***************************************************************************************
*                                    Invariants                                        *
***************************************************************************************/


  ghost predicate AtMostOneInFlightMessagePerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k)
    :: m1 == m2
  }

  ghost predicate HostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoHostOwnsKey(c, v, k)
    ::
    !UniqueKeyInFlight(c, v, k)
  }

  ghost predicate AtMostOwnerPerKeyHosts(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && 0 <= h1 < |c.hosts|
      && 0 <= h2 < |c.hosts|
      && Host.HostOwnsUniqueKey(c.hosts[h1], v.Last().hosts[h1], k) 
      && Host.HostOwnsUniqueKey(c.hosts[h2], v.Last().hosts[h2], k) 
    ::
     h1 == h2
  }  
  
  ghost predicate OwnershipInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && AtMostOneInFlightMessagePerKey(c, v)
    && AtMostOwnerPerKeyHosts(c, v)
    && HostOwnsKeyImpliesNotInFlight(c, v)
  }

  // Base obligation
  lemma InitImpliesOwnershipInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures OwnershipInv(c, v)
  {}

  // Inductive obligation
  lemma OwnershipInvInductive(c: Constants, v: Variables, v': Variables)
    requires OwnershipInv(c, v)
    requires Next(c, v, v')
    ensures OwnershipInv(c, v')
  {
    InvNextAtMostOneInFlightMessagePerKey(c, v, v');
    InvNextHostOwnsKeyImpliesNotInFlight(c, v, v');
    InvNextAtMostOwnerPerKeyHosts(c, v, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


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

lemma InvNextHostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsKeyImpliesNotInFlight(c, v')
{
  forall k | !NoHostOwnsKey(c, v', k)
  ensures !UniqueKeyInFlight(c, v', k)
  {
    if UniqueKeyInFlight(c, v', k) {
      var msg :| KeyInFlightByMessage(c, v', msg , k);
      if msg in v.network.sentMsgs {
        assert KeyInFlightByMessage(c, v, msg, k);
        assert NoHostOwnsKey(c, v, k);  
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        assert dsStep.msgOps.recv.value == msg by {
          if dsStep.msgOps.recv.value != msg {
            var m' := dsStep.msgOps.recv.value;
            assert !KeyInFlightByMessage(c, v, m', k);
          }
        }
      } else {
        assert !(NoHostOwnsKey(c, v, k));
      }
    }
  }
}

lemma InvNextAtMostOwnerPerKeyHosts(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOwnerPerKeyHosts(c, v')
{
  var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
  forall h1, h2, k | 
      && 0 <= h1 < |c.hosts|
      && 0 <= h2 < |c.hosts|
      && Host.HostOwnsUniqueKey(c.hosts[h1], v'.Last().hosts[h1], k) 
      && Host.HostOwnsUniqueKey(c.hosts[h2], v'.Last().hosts[h2], k) 
  ensures
     h1 == h2
  {
    if h1 != h2 {
      if Host.HostOwnsUniqueKey(c.hosts[h2], v'.Last().hosts[h2], k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
        assert UniqueKeyInFlight(c, v, k);
        assert false;
      }
      if Host.HostOwnsUniqueKey(c.hosts[h1], v'.Last().hosts[h1], k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
        assert UniqueKeyInFlight(c, v, k);
        assert false;
      }
    }
  }
}
} // end module ShardedKVProof