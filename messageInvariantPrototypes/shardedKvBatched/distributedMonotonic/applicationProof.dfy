// User level proofs of application invariants

include "spec.dfy"

module ShardedKVProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  ghost predicate HostsCompleteKeys(c: Constants, v: Variables)
   requires v.WF(c)
  {
    forall i:int, idx, k: Key | 
      && v.ValidHistoryIdx(i)
      && c.ValidIdx(idx)
    :: v.History(i).hosts[idx].HasKey(k)
  }

  ghost predicate KeyInFlight(c: Constants, v: Variables, k: Key) 
    requires v.WF(c)
  {
      exists msg :: KeyInFlightByMessage(c, v, msg, k)
  }

  ghost predicate KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: Key) 
    requires v.WF(c)
  {
      && msg in v.network.sentMsgs
      && k in msg.vks
      && c.ValidIdx(msg.dst)
      && v.Last().hosts[msg.dst].HasKey(k)
      && v.Last().hosts[msg.dst].myKeys[k].version < msg.vks[k]
  }

  ghost predicate AtMostOneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k) 
    :: m1 == m2
  }

  ghost predicate NoneHasLiveKey(c: Constants, v: Variables, k: Key) 
    requires v.WF(c)
  {
    forall idx | c.ValidIdx(idx) :: !v.Last().hosts[idx].HasLiveKey(k)
  }
  

  ghost predicate LiveKeyImpliesNoneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoneHasLiveKey(c, v, k)
    ::
    !KeyInFlight(c, v, k)
  }

  
  ghost predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && ValidMessages(c, v)
    && HostsCompleteKeys (c, v)
    && AtMostOneInFlight(c, v)
    && LiveKeyImpliesNoneInFlight(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
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
  {}

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    assert v'.WF(c);
    InvNextHostsCompleteKeys(c, v, v');
    InvNextAtMostOneInFlight(c, v, v');
    InvNextLiveKeyImpliesNoneInFlight(c, v, v');
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
  forall i:int, idx, k: Key | 
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

lemma InvNextAtMostOneInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
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

lemma InvNextAtMostOneInFlightHelper(c: Constants, v: Variables, v': Variables, m1: Message, m2: Message, k: Key)
  requires v'.WF(c)
  requires Inv(c, v)
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

lemma InvNextLiveKeyImpliesNoneInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires HostsCompleteKeys(c, v')
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LiveKeyImpliesNoneInFlight(c, v')
{
  forall k | !NoneHasLiveKey(c, v', k)
  ensures !KeyInFlight(c, v', k)
  {
    forall msg | msg in v'.network.sentMsgs && k in msg.vks
    ensures !KeyInFlightByMessage(c, v', msg, k) {
      var idx :| c.ValidIdx(idx) && v'.Last().hosts[idx].HasLiveKey(k);
      if v.Last().hosts[idx].HasLiveKey(k) {
        // triggers
        assert !KeyInFlight(c, v, k);
        assert !KeyInFlightByMessage(c, v, msg, k);
      } else {
        if msg in v.network.sentMsgs {
          if KeyInFlightByMessage(c, v, msg, k) {
            var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
            var actor, msgOps := dsStep.actor, dsStep.msgOps;
            // triggers
            assert KeyInFlightByMessage(c, v, msgOps.recv.value, k);
            assert KeyInFlight(c, v, k);
          }
        }
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
  forall idx1, idx2, k: Key | 
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

lemma AtMostOneHostHasLiveKey(c: Constants, v: Variables, v': Variables, k: Key, idx: HostId, other: HostId)
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