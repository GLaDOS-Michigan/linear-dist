// User level proofs of application invariants

include "spec.dfy"

module ConventionalToylockProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  predicate MsgInFlight(c: Constants, v: Variables, msg: Message) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && c.ValidIdx(msg.dst) 
    && msg.epoch > v.hosts[msg.dst].myEpoch
  }

  predicate AtMostOneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall m1, m2 | 
      && m1 in v.network.sentMsgs && m2 in v.network.sentMsgs 
      && MsgInFlight(c, v, m1) && MsgInFlight(c, v, m2)
    ::
      m1 == m2
  }

  predicate NoneHasLock(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx | c.ValidIdx(idx) :: !HoldsLock(c, v, idx)
  }
  

  predicate HasLockImpliesNoneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (!NoneHasLock(c, v))
    ==>
    (forall msg | msg in v.network.sentMsgs :: !MsgInFlight(c, v, msg))
  }

  
  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && AtMostOneInFlight(c, v)
    && HasLockImpliesNoneInFlight(c, v)
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
    assert AtMostOneInFlight(c, v');
    assert HasLockImpliesNoneInFlight(c, v');
    assert Safety(c, v');
  }
}
