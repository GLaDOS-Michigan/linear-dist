include "protocol.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem


  ghost predicate HoldsLock(c: Constants, v: Variables, idx: int)
    requires c.WF()
    requires v.WF(c)
    requires c.ValidIdx(idx)
  {
    v.hosts[idx].hasLock
  }

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall idx1, idx2 | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && HoldsLock(c, v, idx1)
    && HoldsLock(c, v, idx2)
    :: idx1 == idx2
  }

  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/

  lemma SuccessorPredecessorRelation(n: int, idx: nat) 
    requires 0 < n
    requires idx < n
    ensures Predecessor(n, Successor(n, idx)) == idx
    ensures Successor(n, Predecessor(n, idx)) == idx
  {}

}
