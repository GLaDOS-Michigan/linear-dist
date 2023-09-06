include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem

  // All Learn messages must be of the same value
  ghost predicate Agreement(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall m1, m2 | 
    && m1 in v.network.sentMsgs 
    && m2 in v.network.sentMsgs 
    && m1.Learn?
    && m2.Learn?
  :: 
    m1.val == m2.val
  }

  // Note that I am skipping Validity proof: All learned values are ones that were
  // proposed by a leader
}
