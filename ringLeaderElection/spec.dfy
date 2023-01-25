include "protocol.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem


  predicate IsLeader(c: Constants, v: Variables, idx: int)
    requires c.WF()
    requires v.WF(c)
    requires c.ValidIdx(idx)
  {
    v.hosts[idx].highest_heard == c.host_constants[idx].hostId
  }

  predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall idx1, idx2 | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && IsLeader(c, v, idx1)
    && IsLeader(c, v, idx2)
    :: idx1 == idx2
  }

  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/
}
