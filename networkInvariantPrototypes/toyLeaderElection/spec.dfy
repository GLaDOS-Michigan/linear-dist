include "protocol.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  // At most one leader is elected
  predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall m1, m2 | 
    && m1 in v.network.sentMsgs && m2 in v.network.sentMsgs
    && m1.Leader?
    && m2.Leader?
    :: m1.src == m2.src
  }

  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/
}
