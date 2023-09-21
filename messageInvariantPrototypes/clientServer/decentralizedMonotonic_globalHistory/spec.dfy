include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  // All responses received by clients are for valid requests
  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall cidx:nat | c.ValidClientIdx(cidx)
    :: SafetySingleClient(v.Last().hosts[cidx].client)
  }

  ghost predicate SafetySingleClient(v: ClientHost.Variables) {
    v.responses <= v.requests 
  }
}
