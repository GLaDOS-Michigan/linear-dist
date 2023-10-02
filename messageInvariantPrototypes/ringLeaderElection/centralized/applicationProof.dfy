include "spec.dfy"

module RingLeaderElectionProof {
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations
  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/


// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  ChordDominates(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ApplicationInv(c, v)
  && Safety(c, v)
}

ghost predicate Between(start: nat, node: nat, end: nat) 
{
  if start < end then
    start < node < end else
    node < end || start < node
}

function Distance(n: nat, start: nat, end: nat) : nat
  requires 0 <= start < n
  requires 0 <= end < n
{
  if start <= end then end - start 
  else n - start + end
}

ghost predicate ChordDominates(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall src:nat, dst:nat, mid:nat | 
      && c.ValidIdx(src)
      && c.ValidIdx(dst)
      && c.ValidIdx(mid)
      && v.hosts[dst].highestHeard == c.hostConstants[src].hostId
      && Between(src, mid, dst)
    :: 
      c.hostConstants[mid].hostId < c.hostConstants[src].hostId
}


/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

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
  ChordDominatesInductive(c, v, v');
  ChordDominatesImpliesSafety(c, v');
}

lemma ChordDominatesImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires ChordDominates(c, v)
  ensures Safety(c, v)
{}

lemma ChordDominatesInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ChordDominates(c, v')
{}

}  // end module RingLeaderElectionProof

