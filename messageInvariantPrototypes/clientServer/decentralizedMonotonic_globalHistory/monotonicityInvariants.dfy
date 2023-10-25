include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

/***************************************************************************************
*                               Monotonicity Invariants                                *
***************************************************************************************/

ghost predicate ClientRequestsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, idx:nat |
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && c.ValidClientIdx(idx) 
  :: 
    v.History(j).clients[idx].requests.SatisfiesMonotonic(v.History(i).clients[idx].requests)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ClientRequestsMonotonic(c, v)
}

// Base obligation
lemma InitImpliesMonotonicityInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MonotonicityInv(c, v)
{}

// Inductive obligation
lemma MonotonicityInvInductive(c: Constants, v: Variables, v': Variables)
  requires MonotonicityInv(c, v)
  requires Next(c, v, v')
  ensures MonotonicityInv(c, v')
{
  VariableNextProperties(c, v, v');
}

} // end module MonotonicityInvariants

