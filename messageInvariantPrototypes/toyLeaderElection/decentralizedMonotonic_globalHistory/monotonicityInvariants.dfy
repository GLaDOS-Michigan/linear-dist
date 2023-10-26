include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

/***************************************************************************************
*                               Monotonicity Invariants                                *
***************************************************************************************/

ghost predicate HostNomineeMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i, j, idx |
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidHostId(idx)
    && i <= j
  ::
    v.History(j).hosts[idx].nominee.SatisfiesMonotonic(v.History(i).hosts[idx].nominee)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && HostNomineeMonotonic(c, v)
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

