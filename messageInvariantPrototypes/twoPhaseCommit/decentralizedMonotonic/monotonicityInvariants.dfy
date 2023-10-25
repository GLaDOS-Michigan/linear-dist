include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

/***************************************************************************************
*                               Monotonicity Invariants                                *
***************************************************************************************/

ghost predicate CoordinatorDecisionMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.coordinator|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).coordinator[idx].decision.SatisfiesWriteOnce(v.History(i).coordinator[idx].decision)
}

ghost predicate ParticipantDecisionMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.participants|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).participants[idx].decision.SatisfiesWriteOnce(v.History(i).participants[idx].decision)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && CoordinatorDecisionMonotonic(c, v)
  && ParticipantDecisionMonotonic(c, v)
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

