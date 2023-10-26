include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

/***************************************************************************************
*                               Monotonicity Invariants                                *
***************************************************************************************/

ghost predicate LeaderCanProposeMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, ldr |
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && c.ValidLeaderIdx(ldr)
    && v.History(i).LeaderCanPropose(c, ldr)
  :: 
    && v.History(j).LeaderCanPropose(c, ldr)
    && v.History(j).leaders[ldr].value == v.History(i).leaders[ldr].value
}

ghost predicate LeaderHighestHeardMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, ldr |
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && c.ValidLeaderIdx(ldr)
  :: 
    v.History(j).leaders[ldr].highestHeardBallot.SatisfiesMonotonic(v.History(i).leaders[ldr].highestHeardBallot)
}

ghost predicate AcceptorAcceptedMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, acc | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidAcceptorIdx(acc)
    && i <= j
  ::
    v.History(j).acceptors[acc].acceptedVB.SatisfiesMonotonic(v.History(i).acceptors[acc].acceptedVB)
}

ghost predicate AcceptorPromisedMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, acc | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidAcceptorIdx(acc)
    && i <= j
  ::
    v.History(j).acceptors[acc].promised.SatisfiesMonotonic(v.History(i).acceptors[acc].promised)
}

ghost predicate LearnerReceivedAcceptsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, lnr | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidLearnerIdx(lnr)
    && i <= j
  ::
    v.History(j).learners[lnr].receivedAccepts.SatisfiesMonotonic(v.History(i).learners[lnr].receivedAccepts)
}


ghost predicate MonotonicityInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && LeaderHighestHeardMonotonic(c, v)
  && LeaderCanProposeMonotonic(c, v)
  && AcceptorAcceptedMonotonic(c, v)
  && AcceptorPromisedMonotonic(c, v)
  && LearnerReceivedAcceptsMonotonic(c, v)
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
  assume false;
  VariableNextProperties(c, v, v');
}

} // end module MonotonicityInvariants

