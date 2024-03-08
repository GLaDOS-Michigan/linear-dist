include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate LeaderHostReceivedPromisesAndValueMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    0 <= idx < |c.leaders|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).leaders[idx].receivedPromisesAndValue.SatisfiesMonotonic(v.History(i).leaders[idx].receivedPromisesAndValue)
}

ghost predicate LeaderHostHighestHeardBallotMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    0 <= idx < |c.leaders|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).leaders[idx].highestHeardBallot.SatisfiesMonotonic(v.History(i).leaders[idx].highestHeardBallot)
}

ghost predicate AcceptorHostPromisedMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    0 <= idx < |c.acceptors|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).acceptors[idx].promised.SatisfiesMonotonic(v.History(i).acceptors[idx].promised)
}

ghost predicate AcceptorHostAcceptedVBMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    0 <= idx < |c.acceptors|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).acceptors[idx].acceptedVB.SatisfiesMonotonic(v.History(i).acceptors[idx].acceptedVB)
}

ghost predicate LearnerHostReceivedAcceptsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    0 <= idx < |c.learners|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).learners[idx].receivedAccepts.SatisfiesMonotonic(v.History(i).learners[idx].receivedAccepts)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && LeaderHostReceivedPromisesAndValueMonotonic(c, v)
  && LeaderHostHighestHeardBallotMonotonic(c, v)
  && AcceptorHostPromisedMonotonic(c, v)
  && AcceptorHostAcceptedVBMonotonic(c, v)
  && LearnerHostReceivedAcceptsMonotonic(c, v)
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