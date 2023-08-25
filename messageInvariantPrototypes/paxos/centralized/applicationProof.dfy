include "spec.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations

// Learner's receivedAccepts contain valid acceptor ids 
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, e:AcceptorId |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].receivedAccepts
    && e in v.learners[lnr].receivedAccepts[vb]
  ::
    c.ValidAcceptorIdx(e)
}

// Learner's learned value must be backed by a quorum of accepts
ghost predicate LearnedImpliesQuorumOfAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, val:Value |
    && c.ValidLearnerIdx(lnr)
    && v.learners[lnr].HasLearnedValue(val)
  ::
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v, vb, lnr)
}


// TODO: Not sure if needed
// Each entry in a learner's receivedAccepts implies that an acceptor accepted it
// ghost predicate LearnerReceivedAcceptImpliesAcceptorAccepted(c: Constants, v: Variables)
//   requires v.WF(c)
// {
//   forall lnr:LearnerId, vb:ValBal, acc:AcceptorId |
//     && c.ValidLearnerIdx(lnr)
//     && c.ValidAcceptorIdx(acc)
//     && vb in v.learners[lnr].receivedAccepts
//     && acc in v.learners[lnr].receivedAccepts[vb]
//   ::
//     v.acceptors[acc].HasAcceptedAtLeast(vb.b) 
// }

// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
ghost predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall acc | 
    && c.ValidAcceptorIdx(acc) 
    && v.acceptors[acc].acceptedVB.Some?
  :: 
    && v.acceptors[acc].promised.Some?
    && v.acceptors[acc].acceptedVB.value.b <= v.acceptors[acc].promised.value
}

// For all ldr, acc such that acc in ldr.receivedPromises, acc's current promise
// must be >= ldr's ballot
ghost predicate LeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && acc in v.leaders[ldr].receivedPromises
  ::
    v.acceptors[acc].HasPromisedAtLeast(ldr)
}

// TODO: From prior experience, this is the ultimate invariant
// If vb is chosen, then for all leaders that can propose, they must have value == vb.v
ghost predicate ChosenValImpliesLeadersProposeOnlyVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && vb.b < ldrBal
    && v.leaders[ldrBal].CanPropose(c.leaderConstants[ldrBal])
  ::
    v.leaders[ldrBal].value == vb.v
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LearnerValidReceivedAccepts(c, v)
  && LearnedImpliesQuorumOfAcceptors(c, v)
  // && LearnerReceivedAcceptImpliesAcceptorAccepted(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  && ChosenValImpliesLeadersProposeOnlyVal(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ApplicationInv(c, v)
  && Agreement(c, v)
}


/***************************************************************************************
*                                Top-level Obligations                                 *
***************************************************************************************/


lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Agreement(c, v)
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
  InvNextLearnedImpliesQuorumOfAcceptors(c, v, v');
  InvNextImpliesChosenValImpliesLeadersProposeOnlyVal(c, v, v');
  assert ApplicationInv(c, v');

  // TODO
  assume AtMostOneChosenVal(c, v');  // this should be implied by invariants
  AtMostOneChosenImpliesSafety(c, v');
  assert Agreement(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextLearnedImpliesQuorumOfAcceptors(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAcceptors(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAcceptors(c, v')
{
  forall lnr:LearnerId, val:Value |
    c.ValidLearnerIdx(lnr) && v'.learners[lnr].HasLearnedValue(val)
  ensures
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v, vb, lnr)
  {
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.P2bStep? {
      if sysStep.learner == lnr {
        // trigger
        assert v.learners[lnr].HasLearnedValue(val);
      }
    }
  }
}

lemma InvNextImpliesChosenValImpliesLeadersProposeOnlyVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ChosenValImpliesLeadersProposeOnlyVal(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P1bStep? {

    // TODO
    assume false;
    assert ChosenValImpliesLeadersProposeOnlyVal(c, v');
  } else if sysStep.P2aStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P2bStep? {

    // TODO
    assume false;
    assert ChosenValImpliesLeadersProposeOnlyVal(c, v');
  } else if sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  }
}


/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f+1
  && (forall id | id in quorum :: c.ValidAcceptorIdx(id))
}

// A learner holds an accept quorum for vb
ghost predicate Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  exists lnr:LearnerId :: ChosenAtLearner(c, v, vb, lnr)
}

// Learner lnr witnessed a vb being chosen
ghost predicate ChosenAtLearner(c: Constants, v: Variables, vb: ValBal, lnr:LearnerId) 
  requires v.WF(c)
{
  && c.ValidLearnerIdx(lnr)
  && vb in v.learners[lnr].receivedAccepts
  && IsAcceptorQuorum(c, v.learners[lnr].receivedAccepts[vb])
}

// At most one value can become Chosen
ghost predicate AtMostOneChosenVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
  :: vb1.v == vb2.v
}

//// Helper Lemmas ////

// A value being learned implies it was chosen at some ballot, and skolemize this ballot
lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires v.learners[lnr].HasLearnedValue(val)
  requires LearnedImpliesQuorumOfAcceptors(c, v)
  ensures vb.v == val
  ensures Chosen(c, v, vb)
{
  // Witness, given by LearnedImpliesQuorumOfAcceptors
  var bal :| ChosenAtLearner(c, v, VB(val, bal), lnr);
  return VB(val, bal);
}

// If only one value can be chosen, then Agreement must be satisfied
lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneChosenVal(c, v)
  requires LearnedImpliesQuorumOfAcceptors(c, v)
  ensures Agreement(c, v)
{
  // Proof by contradiction
  if !Agreement(c, v) {
    var l1, l2 :| 
        && c.ValidLearnerIdx(l1)
        && c.ValidLearnerIdx(l2)
        && v.learners[l1].learned.Some?
        && v.learners[l2].learned.Some?
        && v.learners[l1].learned != v.learners[l2].learned
    ;
    var vb1 := LearnedImpliesChosen(c, v, l1, v.learners[l1].learned.value);
    var vb2 := LearnedImpliesChosen(c, v, l2, v.learners[l2].learned.value);
    assert false;
  }
}

// Lemma: The only system step in which a new vb can be chosen is a P2bStep 
lemma NewChosenOnlyInP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v, v', sysStep)
  requires !sysStep.P2bStep?
  ensures forall vb | Chosen(c, v', vb) :: Chosen(c, v, vb)
{
  forall vb | Chosen(c, v', vb)
  ensures Chosen(c, v, vb)
  {
    var lnr:LearnerId :| ChosenAtLearner(c, v', vb, lnr);   // witness
    assert ChosenAtLearner(c, v, vb, lnr);                  // trigger
  }
}

} // end module PaxosProof