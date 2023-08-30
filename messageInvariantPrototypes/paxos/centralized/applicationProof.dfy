include "spec.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations


ghost predicate OneValuePerBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  && OneValuePerBallotAcceptors(c, v)
  && OneValuePerBallotLearners(c, v)
  && OneValuePerBallotAcceptorsAndLearners(c, v)
  && OneValuePerBallotLeaderAndLearners(c, v)
  && OneValuePerBallotLeaderAndAcceptors(c, v)
}

// Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall a1, a2 |
    && c.ValidAcceptorIdx(a1)
    && c.ValidAcceptorIdx(a2)
    && v.acceptors[a1].acceptedVB.Some?
    && v.acceptors[a2].acceptedVB.Some?
    && v.acceptors[a1].acceptedVB.value.b 
        == v.acceptors[a2].acceptedVB.value.b 
  ::
    v.acceptors[a1].acceptedVB.value.v
        == v.acceptors[a2].acceptedVB.value.v
}

// Learners only have one value for each ballot
ghost predicate OneValuePerBallotLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall l1, l2, vb1, vb2 |
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && vb1 in v.learners[l1].receivedAccepts
    && vb2 in v.learners[l1].receivedAccepts
    && vb1.b == vb2.b
  ::
    vb1.v == vb2.v
}

// Learners and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotAcceptorsAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall a, l, vb1, vb2 |
    && c.ValidAcceptorIdx(a)
    && c.ValidLearnerIdx(l)
    && v.acceptors[a].acceptedVB == Some(vb1)
    && vb2 in v.learners[l].receivedAccepts
    && vb1.b == vb2.b
  ::
    vb1.v == vb2.v
}

// Leaders and Learners only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, lnr, acceptedVal |
    && c.ValidLeaderIdx(ldr)
    && c.ValidLearnerIdx(lnr)
    && v.LeaderCanPropose(c, ldr)
    && VB(acceptedVal, ldr) in v.learners[lnr].receivedAccepts
  ::
    acceptedVal == v.leaders[ldr].value
}

// Leaders and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, acceptedVal |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && v.LeaderCanPropose(c, ldr)
    && v.acceptors[acc].acceptedVB == Some(VB(acceptedVal, ldr))
  ::
    acceptedVal == v.leaders[ldr].value
}

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

// Learner's receivedAccepts contain valid leader ballots
ghost predicate LearnerValidReceivedAcceptsKeys(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].receivedAccepts
  ::
    c.ValidLeaderIdx(vb.b)
}

ghost predicate LearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires LearnerValidReceivedAcceptsKeys(c, v)
{
  forall lnr:LearnerId, vb:ValBal |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].receivedAccepts
  ::
    && v.LeaderCanPropose(c, vb.b)
    && v.leaders[vb.b].value == vb.v
}

// Learner's learned value must be backed by a quorum of accepts
ghost predicate LearnedImpliesQuorumOfAccepts(c: Constants, v: Variables)
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

// Acceptor's fields all host valid leader ballots
ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v:Variables) 
  requires v.WF(c)
{
  forall acc: AcceptorId | c.ValidAcceptorIdx(acc)
  ::
    && (v.acceptors[acc].pendingPrepare.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].pendingPrepare.value.bal))
    && (v.acceptors[acc].promised.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].promised.value))
    && (v.acceptors[acc].acceptedVB.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].acceptedVB.value.b))
}

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

ghost predicate AcceptorAcceptedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
{
  forall acc:AcceptorId, vb:ValBal |
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].acceptedVB == Some(vb)
  ::
    && v.LeaderCanPropose(c, vb.b)
    && v.leaders[vb.b].value == vb.v
}

// For all leaders, its highestHeardBallot is upper bounded by its own ballot
ghost predicate LeaderHighestHeardUpperBound(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId | 
    && c.ValidLeaderIdx(ldr)
    && v.leaders[ldr].highestHeardBallot.Some?
  :: 
    v.leaders[ldr].highestHeardBallot.value < ldr
}

// If a leader has a highestHeardBallot B, then its value has been proposed by the leader 
// with ballot B
ghost predicate LeaderHearedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId | 
    && c.ValidLeaderIdx(ldr)
    && v.leaders[ldr].highestHeardBallot.Some?
  ::
    // note that once a leader CanPropose(), its value does not change
    var b := v.leaders[ldr].highestHeardBallot.value;
    && c.ValidLeaderIdx(b)
    && v.LeaderCanPropose(c, b)
    && v.leaders[b].value == v.leaders[ldr].value
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

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, acc:AcceptorId | 
    && Chosen(c, v, vb)
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].acceptedVB.Some?
    && v.acceptors[acc].acceptedVB.value.b >= vb.b
  ::
     v.acceptors[acc].acceptedVB.value.v == vb.v
}

// If vb is chosen, then for all leaders > vb.b and ready to propose, they must have highest 
// heard >= b
ghost predicate ChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && ldrBal > vb.b
    && v.LeaderCanPropose(c, ldrBal)
  ::
    && v.leaders[ldrBal].highestHeardBallot.Some?
    && v.leaders[ldrBal].highestHeardBallot.value >= vb.b
}

// If vb is chosen, then for all leaders has a highest heard >= vb.b, the value must be vb.v
ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && v.leaders[ldrBal].highestHeardBallot.Some?
    && v.leaders[ldrBal].highestHeardBallot.value >= vb.b
  ::
    v.leaders[ldrBal].value == vb.v
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && OneValuePerBallot(c, v)
  && LearnerValidReceivedAccepts(c, v)
  && LearnerValidReceivedAcceptsKeys(c, v)
  && LearnedImpliesQuorumOfAccepts(c, v)
  && LearnerReceivedAcceptImpliesProposed(c, v)
  // && LearnerReceivedAcceptImpliesAcceptorAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
  && AcceptorAcceptedImpliesProposed(c, v)
  && LeaderHighestHeardUpperBound(c, v)
  && LeaderHearedImpliesProposed(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  && ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  && ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  && ChosenValImpliesLeaderOnlyHearsVal(c, v)
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
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');


  assert LearnerReceivedAcceptImpliesProposed(c, v');
  assert AcceptorAcceptedImpliesProposed(c, v');
  assert LeaderHearedImpliesProposed(c, v');

  InvNextOneValuePerBallot(c, v, v');

  InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');

  assert ApplicationInv(c, v');
  assert AtMostOneChosenVal(c, v');  // this should be implied by invariants
  AtMostOneChosenImpliesSafety(c, v');
  assert Agreement(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextOneValuePerBallot(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires OneValuePerBallot(c, v)
  requires LearnerValidReceivedAcceptsKeys(c, v)  // prereq for LearnerReceivedAcceptImpliesProposed
  requires AcceptorValidPromisedAndAccepted(c, v) // prereq for AcceptorAcceptedImpliesProposed
  requires LearnerReceivedAcceptImpliesProposed(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures OneValuePerBallot(c, v')
{}

lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAccepts(c, v')
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

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
    assert ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  } else if sysStep.P1bStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
    assume false;   // TODO
    assert ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  } else if sysStep.P2aStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
    assert ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  } else if sysStep.P2bStep? {
    assume false;   // TODO
    assert ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  } else if sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
    assert ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  } else {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
    assert ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  }
}

lemma InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ChosenValImpliesAcceptorOnlyAcceptsVal(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? || sysStep.P1bStep? || sysStep.P2aStep? || sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P2bStep? {
    // TODO: Something new may be chosen here
    assume false;
    assert ChosenValImpliesAcceptorOnlyAcceptsVal(c, v');
  }
}

lemma InvNextChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires OneValuePerBallot(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
  ensures ChosenValImpliesLeaderOnlyHearsVal(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? || sysStep.P1bStep? || sysStep.P2aStep? || sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else {
    // P2bStep
    if !ChosenValImpliesLeaderOnlyHearsVal(c, v') {
      var vb, ldrBal:LeaderId :|
          && Chosen(c, v', vb)
          && c.ValidLeaderIdx(ldrBal)
          && v'.leaders[ldrBal].highestHeardBallot.Some?
          && v'.leaders[ldrBal].highestHeardBallot.value >= vb.b
          // This is the contradiction
          && v'.leaders[ldrBal].value != vb.v;
      if vb.b < ldrBal {
        LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
      }
      // Otherwise, when vb.b < ldrBal, violates OneValuePerBallot(c, v')
    }
    assert ChosenValImpliesLeaderOnlyHearsVal(c, v');
  }
}

// Helper lemma for InvNextChosenValImpliesLeaderOnlyHearsVal
lemma LeaderHearsDifferentValueFromChosenImpliesFalse(c: Constants, v: Variables, ldr:LeaderId, chosen: ValBal)
  requires v.WF(c)
  requires Chosen(c, v, chosen)
  requires c.ValidLeaderIdx(ldr)
  requires v.leaders[ldr].highestHeardBallot.Some?
  requires v.leaders[ldr].highestHeardBallot.value >= chosen.b
  requires v.leaders[ldr].value != chosen.v
  requires chosen.b < ldr
  requires OneValuePerBallot(c, v)
  requires LeaderHighestHeardUpperBound(c, v)
  requires LeaderHearedImpliesProposed(c, v)
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  ensures false
{
  /* 
    Suppose leader L hears a value v' != vb.v. Then by LeaderHearedImpliesProposed, another leader L' 
    such that vb.v <= L' < L must have proposed v', 
    Then do recursion all the way down.
  */
  var ldr' := v.leaders[ldr].highestHeardBallot.value;
  assert v.leaders[ldr'].value == v.leaders[ldr].value;
  assert chosen.b <= ldr' < ldr;
  LeaderHearsDifferentValueFromChosenImpliesFalse(c, v, ldr', chosen);
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
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures vb.v == val
  ensures Chosen(c, v, vb)
{
  // Witness, given by LearnedImpliesQuorumOfAccepts
  var bal :| ChosenAtLearner(c, v, VB(val, bal), lnr);
  return VB(val, bal);
}

// If only one value can be chosen, then Agreement must be satisfied
lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneChosenVal(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
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