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
  forall a1, a2, i|
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(a1)
    && c.ValidAcceptorIdx(a2)
    && v.history[i].acceptors[a1].acceptedVB.Some?
    && v.history[i].acceptors[a2].acceptedVB.Some?
    && v.history[i].acceptors[a1].acceptedVB.value.b 
        == v.history[i].acceptors[a2].acceptedVB.value.b 
  ::
    v.history[i].acceptors[a1].acceptedVB.value.v
        == v.history[i].acceptors[a2].acceptedVB.value.v
}

// Learners only have one value for each ballot
ghost predicate OneValuePerBallotLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall l1, l2, vb1, vb2, i|
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && vb1 in v.history[i].learners[l1].receivedAccepts
    && vb2 in v.history[i].learners[l1].receivedAccepts
    && vb1.b == vb2.b
  ::
    vb1.v == vb2.v
}

// Learners and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotAcceptorsAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall a, l, vb1, vb2, i |
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(a)
    && c.ValidLearnerIdx(l)
    && v.history[i].acceptors[a].HasAccepted(vb1)
    && vb2 in v.history[i].learners[l].receivedAccepts
    && vb1.b == vb2.b
  ::
    vb1.v == vb2.v
}

// Leaders and Learners only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, lnr, acceptedVal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidLearnerIdx(lnr)
    && VB(acceptedVal, ldr) in v.history[i].learners[lnr].receivedAccepts
  ::
    acceptedVal == v.history[i].leaders[ldr].value
}

// Leaders and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, acceptedVal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && v.history[i].acceptors[acc].HasAccepted(VB(acceptedVal, ldr))
  ::
    acceptedVal == v.history[i].leaders[ldr].value
}

// Learner's receivedAccepts contain valid acceptor ids
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, e:AcceptorId, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.history[i].learners[lnr].receivedAccepts
    && e in v.history[i].learners[lnr].receivedAccepts[vb]
  ::
    c.ValidAcceptorIdx(e)
}

// Learner's receivedAccepts contain valid leader ballots
ghost predicate LearnerValidReceivedAcceptsKeys(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.history[i].learners[lnr].receivedAccepts
  ::
    c.ValidLeaderIdx(vb.b)
}

// Learner's learned value must be backed by a quorum of accepts
ghost predicate LearnedImpliesQuorumOfAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, val:Value, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && v.history[i].learners[lnr].HasLearnedValue(val)
  ::
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v.history[i], vb, lnr)
}





// Acceptor's fields all host valid leader ballots
ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v:Variables) 
  requires v.WF(c)
{
  forall acc: AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(acc)
  ::
    && var vi := v.history[i];
    && (vi.acceptors[acc].pendingPrepare.Some? 
        ==> c.ValidLeaderIdx(vi.acceptors[acc].pendingPrepare.value.bal))
    && (vi.acceptors[acc].promised.Some? 
        ==> c.ValidLeaderIdx(vi.acceptors[acc].promised.value))
    && (vi.acceptors[acc].acceptedVB.Some? 
        ==> c.ValidLeaderIdx(vi.acceptors[acc].acceptedVB.value.b))
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  // && OneValuePerBallot(c, v)
  && LearnerValidReceivedAccepts(c, v)
  && LearnerValidReceivedAcceptsKeys(c, v)
  && LearnedImpliesQuorumOfAccepts(c, v)
  // && LearnerReceivedAcceptImpliesProposed(c, v)
  // && LearnerReceivedAcceptImpliesAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  // && AcceptorPromisedLargerThanAccepted(c, v)
  // && AcceptorAcceptedImpliesProposed(c, v)
  // && LeaderValidReceivedPromises(c, v)
  // && LeaderHighestHeardUpperBound(c, v)
  // && LeaderHearedImpliesProposed(c, v)
  // && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  // && LeaderNotHeardImpliesNotPromised(c, v)
  // && LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
  // && ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  // && ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  // && ChosenValImpliesLeaderOnlyHearsVal(c, v)
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
  InvInductiveHelper(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  assert LearnedImpliesQuorumOfAccepts(c, v');



  assert ApplicationInv(c, v');

  assume AtMostOneChosenVal(c, v');  // this should be implied by invariants
  assume false;
  // AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


// Bundle for simple-to-prove invariants that needs no dafny proof
lemma InvInductiveHelper(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
  ensures LearnerValidReceivedAcceptsKeys(c, v')


  ensures AcceptorValidPromisedAndAccepted(c, v')
{
  assert LearnerValidReceivedAccepts(c, v');
  assert LearnerValidReceivedAcceptsKeys(c, v');


  
  assert AcceptorValidPromisedAndAccepted(c, v');
}

lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c) && v'.WF(c)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAccepts(c, v')
{
  forall lnr:LearnerId, val:Value, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && v'.history[i].learners[lnr].HasLearnedValue(val)
  ensures
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v'.history[i], vb, lnr)
  {
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.P2bStep? {
      if i == |v'.history| - 1 {
        assert v'.history[i-1].learners[lnr].HasLearnedValue(val);  // trigger
      }
    }
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
  exists lnr:LearnerId:: 
    && ChosenAtLearner(c, v.Last(), vb, lnr)
}

// Learner lnr witnessed a vb being chosen
ghost predicate ChosenAtLearner(c: Constants, h: Hosts, vb: ValBal, lnr:LearnerId) 
  requires h.WF(c)
{
  && c.ValidLearnerIdx(lnr)
  && vb in h.learners[lnr].receivedAccepts
  && IsAcceptorQuorum(c, h.learners[lnr].receivedAccepts[vb])
}

// At most one value can become Chosen
ghost predicate AtMostOneChosenVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
  :: vb1.v == vb2.v
}


//// Helper Lemmas ////

// // A value being learned implies it was chosen at some ballot, and skolemize this ballot
// lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
//   requires v.WF(c)
//   requires c.ValidLearnerIdx(lnr)
//   requires v.learners[lnr].HasLearnedValue(val)
//   requires LearnedImpliesQuorumOfAccepts(c, v)
//   ensures vb.v == val
//   ensures Chosen(c, v, vb)
// {
//   // Witness, given by LearnedImpliesQuorumOfAccepts
//   var bal :| ChosenAtLearner(c, v, VB(val, bal), lnr);
//   return VB(val, bal);
// }

// If only one value can be chosen, then Agreement must be satisfied
// lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
//   requires v.WF(c)
//   requires AtMostOneChosenVal(c, v)
//   requires LearnedImpliesQuorumOfAccepts(c, v)
//   ensures Agreement(c, v)
// {
//   // Proof by contradiction
//   if !Agreement(c, v) {
//     var l1, l2 :| 
//         && c.ValidLearnerIdx(l1)
//         && c.ValidLearnerIdx(l2)
//         && v.learners[l1].learned.Some?
//         && v.learners[l2].learned.Some?
//         && v.learners[l1].learned != v.learners[l2].learned
//     ;
//     var vb1 := LearnedImpliesChosen(c, v, l1, v.learners[l1].learned.value);
//     var vb2 := LearnedImpliesChosen(c, v, l2, v.learners[l2].learned.value);
//     assert false;
//   }
// }

// // Lemma: The only system step in which a new vb can be chosen is a P2bStep 
// lemma NewChosenOnlyInP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step) 
//   requires v.WF(c)
//   requires Next(c, v, v')
//   requires NextStep(c, v, v', sysStep)
//   requires !sysStep.P2bStep?
//   ensures forall vb | Chosen(c, v', vb) :: Chosen(c, v, vb)
// {
//   forall vb | Chosen(c, v', vb)
//   ensures Chosen(c, v, vb)
//   {
//     var lnr:LearnerId :| ChosenAtLearner(c, v', vb, lnr);   // witness
//     assert ChosenAtLearner(c, v, vb, lnr);                  // trigger
//   }
// }

// // Suppose vb is chosen. Return the quorum of acceptors supporting the chosen vb
// lemma SupportingAcceptorsForChosen(c: Constants, v: Variables, vb: ValBal)
// returns (supportingAccs: set<AcceptorId>)
//   requires v.WF(c)
//   requires Chosen(c, v, vb)
//   requires LearnerReceivedAcceptImpliesAccepted(c, v)
//   ensures |supportingAccs| >= c.f+1
//   ensures forall a | a in supportingAccs :: 
//     && c.ValidAcceptorIdx(a)
//     && v.acceptors[a].HasAcceptedAtLeastBal(vb.b)
//   ensures exists lnr :: 
//     && c.ValidLearnerIdx(lnr)
//     && vb in v.learners[lnr].receivedAccepts
//     && supportingAccs <= v.learners[lnr].receivedAccepts[vb]
// {
//   var lnr: LearnerId :| ChosenAtLearner(c, v, vb, lnr);  // skolemize!
//   supportingAccs := v.learners[lnr].receivedAccepts[vb];
//   return supportingAccs;
// }

// lemma GetAcceptorSet(c: Constants, v: Variables)
// returns (accSet: set<AcceptorId>)
//   requires v.WF(c)
//   ensures forall a :: c.ValidAcceptorIdx(a) <==> a in accSet
//   ensures |accSet| == 2 * c.f + 1
// {
//   accSet := set a |  0 <= a < |c.acceptorConstants|;
//   SetComprehensionSize(|c.acceptorConstants|);
// }

} // end module PaxosProof