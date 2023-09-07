include "spec.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
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
    && v.acceptors[a1].Last().acceptedVB.Some?
    && v.acceptors[a2].Last().acceptedVB.Some?
    && v.acceptors[a1].Last().acceptedVB.value.b 
        == v.acceptors[a2].Last().acceptedVB.value.b 
  ::
    v.acceptors[a1].Last().acceptedVB.value.v
        == v.acceptors[a2].Last().acceptedVB.value.v
}

// Learners only have one value for each ballot
ghost predicate OneValuePerBallotLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall l1, l2, vb1, vb2 |
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && vb1 in v.learners[l1].Last().receivedAccepts
    && vb2 in v.learners[l1].Last().receivedAccepts
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
    && v.acceptors[a].HasAccepted(vb1)
    && vb2 in v.learners[l].Last().receivedAccepts
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
    && VB(acceptedVal, ldr) in v.learners[lnr].Last().receivedAccepts
  ::
    acceptedVal == v.leaders[ldr].Last().value
}

// Leaders and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, acceptedVal |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && v.LeaderCanPropose(c, ldr)
    && v.acceptors[acc].HasAccepted(VB(acceptedVal, ldr))
  ::
    acceptedVal == v.leaders[ldr].Last().value
}


// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && OneValuePerBallot(c, v)
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
  // InvNextOneValuePerBallot(c, v, v');
  // InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  // InvNextLeaderNotHeardImpliesNotPromised(c, v, v');
  // InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');
  // InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  // InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  // InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');
  
  assume false;
  assert AtMostOneChosenVal(c, v');  // this should be implied by invariants
  // AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/




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
  && vb in v.learners[lnr].Last().receivedAccepts
  && IsAcceptorQuorum(c, v.learners[lnr].Last().receivedAccepts[vb])
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

// // If only one value can be chosen, then Agreement must be satisfied
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
//         && v.learners[l1].HasLearnedSome()
//         && v.learners[l2].HasLearnedSome()
//         && v.learners[l1].GetLearnedValue() != v.learners[l2].GetLearnedValue()
//     ;
//     var vb1 := LearnedImpliesChosen(c, v, l1, v.learners[l1].Last().learned.value);
//     var vb2 := LearnedImpliesChosen(c, v, l2, v.learners[l2].Last().learned.value);
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
//     && vb in v.learners[lnr].Last().receivedAccepts
//     && supportingAccs <= v.learners[lnr].Last().receivedAccepts[vb]
// {
//   var lnr: LearnerId :| ChosenAtLearner(c, v, vb, lnr);  // skolemize!
//   supportingAccs := v.learners[lnr].Last().receivedAccepts[vb];
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