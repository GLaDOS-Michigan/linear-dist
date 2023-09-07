include "messageInvariants.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened PaxosMessageInvariants
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

// Learner's receivedAccepts contain valid acceptor ids
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, e:AcceptorId |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].Last().receivedAccepts
    && e in v.learners[lnr].Last().receivedAccepts[vb]
  ::
    c.ValidAcceptorIdx(e)
}

// Learner's receivedAccepts contain valid leader ballots
ghost predicate LearnerValidReceivedAcceptsKeys(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].Last().receivedAccepts
  ::
    c.ValidLeaderIdx(vb.b)
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

ghost predicate LearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires LearnerValidReceivedAcceptsKeys(c, v)
{
  forall lnr:LearnerId, vb:ValBal |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].Last().receivedAccepts
  ::
    && v.LeaderCanPropose(c, vb.b)
    && v.leaders[vb.b].Last().value == vb.v
}

// Each entry in a learner's receivedAccepts implies that an acceptor accepted it
ghost predicate LearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, acc:AcceptorId |
    && c.ValidLearnerIdx(lnr)
    && c.ValidAcceptorIdx(acc)
    && vb in v.learners[lnr].Last().receivedAccepts
    && acc in v.learners[lnr].Last().receivedAccepts[vb]
  ::
    v.acceptors[acc].HasAcceptedAtLeastBal(vb.b) 
}

// Acceptor's fields all host valid leader ballots
ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v:Variables) 
  requires v.WF(c)
{
  forall acc: AcceptorId | c.ValidAcceptorIdx(acc)
  ::
    && (v.acceptors[acc].Last().pendingPrepare.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].Last().pendingPrepare.value.bal))
    && (v.acceptors[acc].Last().promised.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].Last().promised.value))
    && (v.acceptors[acc].Last().acceptedVB.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].Last().acceptedVB.value.b))
}

// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
ghost predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall acc | 
    && c.ValidAcceptorIdx(acc) 
    && v.acceptors[acc].Last().acceptedVB.Some?
  :: 
    && v.acceptors[acc].Last().promised.Some?
    && v.acceptors[acc].Last().acceptedVB.value.b <= v.acceptors[acc].Last().promised.value
}

//// Monotonicity Properties

ghost predicate LeaderMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, i | 
    && c.ValidLeaderIdx(ldr)
    && 0 <= i < |v.leaders[ldr].h|
    && v.leaders[ldr].h[i].CanPropose(c.leaderConstants[ldr])
  ::
    && v.LeaderCanPropose(c, ldr)
    && v.leaders[ldr].Last().value == v.leaders[ldr].h[i].value
}

ghost predicate AcceptorMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall acc, i | 
    && c.ValidAcceptorIdx(acc)
    && 0 <= i < |v.acceptors[acc].h|
    && v.acceptors[acc].h[i].acceptedVB.Some?
  ::
    && v.acceptors[acc].Last().acceptedVB.Some?
    && v.acceptors[acc].h[i].acceptedVB.value.b <= v.acceptors[acc].Last().acceptedVB.value.b
}

// Monotonicity Bundle
ghost predicate MonotonicityInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderMonotonic(c, v)
  && AcceptorMonotonic(c, v)
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  && MonotonicityInv(c, v)
  // && OneValuePerBallot(c, v)
  && LearnerValidReceivedAccepts(c, v)
  && LearnerValidReceivedAcceptsKeys(c, v)
  && LearnedImpliesQuorumOfAccepts(c, v)
  && LearnerReceivedAcceptImpliesProposed(c, v)
  && LearnerReceivedAcceptImpliesAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
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
  && MessageInv(c, v)
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
  MessageInvInductive(c, v, v');

  assert LearnerValidReceivedAccepts(c, v');
  assert LearnerValidReceivedAcceptsKeys(c, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  assert LearnedImpliesQuorumOfAccepts(c, v');
  assert LearnerReceivedAcceptImpliesProposed(c, v');
  assert LearnerReceivedAcceptImpliesAccepted(c, v');
  assert AcceptorValidPromisedAndAccepted(c, v');
  assert AcceptorPromisedLargerThanAccepted(c, v');

  
  assert MonotonicityInv(c, v');
  assert ApplicationInv(c, v');
  
  assume false;
  assume AtMostOneChosenVal(c, v');  // this should be implied by invariants
  // AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
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
      && ChosenAtLearner(c, v', vb, lnr)
  {
    var sysStep :| NextStep(c, v, v', sysStep);
    var actor, msgOps := sysStep.actor, sysStep.msgOps;
    if sysStep.LearnerStep? && actor == lnr {
      var step :| LearnerHost.NextStep(c.learnerConstants[lnr], v.learners[lnr], v'.learners[lnr], step, msgOps);
      if !step.LearnStep? {
        assert v.learners[lnr].HasLearnedValue(val);  // trigger
      }
    } else {
      assert v.learners[lnr].HasLearnedValue(val);    // trigger
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

// A value being learned implies it was chosen at some ballot, and skolemize this ballot
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


// Monotonic properties

} // end module PaxosProof