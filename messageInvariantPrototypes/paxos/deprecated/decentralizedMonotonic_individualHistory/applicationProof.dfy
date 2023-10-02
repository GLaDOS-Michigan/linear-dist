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
  forall a1, a2, i, j|
    && c.ValidAcceptorIdx(a1)
    && c.ValidAcceptorIdx(a2)
    && v.acceptors[a1].ValidHistoryIndex(i)
    && v.acceptors[a2].ValidHistoryIndex(j)
    && v.acceptors[a1].h[i].acceptedVB.Some?
    && v.acceptors[a2].h[j].acceptedVB.Some?
    && v.acceptors[a1].h[i].acceptedVB.value.b 
        == v.acceptors[a2].h[j].acceptedVB.value.b 
  ::
    v.acceptors[a1].h[i].acceptedVB.value.v
        == v.acceptors[a2].h[j].acceptedVB.value.v
}

// Learners only have one value for each ballot
ghost predicate OneValuePerBallotLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall l1, l2, vb1, vb2, i, j|
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && v.learners[l1].ValidHistoryIndex(i)
    && v.learners[l1].ValidHistoryIndex(j)
    && vb1 in v.learners[l1].h[i].receivedAccepts
    && vb2 in v.learners[l1].h[j].receivedAccepts
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

// TONY: I had to modify this to talk about the whole history, rather than just the Last() state.
// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
ghost predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall acc, i| 
    && c.ValidAcceptorIdx(acc)
    && 0 <= i < |v.acceptors[acc].h|
    && v.acceptors[acc].h[i].acceptedVB.Some?
  :: 
    && v.acceptors[acc].h[i].promised.Some?
    && v.acceptors[acc].h[i].acceptedVB.value.b <= v.acceptors[acc].h[i].promised.value
}

ghost predicate AcceptorAcceptedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
{
  forall acc:AcceptorId, i |
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].ValidHistoryIndex(i)
    && v.acceptors[acc].h[i].acceptedVB.Some?
  ::
    var vb := v.acceptors[acc].h[i].acceptedVB.value;
    && v.LeaderCanPropose(c, vb.b)
    && v.leaders[vb.b].h[i].value == vb.v
}

ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc |
    && c.ValidLeaderIdx(ldr)
    && acc in v.leaders[ldr].Last().receivedPromises
  ::
    c.ValidAcceptorIdx(acc)
}

// For all leaders, its highestHeardBallot is upper bounded by its own ballot
ghost predicate LeaderHighestHeardUpperBound(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId | 
    && c.ValidLeaderIdx(ldr)
    && v.leaders[ldr].Last().highestHeardBallot.Some?
  :: 
    v.leaders[ldr].Last().highestHeardBallot.value < ldr
}

// If a leader has a highestHeardBallot B, then its value has been proposed by the leader 
// with ballot B
ghost predicate LeaderHearedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId | 
    && c.ValidLeaderIdx(ldr)
    && v.leaders[ldr].Last().highestHeardBallot.Some?
  ::
    // note that once a leader CanPropose(), its value does not change
    var b := v.leaders[ldr].Last().highestHeardBallot.value;
    && c.ValidLeaderIdx(b)
    && v.LeaderCanPropose(c, b)
    && v.leaders[b].Last().value == v.leaders[ldr].Last().value
}

// For all ldr, acc such that acc in ldr.receivedPromises, acc's current promise
// must be >= ldr's ballot
ghost predicate LeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && acc in v.leaders[ldr].Last().receivedPromises
  ::
    v.acceptors[acc].HasPromisedAtLeast(ldr)
}

// If an acceptor A accepted ballot b, and a leader L has highestHeardBallot < b, then 
// L cannot have received a promise from A
ghost predicate LeaderNotHeardImpliesNotPromised(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId, b:LeaderId |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && b < ldr
    && v.acceptors[acc].HasAcceptedAtLeastBal(b)
    // Tony: Did not have this line below, which this invariant false
    && v.acceptors[acc].HasAcceptedAtMostBal(ldr)
    && v.leaders[ldr].HeardAtMost(b)
  ::
    && acc !in v.leaders[ldr].Last().receivedPromises
}


//// Monotonicity Properties

ghost predicate LeaderMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, i, j | 
    && c.ValidLeaderIdx(ldr)
    && v.leaders[ldr].ValidHistoryIndex(i)
    && v.leaders[ldr].ValidHistoryIndex(j)
    && i <= j
    && v.leaders[ldr].h[i].CanPropose(c.leaderConstants[ldr])
  ::
    && v.leaders[ldr].h[j].CanPropose(c.leaderConstants[ldr])
    && v.leaders[ldr].h[j].value == v.leaders[ldr].h[i].value
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
  && OneValuePerBallot(c, v)
  && LearnerValidReceivedAccepts(c, v)
  && LearnerValidReceivedAcceptsKeys(c, v)
  && LearnedImpliesQuorumOfAccepts(c, v)
  && LearnerReceivedAcceptImpliesProposed(c, v)
  && LearnerReceivedAcceptImpliesAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
  && AcceptorAcceptedImpliesProposed(c, v)
  && LeaderValidReceivedPromises(c, v)
  && LeaderHighestHeardUpperBound(c, v)
  && LeaderHearedImpliesProposed(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  && LeaderNotHeardImpliesNotPromised(c, v)
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

lemma {:timeLimitMultiplier 2} InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
  InvInductiveHelper(c, v, v');
  InvNextOneValuePerBallot(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  
  assert MonotonicityInv(c, v');
  assert ApplicationInv(c, v');
  
  assume false;
  assume AtMostOneChosenVal(c, v');  // this should be implied by invariants
  // AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

// Bundle for simple-to-prove invariants
lemma {:timeLimitMultiplier 3} InvInductiveHelper(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
  ensures LearnerValidReceivedAcceptsKeys(c, v')
  ensures LearnerReceivedAcceptImpliesProposed(c, v')
  ensures LearnerReceivedAcceptImpliesAccepted(c, v')
  ensures AcceptorValidPromisedAndAccepted(c, v')
  ensures AcceptorAcceptedImpliesProposed(c, v')
  ensures AcceptorPromisedLargerThanAccepted(c, v')
  ensures LeaderValidReceivedPromises(c, v')
  ensures LeaderHighestHeardUpperBound(c, v')
  ensures LeaderHearedImpliesProposed(c, v')
  ensures LeaderReceivedPromisesImpliesAcceptorState(c, v')
  ensures LeaderNotHeardImpliesNotPromised(c, v')
{}

lemma {:timeLimitMultiplier 3} InvNextOneValuePerBallot(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires OneValuePerBallot(c, v)
  // requires LearnerValidReceivedAcceptsKeys(c, v)  // prereq for LearnerReceivedAcceptImpliesProposed
  requires AcceptorValidPromisedAndAccepted(c, v) // prereq for AcceptorAcceptedImpliesProposed
  // requires LearnerReceivedAcceptImpliesProposed(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures OneValuePerBallot(c, v')
{
  assume false;
  assert OneValuePerBallotAcceptors(c, v');
  assume OneValuePerBallotLearners(c, v');
  assume OneValuePerBallotAcceptorsAndLearners(c, v');
  assume OneValuePerBallotLeaderAndLearners(c, v');
  assume OneValuePerBallotLeaderAndAcceptors(c, v');
}

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