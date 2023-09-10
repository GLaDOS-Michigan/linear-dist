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

ghost predicate LearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires LearnerValidReceivedAcceptsKeys(c, v)
{
  forall lnr:LearnerId, vb:ValBal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.history[i].learners[lnr].receivedAccepts
  ::
    && v.history[i].LeaderCanPropose(c, vb.b)
    && v.history[i].leaders[vb.b].value == vb.v
}



// Each entry in a learner's receivedAccepts implies that an acceptor accepted it
ghost predicate LearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, acc:AcceptorId, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && c.ValidAcceptorIdx(acc)
    && vb in v.history[i].learners[lnr].receivedAccepts
    && acc in v.history[i].learners[lnr].receivedAccepts[vb]
  ::
    v.history[i].acceptors[acc].HasAcceptedAtLeastBal(vb.b) 
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

// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
ghost predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall acc, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(acc) 
    && v.history[i].acceptors[acc].acceptedVB.Some?
  :: 
    && var vi := v.history[i];
    && vi.acceptors[acc].promised.Some?
    && vi.acceptors[acc].acceptedVB.value.b <= vi.acceptors[acc].promised.value
}

ghost predicate AcceptorAcceptedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
{
  forall acc:AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(acc)
    && v.history[i].acceptors[acc].acceptedVB.Some?
  ::
    var vb := v.history[i].acceptors[acc].acceptedVB.value;
    && v.history[i].LeaderCanPropose(c, vb.b)
    && v.history[i].leaders[vb.b].value == vb.v
}

ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && acc in v.history[i].leaders[ldr].receivedPromises
  ::
    c.ValidAcceptorIdx(acc)
}

// For all leaders, its highestHeardBallot is upper bounded by its own ballot
ghost predicate LeaderHighestHeardUpperBound(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v.history[i].leaders[ldr].highestHeardBallot.Some?
  :: 
    v.history[i].leaders[ldr].highestHeardBallot.value < ldr
}

// If a leader has a highestHeardBallot B, then its value has been proposed by the leader 
// with ballot B
ghost predicate LeaderHearedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v.history[i].leaders[ldr].highestHeardBallot.Some?
  ::
    // note that once a leader CanPropose(), its value does not change
    && var vi := v.history[i];
    var b := vi.leaders[ldr].highestHeardBallot.value;
    && c.ValidLeaderIdx(b)
    && vi.LeaderCanPropose(c, b)
    && vi.leaders[b].value == vi.leaders[ldr].value
}

// For all ldr, acc such that acc in ldr.receivedPromises, acc's current promise
// must be >= ldr's ballot
ghost predicate LeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && acc in v.history[i].leaders[ldr].receivedPromises
  ::
    v.history[i].acceptors[acc].HasPromisedAtLeast(ldr)
}

// If an acceptor A accepted ballot b, and a leader L has highestHeardBallot < b, then 
// L cannot have received a promise from A
ghost predicate LeaderNotHeardImpliesNotPromised(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId, b:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && b < ldr
    && v.history[i].acceptors[acc].HasAcceptedAtLeastBal(b)
    // Tony: Did not have this line below, which this invariant false
    && v.history[i].acceptors[acc].HasAcceptedAtMostBal(ldr)
    && v.history[i].leaders[ldr].HeardAtMost(b)
  ::
    && acc !in v.history[i].leaders[ldr].receivedPromises
}

// For any leader L, if an acceptor A is in L.promises, then A cannot have accepted any
// ballot b such that L.highestHeard < b < L
ghost predicate LeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, lnr, vb:ValBal, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && c.ValidLearnerIdx(lnr)
    && vb in v.history[i].learners[lnr].receivedAccepts
    && vb.b < ldr
    && v.history[i].leaders[ldr].HeardAtMost(vb.b)
    && acc in v.history[i].leaders[ldr].receivedPromises
  ::
    acc !in v.history[i].learners[lnr].receivedAccepts[vb]
}

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, acc:AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && Chosen(c, v, vb)
    && c.ValidAcceptorIdx(acc)
    && v.history[i].acceptors[acc].acceptedVB.Some?
    && v.history[i].acceptors[acc].acceptedVB.value.b >= vb.b
  ::
     v.history[i].acceptors[acc].acceptedVB.value.v == vb.v
}

// If vb is chosen, then for all leaders > vb.b and ready to propose, they must have highest 
// heard >= b
ghost predicate ChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && vb.b < ldrBal
    && v.history[i].LeaderCanPropose(c, ldrBal)
  ::
    v.history[i].leaders[ldrBal].HeardAtLeast(vb.b)
}

// If vb is chosen, then for all leaders has a highest heard >= vb.b, the value must be vb.v
ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && v.history[i].leaders[ldrBal].highestHeardBallot.Some?
    && v.history[i].leaders[ldrBal].highestHeardBallot.value >= vb.b
  ::
    v.history[i].leaders[ldrBal].value == vb.v
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
  && LearnerReceivedAcceptImpliesAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
  && AcceptorAcceptedImpliesProposed(c, v)
  && LeaderValidReceivedPromises(c, v)
  && LeaderHighestHeardUpperBound(c, v)
  && LeaderHearedImpliesProposed(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  && LeaderNotHeardImpliesNotPromised(c, v)
  && LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
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

lemma {:timeLimitMultiplier 4} InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  InvNextOneValuePerBallot(c, v, v');
  InvInductiveHelper1(c, v, v');
  InvInductiveHelper2(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  assert LearnedImpliesQuorumOfAccepts(c, v');
  InvNextLearnerReceivedAcceptImpliesAccepted(c, v, v');
  InvNextAcceptorPromisedLargerThanAccepted(c, v, v');
  InvNextLeaderNotHeardImpliesNotPromised(c, v, v');
  InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');

  
  assume ChosenValImpliesAcceptorOnlyAcceptsVal(c, v');
  assume ChosenImpliesProposingLeaderHearsChosenBallot(c, v');
  assume ChosenValImpliesLeaderOnlyHearsVal(c, v');


  assert ApplicationInv(c, v');
  assert AtMostOneChosenVal(c, v');  // this should be implied by invariants
  AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

// Bundle for simple-to-prove invariants that needs no dafny proof
ghost predicate HelperBundle1(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LearnerValidReceivedAccepts(c, v)
  && LearnerValidReceivedAcceptsKeys(c, v)
  && LearnerReceivedAcceptImpliesProposed(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorAcceptedImpliesProposed(c, v)
}

lemma InvInductiveHelper1(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ApplicationInv(c, v)
  requires Next(c, v, v')
  ensures HelperBundle1(c, v')
{
  assert LearnerValidReceivedAccepts(c, v');
  assert LearnerValidReceivedAcceptsKeys(c, v');
  assert LearnerReceivedAcceptImpliesProposed(c, v');
  assert AcceptorValidPromisedAndAccepted(c, v');
  assert AcceptorAcceptedImpliesProposed(c, v');
}

// Bundle for simple-to-prove invariants that needs no dafny proof
ghost predicate HelperBundle2(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderValidReceivedPromises(c, v)
  && LeaderHighestHeardUpperBound(c, v)
  && LeaderHearedImpliesProposed(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
}

// Bundle for simple-to-prove invariants that needs no dafny proof, as bundle1 is overloaded
lemma InvInductiveHelper2(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires HelperBundle2(c, v)
  requires AcceptorPromisedLargerThanAccepted(c, v)
  requires Next(c, v, v')
  ensures HelperBundle2(c, v')
{
  assert LeaderValidReceivedPromises(c, v');
  assert LeaderHighestHeardUpperBound(c, v');
  assert LeaderHearedImpliesProposed(c, v');
  assert LeaderReceivedPromisesImpliesAcceptorState(c, v');
}

lemma {:timeLimitMultiplier 2} InvNextOneValuePerBallot(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires OneValuePerBallot(c, v)
  requires LearnerValidReceivedAcceptsKeys(c, v)  // prereq for LearnerReceivedAcceptImpliesProposed
  requires AcceptorValidPromisedAndAccepted(c, v) // prereq for AcceptorAcceptedImpliesProposed
  requires LearnerReceivedAcceptImpliesProposed(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures OneValuePerBallot(c, v')
{}

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

lemma InvNextLearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnerReceivedAcceptImpliesAccepted(c, v')
{
  forall lnr:LearnerId, vb:ValBal, acc:AcceptorId, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && c.ValidAcceptorIdx(acc)
    && vb in v'.history[i].learners[lnr].receivedAccepts
    && acc in v'.history[i].learners[lnr].receivedAccepts[vb]
  ensures
    v'.history[i].acceptors[acc].HasAcceptedAtLeastBal(vb.b) 
  {
    // Tickle the triggers
  }
}

lemma InvNextAcceptorPromisedLargerThanAccepted(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c) && v'.WF(c)
  requires AcceptorPromisedLargerThanAccepted(c, v)
  requires Next(c, v, v')
  ensures AcceptorPromisedLargerThanAccepted(c, v')
{
  // This needs its own lemma to avoid timeout
}

lemma InvNextLeaderNotHeardImpliesNotPromised(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires LeaderNotHeardImpliesNotPromised(c, v)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires Next(c, v, v')
  ensures LeaderNotHeardImpliesNotPromised(c, v')
{
  forall ldr:LeaderId, acc:AcceptorId, b:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && b < ldr
    && v'.history[i].acceptors[acc].HasAcceptedAtLeastBal(b)
    // Tony: Did not have this line below, which this invariant false
    && v'.history[i].acceptors[acc].HasAcceptedAtMostBal(ldr)
    && v'.history[i].leaders[ldr].HeardAtMost(b)
  ensures
    && acc !in v'.history[i].leaders[ldr].receivedPromises
  {
    // Tickle the triggers
  }
}

lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{
  // This needs its own lemma to avoid timeout
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

// A value being learned implies it was chosen at some ballot, and skolemize this ballot
lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires v.Last().learners[lnr].HasLearnedValue(val)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures vb.v == val
  ensures Chosen(c, v, vb)
{
  // Witness, given by LearnedImpliesQuorumOfAccepts
  var bal :| ChosenAtLearner(c, v.Last(), VB(val, bal), lnr);
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
        && v.Last().learners[l1].learned.Some?
        && v.Last().learners[l2].learned.Some?
        && v.Last().learners[l1].learned != v.Last().learners[l2].learned
    ;
    var vb1 := LearnedImpliesChosen(c, v, l1, v.Last().learners[l1].learned.value);
    var vb2 := LearnedImpliesChosen(c, v, l2, v.Last().learners[l2].learned.value);
    assert false;
  }
}

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