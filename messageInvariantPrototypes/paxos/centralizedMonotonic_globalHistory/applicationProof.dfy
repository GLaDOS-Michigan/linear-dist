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
    && ChosenAtHistory(c, v.history[i], vb)
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
    && ChosenAtHistory(c, v.history[i], vb)
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
    && ChosenAtHistory(c, v.history[i], vb)
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

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  InvNextOneValuePerBallot(c, v, v');
  InvInductiveHelper1(c, v, v');
  InvInductiveHelper2(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  InvNextLearnerReceivedAcceptImpliesAccepted(c, v, v');
  InvNextAcceptorPromisedLargerThanAccepted(c, v, v');
  InvNextLeaderReceivedPromisesImpliesAcceptorState(c, v, v');
  InvNextLeaderNotHeardImpliesNotPromised(c, v, v');
  InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');
  InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  assert AtMostOneChosenVal(c, v') by {
    // this should be implied by invariants
    reveal_Chosen();
    reveal_ChosenAtHistory();
  }
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
  requires HelperBundle1(c, v)
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
}

// Bundle for simple-to-prove invariants that needs no dafny proof, as bundle1 is overloaded
lemma InvInductiveHelper2(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires AcceptorPromisedLargerThanAccepted(c, v)
  requires HelperBundle2(c, v)
  requires Next(c, v, v')
  ensures HelperBundle2(c, v')
{
  assert LeaderValidReceivedPromises(c, v');
  assert LeaderHighestHeardUpperBound(c, v');
  assert LeaderHearedImpliesProposed(c, v');
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
{
  assert OneValuePerBallotAcceptors(c, v');
  assert OneValuePerBallotLearners(c, v');
  assert OneValuePerBallotAcceptorsAndLearners(c, v');
  assert OneValuePerBallotLeaderAndLearners(c, v');
  assert OneValuePerBallotLeaderAndAcceptors(c, v');
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
    var sysStep :| NextStep(c, v.Last(), v'.Last(), sysStep);
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

lemma InvNextLeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires Next(c, v, v')
  ensures LeaderReceivedPromisesImpliesAcceptorState(c, v')
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
  // This needs its own lemma to avoid timeout
}

lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires v.WF(c) && v'.WF(c)
  requires Next(c, v, v')
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{
  reveal_Chosen();
  reveal_ChosenAtHistory();
}

lemma InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ChosenValImpliesLeaderOnlyHearsVal(c, v)
  requires ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromisedAndAccepted(c, v')  // prereq for AcceptorAcceptedImpliesProposed
  
  // prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires AcceptorAcceptedImpliesProposed(c, v')
  requires OneValuePerBallot(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')

  // post-condition
  ensures ChosenValImpliesAcceptorOnlyAcceptsVal(c, v')
{
  forall vb, acc:AcceptorId, i | 
    && v'.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v'.history[i], vb)
    && c.ValidAcceptorIdx(acc)
    && v'.history[i].acceptors[acc].acceptedVB.Some?
    && v'.history[i].acceptors[acc].acceptedVB.value.b >= vb.b
  ensures
     v'.history[i].acceptors[acc].acceptedVB.value.v == vb.v
  {
    var sysStep :| NextStep(c, v.Last(), v'.Last(), sysStep);
    if sysStep.P2bStep? {
      if i == |v'.history| - 1 {
        if v'.history[i].acceptors[acc].acceptedVB.value.v != vb.v {
          var ldr := v'.Last().acceptors[acc].acceptedVB.value.b;
          reveal_Chosen();
          reveal_ChosenAtHistory();
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldr, vb);
        }
      } else {
        assert ChosenAtHistory(c, v.history[i], vb) by {
          reveal_ChosenAtHistory();
        }
      }
    } else {
      InvNextChosenValImpliesAcceptorOnlyAcceptsValHelper(c, v, v', sysStep, i, acc, vb);
    }
  }
}

lemma InvNextChosenValImpliesAcceptorOnlyAcceptsValHelper(c: Constants, v: Variables, v': Variables, 
sysStep: Step, i:int, acc: AcceptorId, vb: ValBal)
  requires v.WF(c) && v'.WF(c)
  requires ChosenValImpliesLeaderOnlyHearsVal(c, v)
  requires ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), sysStep)
  requires !sysStep.P2bStep?
  requires AcceptorValidPromisedAndAccepted(c, v')  // prereq for AcceptorAcceptedImpliesProposed
  
  // prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires AcceptorAcceptedImpliesProposed(c, v')
  requires OneValuePerBallot(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')

  requires && v'.ValidHistoryIdx(i)
            && ChosenAtHistory(c, v'.history[i], vb)
            && c.ValidAcceptorIdx(acc)
            && v'.history[i].acceptors[acc].acceptedVB.Some?
            && v'.history[i].acceptors[acc].acceptedVB.value.b >= vb.b
  ensures v'.history[i].acceptors[acc].acceptedVB.value.v == vb.v
{
  NewChosenOnlyInP2bStep(c, v, v', sysStep);
  reveal_ChosenAtHistory();
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
  forall vb, ldrBal:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v'.history[i], vb)
    && c.ValidLeaderIdx(ldrBal)
    && v'.history[i].leaders[ldrBal].highestHeardBallot.Some?
    && v'.history[i].leaders[ldrBal].highestHeardBallot.value >= vb.b
  ensures
    v'.history[i].leaders[ldrBal].value == vb.v
  {
    var sysStep :| NextStep(c, v.Last(), v'.Last(), sysStep);
    if sysStep.P2bStep? {
      if i == |v'.history| - 1 {
        if v'.history[i].leaders[ldrBal].value != vb.v {
          if vb.b < ldrBal {
            reveal_Chosen();
            reveal_ChosenAtHistory();
            LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
          }
        }
      } else {
        assert ChosenAtHistory(c, v.history[i], vb) by {
          reveal_ChosenAtHistory();
        }
      }
    } else {
      InvNextChosenValImpliesLeaderOnlyHearsValHelper(c, v, v', sysStep, i, ldrBal, vb);
    }
  }
}

lemma InvNextChosenValImpliesLeaderOnlyHearsValHelper(c: Constants, v: Variables, v': Variables,
sysStep: Step, i:int, ldrBal: LeaderId, vb: ValBal)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), sysStep)
  requires !sysStep.P2bStep?
  requires OneValuePerBallot(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
  requires  && v'.ValidHistoryIdx(i)
            && ChosenAtHistory(c, v'.history[i], vb)
            && c.ValidLeaderIdx(ldrBal)
            && v'.history[i].leaders[ldrBal].highestHeardBallot.Some?
            && v'.history[i].leaders[ldrBal].highestHeardBallot.value >= vb.b
  ensures v'.history[i].leaders[ldrBal].value == vb.v
{
  reveal_Chosen();
  reveal_ChosenAtHistory();
  NewChosenOnlyInP2bStep(c, v, v', sysStep);
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  var sysStep :| NextStep(c, v.Last(), v'.Last(), sysStep);
  if sysStep.P1aStep? || sysStep.P2aStep? || sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P1bStep? {
    InvNextChosenImpliesProposingLeaderHearsChosenBallotP1bStep(c, v, v', sysStep);
  } else if sysStep.P2bStep? {
    InvNextChosenImpliesProposingLeaderHearsChosenBallotP2bStep(c, v, v', sysStep);
  }
}

// Helper lemma for P1b branch of InvNextChosenImpliesProposingLeaderHearsChosenBallot
lemma InvNextChosenImpliesProposingLeaderHearsChosenBallotP1bStep(c: Constants, v: Variables, v': Variables, sysStep: Step)
  requires Inv(c, v)
  requires sysStep.P1bStep?
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), sysStep)
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  NewChosenOnlyInP2bStep(c, v, v', sysStep);
  forall vb, ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v'.history[i], vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr 
    && v'.history[i].LeaderCanPropose(c, ldr)
  ensures
    v'.history[i].leaders[ldr].HeardAtLeast(vb.b)
  {
    VariableNextProperties(c, v, v', sysStep);
    reveal_Chosen();
    reveal_ChosenAtHistory();
    if i == |v'.history|-1 {
      if ldr == sysStep.leader {  // if the leader in question is now taking a step
        assume false;  // TODO
      }
    }
  }
}

// Helper lemma for P2b branch of InvNextChosenImpliesProposingLeaderHearsChosenBallot
lemma InvNextChosenImpliesProposingLeaderHearsChosenBallotP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires sysStep.P2bStep?
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  requires NextStep(c, v.Last(), v'.Last(), sysStep)
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  forall vb, ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i) 
    && ChosenAtHistory(c, v'.history[i], vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr 
    && v'.history[i].LeaderCanPropose(c, ldr)
  ensures
    v'.history[i].leaders[ldr].HeardAtLeast(vb.b)
  {
    if i == |v'.history|-1 {
      var choosingAccs := SupportingAcceptorsForChosen(c, v', i, vb);
      // These properties of choosingAccs carry over to pre-state v
      assert forall a | a in choosingAccs ::
        && c.ValidAcceptorIdx(a)
        && v.Last().acceptors[a].HasAcceptedAtLeastBal(vb.b);
      // Leader is also unchanged
      assert v'.Last().leaders[ldr] == v.Last().leaders[ldr];
      assert v.Last().LeaderCanPropose(c, ldr);
      if !v.Last().leaders[ldr].HeardAtLeast(vb.b) {
        // Contradiction via quorum intersection, and LeaderHighestHeardToPromisedRangeHasNoAccepts
        var allAccs := GetAcceptorSet(c, v);
        var e := QuorumIntersection(allAccs, choosingAccs, v.Last().leaders[ldr].receivedPromises);
        assert LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v);  // trigger
        assert false;
      }
    } else {
      reveal_Chosen();
      reveal_ChosenAtHistory();
    }
  }
}

// Helper lemma for InvNextChosenValImpliesLeaderOnlyHearsVal
lemma LeaderHearsDifferentValueFromChosenImpliesFalse(c: Constants, v: Variables, ldr:LeaderId, chosen: ValBal)
  requires v.WF(c)
  requires Chosen(c, v, chosen)
  requires c.ValidLeaderIdx(ldr)
  requires v.Last().leaders[ldr].highestHeardBallot.Some?
  requires v.Last().leaders[ldr].highestHeardBallot.value >= chosen.b
  requires v.Last().leaders[ldr].value != chosen.v
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
  var ldr' := v.Last().leaders[ldr].highestHeardBallot.value;
  assert v.Last().leaders[ldr'].value == v.Last().leaders[ldr].value;
  assert chosen.b <= ldr' < ldr;
  reveal_Chosen();
  reveal_ChosenAtHistory();
  LeaderHearsDifferentValueFromChosenImpliesFalse(c, v, ldr', chosen);
}

// /***************************************************************************************
// *                            Helper Definitions and Lemmas                             *
// ***************************************************************************************/

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f+1
  && (forall id | id in quorum :: c.ValidAcceptorIdx(id))
}

// A learner holds an accept quorum for vb
ghost predicate {:opaque} Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  ChosenAtHistory(c, v.history[|v.history|-1], vb)
}

// A learner holds an accept quorum for vb
ghost predicate {:opaque} ChosenAtHistory(c: Constants, h: Hosts, vb: ValBal) 
  requires h.WF(c)
{
  exists lnr:LearnerId:: 
    && ChosenAtLearner(c, h, vb, lnr)
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


// //// Helper Lemmas ////

// A value being learned implies it was chosen at some ballot, and skolemize this ballot
lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires v.Last().learners[lnr].HasLearnedValue(val)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures vb.v == val
  ensures Chosen(c, v, vb)
{
  reveal_Chosen();
  reveal_ChosenAtHistory();
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

// Lemma: The only system step in which a new vb can be chosen is a P2bStep 
lemma NewChosenOnlyInP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step) 
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), sysStep)
  requires !sysStep.P2bStep?
  ensures forall vb | Chosen(c, v', vb) :: Chosen(c, v, vb)
  ensures forall vb | ChosenAtHistory(c, v'.history[|v'.history|-1], vb) 
      :: && ChosenAtHistory(c, v'.history[|v'.history|-2], vb)
         && ChosenAtHistory(c, v'.history[|v'.history|-2], vb)
         && ChosenAtHistory(c, v.history[|v.history|-1], vb)
        
{
  reveal_Chosen();
  reveal_ChosenAtHistory();
  forall vb | ChosenAtHistory(c, v'.Last(), vb) 
  ensures ChosenAtHistory(c, v'.history[|v'.history|-2], vb) {
    var lnr:LearnerId :| ChosenAtLearner(c, v'.Last(), vb, lnr);   // witness
    assert ChosenAtLearner(c, v.Last(), vb, lnr);                  // trigger
  }
}

// Suppose vb is chosen. Return the quorum of acceptors supporting the chosen vb
lemma SupportingAcceptorsForChosen(c: Constants, v: Variables, i:int, vb: ValBal)
returns (supportingAccs: set<AcceptorId>)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires ChosenAtHistory(c, v.history[i], vb)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  ensures |supportingAccs| >= c.f+1
  ensures forall a | a in supportingAccs :: 
    && c.ValidAcceptorIdx(a)
    && v.history[i].acceptors[a].HasAcceptedAtLeastBal(vb.b)
  ensures exists lnr :: 
    && c.ValidLearnerIdx(lnr)
    && vb in v.history[i].learners[lnr].receivedAccepts
    && supportingAccs <= v.history[i].learners[lnr].receivedAccepts[vb]
{
  reveal_ChosenAtHistory();
  var lnr: LearnerId :| ChosenAtLearner(c, v.history[i], vb, lnr);  // skolemize!
  supportingAccs := v.history[i].learners[lnr].receivedAccepts[vb];
  return supportingAccs;
}

lemma VariableNextProperties(c: Constants, v: Variables, v': Variables, sysStep: Step)
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), sysStep)
  ensures 1 < |v'.history|
  ensures v.Last() == v.history[|v'.history|-2] == v'.history[|v'.history|-2]
  ensures NextStep(c, v.Last(), v'.Last(), sysStep)
{
  assert 0 < |v.history|;
  assert 1 < |v'.history|;
}

lemma GetAcceptorSet(c: Constants, v: Variables)
returns (accSet: set<AcceptorId>)
  requires v.WF(c)
  ensures forall a :: c.ValidAcceptorIdx(a) <==> a in accSet
  ensures |accSet| == 2 * c.f + 1
{
  assert v.history[0].WF(c);  // trigger for |c.acceptorConstants| == 2 * c.f+1
  accSet := set a |  0 <= a < |c.acceptorConstants|;
  SetComprehensionSize(|c.acceptorConstants|);
}

} // end module PaxosProof