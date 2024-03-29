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
  forall a1, a2, i|
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(a1)
    && c.ValidAcceptorIdx(a2)
    && v.History(i).acceptors[a1].acceptedVB.Some?
    && v.History(i).acceptors[a2].acceptedVB.Some?
    && v.History(i).acceptors[a1].acceptedVB.value.b 
        == v.History(i).acceptors[a2].acceptedVB.value.b 
  ::
    v.History(i).acceptors[a1].acceptedVB.value.v
        == v.History(i).acceptors[a2].acceptedVB.value.v
}

// Learners only have one value for each ballot
ghost predicate OneValuePerBallotLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall l1, l2, vb1, vb2, i|
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && vb1 in v.History(i).learners[l1].receivedAccepts
    && vb2 in v.History(i).learners[l1].receivedAccepts
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
    && v.History(i).acceptors[a].HasAccepted(vb1)
    && vb2 in v.History(i).learners[l].receivedAccepts
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
    && VB(acceptedVal, ldr) in v.History(i).learners[lnr].receivedAccepts
  ::
    acceptedVal == v.History(i).leaders[ldr].value
}

// Leaders and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, acceptedVal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && v.History(i).acceptors[acc].HasAccepted(VB(acceptedVal, ldr))
  ::
    acceptedVal == v.History(i).leaders[ldr].value
}

// Learner's receivedAccepts contain valid acceptor ids
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, e:AcceptorId, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.History(i).learners[lnr].receivedAccepts
    && e in v.History(i).learners[lnr].receivedAccepts[vb]
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
    && vb in v.History(i).learners[lnr].receivedAccepts
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
    && v.History(i).learners[lnr].HasLearnedValue(val)
  ::
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v.History(i), vb, lnr)
}

ghost predicate LearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires LearnerValidReceivedAcceptsKeys(c, v)
{
  forall lnr:LearnerId, vb:ValBal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.History(i).learners[lnr].receivedAccepts
  ::
    && v.History(i).LeaderCanPropose(c, vb.b)
    && v.History(i).leaders[vb.b].value == vb.v
}



// Each entry in a learner's receivedAccepts implies that an acceptor accepted it
ghost predicate LearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, acc:AcceptorId, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && c.ValidAcceptorIdx(acc)
    && vb in v.History(i).learners[lnr].receivedAccepts
    && acc in v.History(i).learners[lnr].receivedAccepts[vb]
  ::
    v.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b) 
}


// Acceptor's fields all host valid leader ballots
ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v:Variables) 
  requires v.WF(c)
{
  forall acc: AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(acc)
  ::
    && var vi := v.History(i);
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
    && v.History(i).acceptors[acc].acceptedVB.Some?
  :: 
    && var vi := v.History(i);
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
    && v.History(i).acceptors[acc].acceptedVB.Some?
  ::
    var vb := v.History(i).acceptors[acc].acceptedVB.value;
    && v.History(i).LeaderCanPropose(c, vb.b)
    && v.History(i).leaders[vb.b].value == vb.v
}

ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && acc in v.History(i).leaders[ldr].receivedPromises
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
    && v.History(i).leaders[ldr].highestHeardBallot.Some?
  :: 
    v.History(i).leaders[ldr].highestHeardBallot.value < ldr
}

// If a leader has a highestHeardBallot B, then its value has been proposed by the leader 
// with ballot B
ghost predicate LeaderHearedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v.History(i).leaders[ldr].highestHeardBallot.Some?
  ::
    // note that once a leader CanPropose(), its value does not change
    && var vi := v.History(i);
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
    && acc in v.History(i).leaders[ldr].receivedPromises
  ::
    v.History(i).acceptors[acc].HasPromisedAtLeast(ldr)
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
    && v.History(i).acceptors[acc].HasAcceptedAtLeastBal(b)
    // Tony: Did not have this line below, which this invariant false
    && v.History(i).acceptors[acc].HasAcceptedAtMostBal(ldr)
    && v.History(i).leaders[ldr].HeardAtMost(b)
  ::
    && acc !in v.History(i).leaders[ldr].receivedPromises
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
    && vb in v.History(i).learners[lnr].receivedAccepts
    && vb.b < ldr
    && v.History(i).leaders[ldr].HeardAtMost(vb.b)
    && acc in v.History(i).leaders[ldr].receivedPromises
  ::
    acc !in v.History(i).learners[lnr].receivedAccepts[vb]
}

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, acc:AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v.History(i), vb)
    && c.ValidAcceptorIdx(acc)
    && v.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b)
  ::
     v.History(i).acceptors[acc].acceptedVB.value.v == vb.v
}

// If vb is chosen, then for all leaders > vb.b and ready to propose, they must have highest 
// heard >= b
ghost predicate ChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && vb.b < ldrBal
    && v.History(i).LeaderCanPropose(c, ldrBal)
  ::
    v.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
}

// If vb is chosen, then for all leaders has a highest heard >= vb.b, the value must be vb.v
ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && v.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
  ::
    v.History(i).leaders[ldrBal].value == vb.v
}

//// Monoticity properties

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
    && v.History(i).leaders[ldr].highestHeardBallot.Some?
  :: 
    && v.History(j).leaders[ldr].highestHeardBallot.Some?
    && v.History(i).leaders[ldr].highestHeardBallot.value <= v.History(j).leaders[ldr].highestHeardBallot.value
}

ghost predicate AcceptorAcceptedMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, acc | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidAcceptorIdx(acc)
    && i <= j
    && v.History(i).acceptors[acc].acceptedVB.Some?
  ::
    && v.History(j).acceptors[acc].acceptedVB.Some?
    && v.History(i).acceptors[acc].acceptedVB.value.b <= v.History(j).acceptors[acc].acceptedVB.value.b
}

ghost predicate AcceptorPromisedMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, acc | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidAcceptorIdx(acc)
    && i <= j
    && v.History(i).acceptors[acc].promised.Some?
  ::
    && v.History(j).acceptors[acc].promised.Some?
    && v.History(i).acceptors[acc].promised.value <= v.History(j).acceptors[acc].promised.value
}

ghost predicate LearnerReceivedAcceptsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j, lnr, vb | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && c.ValidLearnerIdx(lnr)
    && i <= j
    && vb in v.History(i).learners[lnr].receivedAccepts
  ::
    && 0 < |v.History(i).learners[lnr].receivedAccepts[vb]|
    && vb in v.History(j).learners[lnr].receivedAccepts
    && v.History(i).learners[lnr].receivedAccepts[vb] <= v.History(j).learners[lnr].receivedAccepts[vb]
}

// Monotonicity Bundle
ghost predicate MonotonicityInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderHighestHeardMonotonic(c, v)
  && LeaderCanProposeMonotonic(c, v)
  && AcceptorAcceptedMonotonic(c, v)
  && AcceptorPromisedMonotonic(c, v)
  && LearnerReceivedAcceptsMonotonic(c, v)
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
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
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
{
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  assert v'.WF(c);
  MessageInvInductive(c, v, v');
  MonotonicityInvInductive(c, v, v');
  InvNextOneValuePerBallot(c, v, v');
  InvNextLearnerValidReceivedAccepts(c, v, v');
  InvNextLearnerValidReceivedAcceptsKeys(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  InvNextLearnerReceivedAcceptImpliesProposed(c, v, v');
  InvNextLearnerReceivedAcceptImpliesAccepted(c, v, v');
  InvNextAcceptorValidPromisedAndAccepted(c, v, v');
  InvNextAcceptorPromisedLargerThanAccepted(c, v, v');
  InvNextAcceptorAcceptedImpliesProposed(c, v, v');
  InvNextLeaderValidReceivedPromises(c, v, v');
  InvNextLeaderHighestHeardUpperBound(c, v, v');
  InvNextLeaderHearedImpliesProposed(c, v, v');
  InvNextLeaderReceivedPromisesImpliesAcceptorState(c, v, v');
  InvNextLeaderNotHeardImpliesNotPromised(c, v, v');
  InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');

  InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');

  InvImpliesAtMostOneChosenVal(c, v');
  AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma MonotonicityInvInductive(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires MonotonicityInv(c, v)
  requires AcceptorPromisedLargerThanAccepted(c, v)
  requires Next(c, v, v')
  ensures MonotonicityInv(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma MessageContainmentPreservesNext(c: Constants, v: Variables, v': Variables, s: Variables, s': Variables)
  requires v.WF(c)
  requires s.WF(c)
  requires Next(c, v, v')
  requires v.history == s.history
  requires v'.history == s'.history
  requires v'.network.sentMsgs <= s'.network.sentMsgs
  requires s.network.sentMsgs == s'.network.sentMsgs
  ensures Next(c, s, s')
{
  var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
  assert NextStep(c, s.Last(), s'.Last(), s.network, s'.network, dsStep); // trigger
}

lemma InvNextOneValuePerBallot(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires MessageInv(c, v')
  requires MonotonicityInv(c, v')
  requires Next(c, v, v')
  ensures OneValuePerBallot(c, v')
{
  VariableNextProperties(c, v, v');
  InvNextOneValuePerBallotAcceptors(c, v, v');
  InvNextOneValuePerBallotLearners(c, v, v');
  InvNextOneValuePerBallotAcceptorsAndLearners(c, v, v');
  InvNextOneValuePerBallotLeaderAndLearners(c, v, v');
  InvNextOneValuePerBallotLeaderAndAcceptors(c, v, v');
}


lemma InvNextOneValuePerBallotAcceptors(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires MessageInv(c, v')
  requires Next(c, v, v')
  ensures OneValuePerBallotAcceptors(c, v')
{
  VariableNextProperties(c, v, v');
  forall a1, a2, i|
    && v'.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(a1)
    && c.ValidAcceptorIdx(a2)
    && v'.History(i).acceptors[a1].acceptedVB.Some?
    && v'.History(i).acceptors[a2].acceptedVB.Some?
    && v'.History(i).acceptors[a1].acceptedVB.value.b 
        == v'.History(i).acceptors[a2].acceptedVB.value.b 
  ensures
    v'.History(i).acceptors[a1].acceptedVB.value.v
        == v'.History(i).acceptors[a2].acceptedVB.value.v
  {
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      VariableNextProperties(c, v, v');
      if dsStep.AcceptorStep? {
        NotLeaderStepImpliesNoPrepareOrPropose(c,  v.Last(), v'.Last(), v.network, v'.network, dsStep);
      }
    }
  }
}

lemma InvNextOneValuePerBallotLearners(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures OneValuePerBallotLearners(c, v')
{
  VariableNextProperties(c, v, v');
  forall l1, l2, vb1, vb2, i|
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && vb1 in v'.History(i).learners[l1].receivedAccepts
    && vb2 in v'.History(i).learners[l1].receivedAccepts
    && vb1.b == vb2.b
  ensures
    vb1.v == vb2.v
  {
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      VariableNextProperties(c, v, v');
      if dsStep.LearnerStep? {
        NotAcceptorStepImpliesNoPromiseOrAccept(c,  v.Last(), v'.Last(), v.network, v'.network, dsStep);
        assert vb1.v == vb2.v;
      } else {
        assert vb1.v == vb2.v;
      }
    }
  }
}

lemma InvNextOneValuePerBallotAcceptorsAndLearners(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires MessageInv(c, v) && MessageInv(c, v')
  requires LeaderCanProposeMonotonic(c, v)
  requires LearnerReceivedAcceptsMonotonic(c, v')
  requires OneValuePerBallot(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v) // prereq for AcceptorAcceptedImpliesProposed
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures OneValuePerBallotAcceptorsAndLearners(c, v')
{
  forall a, l, vb1, vb2, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(a)
    && c.ValidLearnerIdx(l)
    && v'.History(i).acceptors[a].HasAccepted(vb1)
    && vb2 in v'.History(i).learners[l].receivedAccepts
    && vb1.b == vb2.b
  ensures
    vb1.v == vb2.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if dsStep.AcceptorStep? {
        NotLeaderStepImpliesNoPrepareOrPropose(c,  v.Last(), v'.Last(), v.network, v'.network, dsStep);
      } else if dsStep.LearnerStep? {
        NotAcceptorStepImpliesNoPromiseOrAccept(c,  v.Last(), v'.Last(), v.network, v'.network, dsStep);
        if vb1.v != vb2.v { 
          // witnesses and triggers
          var acc2 :| acc2 in v'.History(i).learners[l].receivedAccepts[vb2];
          var accMsg := Accept(vb2, acc2);
          assert IsAcceptMessage(v, accMsg);
          var j :| v.ValidHistoryIdx(j) && v.History(j).acceptors[acc2].HasAccepted(vb2);
          assert false;
        } 
      }
    }
  }
}

lemma InvNextOneValuePerBallotLeaderAndLearners(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires v'.WF(c)
  requires MessageInv(c, v')
  requires LeaderCanProposeMonotonic(c, v')
  requires Next(c, v, v')
  ensures OneValuePerBallotLeaderAndLearners(c, v')
{
  forall ldr, lnr, acceptedVal, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidLearnerIdx(lnr)
    && VB(acceptedVal, ldr) in v'.History(i).learners[lnr].receivedAccepts
  ensures
    acceptedVal == v'.History(i).leaders[ldr].value
  {
    VariableNextProperties(c, v, v');
  }
}

lemma InvNextOneValuePerBallotLeaderAndAcceptors(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires v'.WF(c)
  requires MessageInv(c, v')
  requires LeaderCanProposeMonotonic(c, v')
  requires Next(c, v, v')
  ensures OneValuePerBallotLeaderAndAcceptors(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLearnerValidReceivedAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires LearnerValidReceivedAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLearnerValidReceivedAcceptsKeys(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAcceptsKeys(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires ValidMessageSrc(c, v)  // From MessageInv
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAccepts(c, v')
{
  forall lnr:LearnerId, val:Value, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && v'.History(i).learners[lnr].HasLearnedValue(val)
  ensures
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v'.History(i), vb, lnr)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      reveal_ValidMessageSrc();
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if  && dsStep.LearnerStep?
          && actor == lnr 
      {
        var lc, l, l' := c.learnerConstants[actor], v.Last().learners[actor], v'.Last().learners[actor];
        var step :| LearnerHost.NextStep(lc, l, l', step, msgOps);
        if !step.LearnStep? {
          // trigger and witness
          assert v.History(i-1).learners[lnr].HasLearnedValue(val);
          var b: LeaderId :|
              && var vb := VB(val, b);
              && ChosenAtLearner(c, v.History(i-1), vb, lnr);
        }
      }
    } 
  }
}
 
lemma InvNextLearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidAcceptMessage(c, v)
  requires LeaderCanProposeMonotonic(c, v)
  requires LearnerValidReceivedAcceptsKeys(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires LearnerReceivedAcceptImpliesProposed(c, v)
  requires Next(c, v, v')
  requires LearnerValidReceivedAcceptsKeys(c, v')
  ensures LearnerReceivedAcceptImpliesProposed(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextAcceptorValidPromisedAndAccepted(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidPromisedAndAccepted(c, v')
{
  VariableNextProperties(c, v, v');
  reveal_ValidMessageSrc();
}

lemma InvNextLearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires MonotonicityInv(c, v) && MonotonicityInv(c, v')
  requires ValidMessageSrc(c, v)
  requires ValidAcceptMessage(c, v)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  requires Next(c, v, v')
  ensures LearnerReceivedAcceptImpliesAccepted(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextAcceptorPromisedLargerThanAccepted(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires AcceptorPromisedLargerThanAccepted(c, v)
  requires Next(c, v, v')
  ensures AcceptorPromisedLargerThanAccepted(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextAcceptorAcceptedImpliesProposed(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidProposeMesssage(c, v)
  requires LeaderCanProposeMonotonic(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromisedAndAccepted(c, v')
  ensures AcceptorAcceptedImpliesProposed(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderValidReceivedPromises(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires LeaderValidReceivedPromises(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromises(c, v')
{
  VariableNextProperties(c, v, v');
  reveal_ValidMessageSrc();
}

lemma InvNextLeaderHighestHeardUpperBound(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardUpperBound(c, v')
{
  forall ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v'.History(i).leaders[ldr].highestHeardBallot.Some?
  ensures
    v'.History(i).leaders[ldr].highestHeardBallot.value < ldr
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if dsStep.LeaderStep? {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        var lc, l, l' := c.leaderConstants[actor], v.Last().leaders[actor], v'.Last().leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if step.ReceiveStep? {
          assert IsPromiseMessage(v, msgOps.recv.value);  // trigger
        } 
      }
    }
  }
}

lemma InvNextLeaderHearedImpliesProposed(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHearedImpliesProposed(c, v')
{  
  forall ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v'.History(i).leaders[ldr].highestHeardBallot.Some?
  ensures
    // note that once a leader CanPropose(), its value does not change
    && var vi' := v'.History(i);
    var b := vi'.leaders[ldr].highestHeardBallot.value;
    && c.ValidLeaderIdx(b)
    && vi'.LeaderCanPropose(c, b)
    && vi'.leaders[b].value == vi'.leaders[ldr].value
  { 
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if dsStep.LeaderStep? {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        var lc, l, l' := c.leaderConstants[actor], v.Last().leaders[actor], v'.Last().leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if step.ReceiveStep? {
          assert IsPromiseMessage(v, msgOps.recv.value);  // trigger
        } 
      }
    }
  }
}

lemma InvNextLeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidPromiseMessage(c, v)
  requires MonotonicityInv(c, v)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires Next(c, v, v')
  ensures LeaderReceivedPromisesImpliesAcceptorState(c, v')
{
  forall ldr:LeaderId, acc:AcceptorId, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && acc in v'.History(i).leaders[ldr].receivedPromises
  ensures
    v'.History(i).acceptors[acc].HasPromisedAtLeast(ldr)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if dsStep.LeaderStep? {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        var lc, l, l' := c.leaderConstants[actor], v.Last().leaders[actor], v'.Last().leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if step.ReceiveStep? {
          assert IsPromiseMessage(v, msgOps.recv.value);  // trigger
        } 
      }
    }
  }
}

lemma InvNextLeaderNotHeardImpliesNotPromised(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidPromiseMessage(c, v)
  requires AcceptorPromisedMonotonic(c, v)
  requires ValidHistory(c, v)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires LeaderNotHeardImpliesNotPromised(c, v)
  requires Next(c, v, v')
  ensures LeaderNotHeardImpliesNotPromised(c, v')
{
  VariableNextProperties(c, v, v');
  forall ldr:LeaderId, acc:AcceptorId, b:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && b < ldr
    && v'.History(i).acceptors[acc].HasAcceptedAtLeastBal(b)
    && v'.History(i).acceptors[acc].HasAcceptedAtMostBal(ldr)
    && v'.History(i).leaders[ldr].HeardAtMost(b)
  ensures
    && acc !in v'.History(i).leaders[ldr].receivedPromises
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if && dsStep.LeaderStep?
         && actor == ldr {
        var lc, l, l' := c.leaderConstants[actor], v.Last().leaders[actor], v'.Last().leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if && step.ReceiveStep?
           && acc in l'.receivedPromises 
        {
          var msg := msgOps.recv.value;
          assert IsPromiseMessage(v, msg);  // trigger
          var j: nat  :| PromiseMessageMatchesHistory(c, v, msg, j);    // witness
          assert 0 < j by {
            reveal_ValidHistory();
          }
          if v.History(j).acceptors[acc].HasAcceptedAtMostBal(b) {
            // Acceptor cannot accept between b and ldr
            NotHeardImpliesNotPromisedInHistorySeq(c, v, acc, j, i-1, ldr, b);
          }
          assert false;           
        } 
      }
    }
  }
}

lemma NotHeardImpliesNotPromisedInHistorySeq(c: Constants, v: Variables, acc: AcceptorId, start: int, end: int, promised: LeaderId, acceptedAtMost: LeaderId)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires c.ValidAcceptorIdx(acc)
  requires v.ValidHistoryIdx(start)
  requires v.ValidHistoryIdx(end)
  requires 0 < start < end

  // Input constraints
  requires acceptedAtMost <= promised
  requires forall i | start <= i <= end :: v.History(i).acceptors[acc].HasPromisedAtLeast(promised)
  requires v.History(start).acceptors[acc].HasAcceptedAtMostBal(acceptedAtMost)
  ensures forall i | 
    && start <= i <= end 
    && v.History(i).acceptors[acc].HasAcceptedAtMostBal(promised)
  :: 
    && v.History(i).acceptors[acc].HasAcceptedAtMostBal(acceptedAtMost)
{
  if start < end-1{
    NotHeardImpliesNotPromisedInHistorySeq(c, v, acc, start, end-1, promised, acceptedAtMost);
    forall i | 
      && start <= i <= end 
      && v.History(i).acceptors[acc].HasAcceptedAtMostBal(promised)
    ensures
      && v.History(i).acceptors[acc].HasAcceptedAtMostBal(acceptedAtMost)
    {
      if i == end {
        assert Next(c, v.Truncate(c, i-1), v.Truncate(c, i)) by {
          reveal_ValidHistory();
        }
      }
    }
  } else {
    assert Next(c, v.Truncate(c, start), v.Truncate(c, end)) by {
      reveal_ValidHistory();
    }
  }
}

lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires MessageInv(c, v) && MessageInv(c, v')
  requires MonotonicityInv(c, v) && MonotonicityInv(c, v')
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  requires AcceptorPromisedLargerThanAccepted(c, v)
  requires LeaderNotHeardImpliesNotPromised(c, v) && LeaderNotHeardImpliesNotPromised(c, v')
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{
  forall ldr, acc, lnr, vb:ValBal, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && c.ValidLearnerIdx(lnr)
    && vb in v'.History(i).learners[lnr].receivedAccepts
    && vb.b < ldr
    && v'.History(i).leaders[ldr].HeardAtMost(vb.b)
    && acc in v'.History(i).leaders[ldr].receivedPromises
  ensures
    acc !in v'.History(i).learners[lnr].receivedAccepts[vb]
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if dsStep.LeaderStep? {
        NotAcceptorStepImpliesNoPromiseOrAccept(c,  v.Last(), v'.Last(), v.network, v'.network, dsStep);
        if acc in v'.History(i).learners[lnr].receivedAccepts[vb] {
          // trigger and witness
          assert Accept(vb, acc) in v'.network.sentMsgs;
          var j :|
            && v.ValidHistoryIdx(j)
            && v.History(j).acceptors[acc].HasAccepted(vb)
            && v.History(j).acceptors[acc].HasPromised(vb.b);
          AcceptedAndPromisedImpliesSeen(c, v', j, i, acc, vb, ldr);
          assert false;
        }
      } else if dsStep.LearnerStep? {
        NotAcceptorStepImpliesNoPromiseOrAccept(c,  v.Last(), v'.Last(), v.network, v'.network, dsStep);
        if acc in v'.History(i).learners[lnr].receivedAccepts[vb] {
          // trigger and witness
          assert Accept(vb, acc) in v.network.sentMsgs;
          var j :|
            && v.ValidHistoryIdx(j)
            && v.History(j).acceptors[acc].HasAccepted(vb)
            && v.History(j).acceptors[acc].HasPromised(vb.b);
          AcceptedAndPromisedImpliesSeen(c, v, j, i-1, acc, vb, ldr);
          assert false;
        }
      }
    }
  }
}

lemma AcceptedAndPromisedImpliesSeen(c: Constants, v: Variables, start:int, end: int, acc: AcceptorId, acceptedVB: ValBal, ldr: LeaderId)
  requires v.WF(c)
  // Needed invariants
  requires LeaderHighestHeardMonotonic(c, v)
  requires AcceptorAcceptedMonotonic(c, v)
  requires AcceptorPromisedMonotonic(c, v)
  requires ValidHistory(c, v)
  requires ValidMessageSrc(c, v)
  requires ValidPromiseMessage(c, v)
  
  // Input constraints
  requires c.ValidAcceptorIdx(acc)
  requires c.ValidLeaderIdx(ldr)
  requires v.ValidHistoryIdx(start)
  requires v.ValidHistoryIdx(end)
  requires start <= end
  requires v.History(start).acceptors[acc].acceptedVB == Some(acceptedVB)
  requires v.History(start).acceptors[acc].promised == Some(acceptedVB.b)
  requires acceptedVB.b < ldr
  requires LeaderNotHeardImpliesNotPromised(c, v)
  
  // Desired postcondition
  ensures forall i | 
          && start <= i <= end 
          && acc in v.History(i).leaders[ldr].receivedPromises
          :: 
          v.History(i).leaders[ldr].HeardAtLeast(acceptedVB.b)
  // Needed to make postcondition inductive
  ensures forall p | 
          && IsPromiseMessage(v, p)
          && p.bal == ldr
          && p.acc == acc
          :: 
          && p.vbOpt.Some?
          && p.vbOpt.value.b >= acceptedVB.b
{
  if start < end {
    // Inductive Case
    AcceptedAndPromisedImpliesSeen(c, v, start, end-1, acc, acceptedVB, ldr);
    forall i | 
      && start <= i <= end 
      && acc in v.History(i).leaders[ldr].receivedPromises
    ensures
      v.History(i).leaders[ldr].HeardAtLeast(acceptedVB.b)
    {
      if i == end {
        assert Next(c, v.Truncate(c, i-1), v.Truncate(c, i)) by {
          reveal_ValidHistory();
        }
      }
    }
  } else {
    // Base Case
    forall i | 
      && start <= i <= end 
      && acc in v.History(i).leaders[ldr].receivedPromises
    ensures
      v.History(i).leaders[ldr].HeardAtLeast(acceptedVB.b)
    {
      if !v.History(i).leaders[ldr].HeardAtLeast(acceptedVB.b) {
        // Contradicts LeaderNotHeardImpliesNotPromised
        assert v.History(start).leaders[ldr].HeardAtMost(acceptedVB.b);  // trigger
        assert false;
      }
    }
  }
}

lemma InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
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
    && ChosenAtHistory(c, v'.History(i), vb)
    && c.ValidAcceptorIdx(acc)
    && v'.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b)
  ensures
     v'.History(i).acceptors[acc].acceptedVB.value.v == vb.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if dsStep.LeaderStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if 
        && dsStep.AcceptorStep?
        && actor == acc 
      {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
        var ac, a, a' := c.acceptorConstants[actor], v.Last().acceptors[actor], v'.Last().acceptors[actor];
        var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
        if step.MaybeAcceptStep? {
          ChosenImpliesProposeMessagesOnlyContainValue(c, v, vb);
        } else {
          AcceptorHost.UpdateReceiveAcceptedStep(ac, a, a', step, msgOps);
        }
      } else {
        if v'.History(i).acceptors[acc].acceptedVB.value.v != vb.v {
          var ldr := v'.Last().acceptors[acc].acceptedVB.value.b;
          reveal_Chosen();
          reveal_ChosenAtHistory();
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldr, vb);
        }
      }
    }
  }
}

lemma InvNextChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires Inv(c, v)

  // Prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires OneValuePerBallot(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
  ensures ChosenValImpliesLeaderOnlyHearsVal(c, v')
{
  forall vb, ldrBal:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v'.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && v'.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
  ensures
    v'.History(i).leaders[ldrBal].value == vb.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaderConstants[ldrBal], v.Last().leaders[ldrBal], v'.Last().leaders[ldrBal];
      if dsStep.LeaderStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
        reveal_ChosenAtHistory();
      } else if dsStep.AcceptorStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        if v'.History(i).leaders[ldrBal].value != vb.v {
          assert Chosen(c, v', vb) by {
            reveal_Chosen();
          }
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
        }
      }
    }
  }
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  forall vb, ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && ChosenAtHistory(c, v'.History(i), vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr
    && v'.History(i).LeaderCanPropose(c, ldr)
  ensures
    v'.History(i).leaders[ldr].HeardAtLeast(vb.b)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaderConstants[ldr], v.Last().leaders[ldr], v'.Last().leaders[ldr];
      if dsStep.LeaderStep? {
        InvNextChosenImpliesProposingLeaderHearsChosenBallotLeaderStep(c, v, v', dsStep, vb, ldr);
      } else if dsStep.AcceptorStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        InvNextChosenImpliesProposingLeaderHearsChosenBallotLearnerStep(c, v, v', dsStep, vb, ldr);
      }
    }
  }
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallotLeaderStep(
  c: Constants, v: Variables, v': Variables, dsStep: Step,
  vb: ValBal, ldr:LeaderId)
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires dsStep.LeaderStep?
  requires ValidMessageSrc(c, v)
  requires ValidPromiseMessage(c, v)
  // requires Inv(c, v)
  requires LeaderValidReceivedPromises(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  requires LearnerReceivedAcceptImpliesAccepted(c, v')

  // input constraints
  requires ChosenAtHistory(c, v'.Last(), vb)
  requires c.ValidLeaderIdx(ldr)
  requires vb.b < ldr
  requires v'.Last().LeaderCanPropose(c, ldr)
  ensures v'.Last().leaders[ldr].HeardAtLeast(vb.b)
{
  // Note that proof is identical to atomic case
  VariableNextProperties(c, v, v');
  NewChosenOnlyInLearnerStep(c, v, v', dsStep);
  if ldr == dsStep.actor {  // if the leader in question is now taking a step
    assert ChosenAtHistory(c, v.Last(), vb) by {
      reveal_ChosenAtHistory();
    }
    var choosingAccs := SupportingAcceptorsForChosen(c, v, |v.history|-1, vb);
    var h, h' := v.Last(), v'.Last();
    if h.leaders[ldr].HeardAtMost(vb.b) {
      //Ldr has yet to see ballot b in this step. By quorum intersection, it must see
      // an acceptor in choosingAccs in this step
      var acc := dsStep.msgOps.recv.value.acc;
      if acc !in choosingAccs {
        // In this case, by quorum intersection, acc must already be in ldr.receivePromises
        // Because, choosingAccs !! v.leaders[ldr].receivedPromises
        reveal_ValidMessageSrc();
        var allAccs := GetAcceptorSet(c, v);
        var e := QuorumIntersection(allAccs, choosingAccs, h.leaders[ldr].receivedPromises + {acc});
        assert false;
      }      
    }    
  }
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallotLearnerStep(
  c: Constants, v: Variables, v': Variables, dsStep: Step,
  vb: ValBal, ldr:LeaderId)
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires dsStep.LearnerStep?
  requires LeaderValidReceivedPromises(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  requires LearnerReceivedAcceptImpliesAccepted(c, v')

  // input constraints
  requires ChosenAtHistory(c, v'.Last(), vb)
  requires c.ValidLeaderIdx(ldr)
  requires vb.b < ldr
  requires v'.Last().LeaderCanPropose(c, ldr)
  ensures v'.Last().leaders[ldr].HeardAtLeast(vb.b)
{
  // Note that proof is identical to atomic case
  VariableNextProperties(c, v, v');
  reveal_ChosenAtHistory();
  if !ChosenAtHistory(c, v.Last(), vb) {
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    var lnr:LearnerId:| ChosenAtLearner(c, v'.Last(), vb, lnr);
    if lnr == actor {
       var choosingAccs := SupportingAcceptorsForChosen(c, v', |v'.history|-1, vb);
      // These properties of choosingAccs carry over to pre-state v
      assert v.Last().LeaderCanPropose(c, ldr);  // trigger
      if !v.Last().leaders[ldr].HeardAtLeast(vb.b) {
        var allAccs := GetAcceptorSet(c, v);
        var e := QuorumIntersection(allAccs, choosingAccs, v.Last().leaders[ldr].receivedPromises);
        assert false;
      } 
    } else {
      assert !ChosenAtLearner(c, v.Last(), vb, lnr);  // trigger
    }
  }
}

// Helper lemma for InvNextChosenValImpliesLeaderOnlyHearsVal
lemma LeaderHearsDifferentValueFromChosenImpliesFalse(c: Constants, v: Variables, ldr:LeaderId, chosen: ValBal)
  requires v.WF(c)
  requires Chosen(c, v, chosen)
  requires c.ValidLeaderIdx(ldr)
  requires v.Last().leaders[ldr].HeardAtLeast(chosen.b)
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

/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f+1
  && (forall id | id in quorum :: c.ValidAcceptorIdx(id))
}

// A learner holds an accept quorum for vb
ghost predicate {:opaque} Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  ChosenAtHistory(c, v.Last(), vb)
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
  forall i, j, vb1: ValBal, vb2: ValBal | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && vb1.b <= vb2.b 
    && ChosenAtHistory(c, v.History(i), vb1) 
    && ChosenAtHistory(c, v.History(j), vb2)
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
  reveal_Chosen();
  reveal_ChosenAtHistory();
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
    reveal_Chosen();
    assert false;
  }
}

// Lemma: The only system step in which a new vb can be chosen is a P2bStep 
lemma NewChosenOnlyInLearnerStep(c: Constants, v: Variables, v': Variables, dsStep: Step) 
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires !dsStep.LearnerStep?
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
  requires ChosenAtHistory(c, v.History(i), vb)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  ensures |supportingAccs| >= c.f+1
  ensures forall a | a in supportingAccs :: 
    && c.ValidAcceptorIdx(a)
    && v.History(i).acceptors[a].HasAcceptedAtLeastBal(vb.b)
  ensures exists lnr :: 
    && c.ValidLearnerIdx(lnr)
    && vb in v.History(i).learners[lnr].receivedAccepts
    && supportingAccs <= v.History(i).learners[lnr].receivedAccepts[vb]
{
  reveal_ChosenAtHistory();
  var lnr: LearnerId :| ChosenAtLearner(c, v.History(i), vb, lnr);  // skolemize!
  supportingAccs := v.History(i).learners[lnr].receivedAccepts[vb];
  return supportingAccs;
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

lemma NotLeaderStepImpliesNoPrepareOrPropose(c: Constants, h: Hosts, h': Hosts, 
  n: Network.Variables, n': Network.Variables, dsStep: Step
)
  requires h.WF(c) && h'.WF(c)
  requires NextStep(c, h, h', n, n', dsStep)
  requires !dsStep.LeaderStep?
  ensures forall p | 
    && p in n'.sentMsgs
    && (p.Propose? || p.Prepare?)
  :: 
    p in n.sentMsgs
{}

lemma NotAcceptorStepImpliesNoPromiseOrAccept(c: Constants, h: Hosts, h': Hosts, 
  n: Network.Variables, n': Network.Variables, dsStep: Step
)
  requires h.WF(c) && h'.WF(c)
  requires NextStep(c, h, h', n, n', dsStep)
  requires !dsStep.AcceptorStep?
  ensures forall p | 
    && p in n'.sentMsgs
    && (p.Promise? || p.Accept?)
  :: 
    p in n.sentMsgs
{}

lemma InvImpliesAtMostOneChosenVal(c: Constants, v: Variables)
  requires v.WF(c)
  requires LearnerReceivedAcceptsMonotonic(c, v)
  requires OneValuePerBallot(c, v)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnerValidReceivedAcceptsKeys(c, v)  // prereq for LearnerReceivedAcceptImpliesProposed
  requires LearnerReceivedAcceptImpliesProposed(c, v)
  requires ChosenValImpliesLeaderOnlyHearsVal(c, v)
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  ensures AtMostOneChosenVal(c, v)
{
  forall i, j, vb1: ValBal, vb2: ValBal | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && vb1.b <= vb2.b
    && ChosenAtHistory(c, v.History(i), vb1)
    && ChosenAtHistory(c, v.History(j), vb2)
  ensures 
    vb1.v == vb2.v
  {
    reveal_ChosenAtHistory();
    // vb1 chosen at i implies that vb1 is also chosen at j, by LearnerReceivedAcceptsMonotonic.
    // This means that a leader proposed vb1, and another proposed vb2, by LearnerReceivedAcceptImpliesProposed.
    var lnr1: nat :| ChosenAtLearner(c, v.History(i), vb1, lnr1);
    assert ChosenAtHistory(c, v.History(j), vb1) by {
      SetContainmentCardinality(v.History(i).learners[lnr1].receivedAccepts[vb1], v.History(j).learners[lnr1].receivedAccepts[vb1]);
      assert ChosenAtLearner(c, v.History(j), vb1, lnr1);  // trigger
    }
    // There are then two cases. If vb1.b == vb2.b, then the conclusion holds via OneValuePerBallot
    // Otherwise, leader 2 must hear leader 1's ballot, by ChosenImpliesProposingLeaderHearsChosenBallot.
    // Then by ChosenValImpliesLeaderOnlyHearsVal, leader 2 must have same value as leader 1.
  }
}

lemma ChosenImpliesProposeMessagesOnlyContainValue(c: Constants, v: Variables, vb: ValBal) 
  requires Inv(c, v)
  requires ChosenAtHistory(c, v.Last(), vb)
  ensures forall prop | 
    && IsProposeMessage(v, prop)
    && vb.b <= prop.bal
  ::
    vb.v == prop.val
{
  forall prop | 
    && IsProposeMessage(v, prop)
    && vb.b <= prop.bal
  ensures
    vb.v == prop.val
  {
    if vb.b == prop.bal {
      // Because vb is chosen, leader vb.b proposed it, by LearnerReceivedAcceptImpliesProposed. 
      // Also, leader vb.b sent prop, and so must proposed prob.val, by MessageInv.
      // Result then follows from LeaderCanProposeMonotonic
      reveal_ChosenAtHistory();
    } else {
      // Leader prop.bal must hear leader vb.b's ballot, by ChosenImpliesProposingLeaderHearsChosenBallot.
      // Then by ChosenValImpliesLeaderOnlyHearsVal, leader 2 must have same value as leader 1.
    }
  }
}
} // end module PaxosProof