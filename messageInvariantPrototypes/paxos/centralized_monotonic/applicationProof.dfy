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

ghost predicate AcceptorAcceptedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
{
  forall acc:AcceptorId |
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].Last().acceptedVB.Some?
  ::
    var vb := v.acceptors[acc].Last().acceptedVB.value;
    && v.LeaderCanPropose(c, vb.b)
    && v.leaders[vb.b].Last().value == vb.v
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


// For any leader L, if an acceptor A is in L.promises, then A cannot have accepted any
// ballot b such that L.highestHeard < b < L
ghost predicate LeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, lnr, vb:ValBal | 
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].Last().receivedAccepts
    && vb.b < ldr
    && v.leaders[ldr].HeardAtMost(vb.b)
    && acc in v.leaders[ldr].Last().receivedPromises
  ::
    acc !in v.learners[lnr].Last().receivedAccepts[vb]
}

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, acc:AcceptorId | 
    && Chosen(c, v, vb)
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].Last().acceptedVB.Some?
    && v.acceptors[acc].Last().acceptedVB.value.b >= vb.b
  ::
     v.acceptors[acc].Last().acceptedVB.value.v == vb.v
}

// If vb is chosen, then for all leaders > vb.b and ready to propose, they must have highest 
// heard >= b
ghost predicate ChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && vb.b < ldrBal
    && v.LeaderCanPropose(c, ldrBal)
  ::
    v.leaders[ldrBal].HeardAtLeast(vb.b)
}

// If vb is chosen, then for all leaders has a highest heard >= vb.b, the value must be vb.v
ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && v.leaders[ldrBal].Last().highestHeardBallot.Some?
    && v.leaders[ldrBal].Last().highestHeardBallot.value >= vb.b
  ::
    v.leaders[ldrBal].Last().value == vb.v
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
  InvInductiveHelper(c, v, v');
  InvNextOneValuePerBallot(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  InvNextLeaderNotHeardImpliesNotPromised(c, v, v');
  InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');
  InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');
  
  assert AtMostOneChosenVal(c, v');  // this should be implied by invariants
  AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

// Bundle for simple-to-prove invariants
lemma InvInductiveHelper(c: Constants, v: Variables, v': Variables)
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
{}

lemma {:timeLimitMultiplier 2} InvNextOneValuePerBallot(c: Constants, v: Variables, v': Variables)
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
      && ChosenAtLearner(c, v', vb, lnr)
  {
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.P2bStep? && sysStep.learner == lnr {
      assert v.learners[lnr].HasLearnedValue(val);  // trigger
    } else if sysStep.LearnerInternalStep? && sysStep.learner == lnr {
      var step :| LearnerHost.NextStep(c.learnerConstants[lnr], v.learners[lnr], v'.learners[lnr], step, LearnerHost.InternalLbl());
      if step.StutterStep? {
        assert v.learners[lnr].HasLearnedValue(val);  // trigger
      }
    }
  }
}

lemma InvNextLeaderNotHeardImpliesNotPromised(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires LeaderNotHeardImpliesNotPromised(c, v)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires Next(c, v, v')
  ensures LeaderNotHeardImpliesNotPromised(c, v')
{}

lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
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
  requires NextStep(c, v, v', sysStep)
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  NewChosenOnlyInP2bStep(c, v, v', sysStep);
  forall vb, ldr:LeaderId | 
    && Chosen(c, v', vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr 
    && v'.LeaderCanPropose(c, ldr)
  ensures
    v'.leaders[ldr].HeardAtLeast(vb.b)
  {
    assert Chosen(c, v, vb);
    if ldr == sysStep.leader {  // if the leader in question is now taking a step
      var choosingAccs := SupportingAcceptorsForChosen(c, v, vb);
      if v.leaders[ldr].HeardAtMost(vb.b) {
        // Ldr has yet to see ballot b in this step. By quorum intersection, it must see
        // an acceptor in choosingAccs in this step
        var acc := sysStep.acceptor;
        if acc !in choosingAccs {
          // In this case, by quorum intersection, acc must already be in ldr.receivePromises
          // First prove that choosingAccs !! v.leaders[ldr].receivedPromises
          forall a | a in choosingAccs 
          ensures a !in v.leaders[ldr].Last().receivedPromises
          {
            if !v.acceptors[a].HasAcceptedAtMostBal(ldr) && a in v.leaders[ldr].Last().receivedPromises {
              // via LeaderHighestHeardToPromisedRangeHasNoAccepts
              assert false;
            }
          }
          var allAccs := GetAcceptorSet(c, v);
          var e := QuorumIntersection(allAccs, choosingAccs, v.leaders[ldr].Last().receivedPromises + {acc});
          assert false;
        }        
      }
    }
  }
}

// Helper lemma for P2b branch of InvNextChosenImpliesProposingLeaderHearsChosenBallot
lemma {:timeLimitMultiplier 2} InvNextChosenImpliesProposingLeaderHearsChosenBallotP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires sysStep.P2bStep?
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  requires NextStep(c, v, v', sysStep)
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  forall vb, ldr:LeaderId | 
    && Chosen(c, v', vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr 
    && v'.LeaderCanPropose(c, ldr)
  ensures
    v'.leaders[ldr].HeardAtLeast(vb.b)
  {
    var choosingAccs := SupportingAcceptorsForChosen(c, v', vb);
    // These properties of choosingAccs carry over to pre-state v
    assert forall a | a in choosingAccs ::
      && c.ValidAcceptorIdx(a)
      && v.acceptors[a].HasAcceptedAtLeastBal(vb.b);
    // Leader is also unchanged
    assert v'.leaders[ldr] == v.leaders[ldr];
    assert v.LeaderCanPropose(c, ldr);
    if !v.leaders[ldr].HeardAtLeast(vb.b) {
      // Contradiction via quorum intersection, and LeaderHighestHeardToPromisedRangeHasNoAccepts
      var allAccs := GetAcceptorSet(c, v);
      var e := QuorumIntersection(allAccs, choosingAccs, v.leaders[ldr].Last().receivedPromises);
      assert false;
    }
  }
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
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? || sysStep.P1bStep? || sysStep.P2aStep? || sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P2bStep? {
    if !ChosenValImpliesAcceptorOnlyAcceptsVal(c, v') {
      var vb, acc:AcceptorId :|
        && Chosen(c, v', vb)
        && c.ValidAcceptorIdx(acc)
        && v'.acceptors[acc].Last().acceptedVB.Some?
        && vb.b <= v'.acceptors[acc].Last().acceptedVB.value.b 
        // This is the contradiction
        && v'.acceptors[acc].Last().acceptedVB.value.v != vb.v;
      
      // Then there is a leader that proposed the accepted value, by AcceptorAcceptedImpliesProposed
      var ldr := v'.acceptors[acc].Last().acceptedVB.value.b;
      LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldr, vb);
    }
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
          && v'.leaders[ldrBal].Last().highestHeardBallot.Some?
          && v'.leaders[ldrBal].Last().highestHeardBallot.value >= vb.b
          // This is the contradiction
          && v'.leaders[ldrBal].Last().value != vb.v;
      if vb.b < ldrBal {
        LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
      }
      // Otherwise, when vb.b < ldrBal, violates OneValuePerBallot(c, v')
    }
  }
}

lemma LeaderHearsDifferentValueFromChosenImpliesFalse(c: Constants, v: Variables, ldr:LeaderId, chosen: ValBal)
  requires v.WF(c)
  requires Chosen(c, v, chosen)
  requires c.ValidLeaderIdx(ldr)
  requires v.leaders[ldr].Last().highestHeardBallot.Some?
  requires v.leaders[ldr].Last().highestHeardBallot.value >= chosen.b
  requires v.leaders[ldr].Last().value != chosen.v
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
  var ldr' := v.leaders[ldr].Last().highestHeardBallot.value;
  assert v.leaders[ldr'].Last().value == v.leaders[ldr].Last().value;
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
        && v.learners[l1].HasLearnedSome()
        && v.learners[l2].HasLearnedSome()
        && v.learners[l1].GetLearnedValue() != v.learners[l2].GetLearnedValue()
    ;
    var vb1 := LearnedImpliesChosen(c, v, l1, v.learners[l1].Last().learned.value);
    var vb2 := LearnedImpliesChosen(c, v, l2, v.learners[l2].Last().learned.value);
    assert false;
  }
}

// Lemma: The only system step in which a new vb can be chosen is a P2bStep 
lemma NewChosenOnlyInP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step) 
  requires v.WF(c)
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

// Suppose vb is chosen. Return the quorum of acceptors supporting the chosen vb
lemma SupportingAcceptorsForChosen(c: Constants, v: Variables, vb: ValBal)
returns (supportingAccs: set<AcceptorId>)
  requires v.WF(c)
  requires Chosen(c, v, vb)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  ensures |supportingAccs| >= c.f+1
  ensures forall a | a in supportingAccs :: 
    && c.ValidAcceptorIdx(a)
    && v.acceptors[a].HasAcceptedAtLeastBal(vb.b)
  ensures exists lnr :: 
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].Last().receivedAccepts
    && supportingAccs <= v.learners[lnr].Last().receivedAccepts[vb]
{
  var lnr: LearnerId :| ChosenAtLearner(c, v, vb, lnr);  // skolemize!
  supportingAccs := v.learners[lnr].Last().receivedAccepts[vb];
  return supportingAccs;
}

lemma GetAcceptorSet(c: Constants, v: Variables)
returns (accSet: set<AcceptorId>)
  requires v.WF(c)
  ensures forall a :: c.ValidAcceptorIdx(a) <==> a in accSet
  ensures |accSet| == 2 * c.f + 1
{
  accSet := set a |  0 <= a < |c.acceptorConstants|;
  SetComprehensionSize(|c.acceptorConstants|);
}

} // end module PaxosProof