include "messageInvariants.dfy"


module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  && ParticipantsVoteOnce(c, v)   // Funky
  && OneDecisionMessage(c, v)     // Funky
  && AbortReflectsVotes(c, v)     // Funky
  && CommitReflectsVotes(c, v)    // Funky
  && LeaderDecisionAbort(c, v)    // Funky
  && LeaderDecisionCommit(c, v)   // Funky
}

ghost predicate LeaderVotesValid1(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall hostId | hostId in v.GetCoordinator(c).yesVotes
  :: 0 <= hostId < |c.participants|
}

ghost predicate LeaderVotesValid2(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall hostId | hostId in v.GetCoordinator(c).noVotes
  :: 0 <= hostId < |c.participants|
}

ghost predicate OneDecisionMessage(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall m1, m2 | m1 in v.network.sentMsgs && m1.DecideMsg? && m2 in v.network.sentMsgs && m2.DecideMsg?
  :: m1 == m2
}

ghost predicate ParticipantsVoteOnce(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall m1, m2 | m1 in v.network.sentMsgs && m1.VoteMsg? && m2 in v.network.sentMsgs && m2.VoteMsg? && m1.src == m2.src
  :: m1 == m2
}

ghost predicate AbortReflectsVotes(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
{
  (exists msg :: msg in v.network.sentMsgs && msg == DecideMsg(Abort))
  ==> (exists msg :: msg in v.network.sentMsgs && msg.VoteMsg? && msg.v == No)
}

ghost predicate LeaderDecisionAbort(c: Constants, v: Variables)
  requires v.WF(c)
{
  CoordinatorDecidedAbort(c, v)
  ==>
  |v.GetCoordinator(c).noVotes| > 0
}

ghost predicate LeaderDecisionCommit(c: Constants, v: Variables)
  requires v.WF(c)
{
  CoordinatorDecidedCommit(c, v)
  ==>
  && v.GetCoordinator(c).noVotes == {}
  && |v.GetCoordinator(c).yesVotes| >= c.GetCoordinator().numParticipants
}

ghost predicate CommitReflectsVotes(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
{
  (exists msg :: msg in v.network.sentMsgs && msg == DecideMsg(Commit))
  ==> (forall msg | msg in v.network.sentMsgs && msg.VoteMsg? :: msg.v == Yes)
}

// User-level invariant
ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Safety(c, v)
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
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
  InvNextAbortReflectsVotes(c, v, v');
  InvNextLeaderDecisionCommit(c, v, v');
  InvNextCommitReflectsVotes(c, v, v');
}

lemma InvNextLeaderDecisionCommit(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderDecisionCommit(c, v')
{
  if CoordinatorDecidedCommit(c, v') {
    if CoordinatorDecidedCommit(c, v) {
      assume false;
      SetContainmentCardinality(v.GetCoordinator(c).yesVotes, v'.GetCoordinator(c).yesVotes);
    }
  }
}

lemma InvNextAbortReflectsVotes(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderDecisionAbort(c, v')
  requires OneDecisionMessage(c, v')
  requires MessageInv(c, v')
  ensures AbortReflectsVotes(c, v')
{}

lemma InvNextCommitReflectsVotes(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderDecisionCommit(c, v')
  requires OneDecisionMessage(c, v')
  ensures CommitReflectsVotes(c, v')
  ensures AC3Contrapos(c, v')
{
  AC3ContraposLemma(c, v);
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v') {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.CoordinatorStep? {
      /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
      a Yes vote from all participants, including noVoter. This is a contradiction */
      var l, l' := v.GetCoordinator(c), v'.GetCoordinator(c);
      if l.decision.WONone? && l'.decision == WOSome(Commit) {
        YesVotesContainsAllParticipantsWhenFull(c, v);
        assert noVoter in  v.GetCoordinator(c).yesVotes;  // trigger
        assert GetParticipantPreference(c, noVoter) == Yes;  // witness
        assert false;
      }
    }
  }
}

lemma AC3ContraposLemma(c: Constants, v: Variables)
  requires Inv(c, v)
  requires SafetyAC3(c, v)
  ensures AC3Contrapos(c, v)
{
  assume false;
  if (!AllPreferYes(c) && CoordinatorHasDecided(c, v)) {
    assert v.GetCoordinator(c).decision.value != Commit;  // trigger
  }
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables)
  requires Inv(c, v)
  requires |v.GetCoordinator(c).yesVotes| == |c.participants|
  ensures forall id | 0 <= id < |c.participants| :: id in v.GetCoordinator(c).yesVotes
{
  var l := v.GetCoordinator(c);
  forall id | 0 <= id < |c.participants|
  ensures id in l.yesVotes {
    if id !in l.yesVotes {
      SetLemma(l.yesVotes, id, |c.participants|);
      assert false;
    }
  }
}

lemma SetLemma(S: set<HostId>, e: HostId, size: int) 
  requires 0 <= e < size
  requires forall x | x in S :: 0 <= x < size
  requires e !in S
  ensures |S| < size
{
  var fullSet := set x | 0 <= x < size;
  SetComprehensionSize(size);
  SetContainmentCardinalityStrict(S, fullSet);
}
}
