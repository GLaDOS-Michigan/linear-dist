include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/


// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderVotesValid1(c, v)
  && LeaderVotesValid2(c, v)
  && LeaderTallyReflectsPreferences1(c, v)
  && LeaderTallyReflectsPreferences2(c, v)
}

ghost predicate LeaderVotesValid1(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i, hostId | v.ValidHistoryIdx(i) && hostId in v.History(i).GetCoordinator(c).yesVotes
  :: 0 <= hostId < |c.participants|
}

ghost predicate LeaderVotesValid2(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i, hostId | v.ValidHistoryIdx(i) && hostId in v.History(i).GetCoordinator(c).noVotes
  :: 0 <= hostId < |c.participants|
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences1(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
{
  forall i, hostId | v.ValidHistoryIdx(i) && hostId in v.History(i).GetCoordinator(c).yesVotes
  :: GetParticipantPreference(c, hostId) == Yes
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences2(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid2(c, v)
{
  forall i, hostId | v.ValidHistoryIdx(i) && hostId in v.History(i).GetCoordinator(c).noVotes
  :: GetParticipantPreference(c, hostId) == No
}

// User-level invariant
ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ApplicationInv(c, v)
  && Safety(c, v)
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
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
  MessageInvInductive(c, v, v');
  MonotonicityInvInductive(c, v, v');
  LeaderTallyReflectsPreferencesInductive(c, v, v');
  AC1Proof(c, v, v');
  AC3Proof(c, v, v');
  AC4Proof(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma LeaderTallyReflectsPreferencesInductive(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ApplicationInv(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma AC1Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC1(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma AC3Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AC3Contrapos(c, v')
{
  AC3ContraposLemma(c, v);
  VariableNextProperties(c, v, v');
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v'.Last()) {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    if dsStep.CoordinatorHostStep? {
        /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
        a Yes vote from all participants, including noVoter. This is a contradiction */
        var l, l' := v.Last().GetCoordinator(c), v'.Last().GetCoordinator(c);
        if l.decision.WONone? && l'.decision == WOSome(Commit) {
          YesVotesContainsAllParticipantsWhenFull(c, v, |v.history|-1);
          assert GetParticipantPreference(c, noVoter) == Yes;  // witness
        }
    }
  }
}

lemma AC3ContraposLemma(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures AC3Contrapos(c, v)
{
  if  (!AllPreferYes(c) && CoordinatorHasDecided(c, v.Last())) {
    assert v.Last().GetCoordinator(c).decision.value != Commit;  // trigger
  }
}

lemma AC4Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires MessageInv(c, v')
  requires ApplicationInv(c, v')
  ensures SafetyAC4(c, v')
{
  if AllPreferYes(c) && CoordinatorHasDecided(c, v'.Last()) {
    if !CoordinatorDecidedCommit(c, v'.Last()) {
      var x :| x in v'.Last().GetCoordinator(c).noVotes;
      assert GetParticipantPreference(c, x) == No;  // contradicts AllPreferYes(c)
    }
  }
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables, i: int)
  requires Inv(c, v)
  requires v.ValidHistoryIdx(i)
  requires |v.History(i).GetCoordinator(c).yesVotes| == |c.participants|
  ensures forall id | 0 <= id < |c.participants| :: id in v.History(i).GetCoordinator(c).yesVotes
{
  var l := v.History(i).GetCoordinator(c);
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
