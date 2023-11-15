include "spec.dfy"

module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened System
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
  forall hostId | hostId in v.GetCoordinator(c).yesVotes
  :: 0 <= hostId < |c.participants|
}

ghost predicate LeaderVotesValid2(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall hostId | hostId in v.GetCoordinator(c).noVotes
  :: 0 <= hostId < |c.participants|
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences1(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
{
  var n := |c.participants|;
  && (forall hostId | hostId in v.GetCoordinator(c).yesVotes  ::
      GetParticipantPreference(c, hostId) == Yes )
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences2(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid2(c, v)
{
  var n := |c.participants|;
  && (forall hostId | hostId in v.GetCoordinator(c).noVotes ::
      GetParticipantPreference(c, hostId) == No )
}

// User-level invariant
ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
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
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  LeaderTallyReflectsPreferencesInductive(c, v, v');
  AC1Proof(c, v, v');
  AC3Proof(c, v, v');
  AC4Proof(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma AC1Proof(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC1(c, v')
{}


lemma LeaderTallyReflectsPreferencesInductive(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ApplicationInv(c, v')
{}

lemma AC3Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AC3Contrapos(c, v')
{
  AC3ContraposLemma(c, v);
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v') {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.DecideStep? {
      var decision := sysStep.transmit.m.decision;
      if decision == Commit {
        YesVotesContainsAllParticipantsWhenFull(c, v);
        assert GetParticipantPreference(c, noVoter) == Yes;  // witness
        assert false;
      }
    }
  }
}

lemma AC3ContraposLemma(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures AC3Contrapos(c, v)
{
  if  (!AllPreferYes(c) && CoordinatorHasDecided(c, v)) {
    assert v.GetCoordinator(c).decision.value != Commit;  // trigger
  }
}

lemma AC4Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC4(c, v')
{
  if AllPreferYes(c) && CoordinatorHasDecided(c, v'){
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.DecideStep? {
      /* Proof by contradiction: suppose coord decide no. Then leader's noVotes is
      not empty. By LeaderTallyReflectsPreferences, this member preferred No, which 
      contradicts with AllPreferYes(c, v) */
    }
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

