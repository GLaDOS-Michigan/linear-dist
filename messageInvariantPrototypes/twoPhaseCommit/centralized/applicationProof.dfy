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
  LeaderTallyReflectsPreferences(c, v)
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences(c: Constants, v: Variables)
  requires v.WF(c)
{
  var n := |c.hosts|;
  && (forall hostId | hostId in GetCoordinator(c, v).yesVotes ::
        0 <= hostId < n-1 && GetParticipantPreference(c, hostId) == Yes )
  && (forall hostId | hostId in GetCoordinator(c, v).noVotes ::
        0 <= hostId < n-1 && GetParticipantPreference(c, hostId) == No )
}

// User-level invariant
ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
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
  LeaderTallyReflectsPreferencesInductive(c, v, v');
  AC3Proof(c, v, v');
  AC4Proof(c, v, v');
}

lemma LeaderTallyReflectsPreferencesInductive(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderTallyReflectsPreferences(c, v')
{
  // trigger
  var step :| NextStep(c, v, v', step);
}

lemma AC3Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AC3Contrapos(c, v')
{
  var n := |c.hosts|;
  if ! AllPreferYes(c, v) {
    var noVoter :| 0 <= noVoter < n-1 && c.hosts[noVoter].participant.preference == No;
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.DecideStep? {
      var decision := sysStep.decision;
      if decision == Commit {
        YesVotesContainsAllParticipantsWhenFull(c, v);
        assert GetParticipantPreference(c, noVoter) == Yes;  // witness
        assert false;
      }
    } 
  }
}

lemma AC4Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC4(c, v')
{
  if AllPreferYes(c, v') {
    var n := |v.hosts|;
    forall i | 0 <= i < n && HostHasDecided(v'.hosts[i]) 
    ensures HostDecidedCommit(v'.hosts[i]) {
      var sysStep :| NextStep(c, v, v', sysStep);
      if sysStep.DecideStep? {
        /* Proof by contradiction: suppose coord decide no. Then leader's noVotes is
        not empty. By LeaderTallyReflectsPreferences, this member preferred No, which 
        contradicts with AllPreferYes(c, v) */
        var coord := v.hosts[sysStep.coordinator].coordinator;
        assert coord == GetCoordinator(c, v);  // trigger
      }
    }
  }
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables)
  requires Inv(c, v)
  requires |Last(v.hosts).coordinator.yesVotes| == |c.hosts|-1
  ensures forall id | 0 <= id < |c.hosts|-1 :: id in GetCoordinator(c, v).yesVotes
{
  var l := GetCoordinator(c, v);
  forall id | 0 <= id < |c.hosts|-1 
  ensures id in l.yesVotes {
    if id !in l.yesVotes {
      SetLemma(l.yesVotes, id, |c.hosts|-1);
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

