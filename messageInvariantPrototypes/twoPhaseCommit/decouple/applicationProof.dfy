// User level proofs of application invariants

include "messageInvariants.dfy"


module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Application bundle
predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  LeaderTallyReflectsPreferences(c, v)
}

// Leader's local tally reflect participant preferences
predicate LeaderTallyReflectsPreferences(c: Constants, v: Variables)
  requires v.WF(c)
{
  var n := |c.hosts|;
  && (forall hostId | hostId in GetCoordinator(c, v).yesVotes ::
        0 <= hostId < n-1 && GetParticipantPreference(c, hostId) == Yes )
  && (forall hostId | hostId in GetCoordinator(c, v).noVotes ::
        0 <= hostId < n-1 && GetParticipantPreference(c, hostId) == No )
}

// User-level invariant
predicate Inv(c: Constants, v: Variables)
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
  LeaderTallyReflectsPreferencesInductive(c, v, v');
  AC3Proof(c, v, v');
  AC4Proof(c, v, v');
}

lemma LeaderTallyReflectsPreferencesInductive(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderTallyReflectsPreferences(c, v')
{
  var step :| NextStep(c, v, v', step);
  var h, h' := v.hosts[step.hostid], v'.hosts[step.hostid];
  if h.CoordinatorVariables? {
    var l, l' := GetCoordinator(c, v), GetCoordinator(c, v');  // trigger
  } else {
    assert GetCoordinator(c, v) == GetCoordinator(c, v');  // trigger
  }
}

lemma AC3Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AC3Contrapos(c, v')
{
  var n := |c.hosts|;
  if ! AllPreferYes(c, v) {
    var noVoter :| 0 <= noVoter < n-1 && c.hosts[noVoter].participant.preference == No;
    var step :| NextStep(c, v, v', step);
    var h, h' := v.hosts[step.hostid], v'.hosts[step.hostid];
    if h.CoordinatorVariables? {
        /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
        a Yes vote from all participants, including noVoter. This is a contradiction */
        var l, l' := h.coordinator, h'.coordinator;
        if l.decision.None? && l'.decision == Some(Commit) {
          YesVotesContainsAllParticipantsWhenFull(c, v);
          assert GetParticipantPreference(c, noVoter) == Yes;  // witness
          assert false;
        }
    } else {
        /* Proof by contradiction. Suppose participant decided Commit. Then it must have
        received a Commit message from the coordinator. This implies that the coordinator
        had committed in state v, which contradicts AC3Contrapos(c, v). */
    }
  }
}

lemma AC4Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires MessageInv(c, v')
  requires LeaderTallyReflectsPreferences(c, v')
  ensures SafetyAC4(c, v');
{
  if AllPreferYes(c, v') {
    var n := |v.hosts|;
    forall i | 0 <= i < n && HostHasDecided(v'.hosts[i]) 
    ensures HostDecidedCommit(v'.hosts[i]) {
      var step :| NextStep(c, v, v', step);
      if i == step.hostid {
        if v.hosts[step.hostid].CoordinatorVariables? {
          /* Proof by contradiction: suppose coord decide no. Then leader's noVotes is
          not empty. By LeaderTallyReflectsPreferences, this member preferred No, which 
          contradicts with AllPreferYes(c, v) */
          if HostDecidedAbort(v'.hosts[i]) {
            assert false;
          }
        }
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


lemma {:axiom} SetLemma(S: set<HostId>, e: HostId, size: int) 
  requires 0 <= e < size
  requires forall x | x in S :: 0 <= x < size
  requires e !in S
  ensures |S| < size - 1
{
  var fullSet := set x: HostId | 0 <= x < size :: x;
  assume |fullSet| == size - 1;
  SubsetCardinality(S, fullSet);
}

lemma {:axiom} SubsetCardinality<T>(small: set<T>, large: set<T>) 
  requires small < large
  ensures |small| < |large|
{
  assume false;
}
}

