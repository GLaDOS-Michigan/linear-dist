include "messageInvariants.dfy"

module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MessageInvariants
import opened Obligations

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Monotonicity bundle
ghost predicate MonotonicityInv(c: Constants, v: Variables) 
  requires v.WF(c)
{
  CoordinatorDecisionMonotonic(c, v)
}

ghost predicate CoordinatorDecisionMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i, j |
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && v.History(i).GetCoordinator(c).decision.Some?
  ::
    v.History(i).GetCoordinator(c).decision == v.History(j).GetCoordinator(c).decision
}


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
  forall i | v.ValidHistoryIdx(i) :: 
    var hosts := v.History(i);
    && (forall hostId | hostId in hosts.GetCoordinator(c).yesVotes ::
          0 <= hostId < n-1 && hosts.GetParticipantPreference(c, hostId) == Yes )
    && (forall hostId | hostId in hosts.GetCoordinator(c).noVotes ::
          0 <= hostId < n-1 && hosts.GetParticipantPreference(c, hostId) == No )
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
  assert MonotonicityInv(c, v') by {
    InvNextCoordinatorDecisionMonotonic(c, v, v');
  }
  LeaderTallyReflectsPreferencesInductive(c, v, v');
  AC3Proof(c, v, v');
  AC4Proof(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/


lemma InvNextCoordinatorDecisionMonotonic(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires CoordinatorDecisionMonotonic(c, v)
  requires Next(c, v, v') 
  ensures CoordinatorDecisionMonotonic(c, v')
{
  VariableNextProperties(c, v, v');
}


lemma LeaderTallyReflectsPreferencesInductive(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderTallyReflectsPreferences(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma AC3Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderTallyReflectsPreferences(c, v')
  ensures AC3Contrapos(c, v')
{
  var n := |c.hosts|;
  VariableNextProperties(c, v, v');
  /* Proof by contradiction */
  if !AllPreferYes(c)
     && (exists i ::
        && 0 <= i < n 
        && HostHasDecided(v'.Last().hosts[i])
        && HostDecidedCommit(v'.Last().hosts[i])
    )
  {
    var noVoter :| 0 <= noVoter < n-1 && c.hosts[noVoter].participant.preference == No;
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    // var h, h' := v.Last().hosts[step.actor], v'.Last().hosts[step.actor];
    var traitor :|  0 <= traitor < n 
        && HostHasDecided(v'.Last().hosts[traitor])
        && HostDecidedCommit(v'.Last().hosts[traitor]);
    var t, t' := v.Last().hosts[traitor], v'.Last().hosts[traitor];
    if dsStep.actor == traitor {
      if c.ValidCoordinatorId(traitor) {
        /*  Suppose coordinator decided Commit. Then it must have a Yes vote from all 
        participants, including noVoter. This is a contradiction */
        if !HostDecidedCommit(t) {
          var msgOps := dsStep.msgOps;
          YesVotesContainsAllParticipantsWhenFull(c, v, |v.history|-1);
          assert v.Last().GetParticipantPreference(c, noVoter) == Yes;  // witness
          assert false;
        }
      } else {
        /* Suppose participant decided Commit. Then it must have
        received a Commit message from the coordinator. This implies that the coordinator
        had committed in state v, which contradicts AC3Contrapos(c, v). */
      }
    }
  }
}

lemma AC4Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires MessageInv(c, v')
  requires LeaderTallyReflectsPreferences(c, v')
  ensures SafetyAC4(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables, i: int)
  requires Inv(c, v)
  requires v.ValidHistoryIdx(i)
  requires |Last(v.History(i).hosts).coordinator.yesVotes| == |c.hosts|-1
  ensures forall id | 
    && 0 <= id < |c.hosts|-1 :: id in v.History(i).GetCoordinator(c).yesVotes
{
  var l := v.History(i).GetCoordinator(c);
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

