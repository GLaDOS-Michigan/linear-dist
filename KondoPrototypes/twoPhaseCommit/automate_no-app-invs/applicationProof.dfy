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
  true
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
  AC1Proof(c, v, v');
  AC3Proof(c, v, v');
  AC4Proof(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i | v.ValidHistoryIdx(i) 
  :: 
    var hosts := v.History(i);
    LeaderTallyReflectsPreferencesInHistory(c, hosts)
}

ghost predicate LeaderTallyReflectsPreferencesInHistory(c: Constants, hosts: Hosts)
  requires hosts.WF(c)
{
  var n := |c.participants|;
  && (forall hostId | hostId in hosts.GetCoordinator(c).yesVotes ::
      0 <= hostId < n && GetParticipantPreference(c, hostId) == Yes )
  && (forall hostId | hostId in hosts.GetCoordinator(c).noVotes ::
        0 <= hostId < n && GetParticipantPreference(c, hostId) == No )
}

lemma InvImpliesLeaderTallyReflectsPreferences(c: Constants, v: Variables) 
  requires  && v.WF(c)
            && MessageInv(c, v)
            && MonotonicityInv(c, v)
  ensures LeaderTallyReflectsPreferences(c, v)
{
  forall i | v.ValidHistoryIdx(i) 
  ensures LeaderTallyReflectsPreferencesInHistory(c, v.History(i))
  {
    var hosts := v.History(i);
    var n := |c.participants|;
    forall hostId | hostId in hosts.GetCoordinator(c).yesVotes
    ensures
      0 <= hostId < n && GetParticipantPreference(c, hostId) == Yes
    {
      assert CoordinatorHost.ReceiveVoteTrigger1(c.coordinator[0], v.History(i).coordinator[0], hostId);
      reveal_ReceiveVoteValidity1();
      var j, msg :| && j < i
        && v.ValidHistoryIdxStrict(j)
        && msg in v.network.sentMsgs
        && !CoordinatorHost.ReceiveVoteTrigger1(c.coordinator[0], v.History(j).coordinator[0], hostId)
        && CoordinatorHost.ReceiveVoteTrigger1(c.coordinator[0], v.History(j+1).coordinator[0], hostId)
        && CoordinatorHost.ReceiveVote(c.coordinator[0], v.History(j).coordinator[0], v.History(j+1).coordinator[0], msg);
      assert 0 <= hostId < n && GetParticipantPreference(c, hostId) == Yes;
    }

    forall hostId | hostId in hosts.GetCoordinator(c).noVotes
    ensures
      0 <= hostId < n && GetParticipantPreference(c, hostId) == No
    {
      assert CoordinatorHost.ReceiveVoteTrigger2(c.coordinator[0], v.History(i).coordinator[0], hostId);
      reveal_ReceiveVoteValidity2();
      var j, msg :| && j < i
        && v.ValidHistoryIdxStrict(j)
        && msg in v.network.sentMsgs
        && !CoordinatorHost.ReceiveVoteTrigger2(c.coordinator[0], v.History(j).coordinator[0], hostId)
        && CoordinatorHost.ReceiveVoteTrigger2(c.coordinator[0], v.History(j+1).coordinator[0], hostId)
        && CoordinatorHost.ReceiveVote(c.coordinator[0], v.History(j).coordinator[0], v.History(j+1).coordinator[0], msg);
      assert 0 <= hostId < n && GetParticipantPreference(c, hostId) == No;
    }
  }
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
  requires  && v'.WF(c)
            && MessageInv(c, v')
            && MonotonicityInv(c, v')
  ensures AC3Contrapos(c, v')
{
  InvImpliesLeaderTallyReflectsPreferences(c, v');
  AC3ContraposLemma(c, v);
  VariableNextProperties(c, v, v');
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v'.Last()) {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    if dsStep.CoordinatorStep? {
        /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
        a Yes vote from all participants, including noVoter. This is a contradiction */
        var l, l' := v.Last().GetCoordinator(c), v'.Last().GetCoordinator(c);
        if l.decision.WONone? && l'.decision == WOSome(Commit) {
          YesVotesContainsAllParticipantsWhenFull(c, v, |v.history|-1);
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
  if  (!AllPreferYes(c) && CoordinatorHasDecided(c, v.Last())) {
    assert v.Last().GetCoordinator(c).decision.value != Commit;  // trigger
  }
}

lemma AC4Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires MessageInv(c, v')
  requires  && v'.WF(c)
            && MessageInv(c, v')
            && MonotonicityInv(c, v')
  ensures SafetyAC4(c, v')
{
  InvImpliesLeaderTallyReflectsPreferences(c, v');
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables, i: int)
  requires Inv(c, v)
  requires v.ValidHistoryIdx(i)
  requires |v.History(i).GetCoordinator(c).yesVotes| == |c.participants|
  ensures forall id | 0 <= id < |c.participants| :: id in v.History(i).GetCoordinator(c).yesVotes
{
  InvImpliesLeaderTallyReflectsPreferences(c, v);
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
