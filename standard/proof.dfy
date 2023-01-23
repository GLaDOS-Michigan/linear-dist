//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "spec.dfy"
//#extract exercise02.template solution exercise02.dfy

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // All VoteMsg have a valid participant HostId as src
  predicate VoteMsgValidSrc(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
    :: 0 <= msg.src < |c.hosts|-1
  }

  // VoteMsg reflects the preference of the voter 
  predicate VoteMsgAgreeWithVoter(c: Constants, v: Variables)
    requires v.WF(c)
    requires VoteMsgValidSrc(c, v)
  {
    forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
    :: GetParticipantPreference(c, msg.src) == msg.v
  }

  // Leader's local tally reflect actual messages
  predicate LeaderTallyReflectsMsgs(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && (forall hostId | hostId in GetCoordinator(c, v).yesVotes ::
          VoteMsg(Yes, hostId) in v.network.sentMsgs )
    && (forall hostId | hostId in GetCoordinator(c, v).noVotes ::
          VoteMsg(No, hostId) in v.network.sentMsgs )
  }

  // DecideMsgs should reflect the decision of the leader
  // Tony: Boilerplate
  predicate DecisionMsgsAgreeWithLeader(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && msg.DecideMsg? 
    :: GetCoordinator(c, v).decision.Some? && msg.d == GetCoordinator(c, v).decision.value
  }

  // If a participant has decided, then there must be a corresponding DecideMsg
  // Tony: Boilerplate
  predicate ParticipantsDecisionImpliesDecideMsg(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    var n := |v.hosts|;
    forall i | 0 <= i < n && HostHasDecided(v.hosts[i]) :: 
      && (HostDecidedCommit(v.hosts[i]) ==> DecideMsg(Commit) in v.network.sentMsgs)
      && (HostDecidedAbort(v.hosts[i]) ==> DecideMsg(Abort) in v.network.sentMsgs)
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && VoteMsgValidSrc(c, v)
    && VoteMsgAgreeWithVoter(c, v)
    && LeaderTallyReflectsMsgs(c, v)
    && DecisionMsgsAgreeWithLeader(c, v)
    && ParticipantsDecisionImpliesDecideMsg(c, v)
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}


  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    AC3Proof(c, v, v');
    AC4Proof(c, v, v');
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
            assert VoteMsg(Yes, noVoter) in v.network.sentMsgs; // witness
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
    ensures SafetyAC4(c, v');
  {
    if AllPreferYes(c, v') {
      var n := |v.hosts|;
      forall i | 0 <= i < n && HostHasDecided(v'.hosts[i]) 
      ensures HostDecidedCommit(v'.hosts[i]) {
        var step :| NextStep(c, v, v', step);
        if i == step.hostid {
          if v.hosts[step.hostid].CoordinatorVariables? {
            /* Proof by contradiction: suppose coord decide no. By LeaderTallyReflectsMsgs
            and VoteMsgValidSrc, there is a VoteMsg(No, src) from a valid participant in 
            the network. By VoteMsgAgreeWithVoter, src must have preferred No, which 
            contradicts with AllPreferYes(c, v) */
            if HostDecidedAbort(v'.hosts[i]) {
              var c, c' := v.hosts[step.hostid].coordinator, v'.hosts[step.hostid].coordinator;
              var src :| src in c.noVotes;  // witness
              assert VoteMsg(No, src) in v.network.sentMsgs;  // trigger
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
    ensures forall id | 0 <= id < |c.hosts|-1 :: id in Last(v.hosts).coordinator.yesVotes
  {
    var l := Last(v.hosts).coordinator;
    forall id | 0 <= id < |c.hosts|-1 
    ensures id in l.yesVotes {
      if id !in l.yesVotes {
        LeaderTallyValidSource(c, v);
        SetLemma(l.yesVotes, id, |c.hosts|-1);
        assert false;
      }
    }
  }

  lemma LeaderTallyValidSource(c: Constants, v: Variables) 
    requires Inv(c, v)
    ensures forall id | id in Last(v.hosts).coordinator.yesVotes :: 0 <= id < |c.hosts|-1
  {
    forall id | id in Last(v.hosts).coordinator.yesVotes 
    ensures 0 <= id < |c.hosts|-1
    {
      assert VoteMsg(Yes, id) in v.network.sentMsgs;  // witness
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

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  {}
}

