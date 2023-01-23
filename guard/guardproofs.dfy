//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "spec.dfy"
//#extract exercise02.template solution exercise02.dfy

module TwoPCInvariantGuardsProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // All VoteMsg have a valid participant HostId as src
  // Boilerplate
  predicate VoteMsgValidSrc(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
    :: 0 <= msg.src < |c.hosts|-1
  }

  // VoteMsg reflects the preference of the voter 
  // Boilterplate
  predicate VoteMsgAgreeWithVoter(c: Constants, v: Variables)
    requires v.WF(c)
    requires VoteMsgValidSrc(c, v)
  {
    forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
    :: GetParticipantPreference(c, msg.src) == msg.v
  }

  // Leader's local tally reflect actual messages
  // Boilterplate
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

  predicate GuardInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && VoteMsgValidSrc(c, v)
    && VoteMsgAgreeWithVoter(c, v)
    && LeaderTallyReflectsMsgs(c, v)
    && DecisionMsgsAgreeWithLeader(c, v)
    && ParticipantsDecisionImpliesDecideMsg(c, v)
  }

  lemma InitImpliesGuardInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures GuardInv(c, v)
  {}

  lemma GuardInvInductive(c: Constants, v: Variables, v': Variables)
    requires GuardInv(c, v)
    requires Next(c, v, v')
    ensures GuardInv(c, v')
  {}
}

