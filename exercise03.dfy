//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"
//#extract exercise02.template solution exercise02.dfy

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations



  // // DecideMsgs should reflect the decision of the leader
  // // Tony: Boilerplate
  // predicate DecisionMsgsAgreeWithTally(c: Constants, v: Variables)
  //   requires v.WF(c)
  // {
  //   forall msg | msg in v.network.sentMsgs && msg.DecideMsg? 
  //   :: GetCoordinator(c, v).decision.Some? && msg.d == GetCoordinator(c, v).decision.value
  // }

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

  // There can only be one DecideMsg in the network
  // I think this is implied by from DecisionMsgsAgreeWithLeaderDecision
  // predicate OnlyOneDecisionMsg(c: Constants, v: Variables)
  //   requires v.WF(c)
  // {
  //   var sentMsgs := v.network.sentMsgs;
  //   forall m1, m2 | m1 in sentMsgs && m1.DecideMsg? && m2 in sentMsgs && m2.DecideMsg? 
  //   :: m1 == m2
  // }

  // If a DecideMsg(Commit) message is in the network, every host that decides must 
  // decide Commit, and likewise for Abort.
  // I think this is implied by OnlyOneDecisionMsg
  // predicate HostsAgreeWithDecisionMsg(c: Constants, v: Variables)
  //   requires v.WF(c)
  // {
  //   var n := |v.hosts|;
  //   && (DecideMsg(Commit) in v.network.sentMsgs ==> 
  //     forall i | 0 <= i < n && HostHasDecided(v.hosts[i]) :: HostDecidedCommit(v.hosts[i])
  //   )
  //   && (DecideMsg(Abort) in v.network.sentMsgs ==> 
  //     forall i | 0 <= i < n && HostHasDecided(v.hosts[i]) :: HostDecidedAbort(v.hosts[i])
  //   )
  // }



  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && DecisionMsgsAgreeWithLeader(c, v)
    && ParticipantsDecisionImpliesDecideMsg(c, v)
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}


  /*
    - DecisionMsgsAgreeWithLeader(c, v) and ParticipantsDecisionImpliesDecideMsg(c, v) implies AC1
      AC1 + these two invariants are inductive.
  */
  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    assert SafetyAC1(c, v');
    assert Inv(c, v');
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  {}
}

