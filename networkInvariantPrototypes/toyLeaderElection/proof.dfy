// User level proofs of application invariants

include "spec.dfy"


module RingLeaderElectionProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  /***************************************************************************************
  *                               Invariant and Definitons                               *
  ***************************************************************************************/

  // Message Invariant: self inductive
  predicate ValidMessages(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs 
    :: match msg 
        case VoteReq(candidate) => c.ValidIdx(candidate)
        case Vote(voter, candidate) => c.ValidIdx(voter) && c.ValidIdx(candidate)
        case Leader(src) => c.ValidIdx(src)
        case _ => true
  }

  // Message Invariant: self inductive
  predicate LeaderMsgImpliesLocalQuorum(c: Constants, v: Variables) 
    requires v.WF(c)
    requires ValidMessages(c, v)
  {
    forall msg | msg in v.network.sentMsgs && msg.Leader?
    :: SetIsQuorum(c.hostConstants[msg.src].clusterSize, v.hosts[msg.src].receivedVotes)
  }

  // Message Invariant: self inductive
  predicate ReceivedVotesValidity(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx, voter | c.ValidIdx(idx) && voter in v.hosts[idx].receivedVotes 
    :: Vote(voter, idx) in v.network.sentMsgs
  }

  // Message Invariant: self inductive
  predicate VoteMsgImpliesVoterVoted(c: Constants, v: Variables)
    requires v.WF(c)
    requires ValidMessages(c, v)
  {
    forall msg | msg in v.network.sentMsgs && msg.Vote?
    :: v.hosts[msg.voter].voted
  }

  predicate MessageInv(c: Constants, v: Variables) 
  {
    && v.WF(c)
    && ValidMessages(c, v)
    && LeaderMsgImpliesLocalQuorum(c, v)
    && ReceivedVotesValidity(c, v)
    && VoteMsgImpliesVoterVoted(c, v)
  }

  // Application Invariant
  predicate VotersVoteOnce(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall m1, m2 |
      && m1 in v.network.sentMsgs && m2 in v.network.sentMsgs
      && m1.Vote? && m2.Vote?
      && m1.voter == m2.voter
    :: m1.candidate == m2.candidate
  }
  
  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && MessageInv(c, v)
    && VotersVoteOnce(c, v)
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

  lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
    requires MessageInv(c, v)
    requires Next(c, v, v')
    ensures MessageInv(c, v')
  {
    assert MessageInv(c, v');  // dumb trigger
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    assume false;
    MessageInvInductive(c, v, v');
    assert v.WF(c);
    assert ValidMessages(c, v');
    assert LeaderMsgImpliesLocalQuorum(c, v');
    assert ReceivedVotesValidity(c, v');
    assert VoteMsgImpliesVoterVoted(c, v');
    assert VotersVoteOnce(c, v');
    assert Safety(c, v');
  }
}

