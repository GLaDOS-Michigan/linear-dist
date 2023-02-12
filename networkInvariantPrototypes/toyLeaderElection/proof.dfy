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

  // Application Invariant: requires message invariants to be inductive
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
    MessageInvInductive(c, v, v');
    SafetyProof(c, v');
  }

  lemma SafetyProof(c: Constants, v': Variables) 
    requires MessageInv(c, v')
    requires VotersVoteOnce(c, v')
    ensures Safety(c, v')
  {
    /* Proof by contradiction: Assume two leaders were elected in v', L1 and L2.
    * Then by quorum intersection, there is a common rogueId in both L1.receivedVotes and
    * L2.receivedVotes. This violates VotersVoteOnce, via ReceivedVotesValidity
    */
    if !Safety(c, v') {
      var m1 :| m1 in v'.network.sentMsgs && m1.Leader?;      
      var m2 :| m2 in v'.network.sentMsgs && m2.Leader? && m1.src != m2.src;
      var clusterSize := |c.hostConstants|;
      var allHosts := (set x | 0 <= x < |c.hostConstants|);
      SetComprehensionSize(|c.hostConstants|);
      var rv1, rv2 :=  v'.hosts[m1.src].receivedVotes, v'.hosts[m2.src].receivedVotes;
      var rogueId := QuorumIntersection(allHosts, rv1, rv2);  // witness
      assert false;
    }
  }
}

