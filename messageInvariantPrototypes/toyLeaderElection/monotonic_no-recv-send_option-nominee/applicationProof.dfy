// User level proofs of application invariants

include "messageInvariants.dfy"


module ToyLeaderElectionProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MessageInvariants
import opened Obligations

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Application Invariant: Host having a vote implies voter nominated that host
ghost predicate HasVoteImpliesVoterNominates(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall nominee, voter | 
    && c.ValidIdx(nominee)
    && c.ValidIdx(voter)
    && v.hosts[nominee].HasVoteFrom(voter)
  ::
    v.hosts[voter].Nominates(nominee)
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  HasVoteImpliesVoterNominates(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
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
  MessageInvInductive(c, v, v');
  SafetyProof(c, v');
}

lemma SafetyProof(c: Constants, v: Variables) 
  requires MessageInv(c, v)
  requires HasVoteImpliesVoterNominates(c, v)
  ensures Safety(c, v)
{
  /* Proof by contradiction: Assume two leaders were elected in v', L1 and L2.
  * Then by quorum intersection, there is a common rogueId in both L1.receivedVotes and
  * L2.receivedVotes. This violates VotersVoteOnce, via ReceivedVotesValidity
  */
  if !Safety(c, v) {
    var m1 :| m1 in v.network.sentMsgs && m1.Leader?;      
    var m2 :| m2 in v.network.sentMsgs && m2.Leader? && m1.src != m2.src;
    var clusterSize := |c.hostConstants|;
    var allHosts := (set x | 0 <= x < |c.hostConstants|);
    SetComprehensionSize(|c.hostConstants|);
    var rv1, rv2 :=  v.hosts[m1.src].receivedVotes, v.hosts[m2.src].receivedVotes;
    var rogueId := QuorumIntersection(allHosts, rv1, rv2);  // witness
    assert false;
  }
}
}

