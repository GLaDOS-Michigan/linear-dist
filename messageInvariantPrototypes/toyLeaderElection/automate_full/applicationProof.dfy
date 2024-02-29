include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"


module ToyLeaderElectionProof {
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

// Application Invariant: Host having a vote implies voter nominated that host
ghost predicate HasVoteImpliesVoterNominates(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, nominee: nat, voter: nat 
  {:trigger v.History(i).hosts[voter], v.History(i).hosts[nominee]}
  {:trigger v.History(i).hosts[voter], c.ValidHostId(nominee)}
  {:trigger v.History(i).hosts[nominee], c.ValidHostId(voter)}
  {:trigger c.ValidHostId(voter), c.ValidHostId(nominee), v.History(i)}
  :: (
    && v.ValidHistoryIdx(i)
    && c.ValidHostId(nominee)
    && c.ValidHostId(voter)
    && v.History(i).hosts[nominee].HasVoteFrom(voter)
  ==>
    v.History(i).hosts[voter].Nominates(nominee))
}

ghost predicate ReceivedVotesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, h: nat 
  {:trigger v.History(i).hosts[h]} 
  {:trigger c.ValidHostId(h), v.History(i)} 
  :: (
      && v.ValidHistoryIdx(i)
      && c.ValidHostId(h)
    ==>
      v.History(i).hosts[h].receivedVotes <= (set x | 0 <= x < |c.hosts|))
}

ghost predicate IsLeaderImpliesHasQuorum(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, h: nat 
  {:trigger v.History(i).hosts[h]}
  {:trigger c.hosts[h], v.History(i)}
  {:trigger v.History(i).IsLeader(c, h)}
  {:trigger c.ValidHostId(h), v.History(i)}
  :: (
    && v.ValidHistoryIdx(i)
    && c.ValidHostId(h) 
    && v.History(i).IsLeader(c, h)
  ==> SetIsQuorum(c.hosts[h].clusterSize, v.History(i).hosts[h].receivedVotes))
}

// Monotonicity bundle
ghost predicate MonotonicityInv(c: Constants, v: Variables) 
  requires v.WF(c)
{
  HostNomineeMonotonic(c, v)
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && ReceivedVotesValid(c, v)
  && IsLeaderImpliesHasQuorum(c, v)  // this says that the set size doesn't shrink
  && HasVoteImpliesVoterNominates(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
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
  InitImpliesMonotonicityInv(c, v);
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  InvNextReceivedVotesValid(c, v, v');
  InvNextIsLeaderImpliesHasQuorum(c, v, v');
  InvNextHasVoteImpliesVoterNominates(c, v, v');
  SafetyProof(c, v');
}


/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvNextReceivedVotesValid(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ReceivedVotesValid(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextIsLeaderImpliesHasQuorum(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures IsLeaderImpliesHasQuorum(c, v')
  ensures ReceivedVotesValid(c, v')
{
  VariableNextProperties(c, v, v');
  var allHosts := (set x | 0 <= x < |c.hosts|);
  forall h: nat | c.ValidHostId(h) && v'.Last().IsLeader(c, h)
  ensures
    && SetIsQuorum(c.hosts[h].clusterSize, v'.Last().hosts[h].receivedVotes)
  {}
}

lemma InvNextHasVoteImpliesVoterNominates(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures HasVoteImpliesVoterNominates(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma SafetyProof(c: Constants, v': Variables) 
  requires v'.WF(c)
  requires ApplicationInv(c, v')
  ensures Safety(c, v')
{
  /* Proof by contradiction: Suppose two leaders were elected in v', L1 and L2.
  * Then by quorum intersection, there is a common rogueId in both L1.receivedVotes and
  * L2.receivedVotes. This violates HasVoteImpliesVoterNominates
  */
  if !Safety(c, v') {
    var l1: nat :| c.ValidHostId(l1) && v'.Last().IsLeader(c, l1);
    var l2: nat :| c.ValidHostId(l2) && v'.Last().IsLeader(c, l2) && l2 != l1;
    var allHosts := (set x | 0 <= x < |c.hosts|);
    SetComprehensionSize(|c.hosts|);

    var rv1, rv2 :=  v'.Last().hosts[l1].receivedVotes, v'.Last().hosts[l2].receivedVotes;
    var rogueId := QuorumIntersection(allHosts, rv1, rv2);  // witness

    assert v'.Last().hosts[rogueId].nominee == WOSome(l1);  // trigger
    assert v'.Last().hosts[rogueId].nominee == WOSome(l2);  // trigger
    assert false;
  }
}
} // end module ToyLeaderElectionProof

