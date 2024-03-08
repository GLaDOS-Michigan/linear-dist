include "monotonicityInvariants.dfy"
include "messageInvariants.dfy"


module ToyLeaderElectionProof {
import opened Types
import opened UtilitiesLibrary
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
  forall i, nominee: nat, voter: nat | 
    && v.ValidHistoryIdx(i)
    && c.ValidHostId(nominee)
    && c.ValidHostId(voter)
    && v.History(i).hosts[nominee].HasVoteFrom(voter)
  ::
    v.History(i).hosts[voter].Nominates(nominee)
}

ghost predicate ReceivedVotesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, h: nat |
    && v.ValidHistoryIdx(i)
    && c.ValidHostId(h)
  :: 
    v.History(i).hosts[h].receivedVotes <= (set x | 0 <= x < |c.hosts|)
}

ghost predicate IsLeaderImpliesHasQuorum(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, h: nat | 
    && v.ValidHistoryIdx(i)
    && c.ValidHostId(h) 
    && v.History(i).IsLeader(c, h)
  :: SetIsQuorum(c.hosts[h].clusterSize, v.History(i).hosts[h].receivedVotes)
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
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires ReceivedVotesValid(c, v)
  requires Next(c, v, v')
  ensures ReceivedVotesValid(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextIsLeaderImpliesHasQuorum(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires IsLeaderImpliesHasQuorum(c, v)
  requires Next(c, v, v')
  ensures IsLeaderImpliesHasQuorum(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextHasVoteImpliesVoterNominates(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ReceivedVotesValid(c, v)
  requires HasVoteImpliesVoterNominates(c, v)
  requires Next(c, v, v')
  requires MessageInv(c, v')
  requires HostNomineeMonotonic(c, v')
  ensures HasVoteImpliesVoterNominates(c, v')
{
  forall i, nominee: nat, voter: nat | 
    && v'.ValidHistoryIdx(i)
    && c.ValidHostId(nominee)
    && c.ValidHostId(voter)
    && v'.History(i).hosts[nominee].HasVoteFrom(voter)
  ensures
    v'.History(i).hosts[voter].Nominates(nominee)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history|-1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if !v.Last().hosts[nominee].HasVoteFrom(voter) {
        // actor == nominee;
        var hc, h, h' := c.hosts[actor], v.Last().hosts[actor], v'.Last().hosts[actor];
        var step :| Host.NextStep(hc, h, h', step, msgOps);
        if step.RecvVoteStep? {
          var msg := msgOps.recv.value;
        }  else {
          ReceiveVotesUpdatedInRecvVoteStep(hc, h, h', step, msgOps);
          assert false;
        }
      }
    }
  }
}

lemma SafetyProof(c: Constants, v': Variables) 
  // requires MessageInv(c, v')
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
    var clusterSize := |c.hosts|;
    var allHosts := (set x | 0 <= x < |c.hosts|);
    SetComprehensionSize(|c.hosts|);

    assert v'.Last() == v'.History(|v'.history|-1);  // trigger
    var rv1, rv2 :=  v'.Last().hosts[l1].receivedVotes, v'.Last().hosts[l2].receivedVotes;
    var rogueId := QuorumIntersection(allHosts, rv1, rv2);  // witness
    assert && v'.ValidHistoryIdx(|v'.history|-1)  // trigger
            && c.ValidHostId(l1)
            && c.ValidHostId(rogueId)
            && v'.History(|v'.history|-1).hosts[l1].HasVoteFrom(rogueId);
    assert false;
  }
}

lemma ReceiveVotesUpdatedInRecvVoteStep(hc: Host.Constants, h: Host.Variables, h': Host.Variables, step:  Host.Step, msgOps: MessageOps)
  requires Host.NextStep(hc, h, h', step, msgOps)
  requires !step.RecvVoteStep? 
  ensures h'.receivedVotes == h.receivedVotes
{}

} // end module ToyLeaderElectionProof

