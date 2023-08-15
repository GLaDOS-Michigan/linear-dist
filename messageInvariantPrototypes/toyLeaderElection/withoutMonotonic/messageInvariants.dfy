include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import Host
import opened DistributedSystem

// Message Invariant: self inductive
// Property of send
ghost predicate ValidMessageSource(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: match msg 
      case VoteReq(candidate) => c.ValidIdx(candidate)
      case Vote(voter, candidate) => c.ValidIdx(voter)
      case Leader(src) => c.ValidIdx(src)
      case _ => true
}

// Message Invariant: self inductive
// Property of Send
ghost predicate LeaderMsgImpliesLocalQuorum(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidMessageSource(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Leader?
  :: SetIsQuorum(c.hostConstants[msg.src].clusterSize, v.hosts[msg.src].receivedVotes)
}

// Message Invariant: self inductive
// Property of Receive
ghost predicate ReceivedVotesValidity(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, voter | c.ValidIdx(idx) && voter in v.hosts[idx].receivedVotes 
  :: Vote(voter, idx) in v.network.sentMsgs
}

// Message Invariant: self inductive
// Property of Send
ghost predicate VoteMsgImpliesVoterVoted(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSource(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote?
  :: v.hosts[msg.voter].voted
}

ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessageSource(c, v)
  && LeaderMsgImpliesLocalQuorum(c, v)
  && ReceivedVotesValidity(c, v)
  && VoteMsgImpliesVoterVoted(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextLeaderMsgImpliesLocalQuorum(c, v, v');
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/

lemma InvNextLeaderMsgImpliesLocalQuorum(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSource(c, v)
  requires LeaderMsgImpliesLocalQuorum(c, v)
  requires Next(c, v, v')
  ensures LeaderMsgImpliesLocalQuorum(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Leader?
  ensures SetIsQuorum(c.hostConstants[msg.src].clusterSize, v'.hosts[msg.src].receivedVotes)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actorIdx, dsStep.msgOps;
    var step :| Host.NextStep(c.hostConstants[actor], v.hosts[actor], v'.hosts[actor], step, msgOps);
    if !step.VictoryStep? {
      assert msg in v.network.sentMsgs;  // trigger
      assert SetIsQuorum(c.hostConstants[msg.src].clusterSize, v'.hosts[msg.src].receivedVotes); // trigger
    }
  }
}


}

