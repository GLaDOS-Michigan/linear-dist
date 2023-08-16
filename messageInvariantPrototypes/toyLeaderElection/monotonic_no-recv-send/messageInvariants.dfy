// User level proofs of application invariants

include "spec.dfy"


module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem

// Message Invariant: self inductive
ghost predicate ValidMessages(c: Constants, v: Variables) 
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
ghost predicate LeaderMsgImpliesLocalQuorum(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Leader?
  :: SetIsQuorum(c.hostConstants[msg.src].clusterSize, v.hosts[msg.src].receivedVotes)
}

// Message Invariant: self inductive
ghost predicate ReceivedVotesValidity(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, voter | c.ValidIdx(idx) && voter in v.hosts[idx].receivedVotes 
  :: Vote(voter, idx) in v.network.sentMsgs
}

// Message Invariant: self inductive
ghost predicate VoteMsgImpliesVoterVotedForCandidate(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote?
  :: msg.candidate in v.hosts[msg.voter].voted
}

ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessages(c, v)
  && LeaderMsgImpliesLocalQuorum(c, v)
  && ReceivedVotesValidity(c, v)
  && VoteMsgImpliesVoterVotedForCandidate(c, v)
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
  // triggers
  assert LeaderMsgImpliesLocalQuorum(c, v');
  assert MessageInv(c, v');
}

}

