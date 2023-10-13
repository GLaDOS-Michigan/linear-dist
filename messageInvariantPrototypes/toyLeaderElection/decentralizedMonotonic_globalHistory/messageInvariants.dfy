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
      case VoteReq(candidate) => c.ValidHostId(candidate)
      case Vote(voter, candidate) => c.ValidHostId(voter)
}

// Send invariant
ghost predicate VoteReqSendValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.VoteReq?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && Host.VoteReqSendFunc(c.hosts[msg.candidate], v.History(i).hosts[msg.candidate], v.History(i+1).hosts[msg.candidate], msg)
  )
}

// Send invariant
ghost predicate VoteSendValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.Vote?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && Host.VoteSendFunc(c.hosts[msg.voter], v.History(i).hosts[msg.voter], v.History(i+1).hosts[msg.voter], msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidHistory(c, v)
  && ValidMessages(c, v)
  && VoteReqSendValidity(c, v)
  && VoteSendValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidHistory(c, v);
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  assert ValidMessages(c, v');
  InvNextValidHistory(c, v, v');
  InvNextVoteReqSendValidity(c, v, v');
  InvNextVoteSendValidity(c, v, v');
}

lemma InvNextVoteReqSendValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ValidMessages(c, v)
  requires VoteReqSendValidity(c, v)
  requires Next(c, v, v')
  ensures VoteReqSendValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.VoteReq?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && Host.VoteReqSendFunc(c.hosts[msg.candidate], v'.History(i).hosts[msg.candidate], v'.History(i+1).hosts[msg.candidate], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.VoteReqSendFunc(c.hosts[msg.candidate], v'.History(i).hosts[msg.candidate], v'.History(i+1).hosts[msg.candidate], msg);
    }
  }
}

lemma InvNextVoteSendValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ValidMessages(c, v)
  requires VoteSendValidity(c, v)
  requires Next(c, v, v')
  ensures VoteSendValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.Vote?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && Host.VoteSendFunc(c.hosts[msg.voter], v'.History(i).hosts[msg.voter], v'.History(i+1).hosts[msg.voter], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.VoteSendFunc(c.hosts[msg.voter], v'.History(i).hosts[msg.voter], v'.History(i+1).hosts[msg.voter], msg);
    }
  }
}
}

