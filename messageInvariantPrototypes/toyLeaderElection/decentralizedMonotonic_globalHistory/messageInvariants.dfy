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

// Receive invariant
ghost predicate VoteReqRecvValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg| 
    && v.ValidHistoryIdxStrict(i)
    && c.ValidHostId(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.VoteReq?
  :: 
    && msg in v.network.sentMsgs
    && Host.VoteReqRecvFunc(c.hosts[idx], v.History(i).hosts[idx], v.History(i+1).hosts[idx], msg)
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

// Receive invariant
ghost predicate VoteRecvValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg| 
    && v.ValidHistoryIdxStrict(i)
    && c.ValidHostId(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.Vote?
  :: 
    && msg in v.network.sentMsgs
    && Host.VoteRecvFunc(c.hosts[idx], v.History(i).hosts[idx], v.History(i+1).hosts[idx], msg)
}


ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidHistory(c, v)
  && ValidMessages(c, v)
  && VoteReqSendValidity(c, v)
  // && VoteReqRecvValidity(c, v)
  && VoteSendValidity(c, v)
  // && VoteRecvValidity(c, v)
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
  // InvNextVoteReqRecvValidity(c, v, v');
  InvNextVoteSendValidity(c, v, v');
  // InvNextVoteRecvValidity(c, v, v');
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

lemma InvNextVoteReqRecvValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires VoteReqRecvValidity(c, v)
  requires Next(c, v, v')
  ensures VoteReqRecvValidity(c, v')
{}

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

lemma InvNextVoteRecvValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires VoteRecvValidity(c, v)
  requires Next(c, v, v')
  ensures VoteRecvValidity(c, v')
{}

}

