// User level proofs of application invariants

include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem

// Send invariant
ghost predicate SendVoteReqValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.VoteReq?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && Host.SendVoteReq(c.hosts[msg.candidate], v.History(i).hosts[msg.candidate], v.History(i+1).hosts[msg.candidate], msg)
  )
}

// Send invariant
ghost predicate SendVoteValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.Vote?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && Host.SendVote(c.hosts[msg.voter], v.History(i).hosts[msg.voter], v.History(i+1).hosts[msg.voter], msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidHistory(c, v)
  && ValidMessages(c, v)
  && SendVoteReqValidity(c, v)
  && SendVoteValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidVariables(c, v, v');
  InvNextSendVoteReqValidity(c, v, v');
  InvNextSendVoteValidity(c, v, v');
}

lemma InvNextSendVoteReqValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ValidMessages(c, v)
  requires SendVoteReqValidity(c, v)
  requires Next(c, v, v')
  ensures SendVoteReqValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.VoteReq?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && Host.SendVoteReq(c.hosts[msg.candidate], v'.History(i).hosts[msg.candidate], v'.History(i+1).hosts[msg.candidate], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.SendVoteReq(c.hosts[msg.candidate], v'.History(i).hosts[msg.candidate], v'.History(i+1).hosts[msg.candidate], msg);
    }
  }
}

lemma InvNextSendVoteValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ValidMessages(c, v)
  requires SendVoteValidity(c, v)
  requires Next(c, v, v')
  ensures SendVoteValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.Vote?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && Host.SendVote(c.hosts[msg.voter], v'.History(i).hosts[msg.voter], v'.History(i+1).hosts[msg.voter], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.SendVote(c.hosts[msg.voter], v'.History(i).hosts[msg.voter], v'.History(i+1).hosts[msg.voter], msg);
    }
  }
}
}

