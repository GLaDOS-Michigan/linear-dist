// Network-level "boilerplate" invariants that are application-independent

include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// All VoteMsg have a valid participant HostId as src
ghost predicate VoteMsgValidSrc(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
  :: c.ValidParticipantId( msg.src)
}

// Every VoteMsg is received according to CoordinatorHost.NextReceiveStepRecvFunc
ghost predicate RecvVoteMsgValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg | 
    && 1 <= i < |v.history|
    && c.ValidCoordinatorId(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.VoteMsg?
  :: 
    && msg in v.network.sentMsgs
    && CoordinatorHost.NextReceiveStepRecvFunc(c.hosts[idx].coordinator, v.History(i-1).hosts[idx].coordinator, v.History(i).hosts[idx].coordinator, msg)
}

// Every DecideMsg is sent according to a CoordinatorHost.NextDecisionStepSendFunc
ghost predicate SendDecideMsgValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires VoteMsgValidSrc(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.DecideMsg?
  :: 
  (exists i ::
      && 0 <= i < |v.history|-1
      && CoordinatorHost.NextDecisionStepSendFunc(c.GetCoordinator(), v.History(i).GetCoordinator(c), v.History(i+1).GetCoordinator(c), msg)
  )
}

// Every VoteReqMsg is received according to ParticipantHost.NextReceiveVoteReqStepRecvFunc
ghost predicate RecvVoteReqMsgValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg| 
    && 1 <= i < |v.history|
    && c.ValidParticipantId(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.VoteReqMsg?
  :: 
    && msg in v.network.sentMsgs
    && ParticipantHost.NextReceiveVoteReqStepRecvFunc(c.hosts[idx].participant, v.History(i-1).hosts[idx].participant, v.History(i).hosts[idx].participant, msg)
}

// Every DecideMsg is received according to ParticipantHost.NextReceiveDecisionStepRecvFunc
ghost predicate RecvDecideMsgValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg | 
    && 1 <= i < |v.history|
    && c.ValidParticipantId(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.DecideMsg?
  :: 
    && msg in v.network.sentMsgs
    && ParticipantHost.NextReceiveDecisionStepRecvFunc(c.hosts[idx].participant, v.History(i-1).hosts[idx].participant, v.History(i).hosts[idx].participant, msg)
}

// Every VoteMsg is sent according to ParticipantHost.NextSendVoteStepSendFunc
ghost predicate SendVoteMsgValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires VoteMsgValidSrc(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.VoteMsg?
  :: 
  (exists i ::
      && v.ValidHistoryIdx(i)
      && ParticipantHost.NextSendVoteStepSendFunc(c.hosts[msg.src].participant, v.History(i).hosts[msg.src].participant, msg)
  )
}


ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidHistory(c, v)
  && VoteMsgValidSrc(c, v)
  && RecvVoteMsgValidity(c, v)
  && SendDecideMsgValidity(c, v)
  && RecvVoteReqMsgValidity(c, v)
  && RecvDecideMsgValidity(c, v)
  && SendVoteMsgValidity(c, v)
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
  InvNextValidHistory(c, v, v');
  InvNextRecvVoteMsgValidity(c, v, v');
  InvNextSendDecideMsgValidity(c, v, v');
  InvNextRecvVoteReqMsgValidity(c, v, v');
  InvNextRecvDecideMsgValidity(c, v, v');
}

/***************************************************************************************
*                                         Proofs                                       *
***************************************************************************************/

lemma InvNextRecvVoteMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires RecvVoteMsgValidity(c, v)
  requires Next(c, v, v')
  ensures RecvVoteMsgValidity(c, v')
{
  reveal_ValidHistory();
  VariableNextProperties(c, v, v');
}

lemma InvNextRecvVoteReqMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires RecvVoteReqMsgValidity(c, v)
  requires Next(c, v, v')
  ensures RecvVoteReqMsgValidity(c, v')
{
  reveal_ValidHistory();
  VariableNextProperties(c, v, v');
}

lemma InvNextSendDecideMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires VoteMsgValidSrc(c, v)
  requires SendDecideMsgValidity(c, v)
  requires Next(c, v, v')
  ensures SendDecideMsgValidity(c, v')
{
  reveal_ValidHistory();
  VariableNextProperties(c, v, v');
}

lemma InvNextRecvDecideMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires RecvDecideMsgValidity(c, v)
  requires Next(c, v, v')
  ensures RecvDecideMsgValidity(c, v')
{
  reveal_ValidHistory();
  VariableNextProperties(c, v, v');
}

lemma InvNextSendVoteMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires VoteMsgValidSrc(c, v)
  requires SendVoteMsgValidity(c, v)
  requires Next(c, v, v')
  ensures SendVoteMsgValidity(c, v')
{
  reveal_ValidHistory();
  VariableNextProperties(c, v, v');
}

}

