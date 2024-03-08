include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem

// All VoteMsg have a valid participant HostId as src
ghost predicate VoteMsgValidSrc(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
  :: c.ValidParticipantId( msg.src)
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
      && v.ValidHistoryIdxStrict(i)
      && CoordinatorHost.SendDecideMsg(c.GetCoordinator(), v.History(i).GetCoordinator(c), v.History(i+1).GetCoordinator(c), msg)
  )
}

// Every VoteMsg is sent according to ParticipantHost.SendVote
ghost predicate SendVoteMsgValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires VoteMsgValidSrc(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.VoteMsg?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && ParticipantHost.SendVoteMsg(c.participants[msg.src], v.History(i).participants[msg.src], v.History(i+1).participants[msg.src], msg)
  )
}


ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidHistory(c, v)
  && VoteMsgValidSrc(c, v)
  // && RecvVoteMsgValidity(c, v)
  && SendDecideMsgValidity(c, v)
  // && RecvVoteReqMsgValidity(c, v)
  // && RecvDecideMsgValidity(c, v)
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
  InvNextSendDecideMsgValidity(c, v, v');
  InvNextSendVoteMsgValidity(c, v, v');
}

/***************************************************************************************
*                                         Proofs                                       *
***************************************************************************************/


lemma InvNextSendDecideMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires VoteMsgValidSrc(c, v)
  requires SendDecideMsgValidity(c, v)
  requires Next(c, v, v')
  ensures SendDecideMsgValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.DecideMsg?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && CoordinatorHost.SendDecideMsg(c.GetCoordinator(), v'.History(i).GetCoordinator(c), v'.History(i+1).GetCoordinator(c), msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert CoordinatorHost.SendDecideMsg(c.GetCoordinator(), v'.History(i).GetCoordinator(c), v'.History(i+1).GetCoordinator(c), msg);
    }
  }
}

lemma InvNextSendVoteMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires VoteMsgValidSrc(c, v)
  requires SendVoteMsgValidity(c, v)
  requires Next(c, v, v')
  ensures SendVoteMsgValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.VoteMsg?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && ParticipantHost.SendVoteMsg(c.participants[msg.src], v'.History(i).participants[msg.src], v'.History(i+1).participants[msg.src], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ParticipantHost.SendVoteMsg(c.participants[msg.src], v'.History(i).participants[msg.src], v'.History(i+1).participants[msg.src], msg);
    }
  }
}

}

