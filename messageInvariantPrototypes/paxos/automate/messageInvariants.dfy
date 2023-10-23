include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// Message bundle
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidVariables(c, v)
  // Send Invariants
  && SendPrepareValidity(c, v)
  && SendProposeValidity(c, v)
  && SendPromiseValidity(c, v)
  && SendAcceptValidity(c, v)
  // Receive Invariants
  && LeaderValidReceivedPromiseMsgs(c, v)
  && LearnerValidReceivedAcceptMsgs(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_LeaderValidReceivedPromiseMsgs();
  reveal_LearnerValidReceivedAcceptMsgs();
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidVariables(c, v, v');
  InvNextValidMessageSrc(c, v, v');
  InvNextSendPrepareValidity(c, v, v');
  InvNextSendProposeValidity(c, v, v');
  InvNextSendPromiseValidity(c, v, v');
  InvNextSendAcceptValidity(c, v, v');
  InvNextLeaderValidReceivedPromiseMsgs(c, v, v');
  InvNextLearnerValidReceivedAccepts(c, v, v');
}

/***************************************************************************************
*                               Template Send Invariants                               *
***************************************************************************************/

// Every Prepare is sent according to LeaderHost.SendPrepare
ghost predicate SendPrepareValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg |  msg in v.network.sentMsgs && msg.Prepare?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPrepare(c.leaders[msg.bal], v.History(i).leaders[msg.bal], v.History(i+1).leaders[msg.bal], msg)
  )
}

// Every Propose is sent according to LeaderHost.SendPropose
ghost predicate SendProposeValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg |  msg in v.network.sentMsgs && msg.Propose?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPropose(c.leaders[msg.bal], v.History(i).leaders[msg.bal], v.History(i+1).leaders[msg.bal], msg)
  )
}

// Every Propose is sent according to AcceptorHost.SendPromise
ghost predicate SendPromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg |  msg in v.network.sentMsgs && msg.Promise?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendPromise(c.acceptors[msg.acc], v.History(i).acceptors[msg.acc], v.History(i+1).acceptors[msg.acc], msg)
  )
}

// Every Accept is sent according to AcceptorHost.SendAccept
ghost predicate SendAcceptValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Accept?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendAccept(c.acceptors[msg.acc], v.History(i).acceptors[msg.acc], v.History(i+1).acceptors[msg.acc], msg)
  )
}

/***************************************************************************************
*                               Custom Receive Invariants                              *
***************************************************************************************/

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
ghost predicate {:opaque} LeaderValidReceivedPromiseMsgs(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, i, acc |
    && c.ValidLeaderIdx(ldr)
    && v.ValidHistoryIdx(i)
    && acc in v.History(i).leaders[ldr].receivedPromises
  :: 
    (exists prom: Message :: 
      && prom.Promise?
      && prom in v.network.sentMsgs
      && prom.bal == ldr
      && prom.acc == acc
      && (prom.vbOpt.Some?
          ==> 
          && v.History(i).leaders[ldr].highestHeardBallot.Some?
          && prom.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
        )
    )
}

// certified self-inductive
// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
ghost predicate {:opaque} LearnerValidReceivedAcceptMsgs(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc, i | 
    && c.ValidLearnerIdx(idx)
    && v.ValidHistoryIdx(i)
    && vb in v.History(i).learners[idx].receivedAccepts
    && acc in v.History(i).learners[idx].receivedAccepts[vb]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/

lemma InvNextValidMessageSrc(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires Next(c, v, v')
  ensures ValidMessages(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextSendPrepareValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidMessages(c, v) && ValidMessages(c, v')
  requires SendPrepareValidity(c, v)
  requires Next(c, v, v')
  ensures SendPrepareValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Prepare?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPrepare(c.leaders[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v'.history|-2;
      assert LeaderHost.SendPrepare(c.leaders[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg);
    }
  }
}

lemma InvNextSendProposeValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidMessages(c, v) && ValidMessages(c, v')
  requires SendProposeValidity(c, v)
  requires Next(c, v, v')
  ensures SendProposeValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Propose?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPropose(c.leaders[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v'.history|-2;
      assert LeaderHost.SendPropose(c.leaders[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg);
    }
  }
}

lemma InvNextSendPromiseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidMessages(c, v) && ValidMessages(c, v')
  requires SendPromiseValidity(c, v)
  requires Next(c, v, v')
  ensures SendPromiseValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Promise?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendPromise(c.acceptors[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v'.history|-2;
      assert AcceptorHost.SendPromise(c.acceptors[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg);
    }
  }
}

lemma InvNextSendAcceptValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendAcceptValidity(c, v)
  requires Next(c, v, v')
  ensures SendAcceptValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Accept?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendAccept(c.acceptors[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v'.history|-2;
      assert AcceptorHost.SendAccept(c.acceptors[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg);
    }
  }
}

lemma InvNextLearnerValidReceivedAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerValidReceivedAcceptMsgs(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAcceptMsgs(c, v')
{
  reveal_LearnerValidReceivedAcceptMsgs();
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderValidReceivedPromiseMsgs(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LeaderValidReceivedPromiseMsgs(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromiseMsgs(c, v')
{
  reveal_LeaderValidReceivedPromiseMsgs();
  VariableNextProperties(c, v, v');
}

}  // end module PaxosProof

