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
  && ReceivePromiseValidity(c, v)
  && ReceiveAcceptValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_ReceivePromiseValidity();
  reveal_ReceiveAcceptValidity();
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
  InvNextReceivePromiseValidity(c, v, v');
  InvNextReceiveAcceptValidity(c, v, v');
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

// Leader updates receivedPromises based on Promise messages
ghost predicate {:opaque} ReceivePromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, acc |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaders|  // this can be derived
    && LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v.History(i).leaders[idx], acc)
  :: 
    (exists msg :: 
      && msg in v.network.sentMsgs
      && LeaderHost.ReceivePromiseConclusion(c.leaders[idx], v.History(i).leaders[idx], acc, msg)
    )
}

// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
ghost predicate {:opaque} ReceiveAcceptValidity(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc, i | 
    && c.ValidLearnerIdx(idx)
    && v.ValidHistoryIdx(i)
    && LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v.History(i).learners[idx], acc, vb)
  ::
   (exists msg :: 
      && msg in v.network.sentMsgs
      && LearnerHost.ReceiveAcceptConclusion(c.learners[idx], v.History(i).learners[idx], acc, vb, msg)
   )
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

lemma InvNextReceiveAcceptValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ReceiveAcceptValidity(c, v)
  requires Next(c, v, v')
  ensures ReceiveAcceptValidity(c, v')
{
  reveal_ReceiveAcceptValidity();
  VariableNextProperties(c, v, v');
  forall idx, i, acc, vb |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.learners|
    && LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v'.History(i).learners[idx], acc, vb)
  ensures
    (exists msg :: 
      && msg in v'.network.sentMsgs
      && LearnerHost.ReceiveAcceptConclusion(c.learners[idx], v'.History(i).learners[idx], acc, vb, msg)
    )
  {
    if i == |v'.history| - 1 {
      if !LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v.History(i-1).learners[idx], acc, vb) {
        // trigger
      }
    }
  }
}

lemma InvNextReceivePromiseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ReceivePromiseValidity(c, v)
  requires Next(c, v, v')
  ensures ReceivePromiseValidity(c, v')
{
  reveal_ReceivePromiseValidity();
  VariableNextProperties(c, v, v');
  forall idx, i, acc |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaders|
    && LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v'.History(i).leaders[idx], acc)
  ensures
    (exists msg :: 
      && msg in v'.network.sentMsgs
      && LeaderHost.ReceivePromiseConclusion(c.leaders[idx], v'.History(i).leaders[idx], acc, msg)
    )
  {
    if i == |v'.history| - 1 {
      if !LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v.History(i-1).leaders[idx], acc) {
        // trigger
      }
    }
  }
}

}  // end module PaxosProof

