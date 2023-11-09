include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate SendPrepareValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Prepare?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPrepare(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg)
  )
}

ghost predicate SendProposeValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Propose?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPropose(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg)
  )
}

ghost predicate SendPromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Promise?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && AcceptorHost.SendPromise(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], msg)
  )
}

ghost predicate SendAcceptValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Accept?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && AcceptorHost.SendAccept(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], msg)
  )
}

ghost predicate {:opaque} ReceivePromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, acc |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaders|
    && LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v.History(i).leaders[idx], acc)
  ::
    (exists j, msg ::
      && j < i
      && v.ValidHistoryIdxStrict(j)
      && msg in v.network.sentMsgs
      && !LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v.History(j).leaders[idx], acc)
      && LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v.History(j+1).leaders[idx], acc)
      && LeaderHost.ReceivePromise(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], msg)
    )
}

ghost predicate {:opaque} ReceiveAcceptValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, acc, vb |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.learners|
    && LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v.History(i).learners[idx], acc,vb)
  ::
    (exists j, msg ::
      && j < i
      && v.ValidHistoryIdxStrict(j)
      && msg in v.network.sentMsgs
      && !LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v.History(j).learners[idx], acc,vb)
      && LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v.History(j+1).learners[idx], acc,vb)
      && LearnerHost.ReceiveAccept(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], msg)
    )
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && SendPrepareValidity(c, v)
  && SendProposeValidity(c, v)
  && SendPromiseValidity(c, v)
  && SendAcceptValidity(c, v)
  && ReceivePromiseValidity(c, v)
  && ReceiveAcceptValidity(c, v)
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_ReceivePromiseValidity();
  reveal_ReceiveAcceptValidity();
}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidVariables(c, v, v');
  InvNextSendPrepareValidity(c, v, v');
  InvNextSendProposeValidity(c, v, v');
  InvNextSendPromiseValidity(c, v, v');
  InvNextSendAcceptValidity(c, v, v');
  InvNextReceivePromiseValidity(c, v, v');
  InvNextReceiveAcceptValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/


lemma InvNextSendPrepareValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendPrepareValidity(c, v)
  requires Next(c, v, v')
  ensures SendPrepareValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Prepare?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPrepare(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert LeaderHost.SendPrepare(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg);
    }
  }
}

lemma InvNextSendProposeValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendProposeValidity(c, v)
  requires Next(c, v, v')
  ensures SendProposeValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Propose?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPropose(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert LeaderHost.SendPropose(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg);
    }
  }
}

lemma InvNextSendPromiseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendPromiseValidity(c, v)
  requires Next(c, v, v')
  ensures SendPromiseValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Promise?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && AcceptorHost.SendPromise(c.acceptors[msg.Src()], v'.History(i).acceptors[msg.Src()], v'.History(i+1).acceptors[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert AcceptorHost.SendPromise(c.acceptors[msg.Src()], v'.History(i).acceptors[msg.Src()], v'.History(i+1).acceptors[msg.Src()], msg);
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
    && AcceptorHost.SendAccept(c.acceptors[msg.Src()], v'.History(i).acceptors[msg.Src()], v'.History(i+1).acceptors[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert AcceptorHost.SendAccept(c.acceptors[msg.Src()], v'.History(i).acceptors[msg.Src()], v'.History(i+1).acceptors[msg.Src()], msg);
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
  forall idx, i, acc |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaders|
    && LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v'.History(i).leaders[idx], acc)
  ensures
    (exists j, msg ::
      && j < i
      && v'.ValidHistoryIdxStrict(j)
      && msg in v.network.sentMsgs
      && !LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v'.History(j).leaders[idx], acc)
      && LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v'.History(j+1).leaders[idx], acc)
      && LeaderHost.ReceivePromise(c.leaders[idx], v'.History(j).leaders[idx], v'.History(j+1).leaders[idx], msg)
    )
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      if !LeaderHost.ReceivePromiseTrigger(c.leaders[idx], v.Last().leaders[idx], acc)
      {
        // witness and triggers
        var j := |v.history|-1;
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        var msg := dsStep.msgOps.recv.value;
        assert LeaderHost.ReceivePromise(c.leaders[idx], v'.History(j).leaders[idx], v'.History(j+1).leaders[idx], msg);
      }
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
  forall idx, i, acc, vb |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.learners|
    && LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v'.History(i).learners[idx], acc,vb)
  ensures
    (exists j, msg ::
      && j < i
      && v'.ValidHistoryIdxStrict(j)
      && msg in v.network.sentMsgs
      && !LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v'.History(j).learners[idx], acc,vb)
      && LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v'.History(j+1).learners[idx], acc,vb)
      && LearnerHost.ReceiveAccept(c.learners[idx], v'.History(j).learners[idx], v'.History(j+1).learners[idx], msg)
    )
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      if !LearnerHost.ReceiveAcceptTrigger(c.learners[idx], v.Last().learners[idx], acc,vb)
      {
        // witness and triggers
        var j := |v.history|-1;
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        var msg := dsStep.msgOps.recv.value;
        assert LearnerHost.ReceiveAccept(c.learners[idx], v'.History(j).learners[idx], v'.History(j+1).learners[idx], msg);
      }
    }
  }
}

} // end module MessageInvariants