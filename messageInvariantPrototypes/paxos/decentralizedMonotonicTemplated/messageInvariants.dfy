include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self-inductive
// Every message in the network has a valid source
ghost predicate {:opaque} ValidMessageSrc(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: 
  match msg 
    case Prepare(bal) => c.ValidLeaderIdx(bal)
    case Promise(_, acc, _) => c.ValidAcceptorIdx(acc)
    case Propose(bal, _) => c.ValidLeaderIdx(bal)
    case Accept(_, acc) => c.ValidAcceptorIdx(acc)
}

// Message bundle
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidHistory(c, v)
  && ValidMessageSrc(c, v)
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
  reveal_ValidMessageSrc();
  reveal_LeaderValidReceivedPromiseMsgs();
  reveal_LearnerValidReceivedAcceptMsgs();
  InitImpliesValidHistory(c, v);
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidHistory(c, v, v');
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
  requires ValidMessageSrc(c, v)
{
  reveal_ValidMessageSrc();
  forall msg | IsPrepareMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPrepare(c.leaderConstants[msg.bal], v.History(i).leaders[msg.bal], v.History(i+1).leaders[msg.bal], msg)
  )
}

// Every Propose is sent according to LeaderHost.SendPropose
ghost predicate SendProposeValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  reveal_ValidMessageSrc();
  forall msg | IsProposeMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPropose(c.leaderConstants[msg.bal], v.History(i).leaders[msg.bal], v.History(i+1).leaders[msg.bal], msg)
  )
}

// Every Propose is sent according to AcceptorHost.SendPromise
ghost predicate SendPromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  reveal_ValidMessageSrc();
  forall msg | IsPromiseMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendPromise(c.acceptorConstants[msg.acc], v.History(i).acceptors[msg.acc], v.History(i+1).acceptors[msg.acc], msg)
  )
}

// Every Accept is sent according to AcceptorHost.SendAccept
ghost predicate SendAcceptValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  reveal_ValidMessageSrc();
  forall msg | IsAcceptMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendAccept(c.acceptorConstants[msg.acc], v.History(i).acceptors[msg.acc], v.History(i+1).acceptors[msg.acc], msg)
  )
}

/***************************************************************************************
*                               Custom Receive Invariants                              *
***************************************************************************************/

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
// ghost predicate {:opaque} LeaderValidReceivedPromiseMsgs(c: Constants, v: Variables)
//   requires v.WF(c)
// {
//   forall ldr, i, acc |
//     && c.ValidLeaderIdx(ldr)
//     && v.ValidHistoryIdx(i)
//     && acc in v.History(i).leaders[ldr].receivedPromises
//   :: 
//     (exists prom :: 
//       && IsPromiseMessage(v, prom)
//       && prom.bal == ldr
//       && prom.acc == acc
//       && (prom.vbOpt.Some?
//           ==> 
//           && v.History(i).leaders[ldr].highestHeardBallot.Some?
//           && prom.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
//         )
//     )
// }

// Leader updates receivedPromises based on Promise messages
ghost predicate {:opaque} LeaderValidReceivedPromiseMsgs(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, acc |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaderConstants|
    && LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v.History(i).leaders[idx], acc)
  :: 
    (exists j, msg :: 
      && j < i
      && v.ValidHistoryIdxStrict(j)
      && msg in v.network.sentMsgs
      && !LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v.History(j).leaders[idx], acc)
      && LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v.History(j+1).leaders[idx], acc)
      && LeaderHost.ReceivePromise(c.leaderConstants[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], msg)
    )
}

// certified self-inductive
// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
// ghost predicate {:opaque} LearnerValidReceivedAcceptMsgs(c: Constants, v: Variables) 
//   requires v.WF(c)
// {
//   forall idx, vb, acc, i | 
//     && c.ValidLearnerIdx(idx)
//     && v.ValidHistoryIdx(i)
//     && vb in v.History(i).learners[idx].receivedAccepts
//     && acc in v.History(i).learners[idx].receivedAccepts[vb]
//   ::
//     Accept(vb, acc) in v.network.sentMsgs
// }

// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
ghost predicate {:opaque} LearnerValidReceivedAcceptMsgs(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc, i | 
    && c.ValidLearnerIdx(idx)
    && v.ValidHistoryIdx(i)
    && LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v.History(i).learners[idx], acc, vb)
  ::
   (exists j, msg :: 
       && j < i
       && v.ValidHistoryIdxStrict(j)
       && msg in v.network.sentMsgs
       && !LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v.History(j).learners[idx], acc, vb)
       && LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v.History(j+1).learners[idx], acc, vb)
       && LearnerHost.ReceiveAccept(c.learnerConstants[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], msg)
    )
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/

lemma InvNextValidMessageSrc(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires Next(c, v, v')
  ensures ValidMessageSrc(c, v')
{
  reveal_ValidMessageSrc();
  VariableNextProperties(c, v, v');
}

lemma InvNextSendPrepareValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidMessageSrc(c, v) && ValidMessageSrc(c, v')
  requires SendPrepareValidity(c, v)
  requires Next(c, v, v')
  ensures SendPrepareValidity(c, v')
{
  reveal_ValidMessageSrc();
  forall msg | IsPrepareMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPrepare(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsPrepareMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert LeaderHost.SendPrepare(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg);
    }
  }
}

lemma InvNextSendProposeValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidMessageSrc(c, v) && ValidMessageSrc(c, v')
  requires SendProposeValidity(c, v)
  requires Next(c, v, v')
  ensures SendProposeValidity(c, v')
{
  reveal_ValidMessageSrc();
  forall msg | IsProposeMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPropose(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsProposeMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert LeaderHost.SendPropose(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg);
    }
  }
}

lemma InvNextSendPromiseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidMessageSrc(c, v) && ValidMessageSrc(c, v')
  requires SendPromiseValidity(c, v)
  requires Next(c, v, v')
  ensures SendPromiseValidity(c, v')
{
  reveal_ValidMessageSrc();
  forall msg | IsPromiseMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendPromise(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsPromiseMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert AcceptorHost.SendPromise(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg);
    }
  }
}

lemma InvNextSendAcceptValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires SendAcceptValidity(c, v)
  requires Next(c, v, v')
  ensures SendAcceptValidity(c, v')
{
  reveal_ValidMessageSrc();
  forall msg | IsAcceptMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && AcceptorHost.SendAccept(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsAcceptMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert AcceptorHost.SendAccept(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg);
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
  forall idx, vb, acc, i |
    && 0 <= idx < |c.learnerConstants|
    && v'.ValidHistoryIdx(i)
    && LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v'.History(i).learners[idx], acc, vb)
  ensures
    (exists j, msg :: 
      && j < i
      && v'.ValidHistoryIdxStrict(j)
      && msg in v'.network.sentMsgs
      && !LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v'.History(j).learners[idx], acc, vb)
      && LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v'.History(j+1).learners[idx], acc, vb)
      && LearnerHost.ReceiveAccept(c.learnerConstants[idx], v'.History(j).learners[idx], v'.History(j+1).learners[idx], msg)
    )
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      if !LearnerHost.ReceiveAcceptTrigger(c.learnerConstants[idx], v.Last().learners[idx], acc, vb) {
        // witnesses and triggers
        var j := |v.history|-1;
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        var msg := dsStep.msgOps.recv.value;
        assert LearnerHost.ReceiveAccept(c.learnerConstants[idx], v'.History(j).learners[idx], v'.History(j+1).learners[idx], msg);
      }
    }
  }
}

lemma InvNextLeaderValidReceivedPromiseMsgs(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LeaderValidReceivedPromiseMsgs(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromiseMsgs(c, v')
{
  reveal_LeaderValidReceivedPromiseMsgs();
  forall idx, i, acc |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaderConstants|
    && LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v'.History(i).leaders[idx], acc)
  ensures
    (exists j, msg :: 
      && j < i
      && v'.ValidHistoryIdxStrict(j)
      && msg in v'.network.sentMsgs
      && !LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v'.History(j).leaders[idx], acc)
      && LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v'.History(j+1).leaders[idx], acc)
      && LeaderHost.ReceivePromise(c.leaderConstants[idx], v'.History(j).leaders[idx], v'.History(j+1).leaders[idx], msg)
    )
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      if !LeaderHost.ReceivePromiseTrigger(c.leaderConstants[idx], v.Last().leaders[idx], acc) {
        // witnesses and triggers
        var j := |v.history|-1;
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        var msg := dsStep.msgOps.recv.value;
        assert LeaderHost.ReceivePromise(c.leaderConstants[idx], v'.History(j).leaders[idx], v'.History(j+1).leaders[idx], msg);
      }
    }
  }
}

/***************************************************************************************
*                                        Utils                                         *
***************************************************************************************/

ghost predicate IsPrepareMessage(v: Variables, m: Message) {
  && m.Prepare?
  && m in v.network.sentMsgs
}

ghost predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

ghost predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

ghost predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}

lemma GetAcceptorSet(c: Constants, v: Variables)
returns (accSet: set<AcceptorId>)
  requires v.WF(c)
  ensures forall a :: c.ValidAcceptorIdx(a) <==> a in accSet
  ensures |accSet| == 2 * c.f + 1
{
  assert v.History(0).WF(c);  // trigger for |c.acceptorConstants| == 2 * c.f+1
  accSet := set a |  0 <= a < |c.acceptorConstants|;
  SetComprehensionSize(|c.acceptorConstants|);
}
}  // end module PaxosProof

