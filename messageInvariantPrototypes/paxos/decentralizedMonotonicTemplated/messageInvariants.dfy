include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self-inductive
// Every message in the network has a valid source
ghost predicate ValidMessageSrc(c: Constants, v: Variables) 
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
  && ValidMessageSrc(c, v)
  // From Leader transitions
  && SendPrepareValidity(c, v)
  && SendProposeValidity(c, v)
  // From Acceptor transitions
  && SendPromiseValidity(c, v)
  && SendAcceptValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidMessageSrc(c, v, v');
  InvNextSendPrepareValidity(c, v, v');
  InvNextSendProposeValidity(c, v, v');
  InvNextSendPromiseValidity(c, v, v');
  InvNextSendAcceptValidity(c, v, v');
}

/***************************************************************************************
*                                     Leader Host                                      *
***************************************************************************************/

// Every Prepare is sent according to LeaderHost.PrepareSendFunc
ghost predicate SendPrepareValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall msg | IsPrepareMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.PrepareSendFunc(c.leaderConstants[msg.bal], v.History(i).leaders[msg.bal], v.History(i+1).leaders[msg.bal], msg)
  )
}

// Every Propose is sent according to LeaderHost.ProposeSendFunc
ghost predicate SendProposeValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall msg | IsProposeMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.ProposeSendFunc(c.leaderConstants[msg.bal], v.History(i).leaders[msg.bal], v.History(i+1).leaders[msg.bal], msg)
  )
}

/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/

// Every Propose is sent according to AcceptorHost.PromiseSendFunc
ghost predicate SendPromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall msg | IsPromiseMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && AcceptorHost.PromiseSendFunc(c.acceptorConstants[msg.acc], v.History(i).acceptors[msg.acc], v.History(i+1).acceptors[msg.acc], msg)
  )
}

// Every Accept is sent according to AcceptorHost.AcceptSendFunc
ghost predicate SendAcceptValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall msg | IsAcceptMessage(v, msg)
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && AcceptorHost.AcceptSendFunc(c.acceptorConstants[msg.acc], v.History(i).acceptors[msg.acc], v.History(i+1).acceptors[msg.acc], msg)
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
  VariableNextProperties(c, v, v');
}

lemma InvNextSendPrepareValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires SendPrepareValidity(c, v)
  requires Next(c, v, v')
  ensures SendPrepareValidity(c, v')
{
  forall msg | IsPrepareMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && LeaderHost.PrepareSendFunc(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsPrepareMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert LeaderHost.PrepareSendFunc(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg);
    }
  }
}

lemma InvNextSendProposeValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires SendProposeValidity(c, v)
  requires Next(c, v, v')
  ensures SendProposeValidity(c, v')
{
  forall msg | IsProposeMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && LeaderHost.ProposeSendFunc(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsProposeMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert LeaderHost.ProposeSendFunc(c.leaderConstants[msg.bal], v'.History(i).leaders[msg.bal], v'.History(i+1).leaders[msg.bal], msg);
    }
  }
}

lemma InvNextSendPromiseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires SendPromiseValidity(c, v)
  requires Next(c, v, v')
  ensures SendPromiseValidity(c, v')
{
  forall msg | IsPromiseMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && AcceptorHost.PromiseSendFunc(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsPromiseMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert AcceptorHost.PromiseSendFunc(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg);
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
  forall msg | IsAcceptMessage(v', msg)
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && AcceptorHost.AcceptSendFunc(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg)
  ) {
    VariableNextProperties(c, v, v');
    if !IsAcceptMessage(v, msg) {
      // witness and trigger
      var i := |v'.history|-2;
      assert AcceptorHost.AcceptSendFunc(c.acceptorConstants[msg.acc], v'.History(i).acceptors[msg.acc], v'.History(i+1).acceptors[msg.acc], msg);
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

lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  ensures 1 < |v'.history|
  ensures |v.history| == |v'.history| - 1
  ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)
  ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)
{
  assert 0 < |v.history|;
  assert 1 < |v'.history|;
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

