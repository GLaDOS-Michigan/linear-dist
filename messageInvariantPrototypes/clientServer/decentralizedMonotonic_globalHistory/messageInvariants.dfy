include "spec.dfy"

module MessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self inductive, modulo requires
// Every request message in the network has a proper source
ghost predicate RequestMsgValidSrc(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: c.ValidClientIdx(req.r.clientId)
}

// Send invariant
ghost predicate ServerSendValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires RequestMsgValidSrc(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.ResponseMsg?
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && ServerHost.NextProcessStepSendFunc(c.GetServer(), v.History(i).GetServer(c), v.History(i+1).GetServer(c), msg)
  )
}

// Receive invariant
ghost predicate ServerRecvValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg| 
    && 1 <= i < |v.history|
    && c.ValidServerIdx(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.RequestMsg?
  :: 
    && msg in v.network.sentMsgs
    && ServerHost.NextReceiveStepRecvFunc(c.hosts[idx].server, v.History(i-1).hosts[idx].server, v.History(i).hosts[idx].server, msg)
}

// Send invariant
ghost predicate ClientSendValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires RequestMsgValidSrc(c, v)
{
  forall msg | 
    && msg in v.network.sentMsgs
    && msg.RequestMsg?
  :: 
  (exists i ::
      && var src := msg.r.clientId;
      && v.ValidHistoryIdxStrict(i)
      && ClientHost.NextRequestStepSendFunc(c.GetClient(src), v.History(i).GetClient(c, src), v.History(i+1).GetClient(c, src), msg)
  )
}

// Receive invariant
ghost predicate ClientRecvValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg| 
    && 1 <= i < |v.history|
    && c.ValidClientIdx(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
    && msg.ResponseMsg?
  :: 
    && msg in v.network.sentMsgs
    && ClientHost.NextReceiveRespStepRecvFunc(c.hosts[idx].client, v.History(i-1).hosts[idx].client, v.History(i).hosts[idx].client, msg)
}


ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidHistory(c, v)
  && RequestMsgValidSrc(c, v)
  && ServerSendValidity(c, v)
  && ServerRecvValidity(c, v)
  && ClientSendValidity(c, v)
  && ClientRecvValidity(c, v)
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
  InvNextServerSendValidity(c, v, v');
  InvNextServerRecvValidity(c, v, v');
  InvNextClientSendValidity(c, v, v');
  InvNextClientRecvValidity(c, v, v');
}

/***************************************************************************************
*                                         Proofs                                       *
***************************************************************************************/

lemma InvNextServerSendValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires RequestMsgValidSrc(c, v)
  requires ServerSendValidity(c, v)
  requires Next(c, v, v')
  ensures ServerSendValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.ResponseMsg?
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && ServerHost.NextProcessStepSendFunc(c.GetServer(), v'.History(i).GetServer(c), v'.History(i+1).GetServer(c), msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ServerHost.NextProcessStepSendFunc(c.GetServer(), v'.History(i).GetServer(c), v'.History(i+1).GetServer(c), msg);
    }
  }
}

lemma InvNextServerRecvValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ServerRecvValidity(c, v)
  requires Next(c, v, v')
  ensures ServerRecvValidity(c, v')
{}

lemma InvNextClientSendValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires RequestMsgValidSrc(c, v)
  requires ClientSendValidity(c, v)
  requires Next(c, v, v')
  ensures ClientSendValidity(c, v')
{
  forall msg | 
    && msg in v'.network.sentMsgs
    && msg.RequestMsg?
  ensures
  (exists i ::
      && var src := msg.r.clientId;
      && v'.ValidHistoryIdxStrict(i)
      && ClientHost.NextRequestStepSendFunc(c.GetClient(src), v'.History(i).GetClient(c, src), v'.History(i+1).GetClient(c, src), msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var src := msg.r.clientId;
      var i := |v.history|-1;
      assert ClientHost.NextRequestStepSendFunc(c.GetClient(src), v'.History(i).GetClient(c, src), v'.History(i+1).GetClient(c, src), msg);
    }
  }
}

lemma InvNextClientRecvValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ClientRecvValidity(c, v)
  requires Next(c, v, v')
  ensures ClientRecvValidity(c, v')
{}


}  // end module MessageInvariants

