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
      && ServerHost.SendResponseMsg(c.GetServer(), v.History(i).GetServer(c), v.History(i+1).GetServer(c), msg)
  )
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
      && ClientHost.SendRequestMsg(c.GetClient(src), v.History(i).GetClient(c, src), v.History(i+1).GetClient(c, src), msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidHistory(c, v)
  && RequestMsgValidSrc(c, v)
  && ServerSendValidity(c, v)
  && ClientSendValidity(c, v)
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
  // InvNextServerRecvValidity(c, v, v');
  InvNextClientSendValidity(c, v, v');
  // InvNextClientRecvValidity(c, v, v');
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
      && ServerHost.SendResponseMsg(c.GetServer(), v'.History(i).GetServer(c), v'.History(i+1).GetServer(c), msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ServerHost.SendResponseMsg(c.GetServer(), v'.History(i).GetServer(c), v'.History(i+1).GetServer(c), msg);
    }
  }
}

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
      && ClientHost.SendRequestMsg(c.GetClient(src), v'.History(i).GetClient(c, src), v'.History(i+1).GetClient(c, src), msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var src := msg.r.clientId;
      var i := |v.history|-1;
      assert ClientHost.SendRequestMsg(c.GetClient(src), v'.History(i).GetClient(c, src), v'.History(i+1).GetClient(c, src), msg);
    }
  }
}
}  // end module MessageInvariants

