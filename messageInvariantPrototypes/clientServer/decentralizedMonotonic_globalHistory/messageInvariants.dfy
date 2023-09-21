include "spec.dfy"

module MessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self inductive, modulo requires
// Every request message in the network has a proper source
ghost predicate ValidRequestMsgSource(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: c.ValidClientIdx(req.r.clientId)
}

// certified self inductive, modulo requires
// Every request message in the network comes from the source's request set
// Property of Send
ghost predicate ValidRequestMessage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidRequestMsgSource(c, v)
{
  forall reqMsg | reqMsg in v.network.sentMsgs && reqMsg.RequestMsg?
  :: 
    (exists i ::
      && v.ValidHistoryIdx(i)
      && reqMsg.r.reqId in v.History(i).hosts[reqMsg.r.clientId].client.requests
    )
}

// certified self inductive, modulo requires
// The server's requests must have come from the network
// Property of Receive
ghost predicate ServerValidRequest(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, idx:nat | 
    && v.ValidHistoryIdx(i)
    && c.ValidServerIdx(idx)
    && v.History(i).hosts[idx].server.currentRequest.Some?
  :: 
    RequestMsg(v.History(i).hosts[idx].server.currentRequest.value) in v.network.sentMsgs
}


// certified self inductive, modulo requires
// Every response message in the network comes from the server's request
// Property of Send
ghost predicate ValidResponseMessage(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall resp | resp in v.network.sentMsgs && resp.ResponseMsg?
  :: (exists i :: 
        && v.ValidHistoryIdx(i)
        && v.History(i).GetServer(c).server.currentRequest == Some(resp.r)
  )
}

// certified self inductive, modulo requires
// Every client's collected responses came from the network.
// Property of Receive
ghost predicate ClientResponsesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, idx:nat, respId | 
    && v.ValidHistoryIdx(i)
    && c.ValidClientIdx(idx) 
    && respId in v.History(i).hosts[idx].client.responses
  :: 
    ResponseMsg(Req(idx, respId)) in v.network.sentMsgs
}


ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidRequestMsgSource(c, v)
  && ValidRequestMessage(c, v)
  && ServerValidRequest(c, v)
  && ValidResponseMessage(c, v)
  && ClientResponsesValid(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidRequestMessage(c, v, v');
  InvNextServerValidRequest(c, v, v');
  InvNextValidResponseMessage(c, v, v');
  InvNextClientResponsesValid(c, v, v');
}

/***************************************************************************************
*                                         Proofs                                       *
***************************************************************************************/

lemma InvNextValidRequestMessage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  requires ValidRequestMsgSource(c, v)
  requires ValidRequestMessage(c, v)
  ensures ValidRequestMessage(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextServerValidRequest(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  requires ServerValidRequest(c, v)
  ensures ServerValidRequest(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextValidResponseMessage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  requires ValidResponseMessage(c, v)
  ensures ValidResponseMessage(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextClientResponsesValid(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  requires ClientResponsesValid(c, v)
  ensures ClientResponsesValid(c, v')
{
  VariableNextProperties(c, v, v');
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

}  // end module MessageInvariants

