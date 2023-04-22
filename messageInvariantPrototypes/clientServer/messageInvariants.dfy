include "spec.dfy"

module MessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self inductive, modulo requires
predicate RequestsValidSource(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall req | req in v.network.sentMsgs && req.Request?
  :: c.ValidClientIdx(req.clientId)
}

// certified self inductive, modulo requires
predicate ResponseCorrespondToRequest(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall resp | resp in v.network.sentMsgs && resp.Response?
  :: Request(resp.clientId, resp.reqId) in v.network.sentMsgs
}

// certified self inductive, modulo requires
predicate RequestMessagesValid(c: Constants, v: Variables)
  requires v.WF(c)
  requires RequestsValidSource(c, v)
{
  forall req | req in v.network.sentMsgs && req.Request?
  :: req.reqId in v.hosts[req.clientId].client.requests
}

// certified self inductive, modulo requires
predicate ReceivedResponsesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx:nat, respId | c.ValidClientIdx(idx) && respId in v.hosts[idx].client.responses
  :: Response(idx, respId) in v.network.sentMsgs
}


predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && RequestsValidSource(c, v)
  && ResponseCorrespondToRequest(c, v)
  && RequestMessagesValid(c, v)
  && ReceivedResponsesValid(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{}

}  // end module MessageInvariants

