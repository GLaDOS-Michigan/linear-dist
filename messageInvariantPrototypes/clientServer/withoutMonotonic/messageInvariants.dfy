include "spec.dfy"

module MessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self inductive, modulo requires
// Every request message in the network has a proper source
predicate RequestMsgsValidSource(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: c.ValidClientIdx(req.r.clientId)
}

// certified self inductive, modulo requires
// Every request message in the network comes from the source's request set
// Property of Send
predicate RequestMsgsValid(c: Constants, v: Variables)
  requires v.WF(c)
  requires RequestMsgsValidSource(c, v)
{
  forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: req.r.reqId in v.hosts[req.r.clientId].client.requests
}

// certified self inductive, modulo requires
// Every request message in the network comes from the source's request set
// Property of Receive
predicate ServerCurrentRequestValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx:nat | c.ValidServerIdx(idx) && v.hosts[idx].server.currentRequest.Some?
  :: RequestMsg(v.hosts[idx].server.currentRequest.value) in v.network.sentMsgs
}

// certified self inductive, modulo requires
// Every client's collected responses came from the network.
// Property of Receive
predicate ClientResponsesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx:nat, respId | c.ValidClientIdx(idx) && respId in v.hosts[idx].client.responses
  :: ResponseMsg(Req(idx, respId)) in v.network.sentMsgs
}


predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && RequestMsgsValidSource(c, v)
  && RequestMsgsValid(c, v)
  && ServerCurrentRequestValid(c, v)
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
{}

}  // end module MessageInvariants

