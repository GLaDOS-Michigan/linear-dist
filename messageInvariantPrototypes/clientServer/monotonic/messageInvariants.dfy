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
// The server's requests must have come from the network
// Property of Receive
predicate ServerRequestsValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx:nat, i | c.ValidServerIdx(idx) && 0 <= i < |v.hosts[idx].server.requests|
  :: RequestMsg(v.hosts[idx].server.requests[i]) in v.network.sentMsgs
}


// certified self inductive, modulo requires
// Every response message in the network comes from the server's requests seq
// Property of Send
predicate ResponseMsgsValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall resp | resp in v.network.sentMsgs && resp.ResponseMsg?
  :: (exists i :: 
        && 0 <= i < |v.GetServer(c).requests|
        && v.GetServer(c).requests[i] == resp.r
  )
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
  && ServerRequestsValid(c, v)
  && ResponseMsgsValid(c, v)
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
  InvNextResponseMsgsValid(c, v, v');
}


lemma InvNextResponseMsgsValid(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  requires ResponseMsgsValid(c, v)
  ensures ResponseMsgsValid(c, v')
{
  forall resp | resp in v'.network.sentMsgs && resp.ResponseMsg?
  ensures 
    exists i :: 
      && 0 <= i < |v'.GetServer(c).requests|
      && v'.GetServer(c).requests[i] == resp.r
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actorIdx, dsStep.msgOps;
    if c.ValidServerIdx(actor) && resp !in v.network.sentMsgs {
      var i := |v'.GetServer(c).requests| - 1;  // witness
    } else {
      // witness and trigger
      var i :| 0 <= i < |v.GetServer(c).requests| && v.GetServer(c).requests[i] == resp.r;
      assert 0 <= i < |v'.GetServer(c).requests| && v'.GetServer(c).requests[i] == resp.r;
    }
  }
}
}  // end module MessageInvariants

