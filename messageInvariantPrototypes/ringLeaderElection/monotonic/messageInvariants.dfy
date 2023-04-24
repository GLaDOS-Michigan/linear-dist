// Network-level "boilerplate" invariants that are application-independent

include "spec.dfy"

module MessageInvariants {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // All msg have a valid ringPos as src
  predicate VoteMsgValidSrc(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs
    :: 0 <= msg.src < |c.hostConstants|
  }

  // Every message's val is at least the senders HostId
  predicate PayloadGeqSenderHostId(c: Constants, v: Variables) {
    forall msg | msg in v.network.sentMsgs && 0 <= msg.src < |c.hostConstants|
    :: msg.val >= c.hostConstants[msg.src].hostId
  }

  // Every message's val comes from either the HostId or from highestHeardSeq
  predicate PayloadComesFromHighestHeardSeq(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && 0 <= msg.src < |c.hostConstants|
    :: msg.val == c.hostConstants[msg.src].hostId || msg.val in v.hosts[msg.src].highestHeardSeq
  }

  // For each host, any values in its highestHeardSeq came from a message
  // from its predecessor
  predicate ReceiveValidity(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx, val | 0 <= idx < |c.hostConstants| && val in v.hosts[idx].highestHeardSeq
    :: Msg(val, Predecessor(|c.hostConstants|, idx)) in v.network.sentMsgs 
  }

  predicate MessageInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && VoteMsgValidSrc(c, v)                  // needed
    && PayloadGeqSenderHostId(c, v)           // needed
    && PayloadComesFromHighestHeardSeq(c, v)  // needed
    && ReceiveValidity(c, v)                  // needed
  }

  lemma InitImpliesNetworkInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures MessageInv(c, v)
  {}

  lemma NetworkInvInductive(c: Constants, v: Variables, v': Variables)
    requires MessageInv(c, v)
    requires Next(c, v, v')
    ensures MessageInv(c, v')
  {}
}

