// Network-level "boilerplate" invariants that are application-independent

include "spec.dfy"

module NetworkInvariants {
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
  predicate payloadGeqSenderHostId(c: Constants, v: Variables) {
    forall msg | msg in v.network.sentMsgs && 0 <= msg.src < |c.hostConstants|
    :: msg.val >= c.hostConstants[msg.src].hostId
  }

  // Every message's val less than or eq max(highest seen of nodes[msg.src], hostid of nodes[mag.src])
  predicate payloadLeqSenderMax(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && 0 <= msg.src < |c.hostConstants|
    :: msg.val <= max(c.hostConstants[msg.src].hostId, v.hosts[msg.src].highestHeard())
  }

  // Every message's val comes from either the HostId or from highestHeardSeq
  predicate payloadComesFromHighestHeardSeq(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs && 0 <= msg.src < |c.hostConstants|
    :: msg.val == c.hostConstants[msg.src].hostId || msg.val in v.hosts[msg.src].highestHeardSeq
  }

  // For each host, any values in its highestHeardSeq came from a message
  // from its predecessor
  predicate receiveValidity(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx, val | 0 <= idx < |c.hostConstants| && val in v.hosts[idx].highestHeardSeq
    :: Msg(val, Predecessor(|c.hostConstants|, idx)) in v.network.sentMsgs 
  }

  predicate NetworkInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && VoteMsgValidSrc(c, v)
    && payloadGeqSenderHostId(c, v)
    && payloadLeqSenderMax(c, v)
    && payloadComesFromHighestHeardSeq(c, v)
    && receiveValidity(c, v)
  }

  lemma InitImpliesNetworkInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures NetworkInv(c, v)
  {}

  lemma NetworkInvInductive(c: Constants, v: Variables, v': Variables)
    requires NetworkInv(c, v)
    requires Next(c, v, v')
    ensures NetworkInv(c, v')
  {}
}

