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
  predicate payloadGeqSenderHostId(c: Constants, v: Variables) {
    forall msg | msg in v.network.sentMsgs && 0 <= msg.src < |c.hostConstants|
    :: msg.val >= c.hostConstants[msg.src].hostId
  }

  // For each host, if its highestHeard is >-1, then it must have gotten it from a message
  // from its predecessor
  predicate receiveValidity(c: Constants, v: Variables) 
    requires v.WF(c)
    requires VoteMsgValidSrc(c, v)
  {
    forall idx | 0 <= idx < |c.hostConstants| && v.hosts[idx].highestHeard > -1
    :: (exists msg :: && msg in v.network.sentMsgs 
                      && msg.val == v.hosts[idx].highestHeard 
                      && idx == Successor(|c.hostConstants|, msg.src))
  }

  predicate MessageInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && VoteMsgValidSrc(c, v)
    && payloadGeqSenderHostId(c, v)
    && receiveValidity(c, v)
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
}

