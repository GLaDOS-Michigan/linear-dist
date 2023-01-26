// User level proofs of application invariants

include "spec.dfy"
include "networkInvs.dfy"


module RingLeaderElectionProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations
  import opened NetworkInvariants

  
  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && NetworkInv(c, v)
    // User-level invariants:
    && SentNotMyIdImpliesReceivedId(c, v)
    && ChordDominates(c, v)
    && Safety(c, v)
  }
  

  predicate Between(start: nat, node: nat, end: nat) 
  {
    if start < end then
      start < node < end else
      node < end || start < node
  }

  function Distance(n: nat, start: nat, end: nat) : nat
    requires 0 <= start < n
    requires 0 <= end < n
  {
    if end >= start then end - start 
    else n - end + start
  }

  predicate ChordDominates(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall src:nat, dst:nat, mid:nat | 
        && c.ValidIdx(src)
        && c.ValidIdx(dst)
        && c.ValidIdx(mid)
        && v.hosts[dst].highestHeard == c.hostConstants[src].hostId
        && Between(src, mid, dst)
            :: && c.hostConstants[mid].hostId < c.hostConstants[src].hostId
               && Msg(c.hostConstants[src].hostId, mid) in v.network.sentMsgs
  }

  predicate SentNotMyIdImpliesReceivedId(c: Constants, v: Variables) 
    requires v.WF(c)
    requires VoteMsgValidSrc(c, v)
  {
    var n := |c.hostConstants|;
    forall msg | msg in v.network.sentMsgs && msg.val != c.hostConstants[msg.src].hostId 
    :: Msg(msg.val, Predecessor(n, msg.src)) in v.network.sentMsgs
  }


  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  {}

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    NetworkInvInductive(c, v, v');
    ChordDominatesInductive(c, v, v');
    ChordDominatesImpliesSafety(c, v');
  }

  lemma ChordDominatesImpliesSafety(c: Constants, v: Variables)
    requires v.WF(c)
    requires ChordDominates(c, v)
    ensures Safety(c, v)
  {}

  lemma ChordDominatesInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures ChordDominates(c, v')
    ensures SentNotMyIdImpliesReceivedId(c, v');
  {
    forall src:nat, dst:nat, mid:nat | 
        && c.ValidIdx(src)
        && c.ValidIdx(dst)
        && c.ValidIdx(mid)
        && v'.hosts[dst].highestHeard == c.hostConstants[src].hostId
        && Between(src, mid, dst)
    ensures 
      && c.hostConstants[mid].hostId < c.hostConstants[src].hostId 
      && Msg(c.hostConstants[src].hostId, mid) in v.network.sentMsgs
    {
      var step :| NextStep(c, v, v', step);
      if step.actorIdx == dst {
        var hc := c.hostConstants[step.actorIdx];
        var h, h' := v.hosts[step.actorIdx], v'.hosts[step.actorIdx];
        var hostStep :| Host.NextStep(hc, h, h', hostStep, step.msgOps);
        if hostStep.ReceiveStep? {
          var pred := Predecessor(|c.hostConstants|, dst);
          assert Between(src, pred, dst);
          if pred != mid {
            lemma_MidMustHaveSentSrcHostId(c, v', src, mid, dst);
          }
        } 
      }
    }
  }

  lemma lemma_MidMustHaveSentSrcHostId(c: Constants, v: Variables, src: nat, mid: nat, dst: nat) 
    requires v.WF(c)
    requires NetworkInv(c, v)
    requires SentNotMyIdImpliesReceivedId(c, v)
    requires c.ValidIdx(src)
    requires c.ValidIdx(dst)
    requires c.ValidIdx(mid)
    requires v.hosts[dst].highestHeard == c.hostConstants[src].hostId
    requires Between(src, mid, dst)
    ensures Msg(c.hostConstants[src].hostId, mid) in v.network.sentMsgs 
    decreases Distance(|c.hostConstants|, mid, dst)
  {
    var n := |c.hostConstants|;
    if mid == Predecessor(n, dst) {
      // by receiveValidity
      assert Msg(c.hostConstants[src].hostId, mid) in v.network.sentMsgs;
    } else {
      assume Distance(n, mid, dst) > Distance(n, Successor(n, mid), dst);
      lemma_MidMustHaveSentSrcHostId(c, v, src, Successor(n, mid), dst);
    }
  }
}

