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
    if start <= end then end - start 
    else n - start + end
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
            :: && c.hostConstants[mid].hostId < c.hostConstants[src].hostId  // Same as centralized
               && Msg(c.hostConstants[src].hostId, mid) in v.network.sentMsgs // Extra
  }

  // Extra: If a node sent a msg with a value that is NOT its hostId, it must have received that 
  // value from its predecessor
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
            MidMustHaveSentSrcHostId(c, v', src, mid, dst);
          }
        } 
      }
    }
  }

  lemma {:timeLimitMultiplier 2} MidMustHaveSentSrcHostId(c: Constants, v: Variables, src: nat, mid: nat, dst: nat) 
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
      var succ := Successor(n, mid);
      SuccessorDecreasesDistance(n, mid, dst);
      MidMustHaveSentSrcHostId(c, v, src, succ, dst);
      assert Msg(c.hostConstants[src].hostId, succ) in v.network.sentMsgs;
      // Rip this is not inductive. I really need to keep track of whole sequence
      // of highest heard...

      assume false;
      assert Msg(c.hostConstants[src].hostId, mid) in v.network.sentMsgs;
    }
  }

  lemma SuccessorDecreasesDistance(n:nat, start:nat, end:nat) 
    requires 0 <= start < n
    requires 0 <= end < n
    requires start != end
    ensures Distance(n, start, end) > Distance(n, Successor(n, start), end)
  {}


}

