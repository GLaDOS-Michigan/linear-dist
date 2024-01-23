include "messageInvariantsAutogen.dfy"

module RingLeaderElectionProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants

  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/


// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  true
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Safety(c, v)
}

ghost predicate Between(start: nat, node: nat, end: nat) 
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

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
  MessageInvariantsImplyChordDominates(c, v');
  ChordDominatesImpliesSafety(c, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/


ghost predicate ChordDominates(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i:int, src:nat, dst:nat, mid:nat | 
      && v.ValidHistoryIdx(i)
      && c.ValidIdx(src)
      && c.ValidIdx(dst)
      && c.ValidIdx(mid)
      && v.History(i).hosts[dst].highestHeard == c.hosts[src].hostId
      && Between(src, mid, dst)
    :: 
      c.hosts[mid].hostId < c.hosts[src].hostId
}

lemma ChordDominatesImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires ChordDominates(c, v)
  ensures Safety(c, v)
{}

lemma MessageInvariantsImplyChordDominates(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  ensures ChordDominates(c, v)
{
  forall i:int, src:nat, dst:nat, mid:nat | 
    && v.ValidHistoryIdx(i)
    && c.ValidIdx(src)
    && c.ValidIdx(dst)
    && c.ValidIdx(mid)
    && v.History(i).hosts[dst].highestHeard == c.hosts[src].hostId
    && Between(src, mid, dst)
  ensures
    c.hosts[mid].hostId < c.hosts[src].hostId
  {
    reveal_ReceiveMsgValidity();
    var hh := v.History(i).hosts[dst].highestHeard;
    assert Host.ReceiveMsgTrigger(c.hosts[dst], v.History(i).hosts[dst], hh); // trigger
    var pred := Predecessor(|c.hosts|, dst);
    assert Between(src, pred, dst);
    if pred != mid {
      MidMustHaveSentSrcHostId(c, v, src, mid, dst, i);
    }
  }
}

lemma MidMustHaveSentSrcHostId(c: Constants, v: Variables, src: nat, mid: nat, dst: nat, i:nat) 
  requires v.WF(c)
  requires MessageInv(c, v)
  requires c.ValidIdx(src)
  requires c.ValidIdx(dst)
  requires c.ValidIdx(mid)
  requires v.ValidHistoryIdx(i)
  requires v.History(i).hosts[dst].highestHeard == c.hosts[src].hostId
  requires Between(src, mid, dst)
  ensures Msg(c.hosts[src].hostId, mid) in v.network.sentMsgs 
  decreases Distance(|c.hosts|, mid, dst)
{
  LemmaSentNotMyIdImpliesReceivedId(c, v);
  var n := |c.hosts|;
  if mid == Predecessor(n, dst) {
    // by receiveValidity
    reveal_ReceiveMsgValidity();
    var hh := v.History(i).hosts[dst].highestHeard;
    assert Host.ReceiveMsgTrigger(c.hosts[dst], v.History(i).hosts[dst], hh);
    assert Msg(c.hosts[src].hostId, mid) in v.network.sentMsgs;
  } else {
    reveal_ReceiveMsgValidity();
    var succ := Successor(n, mid);
    SuccessorDecreasesDistance(n, mid, dst);
    MidMustHaveSentSrcHostId(c, v, src, succ, dst, i);
  }
}

lemma SuccessorDecreasesDistance(n:nat, start:nat, end:nat) 
  requires 0 <= start < n
  requires 0 <= end < n
  requires start != end
  ensures Distance(n, start, end) > Distance(n, Successor(n, start), end)
{}

ghost predicate SentNotMyIdImpliesReceivedId(c: Constants, v: Variables) 
  requires v.WF(c)
  requires MessageInv(c, v)
{
  var n := |c.hosts|;
  forall msg | msg in v.network.sentMsgs && msg.val != c.hosts[msg.src].hostId 
  :: Msg(msg.val, Predecessor(n, msg.src)) in v.network.sentMsgs
}

lemma LemmaSentNotMyIdImpliesReceivedId(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  ensures SentNotMyIdImpliesReceivedId(c, v)
{
  reveal_ReceiveMsgValidity();
  var n := |c.hosts|;
  forall msg | msg in v.network.sentMsgs && msg.val != c.hosts[msg.src].hostId 
  ensures Msg(msg.val, Predecessor(n, msg.src)) in v.network.sentMsgs
  {
    var i :| 
      && v.ValidHistoryIdxStrict(i)
      && Host.SendMsg(c.hosts[msg.Src()], v.History(i).hosts[msg.Src()], v.History(i+1).hosts[msg.Src()], msg);
    assert Host.ReceiveMsgTrigger(c.hosts[msg.src], v.History(i).hosts[msg.src], msg.val);  // trigger
  }
}

}  // end module RingLeaderElectionProof

