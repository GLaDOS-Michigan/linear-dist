include "spec.dfy"
include "messageInvariants.dfy"

module PaxosProof {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened PaxosMessageInvariants

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Util: A quorum of Accept messages of the same vb
// Tony: Using monotonic transformations, I can push this to an acceptor host property,
// rather than a network property.
predicate Chosen(c: Constants, v: Variables, vb: ValBal) {
  exists quorum: set<Message> :: IsAcceptQuorum(c, v, quorum, vb)
}

predicate AtMostOneChosenVal(c: Constants, v: Variables) {
  forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
  :: vb1.v == vb2.v
}

predicate OneValuePerProposeBallot(c: Constants, v: Variables)
{
  forall p1, p2 | 
    && IsProposeMessage(v, p1)
    && IsProposeMessage(v, p2)
    && p1.bal == p2.bal
  ::
    p1.val == p2.val
}

// This invariant implies that l.receivedPromises is monotonic increasing, and l.value 
// does not equivocate. This implies OneValuePerProposeBallot
// Tony: Monotonic transformations apply here.
predicate ProposeImpliesLeaderState(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall p | IsProposeMessage(v, p) 
  ::  && |v.leaders[p.bal].receivedPromises| >= c.f+1
      && v.leaders[p.bal].value == p.val
}

predicate PromiseVbImpliesAccepted(c: Constants, v: Variables) {
  forall prom | 
    && IsPromiseMessage(v, prom)
    && prom.vbOpt.Some?
  ::
    Accept(prom.vbOpt.value, prom.acc) in v.network.sentMsgs
}

// For every Accept message in the network, there is a corresponding Propose message
// Tony: This can be turned into two message invariants. Accept message in the network
// means that the acceptor accepted that value at some point in time.
// Then the value being accepted at some point also means that there is some corresponding
// Propose message.
predicate AcceptMessageImpliesProposed(c: Constants, v: Variables) {
  forall acc | IsAcceptMessage(v, acc)
  :: Propose(acc.vb.b, acc.vb.v) in v.network.sentMsgs
}


// For every Accept(vb, src) in the network, the source acceptor must have accepted 
// some ballot >= vb.b. This is not a message invariant because it depends on the fact
// that at every acceptor, accepted bal <= promised bal. I.e. once I accept a ballot, 
// I cannot accept a smaller ballot
// Tony: This can be broken down via monotonic transformation. The Accept message says 
// that leader state had the specific bal at some point in time, and this is a message
// invariant. Another application invariant then says that this accepted seq is monotone
// increasing. 
predicate AcceptMessagesValid(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall acc | IsAcceptMessage(v, acc)
  ::  && v.acceptors[acc.acc].acceptedVB.Some?
      && acc.vb.b <= v.acceptors[acc.acc].acceptedVB.value.b
}

// For every Accept that accepted some vb, every Promise p with p.bal > vb.b from that 
// Accept must carry a non-None vbOpt, and vbOpt.value.b >= vb.b
// Tony: This can be broken down via monotonic transformation. 
predicate AcceptMsgImpliesLargerPromiseCarriesVb(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall accMsg, promMsg | 
    && IsAcceptMessage(v, accMsg)
    && IsPromiseMessage(v, promMsg)
    && promMsg.acc == accMsg.acc
    && accMsg.vb.b < promMsg.bal
  :: 
    && promMsg.vbOpt.Some?
    && accMsg.vb.b <= promMsg.vbOpt.value.b
}

// Tony: If receivedPromises remembers whole messages rather than the source, this 
// need not mention the network (monotonic transformation)
// Every leader's HighestHeard is backed by a set of Promise messages.
predicate HighestHeardBackedByReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx | c.ValidLeaderIdx(idx)
  :: (
    && var ldr := v.leaders[idx];
    && exists pset :: LeaderPromiseSetProperties(c, v, idx, pset)
  )
}

predicate LeaderPromiseSetProperties(c: Constants, v: Variables, idx: int, pset: set<Message>) 
  requires v.WF(c)
  requires c.ValidLeaderIdx(idx)
{
  var ldr := v.leaders[idx];
  var cldr := c.leaderConstants[idx];
  var hbal := ldr.highestHeardBallot;
  && IsPromiseSet(c, v, pset, cldr.id)
  && (hbal.Some? ==> PromiseSetHighestVB(c, v, pset, cldr.id, VB(ldr.value, hbal.value)))
  && (hbal.None? ==> PromiseSetEmptyVB(c, v, pset, cldr.id))
  && |pset| == |ldr.receivedPromises|
  && (forall p: Message | p in pset :: p.acc in ldr.receivedPromises)
}

// Tony: If receivedPromises remembers whole messages rather than the source, this 
// need not mention the network (monotonic transformation)
// Every Propose message is backed by a quorum of Promise messages
predicate ProposeBackedByPromiseQuorum(c: Constants, v: Variables) {
  forall p | IsProposeMessage(v, p)
  :: (exists quorum :: PromiseQuorumSupportsVal(c, v, quorum, p.bal, p.val))
}

// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx | 
    && c.ValidAcceptorIdx(idx) 
    && v.acceptors[idx].acceptedVB.Some?
  :: 
    && v.acceptors[idx].promised.Some?
    && v.acceptors[idx].acceptedVB.value.b <= v.acceptors[idx].promised.value
}

// For all Promise messages prom, prom.bal > prom.vbOpt.value.b
// Tony: This becomes pure application invariant when acceptor keeps history of its entire state
predicate PromiseBalLargerThanAccepted(c: Constants, v: Variables) {
  forall prom | 
    && IsPromiseMessage(v, prom)
    && prom.vbOpt.Some?
  ::
    prom.vbOpt.value.b < prom.bal
}

// Inv: If vb is chosen, then for all leaders that have highestHeard >= vb.b, they must have 
// value == vb.v
predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldr | 
    && Chosen(c, v, vb) 
    && c.ValidLeaderIdx(ldr)
    && v.leaders[ldr].highestHeardBallot.Some?
    && v.leaders[ldr].highestHeardBallot.value >= vb.b
  ::
    v.leaders[ldr].value == vb.v
}

// Inv: If vb is chosen, then for all Propose messages that have bal > vb.b, they must have 
// value == vb.v
// Tony: Using monotonic transformations, by recording the entire history of leader 
// (value, highestHeardBallot) pairs, this becomes implicit from ChosenValImpliesLeaderOnlyHearsVal,
// rather than a network property as an application invariant.
predicate ChosenValImpliesProposeOnlyVal(c: Constants, v: Variables) {
  forall vb, propose | 
    && Chosen(c, v, vb)
    && IsProposeMessage(v, propose)
    && propose.bal > vb.b
  ::
    propose.val == vb.v
}

// Application bundle
predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  && ProposeImpliesLeaderState(c, v)
  && PromiseVbImpliesAccepted(c, v)
  && AcceptMessageImpliesProposed(c, v)
  && AcceptMessagesValid(c, v)
  && AcceptMsgImpliesLargerPromiseCarriesVb(c, v)
  && HighestHeardBackedByReceivedPromises(c, v)
  && ProposeBackedByPromiseQuorum(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
  && PromiseBalLargerThanAccepted(c, v)
  && ChosenValImpliesProposeOnlyVal(c, v)

  // TODO: Can all the ChosenImplies- below be proven as lemmas rather than stated as invariants?
  // It seems that they can all be proven from ChosenValImpliesProposeOnlyVal
  && ChosenValImpliesLeaderOnlyHearsVal(c, v)
  && AtMostOneChosenVal(c, v)
}

predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Agreement(c, v)
}


/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Agreement(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMessageInv(c, v);
  // prove HighestHeardBackedByReceivedPromises(c, v)
  forall idx | c.ValidLeaderIdx(idx)
  ensures 
    && var ldr := v.leaders[idx];
    && exists pset :: LeaderPromiseSetProperties(c, v, idx, pset)
  {
    var pset := {};
    assert LeaderPromiseSetProperties(c, v, idx, pset);  // witness
  }
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
  InvNextProposeImpliesLeaderState(c, v, v');
  InvNextPromiseVbImpliesAccepted(c, v, v');
  InvNextAcceptMessageImpliesProposed(c, v, v');
  InvNextAcceptMessagesValid(c, v, v');
  InvNextImpliesAcceptMsgImpliesLargerPromiseCarriesVb(c, v, v');
  InvNextHighestHeardBackedByReceivedPromises(c, v, v');
  InvNextProposeBackedByPromiseQuorum(c, v, v');
  InvNextAcceptorPromisedLargerThanAccepted(c, v, v');
  InvNextPromiseBalLargerThanAccepted(c, v, v');
  InvNextChosenValImpliesProposeOnlyVal(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  InvNextAtMostOneChosenVal(c, v, v');
  AtMostOneChosenImpliesAgreement(c, v');
}

lemma InvNextProposeImpliesLeaderState(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ProposeImpliesLeaderState(c, v')
  ensures OneValuePerProposeBallot(c, v)  // Implied by ProposeImpliesLeaderState
  ensures OneValuePerProposeBallot(c, v')  // Implied by ProposeImpliesLeaderState
{}

lemma InvNextPromiseVbImpliesAccepted(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures PromiseVbImpliesAccepted(c, v')
{
  forall prom | 
    && IsPromiseMessage(v', prom)
    && prom.vbOpt.Some?
  ensures
    Accept(prom.vbOpt.value, prom.acc) in v'.network.sentMsgs
  {}  // trigger
}

lemma InvNextAcceptMessageImpliesProposed(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptMessageImpliesProposed(c, v')
{}

lemma InvNextAcceptMessagesValid(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptMessagesValid(c, v')
{}

lemma InvNextAcceptorPromisedLargerThanAccepted(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptorPromisedLargerThanAccepted(c, v')
{}

lemma InvNextPromiseBalLargerThanAccepted(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures PromiseBalLargerThanAccepted(c, v')
{}

lemma InvNextImpliesAcceptMsgImpliesLargerPromiseCarriesVb(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptMsgImpliesLargerPromiseCarriesVb(c, v')
{
  // Tony: Surprised that this lemma requires no proof
}

lemma InvNextHighestHeardBackedByReceivedPromises(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures HighestHeardBackedByReceivedPromises(c, v')
{
  var dsStep :| NextStep(c, v, v', dsStep);
  if dsStep.LeaderStep? {
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
    var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
    forall idx | c.ValidLeaderIdx(idx)
    ensures exists pset' :: LeaderPromiseSetProperties(c, v', idx, pset')
    {
      if && step.ReceiveStep? && actor == idx 
        && msgOps.recv.value.Promise? 
        && |l.receivedPromises| <= c.f
        && msgOps.recv.value.acc !in l.receivedPromises
        && msgOps.recv.value.bal == lc.id 
      {
        var pset :| LeaderPromiseSetProperties(c, v, idx, pset);
        var newM := msgOps.recv.value;
        var doUpdate := && newM.vbOpt.Some? 
                        && (|| l.highestHeardBallot.None?
                            || (l.highestHeardBallot.Some? && newM.vbOpt.value.b > l.highestHeardBallot.value));
        if doUpdate {
          var pset' := pset + {msgOps.recv.value};  // witness
          // trigger them triggers
          assert WinningPromiseMessageInQuorum(c, v', pset', idx, newM.vbOpt.value, newM);  
          assert LeaderPromiseSetProperties(c, v', idx, pset');
        } else {
          var pset' := pset + {msgOps.recv.value};  // witness
          if l.highestHeardBallot.Some? {
            var highestheard := VB(l.value, l.highestHeardBallot.value);
            var winningProm :| WinningPromiseMessageInQuorum(c, v, pset, idx, highestheard, winningProm);  // witness
            assert WinningPromiseMessageInQuorum(c, v', pset', idx, highestheard, winningProm);  // trigger
          }
          assert LeaderPromiseSetProperties(c, v', idx, pset');  // trigger
        }
      } else {
        InvNextHighestHeardBackedByReceivedPromisesHelper(c, v, v', dsStep, idx);
      }
    }
  } else {
    forall idx | c.ValidLeaderIdx(idx)
    ensures exists pset' :: LeaderPromiseSetProperties(c, v', idx, pset')
    {
      InvNextHighestHeardBackedByReceivedPromisesHelper(c, v, v', dsStep, idx);
    }
  }
}

// Helper lemma for InvNextHighestHeardBackedByReceivedPromises in the case where the 
// leader stutters. Basically tickling triggers in Dafny
lemma InvNextHighestHeardBackedByReceivedPromisesHelper(c: Constants, v: Variables, v': Variables,
  dsStep: Step, idx: nat) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v, v', dsStep)
  requires c.ValidLeaderIdx(idx)
  requires v'.leaders[idx] == v.leaders[idx]
  ensures exists pset' :: LeaderPromiseSetProperties(c, v', idx, pset')
{
  var pset :| LeaderPromiseSetProperties(c, v, idx, pset);  // witness
  var l := v.leaders[idx];
  if l.highestHeardBallot.Some? {
    var highestheard := VB(l.value, l.highestHeardBallot.value);
    var winningProm :| WinningPromiseMessageInQuorum(c, v, pset, idx, highestheard, winningProm);  // witness
    assert WinningPromiseMessageInQuorum(c, v', pset, idx, highestheard, winningProm);  // trigger
  }
  assert LeaderPromiseSetProperties(c, v', idx, pset);  // trigger
}

lemma InvNextProposeBackedByPromiseQuorum(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ProposeBackedByPromiseQuorum(c, v')
{
  forall p | p in v'.network.sentMsgs && p.Propose?
  ensures exists quorum :: PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.LeaderStep? {
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
      if step.ProposeStep? && p !in v.network.sentMsgs {
        var quorum :| LeaderPromiseSetProperties(c, v, actor, quorum);  // witness
        if l.highestHeardBallot.Some? {
          // This is where HighestHeardBackedByReceivedPromises comes in
          var leaderVB := VB(l.value, l.highestHeardBallot.value);
          var m :| WinningPromiseMessageInQuorum(c, v, quorum, lc.id, leaderVB, m);  // witness
          assert WinningPromiseMessageInQuorum(c, v', quorum, lc.id, leaderVB, m);  // trigger
        }
        assert PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val);  // trigger
      } else {
        InvNextProposeBackedByPromiseQuorumNoNewPropose(c, v, v', p);
      }
    } else {
      InvNextProposeBackedByPromiseQuorumNoNewPropose(c, v, v', p);
    }
  }
}

lemma InvNextProposeBackedByPromiseQuorumNoNewPropose(c: Constants, v: Variables, v': Variables, p: Message) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires IsProposeMessage(v, p)
  requires IsProposeMessage(v', p)
  ensures exists quorum :: PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val)
{
  var quorum :| PromiseQuorumSupportsVal(c, v, quorum, p.bal, p.val);  // witness
  if !PromiseSetEmptyVB(c, v, quorum, p.bal) {
    var hsbal :| PromiseSetHighestVB(c, v, quorum, p.bal, VB(p.val, hsbal));  // witness
    var vb := VB(p.val, hsbal);
    var m :| WinningPromiseMessageInQuorum(c, v, quorum, p.bal, vb, m); // witness
    assert WinningPromiseMessageInQuorum(c, v', quorum, p.bal, vb, m); // trigger
  }
  assert PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val);  // trigger
}

lemma InvNextChosenValImpliesProposeOnlyValAcceptorRecvStep(
  c: Constants, v: Variables, v': Variables, dsStep: Step, step: AcceptorHost.Step)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v, v', dsStep)
  requires dsStep.AcceptorStep?
  requires AcceptorHost.NextStep(
            c.acceptorConstants[dsStep.actor], 
            v.acceptors[dsStep.actor], v'.acceptors[dsStep.actor],
            step, dsStep.msgOps)
  requires step.ReceiveStep?
  requires dsStep.msgOps.recv.value.Propose?
  requires AcceptMessageImpliesProposed(c, v')
  requires AcceptMessagesValid(c, v')
  requires ProposeBackedByPromiseQuorum(c, v')
  requires OneValuePerProposeBallot(c, v')
  requires AcceptMsgImpliesLargerPromiseCarriesVb(c, v')
  requires PromiseVbImpliesAccepted(c, v')
  requires PromiseBalLargerThanAccepted(c, v')
  ensures ChosenValImpliesProposeOnlyVal(c, v')
{
  forall vb, propose | 
    && Chosen(c, v', vb)
    && propose in v'.network.sentMsgs
    && propose.Propose?
    && propose.bal >= vb.b
  ensures propose.val == vb.v
  {
    if !Chosen(c, v, vb) {
      /* This is a point where something can suddenly be chosen.*/
      var ac, a, a' := c.acceptorConstants[dsStep.actor], v.acceptors[dsStep.actor], v'.acceptors[dsStep.actor];
      var propVal, propBal := dsStep.msgOps.recv.value.val, dsStep.msgOps.recv.value.bal;
      var doAccept := a.promised.None? || (a.promised.Some? && a.promised.value <= propBal);
      if doAccept && vb == VB(propVal, propBal) {
        if exists p :: 
          && p in v'.network.sentMsgs
          && p.Propose?
          && p.bal >= vb.b
          && p.val != vb.v 
        {
          var p :|
            && p in v'.network.sentMsgs
            && p.Propose?
            && p.bal >= vb.b
            && p.val != vb.v;
          assert p.bal > vb.b;
          MessageInvInductive(c, v, v');
          ChosenAndConflictingProposeImpliesFalse(c, v', vb, p);
          assert false;
        }
      } else {
        if exists quorum: set<Message> :: IsAcceptQuorum(c, v', quorum, vb) {
          var q :| IsAcceptQuorum(c, v', q, vb);
          assert IsAcceptQuorum(c, v, q, vb);  // trigger
          assert false;
        }
        assert !Chosen(c, v', vb);
      }
    }
  }
}

// Here lies most of the heavy-lifting Paxos logic
lemma ChosenAndConflictingProposeImpliesFalse(c: Constants, v: Variables, chosenVb: ValBal, p: Message) 
  requires MessageInv(c, v)
  requires OneValuePerProposeBallot(c, v)
  requires AcceptMessageImpliesProposed(c, v);
  requires AcceptMessagesValid(c, v)
  requires ProposeBackedByPromiseQuorum(c, v)
  requires AcceptMsgImpliesLargerPromiseCarriesVb(c, v)
  requires PromiseVbImpliesAccepted(c, v)
  requires AcceptMessageImpliesProposed(c, v)
  requires PromiseBalLargerThanAccepted(c, v)
  requires Chosen(c, v, chosenVb)
  requires IsProposeMessage(v, p)
  requires chosenVb.b < p.bal
  requires p.val != chosenVb.v
  decreases p.bal
  ensures false
{
  /* Proof by contradiction. 
  * p's supporting promise quorum, prQuorum, has an intersecting accId with the choosing 
  * quorum acQuorum. Because p.bal > chosenVb.b, by AcceptMsgImpliesLargerPromiseCarriesVb
  * we know that the Promise msg prom from accId has prom.vbOpt.Some?. Furthermore, 
  * prom.vbOpt.b >= chosenVb.b.
  *
  * Because prQuorum supports proposal p, there must be a b' such that 
  * PromiseSetHighestVB(c, v, prQ, p.bal, b', p.val), and 
  * chosenVb.b <= b'. By PromiseVbImpliesAccepted and AcceptMessageImpliesProposed and 
  * OneValuePerProposeBallot, we have chosenVb.b < b'.
  * Moreover, PromiseBalLargerThanAccepted gives prom'.vbOpt.bal < p.b.
  * As such, we have chosenVb.b < prom'.vbOpt.bal < prom'.vbOpt.bal < p.b.
  * By PromiseVbImpliesAccepted and AcceptMessageImpliesProposed, prom' is supported by 
  * a corresponding prop'. 
  * Finally, we make recursive call using prop' */

  var prQuorum :| PromiseQuorumSupportsVal(c, v, prQuorum, p.bal, p.val); // promise quorum supporting p
  var acQuorum :| IsAcceptQuorum(c, v, acQuorum, chosenVb);
  var accId := IntersectingAcceptorInPromiseAndAcceptQuorum(c, v, prQuorum, p.bal, acQuorum, chosenVb);  // witness
  var prom: Message :| prom in prQuorum && prom.acc == accId;  // witness

  var b' :| PromiseSetHighestVB(c, v, prQuorum, p.bal, VB(p.val, b'));
  var prom' :| WinningPromiseMessageInQuorum(c, v, prQuorum, p.bal, VB(p.val, b'),  prom');

  // Corresponding Propose to prom', by PromiseVbImpliesAccepted and AcceptMessageImpliesProposed
  var prop' := Propose(b', p.val);
  assert prop' in v.network.sentMsgs;

  ChosenAndConflictingProposeImpliesFalse(c, v, chosenVb, prop');
  assert false;
}


lemma InvNextChosenValImpliesProposeOnlyVal(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires AcceptMessageImpliesProposed(c, v')
  requires AcceptMessagesValid(c, v')
  requires ProposeBackedByPromiseQuorum(c, v')
  requires OneValuePerProposeBallot(c, v')
  requires AcceptMsgImpliesLargerPromiseCarriesVb(c, v')
  requires PromiseVbImpliesAccepted(c, v')
  requires PromiseBalLargerThanAccepted(c, v')
  ensures ChosenValImpliesProposeOnlyVal(c, v')
{
  InvImpliesChosenValImpliesPromiseQuorumSeesBal(c, v);
  var dsStep :| NextStep(c, v, v', dsStep);
  var actor, msgOps := dsStep.actor, dsStep.msgOps;
  if dsStep.LeaderStep? {
    /* This case is trivial. This is because if something has already been chosen, then
    * then leader can only propose same val by ChosenValImpliesPromiseQuorumSeesBal.
    * Otherwise, the post-condition is vacuously true, as nothing new can be chosen */
    forall vb, propose | 
      && Chosen(c, v', vb)
      && IsProposeMessage(v', propose)
      && propose.bal > vb.b
    ensures
      propose.val == vb.v
    {
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
      assert Chosen(c, v, vb);
      var l := v.leaders[actor];
      if |l.receivedPromises| >= c.f+1 && propose !in v.network.sentMsgs {
        var pquorum :| LeaderPromiseSetProperties(c, v, actor, pquorum);  // by HighestHeardBackedByReceivedPromises
        assert IsPromiseQuorum(c, v, pquorum, actor);  // trigger 
        // remaining proof is true by ChosenValImpliesPromiseQuorumSeesBal
      }
    }
  } else if dsStep.AcceptorStep? {
    var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
    var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
    if step.ReceiveStep? && msgOps.recv.value.Propose? {
      InvNextChosenValImpliesProposeOnlyValAcceptorRecvStep(c, v, v', dsStep, step);
    } else {
      forall vb | Chosen(c, v', vb)
      ensures Chosen(c, v, vb)
      {
        var quorum :| IsAcceptQuorum(c, v', quorum, vb);  // witness
        assert IsAcceptQuorum(c, v, quorum, vb);  // trigger
      }
    }
  } else {
    // Nothing new chosen
    NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
  } 
}

lemma InvNextChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires MessageInv(c, v')
  requires OneValuePerProposeBallot(c, v')
  requires AcceptMessageImpliesProposed(c, v')
  requires PromiseVbImpliesAccepted(c, v')
  requires ChosenValImpliesProposeOnlyVal(c, v')
  ensures ChosenValImpliesLeaderOnlyHearsVal(c, v')
{
  forall chosenVb, idx | 
    && Chosen(c, v', chosenVb) 
    && c.ValidLeaderIdx(idx)
    && v'.leaders[idx].highestHeardBallot.Some?
    && v'.leaders[idx].highestHeardBallot.value >= chosenVb.b
  ensures
    v'.leaders[idx].value == chosenVb.v
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.LeaderStep? || dsStep.LearnerStep? {
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
    } else {
      /* Suppose leader l has l.value != chosenVb.v. By LeaderValidHighestHeard, there is
      * is a Promise message carrying VB(l.value, l.highestHeard). 
      * By PromiseVbImpliesAccepted, there is an Accept message for VB(l.value, l.highestHeard).
      * Note that l.highestHeard != chosenVb.b by OneValuePerAcceptBallotLemma.
      * By AcceptMessageImpliesProposed, there is a Propose for VB(l.value, l.highestHeard)
      * This violates ChosenValImpliesProposeOnlyVal. */ 
      var lc, l, l' := c.leaderConstants[idx], v.leaders[idx], v'.leaders[idx];
      if l'.value != chosenVb.v {
        var prom :| && IsPromiseMessage(v', prom)  // by LeaderValidHighestHeard
                    && prom.bal == lc.id
                    && prom.vbOpt == Some(VB(l'.value, l'.highestHeardBallot.value));
        OneValuePerAcceptBallotLemma(c, v');
        assert false;  // violates ChosenValImpliesProposeOnlyVal
      }
    }
  }
}

lemma InvNextAtMostOneChosenVal(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires OneValuePerProposeBallot(c, v')
  requires AcceptMessageImpliesProposed(c, v')
  requires ChosenValImpliesProposeOnlyVal(c, v')
  ensures AtMostOneChosenVal(c, v')
{}



// Lemma: For any Learn message, that learned value must have been chosen
lemma LearnedImpliesChosen(c: Constants, v: Variables, learnMsg: Message)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires IsLearnMessage(v, learnMsg)
  ensures Chosen(c, v, VB(learnMsg.val, learnMsg.bal))
{
  /* Suppose learnMsg(lnr, bal, val) in network. Then by LearnMsgsValid, lnr has a 
    a quorum of receivedAccepts for vb := VB(bal, val). By LearnerValidReceivedAccepts,
    there is a corresponding set of Accept(vb, _) messages in the network. */
  var l := v.learners[learnMsg.lnr];
  var vb := VB(learnMsg.val, learnMsg.bal);
  var quorum := QuorumFromReceivedAccepts(l.receivedAccepts[vb], vb);  // witness
  assert IsAcceptQuorum(c, v, quorum, vb);  // trigger
}

// Lemma: No new values can be chosen during Leader and Learner steps
lemma NoNewChosenInLeaderOrLearnerSteps(c: Constants, v: Variables, v': Variables, dsStep: Step) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v, v', dsStep)
  requires dsStep.LeaderStep? || dsStep.LearnerStep?
  ensures forall vb | Chosen(c, v', vb) :: Chosen(c, v, vb)
{
  forall vb | Chosen(c, v', vb)
  ensures Chosen(c, v, vb)
  {
    var quorum :| IsAcceptQuorum(c, v', quorum, vb);  // witness
    assert IsAcceptQuorum(c, v, quorum, vb);  // trigger
  }
}



// Lemma: If at most one value can be chosen, then the Agreement property is true
lemma AtMostOneChosenImpliesAgreement(c: Constants, v: Variables) 
  requires v.WF(c)
  requires MessageInv(c, v)
  requires AtMostOneChosenVal(c, v)
  ensures Agreement(c, v)
{
  /* Proof by contradiction. Suppose that v violates agreement, such that there are two
    Learn messages with differnt values. Then by LearnedImpliesChosen, two different 
    values are chosen, thus violating AtMostOneChosenVal */
  if !Agreement(c, v) {
    var m1, m2 :| 
      && IsLearnMessage(v, m1)
      && IsLearnMessage(v, m2)
      && m1.val != m2.val;
    LearnedImpliesChosen(c, v, m1);
    LearnedImpliesChosen(c, v, m2);
    assert false;
  }
}

/***************************************************************************************
*                                        Utils                                         *
***************************************************************************************/

// This is a consequence of OneValuePerProposeBallot, and AcceptMessageImpliesProposed
predicate OneValuePerAcceptBallot(c: Constants, v: Variables)
{
  forall a1, a2 | 
    && IsAcceptMessage(v, a1)
    && IsAcceptMessage(v, a2)
    && a1.vb.b == a2.vb.b
  ::
    a1.vb.v == a2.vb.v
}

lemma OneValuePerAcceptBallotLemma(c: Constants, v: Variables)
  requires OneValuePerProposeBallot(c, v)
  requires AcceptMessageImpliesProposed(c, v)
  ensures OneValuePerAcceptBallot(c, v)
{}


// Implied by Inv: If vb is chosen, then all Promise quorums > vb.b must observe a ballot >= vb.b
predicate ChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, quorum, pbal | 
    && Chosen(c, v, vb)
    && IsPromiseQuorum(c, v, quorum, pbal)
    && vb.b < pbal
  ::
    exists m: Message :: m in quorum && m.vbOpt.Some? && vb.b <= m.vbOpt.value.b
}

// lemma: Inv implies that ChosenValImpliesPromiseQuorumSeesBal
lemma InvImpliesChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
  requires Inv(c, v)
  requires AcceptMsgImpliesLargerPromiseCarriesVb(c, v)
  ensures ChosenValImpliesPromiseQuorumSeesBal(c, v)
{
  forall chosenVb, prQuorum, pbal | 
    && Chosen(c, v, chosenVb)
    && IsPromiseQuorum(c, v, prQuorum, pbal)
    && chosenVb.b < pbal
  ensures
    exists m: Message :: m in prQuorum && m.vbOpt.Some? && chosenVb.b <= m.vbOpt.value.b
  {
    var acQuorum :| IsAcceptQuorum(c, v, acQuorum, chosenVb);
    var accId := IntersectingAcceptorInPromiseAndAcceptQuorum(c, v, prQuorum, pbal, acQuorum, chosenVb);
    var m: Message :| m in prQuorum && m.acc == accId;  // witness
    // m satisfies postcondition via AcceptMsgImpliesLargerPromiseCarriesVb(c, v')
  }
}

// Lemma: Given b1 < b2, there is a finite, strictly ordered sequence 
// [b1, b_a, b_b, ... , b_2] such that for all ballots b where b1 < b < b2, b in seq
lemma FiniteBallots(b1: LeaderId, b2: LeaderId) returns (res: seq<LeaderId>)
  requires b1 < b2
  ensures SeqIsComplete(res, b1, b2)
{
  if b1 == b2 - 1 {
    return [b1, b2];
  } else {
    var sub := FiniteBallots(b1, b2-1);
    return sub + [b2];
  }
}

lemma QuorumFromReceivedAccepts(s: set<AcceptorId>, vb: ValBal) returns (q: set<Message>)
  decreases s
  ensures |q| == |s|
  ensures forall m | m in q :: m.Accept?
  ensures forall m | m in q :: m.vb == vb
  ensures forall m | m in q :: m.acc in s
{
  if |s| == 0 {
    return {};
  } else {
    var acc :| acc in s;
    var subq := QuorumFromReceivedAccepts(s-{acc}, vb);
    return subq + {Accept(vb, acc)};
  }
}

lemma AcceptorsFromPromiseSet(c: Constants, v: Variables, prSet: set<Message>, prBal: LeaderId) 
returns (accs: set<AcceptorId>)  
  requires IsPromiseSet(c, v, prSet, prBal)
  ensures forall a | a in accs 
    :: (exists pr :: pr in prSet && pr.acc == a)
  ensures |accs| == |prSet|
{
  if |prSet| == 0 {
    accs := {};
  } else {
    var p :| p in prSet;
    var accs' := AcceptorsFromPromiseSet(c, v, prSet-{p}, prBal);
    accs := accs' + {p.acc};
  }
}

lemma AcceptorsFromAcceptSet(c: Constants, v: Variables, acSet: set<Message>, vb: ValBal)
returns (accs: set<AcceptorId>)  
  requires IsAcceptSet(c, v, acSet, vb)
  ensures forall a | a in accs 
    :: (exists ac :: ac in acSet && ac.acc == a)
  ensures |accs| == |acSet|
{
  if |acSet| == 0 {
    accs := {};
  } else {
    var a :| a in acSet;
    var accs' := AcceptorsFromAcceptSet(c, v, acSet-{a}, vb);
    accs := accs' + {a.acc};
  }
}

lemma IntersectingAcceptorInPromiseAndAcceptQuorum(c: Constants, v: Variables,
    prQuorum: set<Message>, prBal: LeaderId, acQuorum: set<Message>, vb: ValBal) 
returns (accId: AcceptorId)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires IsPromiseQuorum(c, v, prQuorum, prBal)
  requires IsAcceptQuorum(c, v, acQuorum, vb)
  ensures exists promise, accept :: 
    && promise in prQuorum
    && accept in acQuorum
    && promise.acc == accId
    && accept.acc == accId
{
  var prAccs := AcceptorsFromPromiseSet(c, v, prQuorum, prBal);
  var acAccs := AcceptorsFromAcceptSet(c, v, acQuorum, vb);
  var allAccs := set id | 0 <= id < 2*c.f+1;
  SetComprehensionSize(2*c.f+1);
  var commonAcc := QuorumIntersection(allAccs , prAccs, acAccs);
  return commonAcc;
}

predicate IsPromiseSet(c: Constants, v: Variables, pset: set<Message>, bal: LeaderId) {
  && (forall m | m in pset ::
    && IsPromiseMessage(v, m)
    && m.bal == bal)
  && PromiseSetDistinctAccs(c, v, pset)
}

predicate PromiseSetDistinctAccs(c: Constants, v: Variables, pset: set<Message>) 
  requires forall m | m in pset :: m.Promise?
{
  forall m1, m2 | m1 in pset && m2 in pset && m1.acc == m2.acc
      :: m1 == m2
}

predicate IsPromiseQuorum(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId) {
  && |quorum| >= c.f+1
  && IsPromiseSet(c, v, quorum, bal)
}

predicate PromiseQuorumSupportsVal(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId, val: Value) {
  && IsPromiseQuorum(c, v, quorum, bal)
  && (
    || PromiseSetEmptyVB(c, v, quorum, bal)
    || (exists hsbal :: PromiseSetHighestVB(c, v, quorum, bal, VB(val, hsbal)))
  )
}

predicate PromiseSetEmptyVB(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId)
  requires IsPromiseSet(c, v, pset, qbal)
{
  forall m | m in pset :: m.vbOpt == None
}

predicate PromiseSetHighestVB(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, vb: ValBal)
  requires IsPromiseSet(c, v, pset, qbal)
{
  exists m :: WinningPromiseMessageInQuorum(c, v, pset, qbal, vb, m)
}

predicate WinningPromiseMessageInQuorum(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, vb: ValBal, m: Message)
  requires IsPromiseSet(c, v, pset, qbal)
{
    && m in pset 
    && m.vbOpt == Some(vb)
    && (forall other | 
          && other in pset 
          && other.vbOpt.Some?
        ::
          other.vbOpt.value.b <= vb.b
      )
}

predicate IsAcceptSet(c: Constants, v: Variables, aset: set<Message>, vb: ValBal) {
  forall m | m in aset ::
    && IsAcceptMessage(v, m)
    && m.vb == vb
}

predicate IsAcceptQuorum(c: Constants, v: Variables, aset: set<Message>, vb: ValBal) {
  && |aset| >= c.f+1
  && IsAcceptSet(c, v, aset, vb)
}
}  // end module PaxosProof

