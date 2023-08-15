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
ghost predicate Chosen(c: Constants, v: Variables, vb: ValBal) {
  exists quorum: set<Message> :: IsAcceptQuorum(c, v, quorum, vb)
}


// Acceptor updates its promised ballot based on a Prepare/Propose message carrying 
// that ballot
ghost predicate AcceptorValidPromised(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, b | c.ValidAcceptorIdx(idx) && v.acceptors[idx].promised == Some(b)
  :: (exists m: Message ::
        && (IsPrepareMessage(v, m) || IsProposeMessage(v, m))
        && m.bal == b
    )
}

// Acceptor updates its acceptedVB based on a Propose message carrying that ballot 
// and value, and there is also a corresponding Accept message
ghost predicate AcceptorValidAcceptedVB(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, val, bal | 
    && c.ValidAcceptorIdx(idx) 
    && v.acceptors[idx].acceptedVB == Some(VB(val, bal))
  :: 
    && Propose(bal, val) in v.network.sentMsgs
    && Accept(VB(val, bal), c.acceptorConstants[idx].id) in v.network.sentMsgs
}


// Tony: I once thought this was a message invariant, but it isn't --- it depends on 
// application level knowledge that l.receivedAccepts is monotonically increasing.
// For every Learn(lnr, val) message in the network, the learner must have a quorum of
// accepts for that val, at some common ballot
// Tony update a week later: monotonic variables need to be annotated by the user. Hence,
// if user were to annotate l.receivedAccepts as a monotonic set, then this is a proper 
// message invariant
ghost predicate LearnMsgsValid(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall lnr:LearnerId, bal, val | 
    Learn(lnr, bal, val) in v.network.sentMsgs
  :: 
    && var vb := VB(val, bal);
    && vb in v.learners[lnr].receivedAccepts
    && |v.learners[lnr].receivedAccepts[vb]| >= c.f+1
}

// Tony: I once thought this was a message invariant, but it isn't --- it depends on 
// application level knowledge that a.promised is monotonically increasing.
// Every Promise message in the network has a ballot upper-bounded by the promised ballot
// of the source acceptor
ghost predicate AcceptorPromisedMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, prom | 
    && c.ValidAcceptorIdx(idx) 
    && IsPromiseMessage(v, prom)
    && prom.acc == c.acceptorConstants[idx].id
  ::
    && v.acceptors[idx].promised.Some?
    && prom.bal <= v.acceptors[idx].promised.value
}

ghost predicate OneValuePerProposeBallot(c: Constants, v: Variables)
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
ghost predicate ProposeImpliesLeaderState(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall p | IsProposeMessage(v, p) 
  ::  && |v.leaders[p.bal].receivedPromises| >= c.f+1
      && v.leaders[p.bal].value == p.val
}

ghost predicate PromiseVbImpliesAccepted(c: Constants, v: Variables) {
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
ghost predicate AcceptMessageImpliesProposed(c: Constants, v: Variables) {
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
ghost predicate AcceptMessagesValid(c: Constants, v: Variables)
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
ghost predicate AcceptMsgImpliesLargerPromiseCarriesVb(c: Constants, v: Variables) 
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
ghost predicate HighestHeardBackedByReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx | c.ValidLeaderIdx(idx)
  :: (
    && var ldr := v.leaders[idx];
    && exists pset :: LeaderPromiseSetProperties(c, v, idx, pset)
  )
}

ghost predicate LeaderPromiseSetProperties(c: Constants, v: Variables, idx: int, pset: set<Message>) 
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
ghost predicate ProposeBackedByPromiseQuorum(c: Constants, v: Variables) {
  forall p | IsProposeMessage(v, p)
  :: (exists quorum :: PromiseQuorumSupportsVal(c, v, quorum, p.bal, p.val))
}

// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
ghost predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
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
ghost predicate PromiseBalLargerThanAccepted(c: Constants, v: Variables) {
  forall prom | 
    && IsPromiseMessage(v, prom)
    && prom.vbOpt.Some?
  ::
    prom.vbOpt.value.b < prom.bal
}

// Inv: If vb is chosen, then for all Propose messages that have bal > vb.b, they must have 
// value == vb.v
// Tony: Using monotonic transformations, by recording the entire history of leader 
// (value, highestHeardBallot) pairs, this becomes implicit from ChosenValImpliesLeaderOnlyHearsVal,
// rather than a network property as an application invariant.
ghost predicate ChosenValImpliesProposeOnlyVal(c: Constants, v: Variables) {
  forall vb, propose | 
    && Chosen(c, v, vb)
    && IsProposeMessage(v, propose)
    && propose.bal > vb.b
  ::
    propose.val == vb.v
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  && AcceptorValidPromised(c, v)
  && AcceptorValidAcceptedVB(c, v)
  && LearnMsgsValid(c, v)
  && AcceptorPromisedMonotonic(c, v)
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
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Agreement(c, v)
}


/***************************************************************************************
*                                Top-level Obligations                                 *
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
  InvNextAcceptorValidPromised(c, v, v');
  InvNextAcceptorValidAcceptedVB(c, v, v');
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
  MessageAndApplicationInvImpliesAgreement(c, v');
  assert LearnMsgsValid(c, v');
  assert AcceptorPromisedMonotonic(c, v');
}



/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextAcceptorValidPromised(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidPromised(c, v')
{}

lemma InvNextAcceptorValidAcceptedVB(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidAcceptedVB(c, v')
{}

lemma InvNextProposeImpliesLeaderState(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ProposeImpliesLeaderState(c, v')
  ensures OneValuePerProposeBallot(c, v)  // Implied by ProposeImpliesLeaderState
  ensures OneValuePerProposeBallot(c, v')  // Implied by ProposeImpliesLeaderState
{}

lemma {:timeLimitMultiplier 3} InvNextPromiseVbImpliesAccepted(c: Constants, v: Variables, v': Variables)
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

lemma {:timeLimitMultiplier 4} InvNextHighestHeardBackedByReceivedPromises(c: Constants, v: Variables, v': Variables) 
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

// Helper lemma for InvNextProposeBackedByPromiseQuorum
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

// This is the core Paxos lemma
lemma InvNextChosenValImpliesProposeOnlyVal(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromised(c, v')
  requires AcceptorValidAcceptedVB(c, v')
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
  forall vb, propose | 
    && Chosen(c, v', vb)
    && IsProposeMessage(v', propose)
    && propose.bal > vb.b
  ensures
    propose.val == vb.v
  {
    if dsStep.LeaderStep? {
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
      assert Chosen(c, v, vb);
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
      if step.ProposeStep? && propose !in v.network.sentMsgs {
        /* Suppose vb has been chosen in state v, and propose is of some v' with vb.v != v'. 
        * By HighestHeardBackedByReceivedPromises, this v' was carried by a Promise message
        * with winning ballot b' <= vb.b. 
        * By ChosenValImpliesPromiseQuorumSeesBal, b' >= vb.b. 
        * By PromiseVbImpliesAccepted, there is an Accept(VB(v', b')). By AcceptMessageImpliesProposed,
        * there is a Propose(b', v') in the state v. This contradicts ChosenValImpliesProposeOnlyVal. */
        if propose.val != vb.v {
          assert LeaderHost.NextProposeStep(lc, l, l', msgOps);
          var pquorum :| LeaderPromiseSetProperties(c, v, actor, pquorum);  // by HighestHeardBackedByReceivedPromises
          assert IsPromiseQuorum(c, v, pquorum, actor);   // trigger 
          assert l.highestHeardBallot.Some?;              // trigger
          assert false;
        }
      }
    } else if dsStep.AcceptorStep? {
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.MaybeAcceptStep? {
        var new_prop := a.pendingMsg.value;
        if !Chosen(c, v, vb) && propose.val != vb.v {
          /* This is a point where something can suddenly be chosen.*/
          assert propose.bal > vb.b;
          MessageInvInductive(c, v, v');
          ChosenAndConflictingProposeImpliesFalse(c, v', vb, propose);
          assert false;
        }
      } else {
        // vb already chosen in state v
        var quorum :| IsAcceptQuorum(c, v', quorum, vb);  // witness
        assert IsAcceptQuorum(c, v, quorum, vb);          // trigger
      }
    } else {
      // Nothing new chosen
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
    } 
  }
}

// Helper lemma for InvNextChosenValImpliesProposeOnlyVal. Here lies most of the heavy-lifting Paxos logic
lemma ChosenAndConflictingProposeImpliesFalse(c: Constants, v: Variables, chosenVb: ValBal, p: Message) 
  requires MessageInv(c, v)
  requires OneValuePerProposeBallot(c, v)
  requires AcceptMessageImpliesProposed(c, v)
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


/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/


// Lemma: For any Learn message, that learned value must have been chosen
lemma LearnedImpliesChosen(c: Constants, v: Variables, learnMsg: Message)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires LearnMsgsValid(c, v)
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

// Lemma: If MessageInv and ApplicationInv, then the Agreement property is true
lemma MessageAndApplicationInvImpliesAgreement(c: Constants, v: Variables) 
  requires MessageInv(c, v)
  requires ApplicationInv(c, v)
  ensures Agreement(c, v)
{
  /* Proof by contradiction. Suppose that v violates agreement, such that there are two
    Learn messages with differnt values. Then by LearnedImpliesChosen, two different 
    values are chosen, thus violating fact that at most one value is chosen 
    (at most one chosen value is implied by application invs) */
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


// Implied by Inv: If vb is chosen, then all Promise quorums > vb.b must observe a ballot >= vb.b
ghost predicate ChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
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

ghost predicate IsPromiseSet(c: Constants, v: Variables, pset: set<Message>, bal: LeaderId) {
  && (forall m | m in pset ::
    && IsPromiseMessage(v, m)
    && m.bal == bal)
  && PromiseSetDistinctAccs(c, v, pset)
}

ghost predicate PromiseSetDistinctAccs(c: Constants, v: Variables, pset: set<Message>) 
  requires forall m | m in pset :: m.Promise?
{
  forall m1, m2 | m1 in pset && m2 in pset && m1.acc == m2.acc
      :: m1 == m2
}

ghost predicate IsPromiseQuorum(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId) {
  && |quorum| >= c.f+1
  && IsPromiseSet(c, v, quorum, bal)
}

ghost predicate PromiseQuorumSupportsVal(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId, val: Value) {
  && IsPromiseQuorum(c, v, quorum, bal)
  && (
    || PromiseSetEmptyVB(c, v, quorum, bal)
    || (exists hsbal :: PromiseSetHighestVB(c, v, quorum, bal, VB(val, hsbal)))
  )
}

ghost predicate PromiseSetEmptyVB(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId)
  requires IsPromiseSet(c, v, pset, qbal)
{
  forall m | m in pset :: m.vbOpt == None
}

ghost predicate PromiseSetHighestVB(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, vb: ValBal)
  requires IsPromiseSet(c, v, pset, qbal)
{
  exists m :: WinningPromiseMessageInQuorum(c, v, pset, qbal, vb, m)
}

ghost predicate WinningPromiseMessageInQuorum(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, vb: ValBal, m: Message)
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

ghost predicate IsAcceptSet(c: Constants, v: Variables, aset: set<Message>, vb: ValBal) {
  forall m | m in aset ::
    && IsAcceptMessage(v, m)
    && m.vb == vb
}

ghost predicate IsAcceptQuorum(c: Constants, v: Variables, aset: set<Message>, vb: ValBal) {
  && |aset| >= c.f+1
  && IsAcceptSet(c, v, aset, vb)
}
}  // end module PaxosProof

