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


// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  && LeaderStateMonotonic(c, v)
  && LeaderHighestHeardBackedByReceivedPromises(c, v)
  && ProposeImpliesLeaderState(c, v)
  && AcceptorStateMonotonic(c, v)
  && LearnedValuesValid(c, v)
  && ChosenValImpliesProposeOnlyVal(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Agreement(c, v)
}

// Leader local state's monotonic properties
ghost predicate LeaderStateMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx | c.ValidLeaderIdx(idx)
  ::  && SetMonotoneIncreasing(v.leaders[idx].receivedPromises)
      && SeqOptionMonotoneIncreasing(v.leaders[idx].highestHeardBal)
}


// Highest heard ballot and value backed by received promises, corresponds to HighestHeardBackedByReceivedPromises
ghost predicate LeaderHighestHeardBackedByReceivedPromises(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, i |
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].highestHeardBal|
  ::
    LeaderPromiseSetProperties(c, v, idx, i)
}

ghost predicate LeaderPromiseSetProperties(c: Constants, v: Variables, idx: int, i: int) 
  requires v.WF(c)
  requires c.ValidLeaderIdx(idx)
  requires 0 <= i < |v.leaders[idx].highestHeardBal|
{
  var ldr := v.leaders[idx];
  var cldr := c.leaderConstants[idx];
  var pset := ldr.receivedPromises[i];
  var hbal := ldr.highestHeardBal[i];
  var val := ldr.value[i];
  && IsPromiseSet(pset, cldr.id)
  && (hbal.Some? ==> PromiseSetHighestVB(pset, cldr.id, VB(val, hbal.value)))
  && (hbal.None? ==> PromiseSetEmptyVB(pset, cldr.id))
}

// Corresponds to ProposeImpliesLeaderState. This implies LeaderProposesOneValue, 
// which in turn helps imply at most one value is chosen
ghost predicate ProposeImpliesLeaderState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].proposed|
  ::
    LeaderStateValid(c, v, idx, i)
}

ghost predicate LeaderStateValid(c: Constants, v: Variables, idx: nat, i: nat)
  requires v.WF(c)
  requires c.ValidLeaderIdx(idx)
  requires 0 <= i < |v.leaders[idx].proposed|
{
  && |Last(v.leaders[idx].receivedPromises)| >= c.f+1
  && Last(v.leaders[idx].value) == v.leaders[idx].proposed[i]
}

// This is a corollary of ProposeImpliesLeaderState, and implies at most one value is chosen
ghost predicate LeaderProposesOneValue(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].proposed|
    && 0 <= j < |v.leaders[idx].proposed|
  ::
    v.leaders[idx].proposed[i] == v.leaders[idx].proposed[j]
}

// Acceptor local state's monotonic properties
// This covers AcceptorPromisedMonotonic and AcceptorPromisedLargerThanAccepted and
// PromiseBalLargerThanAccepted and AcceptMsgImpliesLargerPromiseCarriesVb
ghost predicate AcceptorStateMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx | c.ValidAcceptorIdx(idx) 
  :: 
    && SeqMonotoneIncreasing(v.acceptors[idx].promised)
    && SeqOptionVBMonotoneIncreasing(v.acceptors[idx].acceptedVB)
    && (forall p | p in v.acceptors[idx].sentPromises && p.Promise? && p.vbOpt.Some? :: p.vbOpt.value.b < p.bal)
    && (forall i |
          && 0 <= i < |v.acceptors[idx].promised| 
          && v.acceptors[idx].acceptedVB[i].Some?
        ::
          v.acceptors[idx].acceptedVB[i].value.b <= v.acceptors[idx].promised[i]
    )
}

// Corresponds to LearnMsgsValid in non-monotonic land
ghost predicate LearnedValuesValid(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb | 
    && c.ValidLearnerIdx(idx)
    && v.learners[idx].Learned(vb)
  ::
    && vb in v.learners[idx].receivedAccepts
    && (exists i ::  
        && 0 <= i < |v.learners[idx].receivedAccepts[vb]|
        && |v.learners[idx].receivedAccepts[vb][i]| >= c.f+1)
}


// The heavy-hitter inv: If vb is chosen, then for all Leader hosts l such that l's ballot > vb.b, all 
// values in l.proposed messages equals vb.v
ghost predicate ChosenValImpliesProposeOnlyVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, idx, i | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(idx)
    && vb.b < c.leaderConstants[idx].id
    && 0 <= i < |v.leaders[idx].proposed|
  ::
    v.leaders[idx].proposed[i] == vb.v
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
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
  InvNextLeaderHighestHeardBackedByReceivedPromises(c, v, v');
  InvNextProposeImpliesLeaderState(c, v, v');
  InvNextAcceptorStateMonotonic(c, v, v');
  InvNextLearnedValuesValid(c, v, v');
  InvNextChosenValImpliesProposeOnlyVal(c, v, v');
  MessageAndApplicationInvImpliesAgreement(c, v');
}



/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextLeaderHighestHeardBackedByReceivedPromises(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardBackedByReceivedPromises(c, v')
{
  forall idx, i |
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v'.leaders[idx].highestHeardBal|
  ensures
    LeaderPromiseSetProperties(c, v', idx, i)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.LeaderStep? {
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
      if  && actor == idx  
          && step.ReceiveStep?
          && msgOps.recv.value.Promise? 
          && |Last(l.receivedPromises)| <= c.f
          && l.NewAcceptorPromise(lc, msgOps.recv.value.bal, msgOps.recv.value.acc)
          && i == |l'.receivedPromises|-1
      {
        assert LeaderPromiseSetProperties(c, v, idx, i-1);  // trigger
        var prom := msgOps.recv.value;
        var pset := Last(l'.receivedPromises);
        var hbal := l'.highestHeardBal[i];
        if hbal.Some? {
          var vb' := VB(l'.value[i], hbal.value);
          if l.highestHeardBal[i-1].Some? {
            var doUpdate := && prom.vbOpt.Some? 
                            && (l.HighestHeardNone() || prom.vbOpt.value.b > l.GetHighestHeard());
            if doUpdate {
              assert WinningPromiseMessageInQuorum(pset, lc.id, vb', prom);  // trigger
            } else {
              // witness and trigger
              var vb := VB(l.value[i-1], l.highestHeardBal[i-1].value);
              var m :| WinningPromiseMessageInQuorum(l.receivedPromises[i-1], lc.id, vb, m);
              assert WinningPromiseMessageInQuorum(pset, lc.id, vb, m);
            }
          } else {
            assert WinningPromiseMessageInQuorum(pset, lc.id, vb', prom);  // trigger
          }
        }
      } else {
        assert LeaderPromiseSetProperties(c, v, idx, i);  // trigger
      }
    } else {
      assert LeaderPromiseSetProperties(c, v, idx, i);  // trigger
    }
  }
}

lemma InvNextProposeImpliesLeaderState(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ProposeImpliesLeaderState(c, v')
  ensures LeaderProposesOneValue(c, v')
{
  forall idx, i | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v'.leaders[idx].proposed|
  ensures
    LeaderStateValid(c, v', idx, i)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if dsStep.LeaderStep? && idx == actor
    {
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
      if step.ProposeStep? && i == |l'.proposed| - 1 {
        assert LeaderStateValid(c, v', idx, i);
      } else {
        assert LeaderStateValid(c, v, idx, i);  // trigger
      }
    } else {
      assert LeaderStateValid(c, v, idx, i);    // trigger
    }
  }
  
  // Prove corollary LeaderProposesOneValue
  forall idx, i, j | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v'.leaders[idx].proposed|
    && 0 <= j < |v'.leaders[idx].proposed|
  ensures
    v'.leaders[idx].proposed[i] == v'.leaders[idx].proposed[j]
  {
    // triggers
    assert LeaderStateValid(c, v', idx, i);
    assert LeaderStateValid(c, v', idx, j);
  }
}

lemma InvNextAcceptorStateMonotonic(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AcceptorStateMonotonic(c, v')
{}



lemma InvNextLearnedValuesValid(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnedValuesValid(c, v')
{
  forall idx, vb | 
    && c.ValidLearnerIdx(idx)
    && v'.learners[idx].Learned(vb)
  ensures
    && vb in v'.learners[idx].receivedAccepts
    && (exists i ::  
        && 0 <= i < |v'.learners[idx].receivedAccepts[vb]|
        && |v'.learners[idx].receivedAccepts[vb][i]| >= c.f+1)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.LearnerStep? 
       && idx == actor
    {
      var lc, l, l' := c.learnerConstants[actor], v.learners[actor], v'.learners[actor];
      var step :| LearnerHost.NextStep(lc, l, l', step, msgOps);
      if step.LearnStep? {
        var i := |v'.learners[idx].receivedAccepts[vb]| - 1;
        assert |v'.learners[idx].receivedAccepts[vb][i]| >= c.f+1;  // trigger
      } else if step.ReceiveStep? && msgOps.recv.value.Accept? {
        // witness and trigger
        var i :| 0 <= i < |l.receivedAccepts[vb]| && |l.receivedAccepts[vb][i]| >= c.f+1;
        assert 0 <= i < |l'.receivedAccepts[vb]| && |l'.receivedAccepts[vb][i]| >= c.f+1;
      }
    }
  }
}

// This is the core Paxos lemma
lemma InvNextChosenValImpliesProposeOnlyVal(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderStateMonotonic(c, v')
  requires LeaderHighestHeardBackedByReceivedPromises(c, v')
  requires ProposeImpliesLeaderState(c, v')
  requires AcceptorStateMonotonic(c, v')
  requires LearnedValuesValid(c, v')
  requires LeaderProposesOneValue(c, v')
  requires LeaderProposesOneValue(c, v')
  ensures ChosenValImpliesProposeOnlyVal(c, v')
{
  InvImpliesChosenValImpliesPromiseQuorumSeesBal(c, v);
  var dsStep :| NextStep(c, v, v', dsStep);
  var actor, msgOps := dsStep.actor, dsStep.msgOps;
  forall vb, idx, i | 
    && Chosen(c, v', vb)
    && c.ValidLeaderIdx(idx)
    && vb.b < c.leaderConstants[idx].id
    && 0 <= i < |v'.leaders[idx].proposed|
  ensures
    v'.leaders[idx].proposed[i] == vb.v
  {
    if dsStep.LeaderStep? {
        NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
        assert Chosen(c, v, vb);
        var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if actor == idx && step.ProposeStep? && i == |l'.proposed|-1 {
          /* Suppose vb has been chosen in state v, and the new proposal is value v' != vb.v. 
          * By LeaderHighestHeardBackedByReceivedPromises, there is a promise message m in 
          * l.receivedPromises[i] that accepted v' at some b' <= vb.b. 
          * By ChosenValImpliesPromiseQuorumSeesBal, b' >= vb.b. 
          * By ValidPromiseMessage, there is an acceptor that accepted (v', b').
          * By AcceptorValidAcceptedVB, there is a Propose(b', v') in the network of state v.
          * This then contradicts ChosenValImpliesProposeOnlyVal. */
          var pv' := Last(l'.proposed);
          if pv' != vb.v {
            var j := |l.receivedPromises|-1;
            var pquorum := l.receivedPromises[j];
            assert LeaderPromiseSetProperties(c, v, actor, j);    // trigger
            assert IsPromiseQuorum(c, pquorum, lc.id);            // trigger
            var b' := l.highestHeardBal[j].value;
            var m :| WinningPromiseMessageInQuorum(pquorum, lc.id, VB(pv', b'), m);  // witness
            assert IsPromiseMessage(v, m);                        // trigger
            assert false;
          }
        }
    } else if dsStep.AcceptorStep? {
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.ReceiveStep? && msgOps.recv.value.Propose? {
        if !Chosen(c, v, vb) && v'.leaders[idx].proposed[i] != vb.v {
          /* This is a point where something can suddenly be chosen.*/
          MessageInvInductive(c, v, v');
          ChosenAndConflictingProposeImpliesFalse(c, v', vb, idx, i);
        }
      } else {
        var quorum :| IsAcceptorQuorum(c, v', quorum, vb);  // witness
        assert IsAcceptorQuorum(c, v, quorum, vb);          // trigger
      }
    } else {
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
    } 
  }
}


// Helper lemma for InvNextChosenValImpliesProposeOnlyVal. Here lies most of the heavy-lifting Paxos logic
lemma ChosenAndConflictingProposeImpliesFalse(c: Constants, v: Variables, chosenVb: ValBal, proposedBal: LeaderId, i: nat) 
  requires MessageInv(c, v)
  requires LeaderStateMonotonic(c, v)
  requires LeaderHighestHeardBackedByReceivedPromises(c, v)
  requires ProposeImpliesLeaderState(c, v)
  requires AcceptorStateMonotonic(c, v)
  requires LearnedValuesValid(c, v)
  requires LeaderProposesOneValue(c, v)
  requires Chosen(c, v, chosenVb)
  requires c.ValidLeaderIdx(proposedBal)
  requires 0 <= i < |v.leaders[proposedBal].proposed|
  requires v.leaders[proposedBal].proposed[i] != chosenVb.v
  requires chosenVb.b < proposedBal
  decreases proposedBal
  ensures false
{
  /* Proof by contradiction. 
  * Suppose a leader l of ballot b' > vb.b proposed value v' != chosenVb.val. Then l's
  * supporting promise quorum prQuorum has a winning promise message that reflects some
  * accepted b'' where vb.b <= b'' < proposedBal. 
  * Then there is an acceptor that accepted (pv', b''), by ValidPromiseMessage.
  * Then there is a leader that proposed (pv', b''), by AcceptorValidAcceptedVB and ValidProposeMesssage. */
  var l := v.leaders[proposedBal];
  var j := |l.receivedPromises|-1;
  var pv' := v.leaders[proposedBal].proposed[i];
  var prQuorum := l.receivedPromises[j];
  assert LeaderPromiseSetProperties(c, v, proposedBal, j);    // trigger
  assert LeaderStateValid(c, v, proposedBal, i);              // trigger
  assert IsPromiseQuorum(c, prQuorum, proposedBal);           // trigger
  var choosingAccs :| IsAcceptorQuorum(c, v, choosingAccs, chosenVb);
  var promisingAccs := AcceptorsFromPromiseSet(prQuorum, proposedBal);
  var allAccs := set id: AcceptorId | 0 <= id < 2*c.f+1;
  AcceptorSetComprehensionSize(2*c.f+1);
  assert (forall pr | pr in prQuorum :: IsPromiseMessage(v, pr));             // trigger
  var commonAcc := QuorumIntersection(allAccs, choosingAccs, promisingAccs);  // witness
  var b'' := l.highestHeardBal[j].value;
  var x, y :| 
      && 0 <= x < |v.leaders[b''].value|
      && 0 <= y < |v.leaders[b''].proposed|
      && v.leaders[b''].value[x] == pv'
      && |v.leaders[b''].receivedPromises[x]| >= c.f+1
      && pv' == v.leaders[b''].proposed[y];
  ChosenAndConflictingProposeImpliesFalse(c, v, chosenVb, b'', y);
  assert false;
}



/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/


// A quorum of Acceptors accepted the same vb
ghost predicate Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  exists quorum :: IsAcceptorQuorum(c, v, quorum, vb)
}


ghost predicate AtMostOneChosenVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
  :: vb1.v == vb2.v
}

ghost predicate IsAcceptorSet(c: Constants, aset: set<AcceptorId>) {
  forall id | id in aset :: c.ValidAcceptorIdx(id)
}

ghost predicate IsAcceptorQuorum(c: Constants, v: Variables, aset: set<AcceptorId>, vb: ValBal) 
  requires v.WF(c)
{
  && |aset| >= c.f+1
  && IsAcceptorSet(c, aset)
  && (forall id | id in aset :: v.acceptors[id].HasAccepted(vb))
}

// Lemma: For any Learner that learned a Value, that learned value must have been chosen
lemma LearnedImpliesChosen(c: Constants, v: Variables, idx: LearnerId, vb: ValBal)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires LearnedValuesValid(c, v)
  requires c.ValidLearnerIdx(idx)
  requires v.learners[idx].Learned(vb)
  ensures Chosen(c, v, vb)
{
  /* Suppose Learner l learned vb. Then it has a quorum of supporting acceptors for vb in 
  * l.receivedAccepts, by LearnedValuesValid. By LearnerValidReceivedAccepts, there is a 
  * quorum of accept messages in the network supporting vb. By ValidAcceptMessage, this 
  * means there is a quorum of acceptors that accepted vb */
  var l := v.learners[idx];
  var i :| 0 <= i < |l.receivedAccepts[vb]| && |l.receivedAccepts[vb][i]| >= c.f+1;
  var acceptorIds := l.receivedAccepts[vb][i];
  assert IsAcceptorQuorum(c, v, acceptorIds, vb);  // trigger
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
    var quorum :| IsAcceptorQuorum(c, v, quorum, vb);  // witness
    assert IsAcceptorQuorum(c, v, quorum, vb);  // trigger
  }
}


// Lemma: Get a quorum of Accept messages from a set of AcceptorIds
lemma AcceptMessagesFromAcceptorIds(ids: set<AcceptorId>, vb: ValBal) 
returns (out: set<Message>)
  ensures |out| == |ids|
  ensures forall m | m in out :: m.Accept? && m.vb == vb && m.acc in ids
{
  if |ids| == 0 {
    out := {};
  } else {
    var id :| id in ids;
    var sub := AcceptMessagesFromAcceptorIds(ids - {id}, vb);
    out := sub + {Accept(vb, id)};
  }
}

// Lemma: If MessageInv and ApplicationInv, then the Agreement property is true
lemma MessageAndApplicationInvImpliesAgreement(c: Constants, v: Variables) 
  requires MessageInv(c, v)
  requires ApplicationInv(c, v)
  requires AtMostOneChosenVal(c, v)
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
    LearnedImpliesChosen(c, v, m1.lnr, VB(m1.val, m1.bal));
    LearnedImpliesChosen(c, v, m2.lnr, VB(m2.val, m2.bal));
    assert false;
  }
}

ghost predicate SeqOptionVBMonotoneIncreasing(s: seq<Option<ValBal>>) {
  forall i, j | 
    && 0 <= i < |s| 
    && 0 <= j < |s| 
    && i <= j
    && s[i].Some?
  :: s[j].Some? && s[i].value.b <= s[j].value.b
}

ghost predicate IsPromiseSet(pset: set<Message>, bal: LeaderId) {
  && (forall m | m in pset ::
    && m.Promise?     // changed from IsPromiseMsg(v, m), to avoid application definitions mentioning network
    && m.bal == bal)
  && PromiseSetDistinctAccs(pset)
}

ghost predicate IsPromiseQuorum(c: Constants, quorum: set<Message>, bal: LeaderId) {
  && |quorum| >= c.f+1
  && IsPromiseSet(quorum, bal)
}

ghost predicate PromiseSetDistinctAccs(pset: set<Message>) 
  requires forall m | m in pset :: m.Promise?
{
  forall m1, m2 | m1 in pset && m2 in pset && m1.acc == m2.acc
      :: m1 == m2
}

ghost predicate PromiseSetEmptyVB(pset: set<Message>, qbal: LeaderId)
  requires IsPromiseSet(pset, qbal)
{
  forall m | m in pset :: m.vbOpt == None
}

ghost predicate PromiseSetHighestVB(pset: set<Message>, qbal: LeaderId, vb: ValBal)
  requires IsPromiseSet(pset, qbal)
{
  exists m :: WinningPromiseMessageInQuorum(pset, qbal, vb, m)
}

ghost predicate WinningPromiseMessageInQuorum(pset: set<Message>, qbal: LeaderId, vb: ValBal, m: Message)
  requires IsPromiseSet(pset, qbal)
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

ghost predicate AcceptorQuorumSeesVb(c: Constants, v: Variables, quorum: set<AcceptorId>, vb: ValBal) 
  requires v.WF(c)
  requires IsAcceptorSet(c, quorum)
{
  exists idx :: 
    && idx in quorum
    && v.acceptors[idx].HasAccepted(vb)
}

lemma AcceptorSetComprehensionSize(n: nat) 
  ensures |(set x: AcceptorId | 0 <= x < n)| == n
  decreases n
{
  var s := (set x: AcceptorId | 0 <= x < n);
  if n == 0 {
    assert |s| == 0;
  } else {
    AcceptorSetComprehensionSize(n-1);
    assert s == (set x: AcceptorId | 0 <= x < n-1) + {n-1};  // trigger
  }
}

// Collorary of Inv
// Tony: IsPromiseMessage refers to network, but this is ok as this is not an application
// invariant. This is simply needed to get promisingAccs <= allAccs;
ghost predicate ChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, quorum, pbal | 
    && Chosen(c, v, vb)
    && IsPromiseQuorum(c, quorum, pbal)
    && vb.b < pbal
    && (forall pr | pr in quorum :: IsPromiseMessage(v, pr))
  ::
    exists m: Message :: m in quorum && m.vbOpt.Some? && vb.b <= m.vbOpt.value.b
}

// lemma: Inv implies that ChosenValImpliesPromiseQuorumSeesBal
lemma InvImpliesChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
  requires Inv(c, v)
  ensures ChosenValImpliesPromiseQuorumSeesBal(c, v)
{
  forall vb, prQuorum, pbal | 
    && Chosen(c, v, vb)
    && IsPromiseQuorum(c, prQuorum, pbal)
    && vb.b < pbal
    && (forall pr | pr in prQuorum :: IsPromiseMessage(v, pr))
  ensures
    exists m: Message :: m in prQuorum && m.vbOpt.Some? && vb.b <= m.vbOpt.value.b
  {
    var choosingAccs :| IsAcceptorQuorum(c, v, choosingAccs, vb);
    var promisingAccs := AcceptorsFromPromiseSet(prQuorum, pbal);
    var allAccs := set id: AcceptorId | 0 <= id < 2*c.f+1;
    AcceptorSetComprehensionSize(2*c.f+1);
    var commonAcc := QuorumIntersection(allAccs, choosingAccs, promisingAccs);  // witness
  }
}

lemma AcceptorsFromPromiseSet(prSet: set<Message>, prBal: LeaderId) 
returns (accs: set<AcceptorId>)  
  requires IsPromiseSet(prSet, prBal)
  ensures forall a | a in accs 
    :: (exists pr :: pr in prSet && pr.acc == a)
  ensures |accs| == |prSet|
{
  if |prSet| == 0 {
    accs := {};
  } else {
    var p :| p in prSet;
    var accs' := AcceptorsFromPromiseSet(prSet-{p}, prBal);
    accs := accs' + {p.acc};
  }
}

}  // end module PaxosProof

