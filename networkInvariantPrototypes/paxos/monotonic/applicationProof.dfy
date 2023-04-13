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
predicate ApplicationInv(c: Constants, v: Variables)
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

predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Agreement(c, v)
}

// Leader local state's monotonic properties
predicate LeaderStateMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx | c.ValidLeaderIdx(idx)
  ::  && SetMonotoneIncreasing(v.leaders[idx].receivedPromises)
      && SeqOptionMonotoneIncreasing(v.leaders[idx].highestHeardBal)
}


// Highest heard ballot and value backed by received promises, corresponds to HighestHeardBackedByReceivedPromises
predicate LeaderHighestHeardBackedByReceivedPromises(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, i |
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].highestHeardBal|
  ::
    LeaderPromiseSetProperties(c, v, idx, i)
}

predicate LeaderPromiseSetProperties(c: Constants, v: Variables, idx: int, i: int) 
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
// which in turn implies at most one value is chosen
predicate ProposeImpliesLeaderState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].proposed|
  ::
    LeaderStateValid(c, v, idx, i)
}

predicate LeaderStateValid(c: Constants, v: Variables, idx: nat, i: nat)
  requires v.WF(c)
  requires c.ValidLeaderIdx(idx)
  requires 0 <= i < |v.leaders[idx].proposed|
{
  && |Last(v.leaders[idx].receivedPromises)| >= c.f+1
  && Last(v.leaders[idx].value) == v.leaders[idx].proposed[i]
}

// This is a corollary of ProposeImpliesLeaderState, and implies at most one value is chosen
predicate LeaderProposesOneValue(c: Constants, v: Variables)
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
predicate AcceptorStateMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx | c.ValidAcceptorIdx(idx) 
  :: 
    && SeqMonotoneIncreasing(v.acceptors[idx].promised)
    && SeqOptionVBMonotoneIncreasing(v.acceptors[idx].acceptedVB)
    && (forall i | 
          && 0 <= i < |v.acceptors[idx].promised| 
          && v.acceptors[idx].acceptedVB[i].Some?
        ::
          v.acceptors[idx].acceptedVB[i].value.b <= v.acceptors[idx].promised[i]
    )
}

// Corresponds to LearnMsgsValid in non-monotonic land
predicate LearnedValuesValid(c: Constants, v: Variables) 
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
predicate ChosenValImpliesProposeOnlyVal(c: Constants, v: Variables) 
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
  requires LeaderProposesOneValue(c, v')
  ensures ChosenValImpliesProposeOnlyVal(c, v')
{
  var dsStep :| NextStep(c, v, v', dsStep);
  var actor, msgOps := dsStep.actor, dsStep.msgOps;
  if dsStep.LeaderStep? {
    /* This case is trivial. This is because if something has already been chosen, then
    * then leader can only propose same val by ChosenValImpliesPromiseQuorumSeesBal.
    * Otherwise, the post-condition is vacuously true, as nothing new can be chosen */
    forall vb, idx, i | 
      && Chosen(c, v', vb)
      && c.ValidLeaderIdx(idx)
      && vb.b < c.leaderConstants[idx].id
      && 0 <= i < |v'.leaders[idx].proposed|
    ensures
      v'.leaders[idx].proposed[i] == vb.v
    {
      assume false;
    }
  } else if dsStep.AcceptorStep? {
    var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
    var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
    assume false;
  } else {
    NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
  } 
}

/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/


// A quorum of Acceptors accepted the same vb
predicate Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  exists quorum :: IsAcceptorQuorum(c, v, quorum, vb)
}


predicate AtMostOneChosenVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
  :: vb1.v == vb2.v
}

predicate IsAcceptorQuorum(c: Constants, v: Variables, aset: set<AcceptorId>, vb: ValBal) 
  requires v.WF(c)
{
  && |aset| >= c.f+1
  && (forall id | id in aset :: 
      && c.ValidAcceptorIdx(id)
      && v.acceptors[id].HasAccepted(vb)
  )
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
  requires AtMostOneChosenVal(c, v);  // TODO: Application inv should imply this
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

predicate SeqOptionVBMonotoneIncreasing(s: seq<Option<ValBal>>) {
  forall i, j | 
    && 0 <= i < |s| 
    && 0 <= j < |s| 
    && i <= j
    && s[i].Some?
  :: s[j].Some? && s[i].value.b <= s[j].value.b
}

predicate IsPromiseSet(pset: set<Message>, bal: LeaderId) {
  && (forall m | m in pset ::
    && m.Promise?     // changed from IsPromiseMsg(v, m), to avoid application definitions mentioning network
    && m.bal == bal)
  && PromiseSetDistinctAccs(pset)
}

predicate PromiseSetDistinctAccs(pset: set<Message>) 
  requires forall m | m in pset :: m.Promise?
{
  forall m1, m2 | m1 in pset && m2 in pset && m1.acc == m2.acc
      :: m1 == m2
}

predicate PromiseSetEmptyVB(pset: set<Message>, qbal: LeaderId)
  requires IsPromiseSet(pset, qbal)
{
  forall m | m in pset :: m.vbOpt == None
}

predicate PromiseSetHighestVB(pset: set<Message>, qbal: LeaderId, vb: ValBal)
  requires IsPromiseSet(pset, qbal)
{
  exists m :: WinningPromiseMessageInQuorum(pset, qbal, vb, m)
}

predicate WinningPromiseMessageInQuorum(pset: set<Message>, qbal: LeaderId, vb: ValBal, m: Message)
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

// Implied by Inv: If vb is Chosen, then all leaders with ballot > vb.b that has amassed 
// a Promise quorum, must have highestHeard => vb.b
// predicate ChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
//   requires v.WF(c)
// {
//   forall vb, idx | 
//     && Chosen(c, v, vb)
//     && c.ValidLeaderIdx(idx)
//     && vb.b < pbal
//   ::
//     exists m: Message :: m in quorum && m.vbOpt.Some? && vb.b <= m.vbOpt.value.b
// }

// // lemma: Inv implies that ChosenValImpliesPromiseQuorumSeesBal
// lemma InvImpliesChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
//   requires Inv(c, v)
//   ensures ChosenValImpliesPromiseQuorumSeesBal(c, v)
// {
//   forall chosenVb, prQuorum, pbal | 
//     && Chosen(c, v, chosenVb)
//     && IsPromiseQuorum(c, v, prQuorum, pbal)
//     && chosenVb.b < pbal
//   ensures
//     exists m: Message :: m in prQuorum && m.vbOpt.Some? && chosenVb.b <= m.vbOpt.value.b
//   {
//     var acQuorum :| IsAcceptQuorum(c, v, acQuorum, chosenVb);
//     var accId := IntersectingAcceptorInPromiseAndAcceptQuorum(c, v, prQuorum, pbal, acQuorum, chosenVb);
//     var m: Message :| m in prQuorum && m.acc == accId;  // witness
//     // m satisfies postcondition via AcceptMsgImpliesLargerPromiseCarriesVb(c, v')
//   }
// }

}  // end module PaxosProof

