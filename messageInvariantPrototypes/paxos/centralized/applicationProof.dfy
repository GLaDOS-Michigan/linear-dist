include "spec.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations


ghost predicate OneValuePerBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  && OneValuePerBallotAcceptors(c, v)
  && OneValuePerBallotLearners(c, v)
  && OneValuePerBallotAcceptorsAndLearners(c, v)
  && OneValuePerBallotLeaderAndLearners(c, v)
  && OneValuePerBallotLeaderAndAcceptors(c, v)
}

// Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall a1, a2 |
    && c.ValidAcceptorIdx(a1)
    && c.ValidAcceptorIdx(a2)
    && v.acceptors[a1].acceptedVB.Some?
    && v.acceptors[a2].acceptedVB.Some?
    && v.acceptors[a1].acceptedVB.value.b 
        == v.acceptors[a2].acceptedVB.value.b 
  ::
    v.acceptors[a1].acceptedVB.value.v
        == v.acceptors[a2].acceptedVB.value.v
}

// Learners only have one value for each ballot
ghost predicate OneValuePerBallotLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall l1, l2, vb1, vb2 |
    && c.ValidLearnerIdx(l1)
    && c.ValidLearnerIdx(l2)
    && vb1 in v.learners[l1].receivedAccepts
    && vb2 in v.learners[l1].receivedAccepts
    && vb1.b == vb2.b
  ::
    vb1.v == vb2.v
}

// Learners and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotAcceptorsAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall a, l, vb1, vb2 |
    && c.ValidAcceptorIdx(a)
    && c.ValidLearnerIdx(l)
    && v.acceptors[a].acceptedVB == Some(vb1)
    && vb2 in v.learners[l].receivedAccepts
    && vb1.b == vb2.b
  ::
    vb1.v == vb2.v
}

// Leaders and Learners only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, lnr, v1, v2 |
    && c.ValidLeaderIdx(ldr)
    && c.ValidLearnerIdx(lnr)
    && v.leaders[ldr].CanPropose(c.leaderConstants[ldr])
    && v.leaders[ldr].value == v1
    && VB(v2, ldr) in v.learners[lnr].receivedAccepts
  ::
    v1 == v2
}

// Leaders and Acceptors only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, v1, v2 |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && v.leaders[ldr].CanPropose(c.leaderConstants[ldr])
    && v.leaders[ldr].value == v1
    && v.acceptors[acc].acceptedVB == Some(VB(v2, ldr))
  ::
    v1 == v2
}

// Learner's receivedAccepts contain valid acceptor ids
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, e:AcceptorId |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].receivedAccepts
    && e in v.learners[lnr].receivedAccepts[vb]
  ::
    c.ValidAcceptorIdx(e)
}

// Learner's receivedAccepts contain valid leader ballots
ghost predicate LearnerValidReceivedAcceptsKeys(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].receivedAccepts
  ::
    c.ValidLeaderIdx(vb.b)
}

ghost predicate LearnerReceivedAcceptMeansLeaderCanPropose(c: Constants, v: Variables) 
  requires v.WF(c)
  requires LearnerValidReceivedAcceptsKeys(c, v)
{
  forall lnr:LearnerId, vb:ValBal |
    && c.ValidLearnerIdx(lnr)
    && vb in v.learners[lnr].receivedAccepts
  ::
    var lc, l := c.leaderConstants[vb.b], v.leaders[vb.b];
    l.CanPropose(lc)
}

// Learner's learned value must be backed by a quorum of accepts
ghost predicate LearnedImpliesQuorumOfAcceptors(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, val:Value |
    && c.ValidLearnerIdx(lnr)
    && v.learners[lnr].HasLearnedValue(val)
  ::
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v, vb, lnr)
}


// TODO: Not sure if needed
// Each entry in a learner's receivedAccepts implies that an acceptor accepted it
// ghost predicate LearnerReceivedAcceptImpliesAcceptorAccepted(c: Constants, v: Variables)
//   requires v.WF(c)
// {
//   forall lnr:LearnerId, vb:ValBal, acc:AcceptorId |
//     && c.ValidLearnerIdx(lnr)
//     && c.ValidAcceptorIdx(acc)
//     && vb in v.learners[lnr].receivedAccepts
//     && acc in v.learners[lnr].receivedAccepts[vb]
//   ::
//     v.acceptors[acc].HasAcceptedAtLeast(vb.b) 
// }

// Acceptor's fields all host valid leader ballots
ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v:Variables) 
  requires v.WF(c)
{
  forall acc: AcceptorId | c.ValidAcceptorIdx(acc)
  ::
    && (v.acceptors[acc].pendingPrepare.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].pendingPrepare.value.bal))
    && (v.acceptors[acc].promised.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].promised.value))
    && (v.acceptors[acc].acceptedVB.Some? 
        ==> c.ValidLeaderIdx(v.acceptors[acc].acceptedVB.value.b))
}

// If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
ghost predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall acc | 
    && c.ValidAcceptorIdx(acc) 
    && v.acceptors[acc].acceptedVB.Some?
  :: 
    && v.acceptors[acc].promised.Some?
    && v.acceptors[acc].acceptedVB.value.b <= v.acceptors[acc].promised.value
}

ghost predicate AcceptorAcceptedMeansLeaderCanPropose(c: Constants, v: Variables) 
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
{
  forall acc:AcceptorId, vb:ValBal |
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].acceptedVB == Some(vb)
  ::
    var lc, l := c.leaderConstants[vb.b], v.leaders[vb.b];
    l.CanPropose(lc)
}

// For all ldr, acc such that acc in ldr.receivedPromises, acc's current promise
// must be >= ldr's ballot
ghost predicate LeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId |
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && acc in v.leaders[ldr].receivedPromises
  ::
    v.acceptors[acc].HasPromisedAtLeast(ldr)
}

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, acc:AcceptorId | 
    && Chosen(c, v, vb)
    && c.ValidAcceptorIdx(acc)
    && v.acceptors[acc].acceptedVB.Some?
    && v.acceptors[acc].acceptedVB.value.b >= vb.b
  ::
     v.acceptors[acc].acceptedVB.value.v == vb.v
}

// If vb is chosen, then for all leaders has a highest heard >= vb.b, the value must be vb.v
ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId | 
    && Chosen(c, v, vb)
    && c.ValidLeaderIdx(ldrBal)
    && v.leaders[ldrBal].highestHeardBallot.Some?
    && v.leaders[ldrBal].highestHeardBallot.value >= vb.b
  ::
    v.leaders[ldrBal].value == vb.v
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && OneValuePerBallot(c, v)
  && LearnerValidReceivedAccepts(c, v)
  && LearnerValidReceivedAcceptsKeys(c, v)
  && LearnedImpliesQuorumOfAcceptors(c, v)
  && LearnerReceivedAcceptMeansLeaderCanPropose(c, v)
  // && LearnerReceivedAcceptImpliesAcceptorAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorPromisedLargerThanAccepted(c, v)
  && AcceptorAcceptedMeansLeaderCanPropose(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  && ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  && ChosenValImpliesLeaderOnlyHearsVal(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
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
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  InvNextLearnedImpliesQuorumOfAcceptors(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');

  assert LearnerReceivedAcceptMeansLeaderCanPropose(c, v');
  assert AcceptorAcceptedMeansLeaderCanPropose(c, v');


  InvNextOneValuePerBallot(c, v, v');

  assert ApplicationInv(c, v');

  // TODO
  assume AtMostOneChosenVal(c, v');  // this should be implied by invariants
  AtMostOneChosenImpliesSafety(c, v');
  assert Agreement(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextOneValuePerBallot(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires OneValuePerBallot(c, v)
  requires LearnerValidReceivedAcceptsKeys(c, v)  // prereq for LearnerReceivedAcceptMeansLeaderCanPropose
  requires AcceptorValidPromisedAndAccepted(c, v) // prereq for AcceptorAcceptedMeansLeaderCanPropose
  requires LearnerReceivedAcceptMeansLeaderCanPropose(c, v)
  requires AcceptorAcceptedMeansLeaderCanPropose(c, v)
  requires Next(c, v, v')
  ensures OneValuePerBallot(c, v')
{
  assume false;
}

lemma InvNextLearnedImpliesQuorumOfAcceptors(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAcceptors(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAcceptors(c, v')
{
  forall lnr:LearnerId, val:Value |
    c.ValidLearnerIdx(lnr) && v'.learners[lnr].HasLearnedValue(val)
  ensures
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v, vb, lnr)
  {
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.P2bStep? {
      if sysStep.learner == lnr {
        // trigger
        assert v.learners[lnr].HasLearnedValue(val);
      }
    }
  }
}

lemma InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ChosenValImpliesAcceptorOnlyAcceptsVal(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P1bStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else if sysStep.P2aStep? {

    NewChosenOnlyInP2bStep(c, v, v', sysStep);
    forall vb, acc:AcceptorId | 
      && Chosen(c, v', vb)
      && c.ValidAcceptorIdx(acc)
      && v'.acceptors[acc].acceptedVB.Some?
      && v'.acceptors[acc].acceptedVB.value.b >= vb.b
    ensures
      v'.acceptors[acc].acceptedVB.value.v == vb.v
    {
      assert Chosen(c, v, vb);
      if acc == sysStep.acceptor {
        var ldr := sysStep.leader;
        var lc, l, l' := c.leaderConstants[ldr], v.leaders[ldr], v'.leaders[ldr];
        var ac, a, a' := c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc];
        assert l == l';

        var val := l.value;
        var accLbl := AcceptorHost.MaybeAcceptLbl(ldr, val);
        assert AcceptorHost.Next(ac, a, a', accLbl);
        if ldr > vb.b {
          assert l.CanPropose(lc);


          // TODO: These are the statements to prove
          assume false;
          assert l.highestHeardBallot.Some?;
          assert l.highestHeardBallot.value >= vb.b;


          assert l.value == vb.v;
          assert v'.acceptors[acc].acceptedVB.value.v == vb.v;
        } else {
          // Case where ldr == vb.b
          // Should be true because propose only one value per ballot?
          // Then this is proven, as chosen(c, v, vb) means that leader has value v.

          // assume OneProposedValuePerBallot(c, v);
          var lnr :| ChosenAtLearner(c, v, vb, lnr);


          assume false;
          assume c.ValidLeaderIdx(vb.b);

          assume v.leaders[vb.b].CanPropose(c.leaderConstants[vb.b]);

          assert vb.b == ldr;
          assert l.value == vb.v;

          assert v'.acceptors[acc].acceptedVB.value.v == vb.v;
        }
      }
    }
    assert ChosenValImpliesAcceptorOnlyAcceptsVal(c, v');
  } else if sysStep.P2bStep? {
    // TODO
    assume false;
    assert ChosenValImpliesAcceptorOnlyAcceptsVal(c, v');
  } else if sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);

    assert ChosenValImpliesAcceptorOnlyAcceptsVal(c, v');
  }
}


lemma InvNextChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ChosenValImpliesLeaderOnlyHearsVal(c, v')
{
  var sysStep :| NextStep(c, v, v', sysStep);
  if sysStep.P1aStep? || sysStep.P1bStep? || sysStep.P2aStep? || sysStep.LearnerInternalStep? {
    NewChosenOnlyInP2bStep(c, v, v', sysStep);
  } else {
    // P2bStep
    



    // TODO
    assume false;
    assert ChosenValImpliesLeaderOnlyHearsVal(c, v');
  }
}


/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f+1
  && (forall id | id in quorum :: c.ValidAcceptorIdx(id))
}

// A learner holds an accept quorum for vb
ghost predicate Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  exists lnr:LearnerId :: ChosenAtLearner(c, v, vb, lnr)
}

// Learner lnr witnessed a vb being chosen
ghost predicate ChosenAtLearner(c: Constants, v: Variables, vb: ValBal, lnr:LearnerId) 
  requires v.WF(c)
{
  && c.ValidLearnerIdx(lnr)
  && vb in v.learners[lnr].receivedAccepts
  && IsAcceptorQuorum(c, v.learners[lnr].receivedAccepts[vb])
}

// At most one value can become Chosen
ghost predicate AtMostOneChosenVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
  :: vb1.v == vb2.v
}

//// Helper Lemmas ////

// A value being learned implies it was chosen at some ballot, and skolemize this ballot
lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires v.learners[lnr].HasLearnedValue(val)
  requires LearnedImpliesQuorumOfAcceptors(c, v)
  ensures vb.v == val
  ensures Chosen(c, v, vb)
{
  // Witness, given by LearnedImpliesQuorumOfAcceptors
  var bal :| ChosenAtLearner(c, v, VB(val, bal), lnr);
  return VB(val, bal);
}

// If only one value can be chosen, then Agreement must be satisfied
lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneChosenVal(c, v)
  requires LearnedImpliesQuorumOfAcceptors(c, v)
  ensures Agreement(c, v)
{
  // Proof by contradiction
  if !Agreement(c, v) {
    var l1, l2 :| 
        && c.ValidLearnerIdx(l1)
        && c.ValidLearnerIdx(l2)
        && v.learners[l1].learned.Some?
        && v.learners[l2].learned.Some?
        && v.learners[l1].learned != v.learners[l2].learned
    ;
    var vb1 := LearnedImpliesChosen(c, v, l1, v.learners[l1].learned.value);
    var vb2 := LearnedImpliesChosen(c, v, l2, v.learners[l2].learned.value);
    assert false;
  }
}

// Lemma: The only system step in which a new vb can be chosen is a P2bStep 
lemma NewChosenOnlyInP2bStep(c: Constants, v: Variables, v': Variables, sysStep: Step) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires NextStep(c, v, v', sysStep)
  requires !sysStep.P2bStep?
  ensures forall vb | Chosen(c, v', vb) :: Chosen(c, v, vb)
{
  forall vb | Chosen(c, v', vb)
  ensures Chosen(c, v, vb)
  {
    var lnr:LearnerId :| ChosenAtLearner(c, v', vb, lnr);   // witness
    assert ChosenAtLearner(c, v, vb, lnr);                  // trigger
  }
}

} // end module PaxosProof