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
  && LearnedValuesValid(c, v)
}

predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ApplicationInv(c, v)
  && Agreement(c, v)
}


// Analogous to LearnMsgsValid in non-monotonic land
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
  InvNextLearnedValuesValid(c, v, v');
  assume Agreement(c, v');
}



/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/



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

/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/

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
  * l.receivedAccepts, by LearnedValuesValid. By LearnerValidReceivedAccepts, there is a quorum of accept messages
  * in the network supporting vb. By ValidAcceptMessage, this means there is a quorum of 
  * acceptors that accepted vb */
  var l := v.learners[idx];

  // assert vb in l.receivedAccepts;

  assume false;
  assert Chosen(c, v, vb);
}

// A quorum of Acceptors accepted the same vb
predicate Chosen(c: Constants, v: Variables, vb: ValBal) 
  requires v.WF(c)
{
  exists quorum :: IsAcceptorQuorum(c, v, quorum, vb)
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

}  // end module PaxosProof

