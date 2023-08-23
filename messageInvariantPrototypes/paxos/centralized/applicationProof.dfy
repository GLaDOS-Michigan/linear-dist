include "spec.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations

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
      && vb in v.learners[lnr].receivedAccepts
      && IsAcceptorQuorum(c, v.learners[lnr].receivedAccepts[vb])
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LearnerValidReceivedAccepts(c, v)
  && LearnedImpliesQuorumOfAcceptors(c, v)
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
  assert ApplicationInv(c, v');

  // TODO
  assume false;
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

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
      && vb in v'.learners[lnr].receivedAccepts
      && IsAcceptorQuorum(c, v'.learners[lnr].receivedAccepts[vb])
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


/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f+1
  && (forall id | id in quorum :: c.ValidAcceptorIdx(id))
}

} // end module PaxosProof