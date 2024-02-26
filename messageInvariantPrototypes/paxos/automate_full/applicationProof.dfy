include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations

// Leaders and Learners only have one value for each ballot
ghost predicate OneValuePerBallotLeaderAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, lnr, acceptedVal, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidLearnerIdx(lnr)
    && VB(acceptedVal, ldr) in v.History(i).learners[lnr].receivedAccepts.m
  ::
    acceptedVal == v.History(i).leaders[ldr].Value()
}

// Learner's receivedAccepts.m contain valid acceptor ids
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, e:AcceptorId, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.History(i).learners[lnr].receivedAccepts.m
    && e in v.History(i).learners[lnr].receivedAccepts.m[vb]
  ::
    c.ValidAcceptorIdx(e)
}

ghost predicate LearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, i 
    {:trigger vb.v, v.History(i).learners[lnr]}
    {:trigger vb.v, c.ValidLearnerIdx(lnr), v.History(i)}
    {:trigger vb.v, c.ValidLearnerIdx(lnr), v.ValidHistoryIdx(i)}
    {:trigger vb.b, v.History(i).learners[lnr]}
    {:trigger vb.b, c.ValidLearnerIdx(lnr),v.History(i)}
    {:trigger vb.b, c.ValidLearnerIdx(lnr), v.ValidHistoryIdx(i)}
  :: (
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v.History(i).learners[lnr].receivedAccepts.m
    && c.ValidLeaderIdx(vb.b)
  ==>
    && v.History(i).LeaderCanPropose(c, vb.b)
    && v.History(i).leaders[vb.b].Value() == vb.v
  )
}

// Learner's learned value must be backed by a quorum of accepts
ghost predicate LearnedImpliesQuorumOfAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, val:Value, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && v.History(i).learners[lnr].HasLearnedValue(val)
  ::
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v.History(i), vb, lnr)
}

// Each entry in a learner's receivedAccepts.m implies that an acceptor accepted it
ghost predicate LearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall lnr:LearnerId, vb:ValBal, acc:AcceptorId, i |
    && v.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && c.ValidAcceptorIdx(acc)
    && vb in v.History(i).learners[lnr].receivedAccepts.m
    && acc in v.History(i).learners[lnr].receivedAccepts.m[vb]
  ::
    v.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b) 
}


// Acceptor's fields all host valid leader ballots
ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v:Variables) 
  requires v.WF(c)
{
  forall acc: AcceptorId, i 
    {:trigger v.History(i).acceptors[acc]}
    {:trigger v.History(i), c.ValidAcceptorIdx(acc)}
    {:trigger c.ValidAcceptorIdx(acc), v.ValidHistoryIdx(i)}
  :: (
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(acc)
    && v.History(i).acceptors[acc].acceptedVB.MVBSome? 
    ==> 
    c.ValidLeaderIdx(v.History(i).acceptors[acc].acceptedVB.value.b)
  )
}

ghost predicate AcceptorAcceptedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
{
  forall acc:AcceptorId, i 
    {:trigger v.History(i).acceptors[acc]}
    {:trigger v.History(i), c.ValidAcceptorIdx(acc)}
    {:trigger c.ValidAcceptorIdx(acc), v.ValidHistoryIdx(i)}
  :: (
    && v.ValidHistoryIdx(i)
    && c.ValidAcceptorIdx(acc)
    && v.History(i).acceptors[acc].acceptedVB.MVBSome?
  ==>
    var vb := v.History(i).acceptors[acc].acceptedVB.value;
    && v.History(i).LeaderCanPropose(c, vb.b)
    && v.History(i).leaders[vb.b].Value() == vb.v
  )
}

ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && acc in v.History(i).leaders[ldr].ReceivedPromises()
  ::
    c.ValidAcceptorIdx(acc)
}

// For all leaders, its highestHeardBallot is upper bounded by its own ballot
ghost predicate LeaderHighestHeardUpperBound(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId, i 
    {:trigger v.History(i).leaders[ldr]}
    {:trigger v.History(i), c.ValidLeaderIdx(ldr)}
    {:trigger c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
  :: (
      && v.ValidHistoryIdx(i)
      && c.ValidLeaderIdx(ldr)
      && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
    ==>
      v.History(i).leaders[ldr].highestHeardBallot.value < ldr
  )
}

// If a leader has a highestHeardBallot B, then its value has been proposed by the leader 
// with ballot B
ghost predicate LeaderHearedImpliesProposed(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall ldr:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
    && c.ValidLeaderIdx(v.History(i).leaders[ldr].highestHeardBallot.value)
  ::
    // note that once a leader CanPropose(), its value does not change
    && var vi := v.History(i);
    var b := vi.leaders[ldr].highestHeardBallot.value;
    // && c.ValidLeaderIdx(b)
    && vi.LeaderCanPropose(c, b)
    && vi.leaders[b].Value() == vi.leaders[ldr].Value()
}

// For all ldr, acc such that acc in ldr.ReceivedPromises(), acc's current promise
// must be >= ldr's ballot
ghost predicate LeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr:LeaderId, acc:AcceptorId, i 
  {:trigger v.History(i).acceptors[acc], v.History(i).leaders[ldr]}
  {:trigger v.History(i).acceptors[acc], c.ValidLeaderIdx(ldr)}
  {:trigger v.History(i).leaders[ldr], c.ValidAcceptorIdx(acc)}
  {:trigger c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
  :: (
    && v.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && acc in v.History(i).leaders[ldr].ReceivedPromises()
  ==>
    v.History(i).acceptors[acc].HasPromisedAtLeast(ldr)
  )
}

// For any leader L, if an acceptor A is in L.promises, then A cannot have accepted any
// ballot b such that L.highestHeard < b < L

//{vb.b, v.History(i), c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr)}
//{vb.b, c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
ghost predicate LeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, acc, lnr, vb:ValBal, i 
  {:trigger v.History(i).leaders[ldr], vb.b, v.History(i).learners[lnr], c.ValidAcceptorIdx(acc)}
  {:trigger v.History(i).leaders[ldr], vb.b, c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc)}
  {:trigger vb.b, v.History(i).learners[lnr], c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr)}
  {:trigger vb.b, c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
  {:trigger vb.b, c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.History(i)}
  :: (
      && v.ValidHistoryIdx(i)
      && c.ValidLeaderIdx(ldr)
      && c.ValidAcceptorIdx(acc)
      && c.ValidLearnerIdx(lnr)
      && vb in v.History(i).learners[lnr].receivedAccepts.m
      && vb.b < ldr
      && v.History(i).leaders[ldr].HeardAtMost(vb.b)
      && acc in v.History(i).leaders[ldr].ReceivedPromises()
    ==>
      acc !in v.History(i).learners[lnr].receivedAccepts.m[vb]
  )
}

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, acc:AcceptorId, i | 
    && v.ValidHistoryIdx(i)
    && Chosen(c, v.History(i), vb)
    && c.ValidAcceptorIdx(acc)
    && v.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b)
  ::
     v.History(i).acceptors[acc].acceptedVB.value.v == vb.v
}

// If vb is chosen, then for all leaders > vb.b and ready to propose, they must have highest 
// heard >= b
ghost predicate ChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && Chosen(c, v.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && vb.b < ldrBal
    && v.History(i).LeaderCanPropose(c, ldrBal)
  ::
    v.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
}

// If vb is chosen, then for all leaders has a highest heard >= vb.b, the value must be vb.v
ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall vb, ldrBal:LeaderId, i | 
    && v.ValidHistoryIdx(i)
    && Chosen(c, v.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && v.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
  ::
    v.History(i).leaders[ldrBal].Value() == vb.v
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LearnerValidReceivedAccepts(c, v)
  && LearnedImpliesQuorumOfAccepts(c, v)
  && LearnerReceivedAcceptImpliesProposed(c, v)  // 2
  && LearnerReceivedAcceptImpliesAccepted(c, v)  // 2
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorAcceptedImpliesProposed(c, v)       // 2
  && LeaderValidReceivedPromises(c, v)
  && LeaderHighestHeardUpperBound(c, v)
  && LeaderHearedImpliesProposed(c, v)           // 2
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)   // 2
  && LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
  && ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  && ChosenImpliesProposingLeaderHearsChosenBallot(c, v)  // 2
  && ChosenValImpliesLeaderOnlyHearsVal(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
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
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
  MonotonicityInvInductive(c, v, v');

  InvNextLearnerValidReceivedAccepts(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  InvNextLearnerReceivedAcceptImpliesProposed(c, v, v');
  InvNextLearnerReceivedAcceptImpliesAccepted(c, v, v');

  InvNextAcceptorValidBundle(c, v, v');
  
  InvNextLeaderValidReceivedPromises(c, v, v');
  InvNextLeaderHighestHeardUpperBound(c, v, v');
  InvNextLeaderHearedImpliesProposed(c, v, v');
  InvNextLeaderReceivedPromisesImpliesAcceptorState(c, v, v');
  InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');

  InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');

  InvImpliesAtMostOneChosenVal(c, v');
  AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma InvNextLearnerValidReceivedAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires LearnerValidReceivedAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAccepts(c, v')
{
  forall lnr:LearnerId, val:Value, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && v'.History(i).learners[lnr].HasLearnedValue(val)
  ensures
    exists b: LeaderId ::
      && var vb := VB(val, b);
      && ChosenAtLearner(c, v'.History(i), vb, lnr)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if  && dsStep.LearnerHostStep?
          && actor == lnr 
      {
        var lc, l, l' := c.learners[actor], v.Last().learners[actor], v'.Last().learners[actor];
        var step :| LearnerHost.NextStep(lc, l, l', step, msgOps);
        if !step.LearnStep? {
          // trigger and witness
          assert v.History(i-1).learners[lnr].HasLearnedValue(val);
          var b: LeaderId :|
              && var vb := VB(val, b);
              && ChosenAtLearner(c, v.History(i-1), vb, lnr);
        }
      }
    } 
  }
}
 
lemma InvNextLearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires LearnerReceivedAcceptImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures LearnerReceivedAcceptImpliesProposed(c, v')
{
  forall lnr:LearnerId, vb:ValBal, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && vb in v'.History(i).learners[lnr].receivedAccepts.m
    && c.ValidLeaderIdx(vb.b)
  ensures
    && v'.History(i).LeaderCanPropose(c, vb.b)
    && v'.History(i).leaders[vb.b].Value() == vb.v
  {
    VariableNextProperties(c, v, v');
  }
}

lemma InvNextLearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  requires Next(c, v, v')
  ensures LearnerReceivedAcceptImpliesAccepted(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextAcceptorValidBundle(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidPromisedAndAccepted(c, v')
  ensures AcceptorAcceptedImpliesProposed(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderValidReceivedPromises(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires LeaderValidReceivedPromises(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromises(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderHighestHeardUpperBound(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardUpperBound(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderHearedImpliesProposed(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires LeaderHearedImpliesProposed(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromisedAndAccepted(c, v')
  requires AcceptorAcceptedImpliesProposed(c, v')
  ensures LeaderHearedImpliesProposed(c, v')
{  
  assume false;  // TODO
  forall ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && v'.History(i).leaders[ldr].highestHeardBallot.MNSome?
  ensures
    // note that once a leader CanPropose(), its value does not change
    && var vi' := v'.History(i);
    var b := vi'.leaders[ldr].highestHeardBallot.value;
    && c.ValidLeaderIdx(b)
    && vi'.LeaderCanPropose(c, b)
    && vi'.leaders[b].Value() == vi'.leaders[ldr].Value()
  { 
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if dsStep.LeaderHostStep? {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        var lc, l, l' := c.leaders[actor], v.Last().leaders[actor], v'.Last().leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if step.ReceiveStep? {
          assert IsPromiseMessage(v, msgOps.recv.value);  // trigger
          assert c.ValidAcceptorIdx(msgOps.recv.value.acc);  // trigger
        } 
      }
    }
  }
}

lemma InvNextLeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires LeaderHearedImpliesProposed(c, v)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires Next(c, v, v')
  ensures LeaderReceivedPromisesImpliesAcceptorState(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  // v requirements
  requires ValidMessages(c, v)
  requires SendAcceptValidity(c, v)
  requires MonotonicityInv(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)

  // v' requirements
  requires Next(c, v, v')
  requires ReceiveAcceptValidity(c, v')  // custom receive invariant
  requires ReceivePromiseValidity(c, v')  // custom receive invariant
  requires SendAcceptValidity(c, v')
  requires SendPromiseValidity(c, v')
  requires AcceptorHostAcceptedVBMonotonic(c, v')
  requires LeaderHostHighestHeardBallotMonotonic(c, v')
  // postcondition
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{ 
  forall ldr, acc, lnr, vb:ValBal, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && c.ValidLearnerIdx(lnr)
    && vb in v'.History(i).learners[lnr].receivedAccepts.m
    && vb.b < ldr
    && v'.History(i).leaders[ldr].HeardAtMost(vb.b)
    && acc in v'.History(i).leaders[ldr].ReceivedPromises()
  ensures
    acc !in v'.History(i).learners[lnr].receivedAccepts.m[vb]
  {
    VariableNextProperties(c, v, v');
    if acc in v'.History(i).learners[lnr].receivedAccepts.m[vb] {
      var acceptMsg := AcceptMessageExistence(c, v', i, lnr, vb, acc);
      var prom := PromiseMessageExistence(c, v', i, ldr, acc);
    }
  }
}

lemma PromiseMessageExistence(c: Constants, v: Variables, i: int, ldr: LeaderId, acc: AcceptorId) 
  returns (promiseMsg : Message)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLeaderIdx(ldr)
  requires LeaderHostHighestHeardBallotMonotonic(c, v)
  requires LeaderHost.ReceivePromiseTrigger(c.leaders[ldr], v.History(i).leaders[ldr], acc)
  requires ReceivePromiseValidity(c, v)
  ensures   && promiseMsg.Promise?
            && promiseMsg in v.network.sentMsgs
            && promiseMsg.bal == ldr
            && promiseMsg.acc == acc
            && (promiseMsg.vbOpt.Some?
                ==> 
                && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
                && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
            )
{
  reveal_ReceivePromiseValidity();
  promiseMsg :| && promiseMsg.Promise?
                && promiseMsg in v.network.sentMsgs
                && promiseMsg.bal == ldr
                && promiseMsg.acc == acc
                && (promiseMsg.vbOpt.Some?
                    ==> 
                    && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
                    && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
                );
}

lemma AcceptMessageExistence(c: Constants, v: Variables, i: int, lnr:LearnerId, vb: ValBal, acc: AcceptorId) 
  returns (acceptMsg : Message)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  requires vb in v.History(i).learners[lnr].receivedAccepts.m
  requires LearnerHost.ReceiveAcceptTrigger(c.learners[lnr], v.History(i).learners[lnr], acc, vb)
  requires ReceiveAcceptValidity(c, v)  // custom receive invariant
  ensures acceptMsg in v.network.sentMsgs
  ensures acceptMsg == Accept(vb, acc)
{
  reveal_ReceiveAcceptValidity();
  acceptMsg := Accept(vb, acc);
}

ghost predicate PromiseMessageMatchesHistory(c: Constants, v: Variables, prom: Message, i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires IsPromiseMessage(v, prom)
{
  && v.ValidHistoryIdx(i)
  && v.History(i).acceptors[prom.acc].promised.MNSome?
  && prom.bal == v.History(i).acceptors[prom.acc].promised.value
  && prom.vbOpt == v.History(i).acceptors[prom.acc].acceptedVB.ToOption()
}

lemma InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromisedAndAccepted(c, v')  // prereq for AcceptorAcceptedImpliesProposed
  
  // prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires AcceptorAcceptedImpliesProposed(c, v')
  requires OneValuePerBallotLeaderAndLearners(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')

  // post-condition
  ensures ChosenValImpliesAcceptorOnlyAcceptsVal(c, v')
{
  forall vb, acc:AcceptorId, i | 
    && v'.ValidHistoryIdx(i)
    && Chosen(c, v'.History(i), vb)
    && c.ValidAcceptorIdx(acc)
    && v'.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b)
  ensures
     v'.History(i).acceptors[acc].acceptedVB.value.v == vb.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if dsStep.LeaderHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if 
        && dsStep.AcceptorHostStep?
        && actor == acc 
      {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
        var ac, a, a' := c.acceptors[actor], v.Last().acceptors[actor], v'.Last().acceptors[actor];
        var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
        if step.MaybeAcceptStep? {
          ChosenImpliesProposeMessagesOnlyContainValue(c, v, vb);
        } else {
          AcceptorHost.UpdateReceiveAcceptedStep(ac, a, a', step, msgOps);
        }
      } else {
        if v'.History(i).acceptors[acc].acceptedVB.value.v != vb.v {
          var ldr := v'.Last().acceptors[acc].acceptedVB.value.b;
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldr, vb);
        }
      }
    }
  }
}

lemma InvNextChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires Inv(c, v)

  // Prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires OneValuePerBallotLeaderAndLearners(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
  ensures ChosenValImpliesLeaderOnlyHearsVal(c, v')
{
  forall vb, ldrBal:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && Chosen(c, v'.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && v'.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
  ensures
    v'.History(i).leaders[ldrBal].Value() == vb.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaders[ldrBal], v.Last().leaders[ldrBal], v'.Last().leaders[ldrBal];
      if dsStep.LeaderHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if dsStep.AcceptorHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        if v'.History(i).leaders[ldrBal].Value() != vb.v {
          assert Chosen(c, v'.Last(), vb);
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
        }
      }
    }
  }
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  forall vb, ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && Chosen(c, v'.History(i), vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr
    && v'.History(i).LeaderCanPropose(c, ldr)
  ensures
    v'.History(i).leaders[ldr].HeardAtLeast(vb.b)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaders[ldr], v.Last().leaders[ldr], v'.Last().leaders[ldr];
      if dsStep.LeaderHostStep? {
        InvNextChosenImpliesProposingLeaderHearsChosenBallotLeaderStep(c, v, v', dsStep, vb, ldr);
      } else if dsStep.AcceptorHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        InvNextChosenImpliesProposingLeaderHearsChosenBallotLearnerStep(c, v, v', dsStep, vb, ldr);
      }
    }
  }
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallotLeaderStep(
  c: Constants, v: Variables, v': Variables, dsStep: Step,
  vb: ValBal, ldr:LeaderId)
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires dsStep.LeaderHostStep?
  requires ValidMessages(c, v)
  requires LeaderValidReceivedPromises(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  requires LearnerReceivedAcceptImpliesAccepted(c, v')

  // input constraints
  requires Chosen(c, v'.Last(), vb)
  requires c.ValidLeaderIdx(ldr)
  requires vb.b < ldr
  requires v'.Last().LeaderCanPropose(c, ldr)
  ensures v'.Last().leaders[ldr].HeardAtLeast(vb.b)
{
  // Note that proof is identical to atomic case
  VariableNextProperties(c, v, v');
  NewChosenOnlyInLearnerStep(c, v, v', dsStep);
  if ldr == dsStep.actor {  // if the leader in question is now taking a step
    assert Chosen(c, v.Last(), vb);
    var choosingAccs := SupportingAcceptorsForChosen(c, v, |v.history|-1, vb);
    var h, h' := v.Last(), v'.Last();
    if h.leaders[ldr].HeardAtMost(vb.b) {
      //Ldr has yet to see ballot b in this step. By quorum intersection, it must see
      // an acceptor in choosingAccs in this step
      var acc := dsStep.msgOps.recv.value.acc;
      if acc !in choosingAccs {
        // In this case, by quorum intersection, acc must already be in ldr.receivePromises
        // Because, choosingAccs !! v.leaders[ldr].ReceivedPromises()
        var allAccs := GetAcceptorSet(c, v);
        var e := QuorumIntersection(allAccs, choosingAccs, h.leaders[ldr].ReceivedPromises() + {acc});
        assert false;
      }      
    }    
  }
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallotLearnerStep(
  c: Constants, v: Variables, v': Variables, dsStep: Step,
  vb: ValBal, ldr:LeaderId)
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires dsStep.LearnerHostStep?
  requires LeaderValidReceivedPromises(c, v)
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  requires LearnerReceivedAcceptImpliesAccepted(c, v')

  // input constraints
  requires Chosen(c, v'.Last(), vb)
  requires c.ValidLeaderIdx(ldr)
  requires vb.b < ldr
  requires v'.Last().LeaderCanPropose(c, ldr)
  ensures v'.Last().leaders[ldr].HeardAtLeast(vb.b)
{
  // Note that proof is identical to atomic case
  VariableNextProperties(c, v, v');
  if !Chosen(c, v.Last(), vb) {
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    var lnr:LearnerId:| ChosenAtLearner(c, v'.Last(), vb, lnr);
    if lnr == actor {
       var choosingAccs := SupportingAcceptorsForChosen(c, v', |v'.history|-1, vb);
      // These properties of choosingAccs carry over to pre-state v
      assert v.Last().LeaderCanPropose(c, ldr);  // trigger
      if !v.Last().leaders[ldr].HeardAtLeast(vb.b) {
        var allAccs := GetAcceptorSet(c, v);
        var e := QuorumIntersection(allAccs, choosingAccs, v.Last().leaders[ldr].ReceivedPromises());
        assert false;
      } 
    } else {
      assert !ChosenAtLearner(c, v.Last(), vb, lnr);  // trigger
    }
  }
}

// Helper lemma for InvNextChosenValImpliesLeaderOnlyHearsVal
lemma LeaderHearsDifferentValueFromChosenImpliesFalse(c: Constants, v: Variables, ldr:LeaderId, chosen: ValBal)
  requires v.WF(c)
  requires Chosen(c, v.Last(), chosen)
  requires c.ValidLeaderIdx(ldr)
  requires v.Last().leaders[ldr].highestHeardBallot.MNSome?
  requires v.Last().leaders[ldr].highestHeardBallot.value >= chosen.b
  requires v.Last().leaders[ldr].Value() != chosen.v
  requires chosen.b < ldr
  requires OneValuePerBallotLeaderAndLearners(c, v)
  requires LeaderHighestHeardUpperBound(c, v)
  requires LeaderHearedImpliesProposed(c, v)
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  ensures false
{
  /* 
    Suppose leader L hears a value v' != vb.v. Then by LeaderHearedImpliesProposed, another leader L' 
    such that vb.v <= L' < L must have proposed v', 
    Then do recursion all the way down.
  */
  var ldr' := v.Last().leaders[ldr].highestHeardBallot.value;
  assert v.Last().leaders[ldr'].Value() == v.Last().leaders[ldr].Value();
  assert chosen.b <= ldr' < ldr;
  LeaderHearsDifferentValueFromChosenImpliesFalse(c, v, ldr', chosen);
}

/***************************************************************************************
*                            Helper Definitions and Lemmas                             *
***************************************************************************************/

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f+1
  && (forall id | id in quorum :: c.ValidAcceptorIdx(id))
}

// A learner holds an accept quorum for vb
ghost predicate Chosen(c: Constants, h: Hosts, vb: ValBal) 
  requires h.WF(c)
{
  exists lnr:LearnerId:: 
    && ChosenAtLearner(c, h, vb, lnr)
}

// Learner lnr witnessed a vb being chosen
ghost predicate ChosenAtLearner(c: Constants, h: Hosts, vb: ValBal, lnr:LearnerId) 
  requires h.WF(c)
{
  && c.ValidLearnerIdx(lnr)
  && vb in h.learners[lnr].receivedAccepts.m
  && IsAcceptorQuorum(c, h.learners[lnr].receivedAccepts.m[vb])
}

// At most one value can become Chosen
ghost predicate AtMostOneChosenVal(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i, j, vb1: ValBal, vb2: ValBal 
    {:trigger vb2.v, vb1.v, v.ValidHistoryIdx(i), v.ValidHistoryIdx(j)}
    {:trigger vb2.v, vb1.b, v.ValidHistoryIdx(i), v.ValidHistoryIdx(j)}
    {:trigger vb2.v, Chosen(c, v.History(i), vb1), v.ValidHistoryIdx(j)}
    {:trigger vb1.v, vb2.b, v.ValidHistoryIdx(i), v.ValidHistoryIdx(j)}
    {:trigger vb1.v, Chosen(c, v.History(j), vb2), v.ValidHistoryIdx(i)}
    {:trigger vb2.b, vb1.b, v.ValidHistoryIdx(i), v.ValidHistoryIdx(j)}
    {:trigger vb2.b, Chosen(c, v.History(i), vb1), v.ValidHistoryIdx(j)}
    {:trigger vb1.b, Chosen(c, v.History(j), vb2), v.ValidHistoryIdx(i)}
    {:trigger Chosen(c, v.History(i), vb1), Chosen(c, v.History(j), vb2)}
  :: (
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && vb1.b <= vb2.b 
    && Chosen(c, v.History(i), vb1) 
    && Chosen(c, v.History(j), vb2)
  ==>
    && c.ValidLeaderIdx(vb1.b)
    && c.ValidLeaderIdx(vb2.b)
    && vb1.v == vb2.v
  )
}

ghost predicate IsPrepareMessage(v: Variables, m: Message) {
  && m.Prepare?
  && m in v.network.sentMsgs
}

ghost predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

ghost predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

ghost predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}


//// Helper Lemmas ////

// A value being learned implies it was chosen at some ballot, and skolemize this ballot
lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires v.Last().learners[lnr].HasLearnedValue(val)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures vb.v == val
  ensures Chosen(c, v.Last(), vb)
{
  var bal :| ChosenAtLearner(c, v.Last(), VB(val, bal), lnr);
  return VB(val, bal);
}

lemma InvImpliesAtMostOneChosenVal(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires ApplicationInv(c, v)
  ensures AtMostOneChosenVal(c, v)
{
  forall i, j, vb1: ValBal, vb2: ValBal | 
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
    && vb1.b <= vb2.b
    && Chosen(c, v.History(i), vb1)
    && Chosen(c, v.History(j), vb2)
  ensures 
    && c.ValidLeaderIdx(vb1.b)
    && c.ValidLeaderIdx(vb2.b)
    && vb1.v == vb2.v
  {
    //reveal_ChosenAtHistory();
    // vb1 chosen at i implies that vb1 is also chosen at j, by LearnerReceivedAcceptsMonotonic.
    // This means that a leader proposed vb1, and another proposed vb2, by LearnerReceivedAcceptImpliesProposed.
    var lnr1: nat :| ChosenAtLearner(c, v.History(i), vb1, lnr1);
    assert Chosen(c, v.History(j), vb1) by {
      SetContainmentCardinality(v.History(i).learners[lnr1].receivedAccepts.m[vb1], v.History(j).learners[lnr1].receivedAccepts.m[vb1]);
      assert ChosenAtLearner(c, v.History(j), vb1, lnr1);  // trigger
    }
    // There are then two cases. If vb1.b == vb2.b, then the conclusion holds via OneValuePerBallot
    // Otherwise, leader 2 must hear leader 1's ballot, by ChosenImpliesProposingLeaderHearsChosenBallot.
    // Then by ChosenValImpliesLeaderOnlyHearsVal, leader 2 must have same value as leader 1.
    // assert vb1.v == vb2.v;
  }
}

// If only one value can be chosen, then Agreement must be satisfied
lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneChosenVal(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures Agreement(c, v)
{
  // Proof by contradiction
  if !Agreement(c, v) {
    var l1, l2 :| 
        && c.ValidLearnerIdx(l1)
        && c.ValidLearnerIdx(l2)
        && v.Last().learners[l1].learned.Some?
        && v.Last().learners[l2].learned.Some?
        && v.Last().learners[l1].learned != v.Last().learners[l2].learned
    ;
    var vb1 := LearnedImpliesChosen(c, v, l1, v.Last().learners[l1].learned.value);
    var vb2 := LearnedImpliesChosen(c, v, l2, v.Last().learners[l2].learned.value);
    assert false;
  }
}

// Lemma: The only system step in which a new vb can be chosen is a P2bStep 
lemma NewChosenOnlyInLearnerStep(c: Constants, v: Variables, v': Variables, dsStep: Step) 
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires !dsStep.LearnerHostStep?
  ensures forall vb | Chosen(c, v'.Last(), vb) :: Chosen(c, v.Last(), vb)
  ensures forall vb | Chosen(c, v'.history[|v'.history|-1], vb) 
      :: && Chosen(c, v'.history[|v'.history|-2], vb)
         && Chosen(c, v'.history[|v'.history|-2], vb)
         && Chosen(c, v.history[|v.history|-1], vb)
        
{
  forall vb | Chosen(c, v'.Last(), vb) 
  ensures Chosen(c, v'.history[|v'.history|-2], vb) {
    var lnr:LearnerId :| ChosenAtLearner(c, v'.Last(), vb, lnr);   // witness
    assert ChosenAtLearner(c, v.Last(), vb, lnr);                  // trigger
  }
}

// Suppose vb is chosen. Return the quorum of acceptors supporting the chosen vb
lemma SupportingAcceptorsForChosen(c: Constants, v: Variables, i:int, vb: ValBal)
returns (supportingAccs: set<AcceptorId>)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires Chosen(c, v.History(i), vb)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  ensures |supportingAccs| >= c.f+1
  ensures forall a | a in supportingAccs :: 
    && c.ValidAcceptorIdx(a)
    && v.History(i).acceptors[a].HasAcceptedAtLeastBal(vb.b)
  ensures exists lnr :: 
    && c.ValidLearnerIdx(lnr)
    && vb in v.History(i).learners[lnr].receivedAccepts.m
    && supportingAccs <= v.History(i).learners[lnr].receivedAccepts.m[vb]
{
  var lnr: LearnerId :| ChosenAtLearner(c, v.History(i), vb, lnr);  // skolemize!
  supportingAccs := v.History(i).learners[lnr].receivedAccepts.m[vb];
  return supportingAccs;
}

lemma GetAcceptorSet(c: Constants, v: Variables)
returns (accSet: set<AcceptorId>)
  requires v.WF(c)
  ensures forall a :: c.ValidAcceptorIdx(a) <==> a in accSet
  ensures |accSet| == 2 * c.f + 1
{
  assert v.history[0].WF(c);  // trigger for |c.acceptors| == 2 * c.f+1
  accSet := set a |  0 <= a < |c.acceptors|;
  SetComprehensionSize(|c.acceptors|);
}

lemma ChosenImpliesProposeMessagesOnlyContainValue(c: Constants, v: Variables, vb: ValBal) 
  requires Inv(c, v)
  requires Chosen(c, v.Last(), vb)
  ensures forall prop | 
    && IsProposeMessage(v, prop)
    && vb.b <= prop.bal
  ::
    vb.v == prop.val
{
  forall prop | 
    && IsProposeMessage(v, prop)
    && vb.b <= prop.bal
  ensures
    vb.v == prop.val
  {
    if vb.b == prop.bal {
      // Because vb is chosen, leader vb.b proposed it, by LearnerReceivedAcceptImpliesProposed. 
      // Also, leader vb.b sent prop, and so must proposed prob.val, by MessageInv.
      // Result then follows from LeaderCanProposeMonotonic
      //reveal_ChosenAtHistory();
    } else {
      // Leader prop.bal must hear leader vb.b's ballot, by ChosenImpliesProposingLeaderHearsChosenBallot.
      // Then by ChosenValImpliesLeaderOnlyHearsVal, leader 2 must have same value as leader 1.
    }
  }
}
} // end module PaxosProof
