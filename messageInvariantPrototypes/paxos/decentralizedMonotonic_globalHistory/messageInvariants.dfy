include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self-inductive
// Every message in the network has a valid source
ghost predicate ValidMessageSrc(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: 
  match msg 
    case Prepare(bal) => c.ValidLeaderIdx(bal)
    case Promise(_, acc, _) => c.ValidAcceptorIdx(acc)
    case Propose(bal, _) => c.ValidLeaderIdx(bal)
    case Accept(_, acc) => c.ValidAcceptorIdx(acc)
}

// Message bundle
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessageSrc(c, v)
  // From Leader transitions
  && LeaderValidReceivedPromises(c, v)
  && LeaderValidHighestHeard(c, v)
  && ValidProposeMesssage(c, v)
  // From Acceptor transitions
  && AcceptorValidPendingPrepare(c, v)
  && AcceptorValidAccepted(c, v)
  && ValidPromiseMessage(c, v)
  && ValidAcceptMessage(c, v)
  // From Learner transitions
  && LearnerValidReceivedAccepts(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidMessageSrc(c, v, v');
  InvNextLeaderValidReceivedPromises(c, v, v');
  InvNextLeaderValidHighestHeard(c, v, v');
  InvNextValidProposeMesssage(c, v, v');
  InvNextAcceptorValidPendingPrepare(c, v, v');
  InvNextAcceptorValidAccepted(c, v, v');
  InvNextValidPromiseMessage(c, v, v');
  InvNextValidAcceptMessage(c, v, v');
  InvNextLearnerValidReceivedAccepts(c, v, v');
}

/***************************************************************************************
*                                     Leader Host                                      *
***************************************************************************************/

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
// Property of Receive
ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, i, acc | 
    && c.ValidLeaderIdx(ldr)
    && v.ValidHistoryIdx(i)
    && acc in v.History(i).leaders[ldr].receivedPromises
  :: 
    (exists prom :: 
      && IsPromiseMessage(v, prom)
      && prom.bal == ldr
      && prom.acc == acc
    )
}

ghost predicate LeaderValidHighestHeard(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall ldr, i | 
    && c.ValidLeaderIdx(ldr)
    && v.ValidHistoryIdx(i)
    && v.History(i).leaders[ldr].highestHeardBallot.Some?
  :: 
    (exists prom :: 
      && IsPromiseMessage(v, prom)
      && prom.bal == ldr
      && prom.vbOpt == Some(VB(v.History(i).leaders[ldr].value, v.History(i).leaders[ldr].highestHeardBallot.value))
    )
}

// certified self-inductive
// Property of Send
ghost predicate ValidProposeMesssage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall prop | IsProposeMessage(v, prop)
  ::
    (exists i ::
      && v.ValidHistoryIdx(i)
      && var ldr := v.History(i).leaders[prop.bal];
      && ldr.CanPropose(c.leaderConstants[prop.bal])
      && prop.val == ldr.value
    )
}

/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/


// Acceptor's pendingPrepare comes from the network
ghost predicate AcceptorValidPendingPrepare(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall acc, i |
    && c.ValidAcceptorIdx(acc) 
    && v.ValidHistoryIdx(i)
    && v.History(i).acceptors[acc].pendingPrepare.Some?
  :: 
    Prepare(v.History(i).acceptors[acc].pendingPrepare.value.bal) in v.network.sentMsgs
} 

// certified self-inductive
// Acceptor updates its acceptedVB based on a Propose message carrying that ballot and value
ghost predicate AcceptorValidAccepted(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall acc, i |
    && c.ValidAcceptorIdx(acc) 
    && v.ValidHistoryIdx(i)
    && v.History(i).acceptors[acc].acceptedVB.Some?
  :: 
    && var vb := v.History(i).acceptors[acc].acceptedVB.value;
    && Propose(vb.b, vb.v) in v.network.sentMsgs
}

// certified self-inductive
// Every Promise message ballot reflects acceptor's local promised history, and 
// it's vbOpt represents a prior accepted value
// Property of Send
ghost predicate ValidPromiseMessage(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall prom | IsPromiseMessage(v, prom)
  ::
  (exists i :: PromiseMessageMatchesHistory(c, v, prom, i))
}

ghost predicate PromiseMessageMatchesHistory(c: Constants, v: Variables, prom: Message, i: nat)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires IsPromiseMessage(v, prom)
{
  && v.ValidHistoryIdx(i)
  && v.History(i).acceptors[prom.acc].promised.Some?
  && prom.bal == v.History(i).acceptors[prom.acc].promised.value
  && prom.vbOpt == v.History(i).acceptors[prom.acc].acceptedVB
}

// certified self-inductive
// Every Accept message reflects acceptor state history
// Property of Send
ghost predicate ValidAcceptMessage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall accept | IsAcceptMessage(v, accept)
  ::
  (exists i :: 
    && v.ValidHistoryIdx(i)
    && v.History(i).acceptors[accept.acc].acceptedVB == Some(accept.vb)
  )
}


/***************************************************************************************
*                                     Learner Host                                     *
***************************************************************************************/

// certified self-inductive
// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
// Property of Receive
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc, i | 
    && c.ValidLearnerIdx(idx)
    && v.ValidHistoryIdx(i)
    && vb in v.History(i).learners[idx].receivedAccepts
    && acc in v.History(i).learners[idx].receivedAccepts[vb]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/

lemma InvNextValidMessageSrc(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires Next(c, v, v')
  ensures ValidMessageSrc(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderValidReceivedPromises(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LeaderValidReceivedPromises(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromises(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderValidHighestHeard(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LeaderValidHighestHeard(c, v)
  requires Next(c, v, v')
  ensures LeaderValidHighestHeard(c, v')
{
  VariableNextProperties(c, v, v');
}


lemma InvNextValidProposeMesssage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidProposeMesssage(c, v)
  requires Next(c, v, v')
  ensures ValidProposeMesssage(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextAcceptorValidPendingPrepare(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires AcceptorValidPendingPrepare(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidPendingPrepare(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextAcceptorValidAccepted(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires AcceptorValidAccepted(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidAccepted(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextValidPromiseMessage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidPromiseMessage(c, v)
  requires Next(c, v, v')
  ensures ValidPromiseMessage(c, v')
{
  forall prom | IsPromiseMessage(v', prom)
  ensures
    exists i :: PromiseMessageMatchesHistory(c, v', prom, i)
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.AcceptorStep? 
       && prom.acc == actor 
       && msgOps.send == Some(prom)
    {
      var ac, a, a' := c.acceptorConstants[actor], v.Last().acceptors[actor], v'.Last().acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.MaybePromiseStep? {
        var doPromise := a.promised.None? || (a.promised.Some? && a.promised.value < a.pendingPrepare.value.bal);
        if doPromise {
          assert PromiseMessageMatchesHistory(c, v', prom, |v'.history|-1);  // trigger
        }
      }
    } else {
      assert IsPromiseMessage(v, prom);  // trigger
      var i :| PromiseMessageMatchesHistory(c, v, prom, i);  // witness
      assert PromiseMessageMatchesHistory(c, v', prom, i);   // trigger
    }
  }
}

lemma InvNextValidAcceptMessage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidAcceptMessage(c, v)
  requires Next(c, v, v')
  ensures ValidAcceptMessage(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLearnerValidReceivedAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerValidReceivedAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
{
  VariableNextProperties(c, v, v');
}

/***************************************************************************************
*                                        Utils                                         *
***************************************************************************************/

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

lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires Next(c, v, v')
  ensures 1 < |v'.history|
  ensures |v.history| == |v'.history| - 1
  ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)
  ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)
{
  assert 0 < |v.history|;
  assert 1 < |v'.history|;
}

lemma GetAcceptorSet(c: Constants, v: Variables)
returns (accSet: set<AcceptorId>)
  requires v.WF(c)
  ensures forall a :: c.ValidAcceptorIdx(a) <==> a in accSet
  ensures |accSet| == 2 * c.f + 1
{
  assert v.History(0).WF(c);  // trigger for |c.acceptorConstants| == 2 * c.f+1
  accSet := set a |  0 <= a < |c.acceptorConstants|;
  SetComprehensionSize(|c.acceptorConstants|);
}
}  // end module PaxosProof

