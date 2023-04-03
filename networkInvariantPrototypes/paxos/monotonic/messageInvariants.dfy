include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self-inductive
// Every message in the network has a valid source
predicate ValidMessageSrc(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: 
  match msg 
    case Prepare(bal) => c.ValidLeaderIdx(bal)
    case Promise(_, acc, _) => c.ValidAcceptorIdx(acc)
    case Propose(bal, _) => c.ValidLeaderIdx(bal)
    case Accept(_, acc) => c.ValidAcceptorIdx(acc)
    case Learn(lnr, _, _) => c.ValidLearnerIdx(lnr)
}

// Message bundle
predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessageSrc(c, v)
  // Leader stuff
  && LeaderValidHighestHeard(c, v)
  && LeaderValidReceivedPromises(c, v)
  // Acceptor stuff
  && AcceptorValidPromised(c, v)
  && AcceptorValidAcceptedVB(c, v)
  && ValidPromiseMessage(c, v)
  // Learner stuff
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
  InvNextAcceptorValidPromised(c, v, v');
  InvNextValidPromiseMessage(c, v, v');
}

/***************************************************************************************
*                                     Leader Host                                      *
***************************************************************************************/

// certified self-inductive
// Leader updates its highestHeard and value based on a Promise message carrying that
// ballot and value
predicate LeaderValidHighestHeard(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, b| c.ValidLeaderIdx(idx) && v.leaders[idx].highestHeardBallot == Some(b)
  :: (exists prom: Message ::
        && IsPromiseMessage(v, prom)
        && prom.bal == idx
        && prom.vbOpt == Some(VB(v.leaders[idx].value, b))
    )
}

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, src | c.ValidLeaderIdx(idx) && src in v.leaders[idx].receivedPromises
  :: (exists prom: Message ::
        && IsPromiseMessage(v, prom)
        && prom.bal == idx
    )
} 

/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/

// certified self-inductive
// Acceptor updates its promised ballot based on a Prepare/Propose message carrying 
// that ballot. Derived from only NextReceiveStep
predicate AcceptorValidPromised(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i | 
    && c.ValidAcceptorIdx(idx) 
    && 0 <= i < |v.acceptors[idx].promised|
  :: 
    ExistsIsPrepareOrPropose(c, v, idx, i)
}

// certified self-inductive
// Acceptor updates its acceptedVB based on a Propose message carrying that ballot 
// and value, and there is also a corresponding Accept message
predicate AcceptorValidAcceptedVB(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i | 
    && c.ValidAcceptorIdx(idx) 
    && 0 <= i < |v.acceptors[idx].acceptedVB|
    && v.acceptors[idx].acceptedVB[i].Some?
  :: 
    && var vb := v.acceptors[idx].acceptedVB[i].value;
    && Propose(vb.b, vb.v) in v.network.sentMsgs
    && Accept(vb, c.acceptorConstants[idx].id) in v.network.sentMsgs
}

// Every Promise message ballot reflects acceptor's local promised history, and 
// it's vbOpt represents a prior accepted value
predicate ValidPromiseMessage(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall prom | IsPromiseMessage(v, prom)
  ::
  (exists i :: PromiseMessageMatchesHistory(c, v, prom, i))
}

// Every Accept message reflects acceptor state history
// predicate ValidAcceptMessage(c: Constants, v: Variables)


/***************************************************************************************
*                                     Learner Host                                     *
***************************************************************************************/



// certified self-inductive
// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
predicate LearnerValidReceivedAccepts(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc | 
    && c.ValidLearnerIdx(idx)
    && vb in v.learners[idx].receivedAccepts
    && acc in v.learners[idx].receivedAccepts[vb]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/

// Tony: This message invariant requires proof. What do I make of this?
// Also the copy-pasta for the unchanged cases are is gross
lemma InvNextAcceptorValidPromised(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires v'.WF(c)
  requires AcceptorValidPromised(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidPromised(c, v')
{
  forall idx, i | 
    && c.ValidAcceptorIdx(idx) 
    && 0 <= i < |v'.acceptors[idx].promised|
  ensures
    ExistsIsPrepareOrPropose(c, v', idx, i)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if dsStep.AcceptorStep? && idx == actor && i == |v'.acceptors[idx].promised| - 1 {
      var ac, a, a' := c.acceptorConstants[idx], v.acceptors[idx], v'.acceptors[idx];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.ReceiveStep? {
        var m := msgOps.recv.value;
        if m.Prepare? && (a.PromisedNone() || a.GetPromised() < m.bal) {
          assert IsPrepareOrPropose(v', m, a'.promised[i]);  // trigger
        } else if m.Propose? && (a.PromisedNone() || a.GetPromised() <= m.bal) {
          assert IsPrepareOrPropose(v', m, a'.promised[i]);  // trigger
        } else {
          assert ExistsIsPrepareOrPropose(c, v, idx, i);                    // trigger
          var m :| IsPrepareOrPropose(v, m, v.acceptors[idx].promised[i]);  // witness
          assert IsPrepareOrPropose(v', m, v'.acceptors[idx].promised[i]);  // trigger
        }
      } else {
        assert ExistsIsPrepareOrPropose(c, v, idx, i);                    // trigger
        var m :| IsPrepareOrPropose(v, m, v.acceptors[idx].promised[i]);  // witness
        assert IsPrepareOrPropose(v', m, v'.acceptors[idx].promised[i]);  // trigger
      }
    } else {
      assert ExistsIsPrepareOrPropose(c, v, idx, i);                    // trigger
      var m :| IsPrepareOrPropose(v, m, v.acceptors[idx].promised[i]);  // witness
      assert IsPrepareOrPropose(v', m, v'.acceptors[idx].promised[i]);  // trigger
    }
  }
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
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.AcceptorStep? 
       && prom.acc == actor 
       && msgOps.send == Some(prom)
    {
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.ReceiveStep? && msgOps.recv.value.Prepare? {
        var doPromise := a.PromisedNone() || a.GetPromised() < msgOps.recv.value.bal;
        if doPromise {
          assert PromiseMessageMatchesHistory(c, v', prom, |a'.promised|-1);  // trigger
        }
      }
    } else {
      assert IsPromiseMessage(v, prom);  // trigger
      var i :| PromiseMessageMatchesHistory(c, v, prom, i);  // witness
      assert PromiseMessageMatchesHistory(c, v', prom, i);   // trigger
    }
  }
}

/***************************************************************************************
*                                        Utils                                         *
***************************************************************************************/

predicate IsPrepareMessage(v: Variables, m: Message) {
  && m.Prepare?
  && m in v.network.sentMsgs
}

predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}

predicate IsLearnMessage(v: Variables, m: Message) {
  && m.Learn?
  && m in v.network.sentMsgs
} 

predicate IsPrepareOrPropose(v: Variables, m: Message, bal: LeaderId) {
  && m in v.network.sentMsgs
  && (m.Prepare? || m.Propose?)
  && m.bal == bal
}

// Tony: Dafny is somehow unable to prove AcceptorValidPromised(c, v') if the exists is
// not wrapped in such a predicate
predicate ExistsIsPrepareOrPropose(c: Constants, v: Variables, idx: nat, i: int) 
  requires v.WF(c)
  requires c.ValidAcceptorIdx(idx) 
  requires 0 <= i < |v.acceptors[idx].promised|
{
  exists m :: IsPrepareOrPropose(v, m, v.acceptors[idx].promised[i])
}

predicate PromiseMessageMatchesHistory(c: Constants, v: Variables, prom: Message, i: nat)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires IsPromiseMessage(v, prom)
{
  && 0 <= i < |v.acceptors[prom.acc].promised|
  && 0 <= i < |v.acceptors[prom.acc].acceptedVB|
  && prom.bal == v.acceptors[prom.acc].promised[i]
  && prom.vbOpt == v.acceptors[prom.acc].acceptedVB[i]
}

}  // end module PaxosProof

