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
  // From Leader transitions
  && LeaderValidReceivedPromises(c, v)
  && LeaderValidProposedSeq(c, v)
  && ValidProposeMesssage(c, v)
  // From Acceptor transitions
  && AcceptorValidPromised(c, v)
  && AcceptorValidAcceptedVB(c, v)
  && ValidPromiseMessage(c, v)
  && ValidAcceptMessage(c, v)
  // From Learner transitions
  && LearnerValidReceivedAccepts(c, v)
  && ValidLearnMessage(c, v)
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
  InvNextLeaderValidReceivedPromises(c, v, v');
  InvNextValidProposeMesssage(c, v, v');
  InvNextAcceptorValidPromised(c, v, v');
  InvNextValidPromiseMessage(c, v, v');
  InvNextValidAcceptMessage(c, v, v');
}

/***************************************************************************************
*                                     Leader Host                                      *
***************************************************************************************/

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, p | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].receivedPromises|
    && p in v.leaders[idx].receivedPromises[i]
  :: 
    IsPromiseMessage(v, p)
}

predicate LeaderValidProposedSeq(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, i | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v.leaders[idx].proposed|
  ::
    Propose(c.leaderConstants[idx].id, v.leaders[idx].proposed[i]) in v.network.sentMsgs
}

// certified self-inductive
predicate ValidProposeMesssage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall prop | IsProposeMessage(v, prop)
  ::
    && prop.val in v.leaders[prop.bal].proposed
    && (exists i, j ::
      && 0 <= i < |v.leaders[prop.bal].value|
      && 0 <= j < |v.leaders[prop.bal].proposed|
      && v.leaders[prop.bal].value[i] == prop.val
      && |v.leaders[prop.bal].receivedPromises[i]| >= c.f+1
      && prop.val == v.leaders[prop.bal].proposed[j]
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

// certified self-inductive
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

predicate PromiseMessageMatchesHistory(c: Constants, v: Variables, prom: Message, i: nat)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires IsPromiseMessage(v, prom)
{
  && prom in v.acceptors[prom.acc].sentPromises
  && 0 <= i < |v.acceptors[prom.acc].promised|
  && 0 <= i < |v.acceptors[prom.acc].acceptedVB|
  && prom.bal == v.acceptors[prom.acc].promised[i]
  && prom.vbOpt == v.acceptors[prom.acc].acceptedVB[i]
}

// certified self-inductive
// Every Accept message reflects acceptor state history
predicate ValidAcceptMessage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall accept | IsAcceptMessage(v, accept)
  ::
  (exists i :: 
    && 0 <= i < |v.acceptors[accept.acc].acceptedVB|
    && v.acceptors[accept.acc].acceptedVB[i] == Some(accept.vb)
    && v.acceptors[accept.acc].promised[i] == accept.vb.b
  )
}


/***************************************************************************************
*                                     Learner Host                                     *
***************************************************************************************/

// certified self-inductive
// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
predicate LearnerValidReceivedAccepts(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc, i | 
    && c.ValidLearnerIdx(idx)
    && vb in v.learners[idx].receivedAccepts
    && 0 <= i < |v.learners[idx].receivedAccepts[vb]|
    && acc in v.learners[idx].receivedAccepts[vb][i]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}

// certified self-inductive
predicate ValidLearnMessage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall learn | IsLearnMessage(v, learn)
  :: 
  VB(learn.val, learn.bal) in v.learners[learn.lnr].learned
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/


lemma InvNextLeaderValidReceivedPromises(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LeaderValidReceivedPromises(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromises(c, v')
{
  forall idx, i, p | 
    && c.ValidLeaderIdx(idx)
    && 0 <= i < |v'.leaders[idx].receivedPromises|
    && p in v'.leaders[idx].receivedPromises[i]
  ensures
    IsPromiseMessage(v', p)
  {
    assert IsPromiseMessage(v, p);  // trigger
  }
}


// Tony: This message invariant requires proof. What do I make of this?
// Because dafny can't handle alternating quantifiers
lemma InvNextValidProposeMesssage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidProposeMesssage(c, v)
  requires Next(c, v, v')
  ensures ValidProposeMesssage(c, v')
{
  forall prop | IsProposeMessage(v', prop)
  ensures
    && prop.val in v'.leaders[prop.bal].proposed
    && (exists i, j ::
      && 0 <= i < |v'.leaders[prop.bal].value|
      && 0 <= j < |v'.leaders[prop.bal].proposed|
      && v'.leaders[prop.bal].value[i] == prop.val
      && |v'.leaders[prop.bal].receivedPromises[i]| >= c.f+1
      && prop.val == v'.leaders[prop.bal].proposed[j]
    )
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if dsStep.LeaderStep? && prop.bal == actor {
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
      if step.ProposeStep? && prop == msgOps.send.value {
        var i := |l'.value| - 1;
      } else {
        // witness and trigger
        var i :| 0 <= i < |l.value| && l.value[i] == prop.val && |l.receivedPromises[i]| >= c.f+1;
        assert 0 <= i < |l'.value| && l'.value[i] == prop.val && |l'.receivedPromises[i]| >= c.f+1;
      }
    }
  }
}

// Tony: This message invariant requires proof. What do I make of this?
// Because dafny can't handle alternating quantifiers
lemma InvNextAcceptorValidPromised(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
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

// Because dafny can't handle alternating quantifiers
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

// Because dafny can't handle alternating quantifiers
lemma InvNextValidAcceptMessage(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidAcceptMessage(c, v)
  requires Next(c, v, v')
  ensures ValidAcceptMessage(c, v')
{
  forall accept | IsAcceptMessage(v', accept)
  ensures exists i :: 
    && 0 <= i < |v'.acceptors[accept.acc].acceptedVB|
    && v'.acceptors[accept.acc].acceptedVB[i] == Some(accept.vb)
    && v'.acceptors[accept.acc].promised[i] == accept.vb.b
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.AcceptorStep? 
       && accept.acc == actor 
       && msgOps.send == Some(accept)
    {
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.ReceiveStep? && msgOps.recv.value.Propose? {
        var doAccept := a.PromisedNone() || a.GetPromised() <= msgOps.recv.value.bal;
        if doAccept {
          var i := |a'.acceptedVB|-1;
          assert v'.acceptors[accept.acc].acceptedVB[i] == Some(accept.vb); // trigger
          assert v'.acceptors[accept.acc].promised[i] == accept.vb.b;       // trigger
        }
      }
    } else {
      assert IsAcceptMessage(v, accept);  // trigger
      var i :|  && 0 <= i < |v.acceptors[accept.acc].acceptedVB|   // witness
                && v.acceptors[accept.acc].acceptedVB[i] == Some(accept.vb)
                && v.acceptors[accept.acc].promised[i] == accept.vb.b;
      assert  && 0 <= i < |v'.acceptors[accept.acc].acceptedVB|    // trigger
              && v'.acceptors[accept.acc].acceptedVB[i] == Some(accept.vb)
              && v'.acceptors[accept.acc].promised[i] == accept.vb.b;
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
}  // end module PaxosProof

