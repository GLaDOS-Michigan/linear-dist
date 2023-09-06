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
    case Learn(lnr, _, _) => c.ValidLearnerIdx(lnr)
}

// Message bundle
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessageSrc(c, v)
  // From Leader transitions
  // && LeaderValidReceivedPromises(c, v)
  && ValidProposeMesssage(c, v)
  // From Acceptor transitions
  && AcceptorValidAccepted(c, v)
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
  // InvNextLeaderValidReceivedPromises(c, v, v');
  InvNextValidProposeMesssage(c, v, v');
  InvNextValidPromiseMessage(c, v, v');
  InvNextValidAcceptMessage(c, v, v');
  InvNextLeaderValidLearnMessages(c, v, v');
}

/***************************************************************************************
*                                     Leader Host                                      *
***************************************************************************************/

// TONY: Whether or not I need the following LeaderValidReceivedPromises invariant
// affects whether I need to store received messages.

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
// Property of Receive
// ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
//   requires v.WF(c)
// {
//   forall idx, i, p | 
//     && c.ValidLeaderIdx(idx)
//     && 0 <= i < |v.leaders[idx].receivedPromises|
//     && p in v.leaders[idx].receivedPromises[i]
//   :: 
//     IsPromiseMessage(v, p)
// }

// certified self-inductive
// Property of Send
ghost predicate ValidProposeMesssage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall prop | IsProposeMessage(v, prop)
  ::
    (exists i ::
      && 0 <= i < |v.leaders[prop.bal].h|
      && var vi := v.leaders[prop.bal].h[i];
      && vi.CanPropose(c.leaderConstants[prop.bal])
      && prop.val == vi.value
    )
}

/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/

// certified self-inductive
// Acceptor updates its acceptedVB based on a Propose message carrying that ballot 
// and value
ghost predicate AcceptorValidAccepted(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && c.ValidAcceptorIdx(idx) 
    && 0 <= i < |v.acceptors[idx].h|
    && v.acceptors[idx].h[i].acceptedVB.Some?
  :: 
    && var vb :=v.acceptors[idx].h[i].acceptedVB.value;
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
  && 0 <= i < |v.acceptors[prom.acc].h|
  && v.acceptors[prom.acc].h[i].promised.Some?
  && prom.bal == v.acceptors[prom.acc].h[i].promised.value
  && prom.vbOpt == v.acceptors[prom.acc].h[i].acceptedVB
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
    && 0 <= i < |v.acceptors[accept.acc].h|
    && v.acceptors[accept.acc].h[i].acceptedVB == Some(accept.vb)
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
    && 0 <= i < |v.learners[idx].h|
    && vb in v.learners[idx].h[i].receivedAccepts
    && acc in v.learners[idx].h[i].receivedAccepts[vb]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}

// certified self-inductive
ghost predicate ValidLearnMessage(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall learn | IsLearnMessage(v, learn)
  :: 
  (exists i ::
    && 0 <= i < |v.learners[learn.lnr].h| 
    && var vb := VB(learn.val, learn.bal);
    && vb in v.learners[learn.lnr].h[i].receivedAccepts
    && |v.learners[learn.lnr].h[i].receivedAccepts[vb]| >= c.f + 1
  )
}


/***************************************************************************************
*                               Proofs (how unfortunate)                               *
***************************************************************************************/


// lemma InvNextLeaderValidReceivedPromises(c: Constants, v: Variables, v': Variables)
//   requires v.WF(c)
//   requires LeaderValidReceivedPromises(c, v)
//   requires Next(c, v, v')
//   ensures LeaderValidReceivedPromises(c, v')
// {
//   forall idx, i, p | 
//     && c.ValidLeaderIdx(idx)
//     && 0 <= i < |v'.leaders[idx].receivedPromises|
//     && p in v'.leaders[idx].receivedPromises[i]
//   ensures
//     IsPromiseMessage(v', p)
//   {
//     assert IsPromiseMessage(v, p);  // trigger
//   }
// }


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
    (exists i ::
      && 0 <= i < |v'.leaders[prop.bal].h|
      && var vi := v'.leaders[prop.bal].h[i];
      && vi.CanPropose(c.leaderConstants[prop.bal])
      && prop.val == vi.value
    )
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    var i: int;
    if dsStep.LeaderStep? && actor == prop.bal {
      if msgOps.send == Some(prop) {
        // witness
        i := |v.leaders[prop.bal].h| - 1;
      } else {
        assert IsProposeMessage(v, prop);
        // witness
        i :|       
            && 0 <= i < |v.leaders[prop.bal].h|
            && var vi := v.leaders[prop.bal].h[i];
            && vi.CanPropose(c.leaderConstants[prop.bal])
            && prop.val == vi.value;
      }
      // trigger
      assert  
        && 0 <= i < |v'.leaders[prop.bal].h|
        && var vi := v'.leaders[prop.bal].h[i];
        && vi.CanPropose(c.leaderConstants[prop.bal])
        && prop.val == vi.value;
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
      if step.MaybePromiseStep? {
        var doPromise := a.Last().promised.None? || (a.Last().promised.Some? && a.Last().promised.value < a.Last().pendingPrepare.value.bal);
        if doPromise {
          assert PromiseMessageMatchesHistory(c, v', prom, |a'.h|-1);  // trigger
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
    && 0 <= i < |v'.acceptors[accept.acc].h|
    && v'.acceptors[accept.acc].h[i].acceptedVB == Some(accept.vb)
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.AcceptorStep? 
       && accept.acc == actor 
       && msgOps.send == Some(accept)
    {
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.BroadcastAcceptedStep?  {
        var i := |a.h|-1;
        assert  && 0 <= i < |v'.acceptors[accept.acc].h|  // trigger 
                && v'.acceptors[accept.acc].h[i].acceptedVB == Some(accept.vb);
      }
    } else {
      assert IsAcceptMessage(v, accept);  // trigger
      var i :|  && 0 <= i < |v.acceptors[accept.acc].h|  // witness
                && v.acceptors[accept.acc].h[i].acceptedVB == Some(accept.vb);
      assert    && 0 <= i < |v'.acceptors[accept.acc].h|  // trigger 
                && v'.acceptors[accept.acc].h[i].acceptedVB == Some(accept.vb);
    }
  }
}

lemma InvNextLeaderValidLearnMessages(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires ValidLearnMessage(c, v)
  requires Next(c, v, v')
  ensures ValidLearnMessage(c, v')
{
  forall learn | IsLearnMessage(v', learn)
  ensures exists i ::
    && 0 <= i < |v'.learners[learn.lnr].h| 
    && var vb := VB(learn.val, learn.bal);
    && vb in v'.learners[learn.lnr].h[i].receivedAccepts
    && |v'.learners[learn.lnr].h[i].receivedAccepts[vb]| >= c.f + 1
  {
    var vb := VB(learn.val, learn.bal);
    var i: nat;
    var dsStep :| NextStep(c, v, v', dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.LearnerStep? 
       && learn.lnr == actor 
       && msgOps.send == Some(learn)
    { 
      i := |v.learners[learn.lnr].h| - 1;  // witness
    } else {
      // witness and trigger
      i :| 
        && 0 <= i < |v.learners[learn.lnr].h| 
        && vb in v.learners[learn.lnr].h[i].receivedAccepts
        && |v.learners[learn.lnr].h[i].receivedAccepts[vb]| >= c.f + 1;
    }
    // trigger
    assert 
        && 0 <= i < |v'.learners[learn.lnr].h| 
        && vb in v'.learners[learn.lnr].h[i].receivedAccepts
        && |v'.learners[learn.lnr].h[i].receivedAccepts[vb]| >= c.f + 1;
  }
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

ghost predicate IsLearnMessage(v: Variables, m: Message) {
  && m.Learn?
  && m in v.network.sentMsgs
} 
}  // end module PaxosProof

