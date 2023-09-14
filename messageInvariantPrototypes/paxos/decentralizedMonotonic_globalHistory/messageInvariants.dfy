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
  // && LeaderValidReceivedPromises(c, v)
  && ValidProposeMesssage(c, v)
  // From Acceptor transitions
  && AcceptorValidAccepted(c, v)
  && ValidPromiseMessage(c, v)
  && ValidAcceptMessage(c, v)
  // // From Learner transitions
  && LearnerValidReceivedAccepts(c, v)
  // && ValidLearnMessage(c, v)
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
  InvNextAcceptorValidAccepted(c, v, v');
  InvNextValidPromiseMessage(c, v, v');
  InvNextValidAcceptMessage(c, v, v');
  InvNextLearnerValidReceivedAccepts(c, v, v');
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
      && v.ValidHistoryIdx(i)
      && var ldr := v.History(i).leaders[prop.bal];
      && ldr.CanPropose(c.leaderConstants[prop.bal])
      && prop.val == ldr.value
    )
}

/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/

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
      && v'.ValidHistoryIdx(i)
      && var ldr := v'.History(i).leaders[prop.bal];
      && ldr.CanPropose(c.leaderConstants[prop.bal])
      && prop.val == ldr.value
    )
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    var i: int;
    if && dsStep.LeaderStep? 
       && actor == prop.bal
       && msgOps.send == Some(prop) {
        // witness
        i := |v.history| - 1;
    } else {
      assert IsProposeMessage(v, prop);
      // witness
      i :|       
          && v.ValidHistoryIdx(i)
          && var ldr := v.History(i).leaders[prop.bal];
          && ldr.CanPropose(c.leaderConstants[prop.bal])
          && prop.val == ldr.value;
    }
    // trigger
      assert  
        && v'.ValidHistoryIdx(i)
        && var ldr := v'.History(i).leaders[prop.bal];
        && ldr.CanPropose(c.leaderConstants[prop.bal])
        && prop.val == ldr.value;
  }
}

lemma InvNextAcceptorValidAccepted(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires AcceptorValidAccepted(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidAccepted(c, v')
{
  forall acc, i |
    && c.ValidAcceptorIdx(acc) 
    && v'.ValidHistoryIdx(i)
    && v'.History(i).acceptors[acc].acceptedVB.Some?
  ensures
    && var vb := v'.History(i).acceptors[acc].acceptedVB.value;
    && Propose(vb.b, vb.v) in v'.network.sentMsgs
  {
    var vb := v'.History(i).acceptors[acc].acceptedVB.value;
    if Propose(vb.b, vb.v) in v.network.sentMsgs {
      assert Propose(vb.b, vb.v) in v'.network.sentMsgs;
    } else {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if i == |v'.history| - 1 {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        if && dsStep.AcceptorStep?
          && actor == acc
        {
          assert AcceptorHost.Next(c.acceptorConstants[actor], v.Last().acceptors[actor], v'.Last().acceptors[actor], msgOps);
          var ac, a, a' := c.acceptorConstants[actor], v.Last().acceptors[actor], v'.Last().acceptors[actor];
          var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
          if step.MaybeAcceptStep? {
            assert Propose(vb.b, vb.v) in v'.network.sentMsgs;
          } else {
            assert v.History(i-1).acceptors[acc].acceptedVB.Some?;  // trigger
          }
        } else {
          assert v.History(i-1).acceptors[acc].acceptedVB.Some?;  // trigger
        }
      } else {
        assert v.History(i).acceptors[acc].acceptedVB.Some?;  // trigger
      }
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
  forall accept | IsAcceptMessage(v', accept)
  ensures exists i :: 
    && v'.ValidHistoryIdx(i)
    && v'.History(i).acceptors[accept.acc].acceptedVB == Some(accept.vb)
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    var actor, msgOps := dsStep.actor, dsStep.msgOps;
    if && dsStep.AcceptorStep? 
       && accept.acc == actor 
       && msgOps.send == Some(accept)
    {
      var ac, a, a' := c.acceptorConstants[actor], v.Last().acceptors[actor], v'.Last().acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.BroadcastAcceptedStep?  {
        var i := |v'.history|-1;
        assert  && v'.ValidHistoryIdx(i)  // trigger 
                && v'.History(i).acceptors[accept.acc].acceptedVB == Some(accept.vb);
      }
    } else {
      var i :|  && v.ValidHistoryIdx(i)   // witness 
                && v.History(i).acceptors[accept.acc].acceptedVB == Some(accept.vb);
      assert  && v'.ValidHistoryIdx(i)    // trigger 
              && v'.History(i).acceptors[accept.acc].acceptedVB == Some(accept.vb);
    }
  }
}

lemma InvNextLearnerValidReceivedAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerValidReceivedAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
{
  forall idx, vb, acc, i | 
    && c.ValidLearnerIdx(idx)
    && v'.ValidHistoryIdx(i)
    && vb in v'.History(i).learners[idx].receivedAccepts
    && acc in v'.History(i).learners[idx].receivedAccepts[vb]
  ensures
    && Accept(vb, acc) in v'.network.sentMsgs
  {
    if Accept(vb, acc) in v.network.sentMsgs {
      assert Accept(vb, acc) in v'.network.sentMsgs;
    } else {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if i == |v'.history| - 1 {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        if && dsStep.LearnerStep?
           && actor == idx
        {
          var lc, l, l' := c.learnerConstants[actor], v.Last().learners[actor], v'.Last().learners[actor];
          var step :| LearnerHost.NextStep(lc, l, l', step, msgOps);
          if  && vb in l.receivedAccepts
              && acc in l.receivedAccepts[vb]
          {
            assert  && vb in v.History(i-1).learners[idx].receivedAccepts   // trigger
                    && acc in v.History(i-1).learners[idx].receivedAccepts[vb];
          }
        } else {
          assert  && vb in v.History(i-1).learners[idx].receivedAccepts     // trigger
                  && acc in v.History(i-1).learners[idx].receivedAccepts[vb];
        }
      } else {
        assert  && vb in v.History(i).learners[idx].receivedAccepts         // trigger
                && acc in v.History(i).learners[idx].receivedAccepts[vb];
      }
    }
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

