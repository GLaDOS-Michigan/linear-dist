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

  // Util: A quorum of Accept messages of the same vb
  // Tony: Using monotonic transformations, I can push this to an acceptor host property,
  // rather than a network property.
  predicate Chosen(c: Constants, v: Variables, vb: ValBal) {
    exists quorum: set<Message> :: IsAcceptQuorum(c, v, quorum, vb)
  }

  predicate AtMostOneChosenVal(c: Constants, v: Variables) {
    forall vb1, vb2 | Chosen(c, v, vb1) && Chosen(c, v, vb2) 
    :: vb1.v == vb2.v
  }

  predicate OneValuePerProposeBallot(c: Constants, v: Variables)
  {
    forall p1, p2 | 
      && p1 in v.network.sentMsgs
      && p2 in v.network.sentMsgs
      && p1.Propose? && p2.Propose?
      && p1.bal == p2.bal
    ::
      p1.val == p2.val
  }

  // For every Accept(vb, src) in the network, the source acceptor must have accepted 
  // some ballot >= vb.b. This is not a message invariant because it depends on the fact
  // that at every acceptor, accepted bal <= promised bal. I.e. once I accept a ballot, 
  // I cannot accept a smaller ballot
  // Tony: This can be broken down via monotonic transformation. The Accept message says 
  // that leader state had the specific bal at some point in time, and this is a message
  // invariant. Another application invariant then says that this accepted seq is monotone
  // increasing. 
  predicate AcceptMessagesValid(c: Constants, v: Variables)
    requires v.WF(c)
    requires ValidMessageSrc(c, v)
  {
    forall acc | acc in v.network.sentMsgs && acc.Accept?
    ::  && v.acceptors[acc.acc].acceptedVB.Some?
        && acc.vb.b <= v.acceptors[acc.acc].acceptedVB.value.b
  }

  // For every acceptor that accepted some vb, every Promise p with p.bal > vb.b from that 
  // acceptor must carry a non-None vbOpt. This is not a message invariant because it depends
  // on the fact that at every acceptor, accepted bal <= promised bal. I.e. once I accept 
  // a ballot, I cannot accept a smaller ballot
  // Tony: This can be broken down via monotonic transformation
  predicate AcceptedImpliesLargerPromiseCarriesVb(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx, prom | 
      && c.ValidAcceptorIdx(idx) 
      && v.acceptors[idx].acceptedVB.Some?
      && prom in v.network.sentMsgs
      && prom.Promise?
      && prom.acc == c.acceptorConstants[idx].id
      && v.acceptors[idx].acceptedVB.value.b < prom.bal
    :: 
      prom.vbOpt.Some?
  }

  // Tony: If receivedPromises remembers whole messages rather than the source, this 
  // need not mention the network (monotonic transformation)
  // Every leader's HighestHeard is backed by a set of Promise messages.
  predicate HighestHeardBackedByReceivedPromises(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall idx | c.ValidLeaderIdx(idx)
    :: (
      && var ldr := v.leaders[idx];
      && exists pset :: LeaderPromiseSetProperties(c, v, idx, pset)
    )
  }

  predicate LeaderPromiseSetProperties(c: Constants, v: Variables, idx: int, pset: set<Message>) 
    requires v.WF(c)
    requires c.ValidLeaderIdx(idx)
  {
    var ldr := v.leaders[idx];
    var cldr := c.leaderConstants[idx];
    var hbal := ldr.highestHeardBallot;
    && IsPromiseSet(c, v, pset, cldr.id)
    && (hbal.Some? ==> PromiseSetHighestVBOptVal(c, v, pset, cldr.id, hbal.value, ldr.value))
    && (hbal.None? ==> PromiseSetEmptyVBOpt(c, v, pset, cldr.id))
    && |pset| == |ldr.receivedPromises|
    && (forall p: Message | p in pset :: p.acc in ldr.receivedPromises)
  }

  // Tony: If receivedPromises remembers whole messages rather than the source, this 
  // need not mention the network (monotonic transformation)
  // Every Propose message is backed by a quorum of Promise messages
  predicate ProposeBackedByPromiseQuorum(c: Constants, v: Variables) {
    forall p | p in v.network.sentMsgs && p.Propose?
    :: (exists quorum :: PromiseQuorumSupportsVal(c, v, quorum, p.bal, p.val))
  }

  // If an acceptor has accepted vb, then it must have promised a ballot >= vb.b
  predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx | 
      && c.ValidAcceptorIdx(idx) 
      && v.acceptors[idx].acceptedVB.Some?
    :: 
      && v.acceptors[idx].promised.Some?
      && v.acceptors[idx].acceptedVB.value.b <= v.acceptors[idx].promised.value
  }

  // Inv: If vb is chosen, then for all acceptors that have acceptedVB.b >= vb.b, they have
  // acceptedVB.v == vb.v
  predicate ChosenValImpliesLargerAcceptorsHoldsVal(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall vb, acc | 
      && Chosen(c, v, vb) 
      && c.ValidAcceptorIdx(acc)
      && v.acceptors[acc].acceptedVB.Some?
      && v.acceptors[acc].acceptedVB.value.b >= vb.b
    ::
      v.acceptors[acc].acceptedVB.value.v == vb.v
  }

  // Inv: If vb is chosen, then for all Accept messages that have msg.vb.b >= vb.b, they have
  // msg.vb.v == vb.v
  predicate ChosenValImpliesLargerAcceptMsgsHoldsVal(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall vb, msg | 
      && Chosen(c, v, vb) 
      && msg in v.network.sentMsgs
      && msg.Accept?
      && msg.vb.b >= vb.b
    ::
      msg.vb.v == vb.v
  }

  // Inv: If vb is chosen, then for all leaders that have highestHeard >= vb.b, they must have 
  // value == vb.v
  predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall vb, ldr | 
      && Chosen(c, v, vb) 
      && c.ValidLeaderIdx(ldr)
      && v.leaders[ldr].highestHeardBallot.Some?
      && v.leaders[ldr].highestHeardBallot.value >= vb.b
    ::
      v.leaders[ldr].value == vb.v
  }

  // Inv: If vb is chosen, then for all Propose messages that have bal >= vb.b, they must have 
  // value == vb.v
  // Tony: Using monotonic transformations, by recording the entire history of leader 
  // (value, highestHeardBallot) pairs, this becomes implicit from ChosenValImpliesLeaderOnlyHearsVal,
  // rather than a network property as an application invariant.
  predicate ChosenValImpliesProposeOnlyVal(c: Constants, v: Variables) {
    forall vb, propose | 
      && Chosen(c, v, vb)
      && propose in v.network.sentMsgs
      && propose.Propose?
      && propose.bal >= vb.b
    ::
      propose.val == vb.v
  }

  // Inv: If vb is chosen, then for all Promise messages that reflect a prior accepted (bal, val)
  // such that bal >= b, they must have val == vb.v
  // Tony: Using monotonic transformations, by recording the entire history of accepted 
  // pairs at each acceptor, this can be written as a property on acceptor local states,
  // and the corresponding constraint on Promise message becomes a trivial message invariant. 
  predicate ChosenValImpliesPromiseVBOnlyVal(c: Constants, v: Variables)
  {
    forall vb, promise | 
      && Chosen(c, v, vb)
      && promise in v.network.sentMsgs
      && promise.Promise?
      && promise.vbOpt.Some?
      && promise.vbOpt.value.b >= vb.b
    ::
      promise.vbOpt.value.v == vb.v
  }

  // Inv: If vb is chosen, and the leader has a quorum of receivedPromises, then its 
  // highestHeardBallot must be >= vb.b. This ensures that they can only propose vb.v
  predicate ChosenValImpliesPromiseQuorumSeesBal(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall vb, ldr | 
      && Chosen(c, v, vb) 
      && c.ValidLeaderIdx(ldr)
      && |v.leaders[ldr].receivedPromises| >= c.f+1
    ::
      && v.leaders[ldr].highestHeardBallot.Some?
      && v.leaders[ldr].highestHeardBallot.value >= vb.b
  }

  // Application bundle
  predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
    requires MessageInv(c, v)
  {
    && OneValuePerProposeBallot(c, v)
    && AcceptMessagesValid(c, v)
    && AcceptedImpliesLargerPromiseCarriesVb(c, v)
    && HighestHeardBackedByReceivedPromises(c, v)
    && ProposeBackedByPromiseQuorum(c, v)
    && AcceptorPromisedLargerThanAccepted(c, v)
    && ChosenValImpliesProposeOnlyVal(c, v)
    && ChosenValImpliesPromiseQuorumSeesBal(c, v)
    && ChosenValImpliesLeaderOnlyHearsVal(c, v)
    && ChosenValImpliesLargerAcceptMsgsHoldsVal(c, v)
    // && ChosenValImpliesLargerAcceptorsHoldsVal(c, v)   // not sure if needed
    // && ChosenValImpliesPromiseVBOnlyVal(c, v)          // not sure if needed
    && AtMostOneChosenVal(c, v)
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && MessageInv(c, v)
    && ApplicationInv(c, v)
    && Agreement(c, v)
  }


  /***************************************************************************************
  *                                        Proof                                         *
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
    // prove HighestHeardBackedByReceivedPromises(c, v)
    forall idx | c.ValidLeaderIdx(idx)
    ensures 
      && var ldr := v.leaders[idx];
      && exists pset :: LeaderPromiseSetProperties(c, v, idx, pset)
    {
      var pset := {};
      assert LeaderPromiseSetProperties(c, v, idx, pset);  // witness
    }
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    MessageInvInductive(c, v, v');

    assume OneValuePerProposeBallot(c, v');
    InvNextAcceptMessagesValid(c, v, v');
    InvNextAcceptedImpliesLargerPromiseCarriesVb(c, v, v');
    InvNextHighestHeardBackedByReceivedPromises(c, v, v');
    InvNextProposeBackedByPromiseQuorum(c, v, v');


    InvNextChosenValImpliesProposeOnlyVal(c, v, v');

    assume AcceptorPromisedLargerThanAccepted(c, v');
    assume ChosenValImpliesPromiseQuorumSeesBal(c, v');
    assume ChosenValImpliesLeaderOnlyHearsVal(c, v');
    assume ChosenValImpliesLargerAcceptMsgsHoldsVal(c, v');
    // assume ChosenValImpliesLargerAcceptorsHoldsVal(c, v');  // not sure if needed
    // assume ChosenValImpliesPromiseVBOnlyVal(c, v');  // not sure if needed
    AtMostOneChosenValNext(c, v, v');
    AtMostOneChosenImpliesAgreement(c, v');
  }

  lemma InvNextAcceptMessagesValid(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    ensures AcceptMessagesValid(c, v')
  {}

  lemma InvNextAcceptedImpliesLargerPromiseCarriesVb(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    ensures AcceptedImpliesLargerPromiseCarriesVb(c, v')
  {}

  lemma InvNextHighestHeardBackedByReceivedPromises(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    ensures HighestHeardBackedByReceivedPromises(c, v')
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.LeaderStep? {
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
      forall idx | c.ValidLeaderIdx(idx)
      ensures exists pset' :: LeaderPromiseSetProperties(c, v', idx, pset')
      {
        if && step.ReceiveStep? && actor == idx 
          && msgOps.recv.value.Promise? && msgOps.recv.value.bal == lc.id 
        {
          var pset :| LeaderPromiseSetProperties(c, v, idx, pset);
          var pset' := pset + {msgOps.recv.value};  // witness
          assert LeaderPromiseSetProperties(c, v', idx, pset');  // trigger
        } else {
          var pset :| LeaderPromiseSetProperties(c, v, idx, pset);  // witness
          assert LeaderPromiseSetProperties(c, v', idx, pset);  // trigger
        }
      }
    } else {
      forall idx | c.ValidLeaderIdx(idx)
      ensures exists pset' :: LeaderPromiseSetProperties(c, v', idx, pset')
      {
        var pset :| LeaderPromiseSetProperties(c, v, idx, pset);  // witness
        assert LeaderPromiseSetProperties(c, v', idx, pset);  // trigger
      }
    }
  }


  lemma InvNextProposeBackedByPromiseQuorum(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    ensures ProposeBackedByPromiseQuorum(c, v')
  {
    forall p | p in v'.network.sentMsgs && p.Propose?
    ensures exists quorum :: PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val)
    {
      var dsStep :| NextStep(c, v, v', dsStep);
      if dsStep.LeaderStep? {
        var actor, msgOps := dsStep.actor, dsStep.msgOps;
        var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
        var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
        if step.ProposeStep? && p !in v.network.sentMsgs {
          var quorum :| LeaderPromiseSetProperties(c, v, actor, quorum);  // witness
          if l.highestHeardBallot.Some? {
            assert PromiseSetHighestVBOptVal(c, v', quorum, actor, l.highestHeardBallot.value, l.value);  // trigger
          }
          assert PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val);  // trigger
        } else {
          InvNextProposeBackedByPromiseQuorumNoNewPropose(c, v, v', p);
        }
      } else {
        InvNextProposeBackedByPromiseQuorumNoNewPropose(c, v, v', p);
      }
    }
  }

  lemma InvNextProposeBackedByPromiseQuorumNoNewPropose(c: Constants, v: Variables, v': Variables, p: Message) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    requires p in v.network.sentMsgs
    requires p in v'.network.sentMsgs
    requires p.Propose?
    ensures exists quorum :: PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val)
  {
    var quorum :| PromiseQuorumSupportsVal(c, v, quorum, p.bal, p.val);  // witness
    if !PromiseSetEmptyVBOpt(c, v, quorum, p.bal) {
      var hsbal :| PromiseSetHighestVBOptVal(c, v, quorum, p.bal, hsbal, p.val);  // witness
      assert PromiseSetHighestVBOptVal(c, v', quorum, p.bal, hsbal, p.val);  // trigger
    }
    assert PromiseQuorumSupportsVal(c, v', quorum, p.bal, p.val);  // trigger
  }

  lemma InvNextChosenValImpliesProposeOnlyValAcceptorRecvStep(
    c: Constants, v: Variables, v': Variables, dsStep: Step, step: AcceptorHost.Step)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    requires NextStep(c, v, v', dsStep)
    requires dsStep.AcceptorStep?
    requires AcceptorHost.NextStep(
              c.acceptorConstants[dsStep.actor], 
              v.acceptors[dsStep.actor], v'.acceptors[dsStep.actor],
              step, dsStep.msgOps)
    requires step.ReceiveStep?
    requires dsStep.msgOps.recv.value.Propose?
    requires AcceptMessagesValid(c, v')
    requires ProposeBackedByPromiseQuorum(c, v')
    requires OneValuePerProposeBallot(c, v')
    ensures ChosenValImpliesProposeOnlyVal(c, v')
  {
    forall vb, propose | 
      && Chosen(c, v', vb)
      && propose in v'.network.sentMsgs
      && propose.Propose?
      && propose.bal >= vb.b
    ensures propose.val == vb.v
    {
      if !Chosen(c, v, vb) {
        /* This is a point where something can suddenly be chosen.*/
        var ac, a, a' := c.acceptorConstants[dsStep.actor], v.acceptors[dsStep.actor], v'.acceptors[dsStep.actor];
        var propVal, propBal := dsStep.msgOps.recv.value.val, dsStep.msgOps.recv.value.bal;
        var doAccept := a.promised.None? || (a.promised.Some? && a.promised.value <= propBal);
        if doAccept && vb == VB(propVal, propBal) {
          if exists p :: 
            && p in v'.network.sentMsgs
            && p.Propose?
            && p.bal >= vb.b
            && p.val != vb.v 
          {
            var p :|
              && p in v'.network.sentMsgs
              && p.Propose?
              && p.bal >= vb.b
              && p.val != vb.v;
            assert p.bal > vb.b;
            ChosenAndConflictingProposeImpliesFalse(c, v', vb, p);
            assert false;
          }
        } else {
          if exists quorum: set<Message> :: IsAcceptQuorum(c, v', quorum, vb) {
            var q :| IsAcceptQuorum(c, v', q, vb);
            assert IsAcceptQuorum(c, v, q, vb);  // trigger
            assert false;
          }
          assert !Chosen(c, v', vb);
        }
      }
    }
  }

  lemma ChosenAndConflictingProposeImpliesFalse(c: Constants, v: Variables, chosenVb: ValBal, p: Message) 
    requires MessageInv(c, v)
    requires AcceptMessagesValid(c, v)
    requires ProposeBackedByPromiseQuorum(c, v)
    requires p.Propose?
    requires p in v.network.sentMsgs
    requires p.bal > chosenVb.b
    requires p.val != chosenVb.v
    requires Chosen(c, v, chosenVb)
    ensures false
  {
    var pquorum :| PromiseQuorumSupportsVal(c, v, pquorum, p.bal, p.val); // promise quorum supporting p
    /* Proof by contradiction. There are two cases */
    if PromiseSetEmptyVBOpt(c, v, pquorum, p.bal) {
      /* Case 1: p's promise quorum has not seen vb accepted. Then there is some acc source
      *  in both the promise quorum, and the chosen Accept quorum. Hence, this acc accepted
      *  >= chosenVb.b, by AcceptMessagesValid. However, it also sent a promise >= chosenVb.b 
      * that carried no prior vbOpt value. This contradicts AcceptedImpliesLargerPromiseCarriesVb */

      // var aquorum :|

      // new invariant: accept message implies acceptor accepted >= m.bal
      // new invariant: accepted implies larger ballots promise carries some vbOpt.

      assume false;
      assert false;
    } else {
      /* Proof by contradiction. There are two cases:
      * 2. p's promise quorum has seen vb accepted. Because vb.v != p.val, it must (need promised implies proposed here)
      *    have saw some vb' such that vb.b < vb'.b < p.b. Then we keep recursing down
      *    until we get a contradiction??? I.e. by the finite ballots lemma.
      */
      assume false;
      assert false;
    }
  }


  lemma InvNextChosenValImpliesProposeOnlyVal(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    requires AcceptMessagesValid(c, v')
    requires ProposeBackedByPromiseQuorum(c, v')
    requires OneValuePerProposeBallot(c, v')
    ensures ChosenValImpliesProposeOnlyVal(c, v')
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.LeaderStep? {
      /* This case is trivial. This is because if something has already been chosen, then
      * then leader can only propose same val by ChosenValImpliesPromiseQuorumSeesBal.
      * Otherwise, the post-condition is vacuously true, as nothing new can be chosen */
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
    } else if dsStep.AcceptorStep? {
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.ReceiveStep? && msgOps.recv.value.Propose? {
        InvNextChosenValImpliesProposeOnlyValAcceptorRecvStep(c, v, v', dsStep, step);
      } else {
        forall vb | Chosen(c, v', vb)
        ensures Chosen(c, v, vb)
        {
          var quorum :| IsAcceptQuorum(c, v', quorum, vb);  // witness
          assert IsAcceptQuorum(c, v, quorum, vb);  // trigger
        }
      }
    } else {
      // Nothing new chosen
      NoNewChosenInLeaderOrLearnerSteps(c, v, v', dsStep);
    } 
  }

  // Lemma: For any Learn message, that learned value must have been chosen
  lemma LearnedImpliesChosen(c: Constants, v: Variables, learnMsg: Message)
    requires v.WF(c)
    requires MessageInv(c, v)
    requires learnMsg.Learn?
    requires learnMsg in v.network.sentMsgs
    ensures Chosen(c, v, VB(learnMsg.val, learnMsg.bal))
  {
    /* Suppose learnMsg(lnr, bal, val) in network. Then by LearnMsgsValid, lnr has a 
      a quorum of receivedAccepts for vb := VB(bal, val). By LearnerValidReceivedAccepts,
      there is a corresponding set of Accept(vb, _) messages in the network. */
    var l := v.learners[learnMsg.lnr];
    var vb := VB(learnMsg.val, learnMsg.bal);
    var quorum := QuorumFromReceivedAccepts(l.receivedAccepts[vb], vb);  // witness
    assert IsAcceptQuorum(c, v, quorum, vb);  // trigger
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
      var quorum :| IsAcceptQuorum(c, v', quorum, vb);  // witness
      assert IsAcceptQuorum(c, v, quorum, vb);  // trigger
    }
  }



  // Lemma: If at most one value can be chosen, then the Agreement property is true
  lemma AtMostOneChosenImpliesAgreement(c: Constants, v: Variables) 
    requires v.WF(c)
    requires MessageInv(c, v)
    requires AtMostOneChosenVal(c, v)
    ensures Agreement(c, v)
  {
    /* Proof by contradiction. Suppose that v violates agreement, such that there are two
      Learn messages with differnt values. Then by LearnedImpliesChosen, two different 
      values are chosen, thus violating AtMostOneChosenVal */
    if !Agreement(c, v) {
      var m1, m2 :| 
        && m1 in v.network.sentMsgs 
        && m2 in v.network.sentMsgs 
        && m1.Learn?
        && m2.Learn?
        && m1.val != m2.val;
      LearnedImpliesChosen(c, v, m1);
      LearnedImpliesChosen(c, v, m2);
      assert false;
    }
  }

  // Lemma: Invariant AtMostOneChosenVal is inductive
  lemma AtMostOneChosenValNext(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    requires ChosenValImpliesLargerAcceptMsgsHoldsVal(c, v')
    ensures AtMostOneChosenVal(c, v')
  {}

  // Lemma: Given b1 < b2, there is a finite, strictly ordered sequence 
  // [b1, b_a, b_b, ... , b_2] such that for all ballots b where b1 < b < b2, b in seq
  lemma FiniteBallots(b1: LeaderId, b2: LeaderId) returns (res: seq<LeaderId>)
    requires b1 < b2
    ensures SeqIsComplete(res, b1, b2)
  {
    if b1 == b2 - 1 {
      return [b1, b2];
    } else {
      var sub := FiniteBallots(b1, b2-1);
      return sub + [b2];
    }
  }
  

  /***************************************************************************************
  *                                        Utils                                         *
  ***************************************************************************************/
  
  lemma QuorumFromReceivedAccepts(s: set<AcceptorId>, vb: ValBal) returns (q: set<Message>)
    decreases s
    ensures |q| == |s|
    ensures forall m | m in q :: m.Accept?
    ensures forall m | m in q :: m.vb == vb
    ensures forall m | m in q :: m.acc in s
  {
    if |s| == 0 {
      return {};
    } else {
      var acc :| acc in s;
      var subq := QuorumFromReceivedAccepts(s-{acc}, vb);
      return subq + {Accept(vb, acc)};
    }
  }

  predicate IsPromiseSet(c: Constants, v: Variables, pset: set<Message>, bal: LeaderId) {
    forall m | m in pset ::
      && m.Promise?
      && m in v.network.sentMsgs
      && m.bal == bal
  }

  predicate IsPromiseQuorum(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId) {
    && |quorum| >= c.f+1
    && IsPromiseSet(c, v, quorum, bal)
  }

  predicate PromiseQuorumSupportsVal(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId, val: Value) {
    && IsPromiseQuorum(c, v, quorum, bal)
    && (
      || PromiseSetEmptyVBOpt(c, v, quorum, bal)
      || (exists hsbal :: PromiseSetHighestVBOptVal(c, v, quorum, bal, hsbal, val))
    )
  }

  predicate PromiseSetEmptyVBOpt(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId)
    requires IsPromiseSet(c, v, pset, qbal)
  {
    forall m | m in pset :: m.vbOpt == None
  }

  predicate PromiseSetHighestVBOptVal(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, hsBal: LeaderId, val: Value)
    requires IsPromiseSet(c, v, pset, qbal)
  {
    exists m ::
      && m in pset 
      && m.vbOpt.Some?
      && m.vbOpt.value.v == val
      && m.vbOpt.value.b == hsBal
      && (forall other | 
            && other in pset 
            && other.vbOpt.Some?
          ::
            other.vbOpt.value.b <= hsBal
        )
  }

  predicate IsAcceptSet(c: Constants, v: Variables, aset: set<Message>, vb: ValBal) {
    forall m | m in aset ::
      && m.Accept?
      && m in v.network.sentMsgs
      && m.vb == vb
  }

  predicate IsAcceptQuorum(c: Constants, v: Variables, aset: set<Message>, vb: ValBal) {
    && |aset| >= c.f+1
    && IsAcceptSet(c, v, aset, vb)
  }

}  // end module PaxosProof

