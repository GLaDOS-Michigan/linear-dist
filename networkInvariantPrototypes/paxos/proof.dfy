include "spec.dfy"

module PaxosProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations
  
  /***************************************************************************************
  *                                  Message Invariants                                  *
  ***************************************************************************************/

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

  // certified self-inductive
  // Leader updates its highestHeard and value based on a Promise message carrying that
  // ballot and value
  predicate LeaderValidHighestHeard(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx, b| c.ValidLeaderIdx(idx) && v.leaders[idx].highestHeardBallot == Some(b)
    :: (exists prom: Message ::
          && prom.Promise? && prom in v.network.sentMsgs 
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
          && prom.Promise? && prom in v.network.sentMsgs 
          && prom.bal == idx
      )
  } 

  // certified self-inductive
  // Acceptor updates its promised ballot based on a Prepare/Propose message carrying 
  // that ballot
  predicate AcceptorValidPromised(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall idx, b | c.ValidAcceptorIdx(idx) && v.acceptors[idx].promised == Some(b)
    :: (exists m: Message ::
          && m in v.network.sentMsgs 
          && (m.Promise? || m.Propose?)
          && m.bal == b
      )
  }

  // certified self-inductive
  // Acceptor updates its acceptedVB based on a Propose message carrying that ballot 
  // and value
  predicate AcceptorValidAcceptedVB(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall idx, val, bal | 
      && c.ValidAcceptorIdx(idx) 
      && v.acceptors[idx].acceptedVB == Some(VB(val, bal))
    :: 
      Propose(bal, val) in v.network.sentMsgs
  }
  
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

  // certified self-inductive, modulo ValidMessageSrc(c, v)
  // For every Learn(lnr, val) message in the network, the learner must have a quorum of
  // accepts for that val, at some common ballot
  predicate LearnMsgsValid(c: Constants, v: Variables)
    requires v.WF(c)
    requires ValidMessageSrc(c, v)
  {
    forall lnr:LearnerId, bal, val | 
      Learn(lnr, bal, val) in v.network.sentMsgs
    :: 
      && var vb := VB(val, bal);
      && vb in v.learners[lnr].receivedAccepts
      && |v.learners[lnr].receivedAccepts[vb]| >= c.f+1
  }

  // Message bundle
  predicate MessageInv(c: Constants, v: Variables) 
  {
    && v.WF(c)
    && ValidMessageSrc(c, v)
    && LeaderValidHighestHeard(c, v)
    && LeaderValidReceivedPromises(c, v)
    && AcceptorValidPromised(c, v)
    && AcceptorValidAcceptedVB(c, v)
    && LearnerValidReceivedAccepts(c, v)
    && LearnMsgsValid(c, v)
  }

  lemma InitImpliesMessageInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
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

  lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
    requires MessageInv(c, v)
    requires Next(c, v, v')
    ensures MessageInv(c, v')
  {}


  /***************************************************************************************
  *                                Application Invariants                                *
  ***************************************************************************************/

  /*
  1. Learn implies chosen.
  2. chosen implies that is the only thing that can be chosen in all ballots.
  */

  // Inv: An acceptor's promised ballot is at least as large as its accepted ballot, if any.
  // predicate AcceptorPromisedLargerThanAccepted(c: Constants, v: Variables) 
  //   requires v.WF(c)
  // {
  //   forall acc | 
  //     && c.ValidAcceptorIdx(acc)
  //     && v.acceptors[acc].acceptedVB.Some?
  //   ::
  //     && v.acceptors[acc].promised.Some?
  //     && v.acceptors[acc].acceptedVB.value.b <= v.acceptors[acc].promised.value
  // }


  // Util: A quorum of Accept messages of the same vb
  // Tony: Using monotonic transformations, I can push this to an acceptor host property,
  // rather than a network property.
  predicate Chosen(c: Constants, v: Variables, vb: ValBal) {
    exists quorum: set<Message> :: 
    && |quorum| >= c.f+1
    && (forall m | m in quorum ::
          && m.Accept?
          && m in v.network.sentMsgs
          && m.vb == vb
    )
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
  {
    // && AcceptorPromisedLargerThanAccepted(c, v)
    && OneValuePerProposeBallot(c, v)
    && HighestHeardBackedByReceivedPromises(c, v)
    && ProposeBackedByPromiseQuorum(c, v)
    && ChosenValImpliesProposeOnlyVal(c, v)
    && ChosenValImpliesPromiseQuorumSeesBal(c, v)
    && ChosenValImpliesLeaderOnlyHearsVal(c, v)
    && ChosenValImpliesLargerAcceptMsgsHoldsVal(c, v)
    // && ChosenValImpliesLargerAcceptorsHoldsVal(c, v)
    // && ChosenValImpliesPromiseVBOnlyVal(c, v)
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
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    MessageInvInductive(c, v, v');

    // assume AcceptorPromisedLargerThanAccepted(c, v');
    assume OneValuePerProposeBallot(c, v');
    InvNextHighestHeardBackedByReceivedPromises(c, v, v');
    InvNextProposeBackedByPromiseQuorum(c, v, v');


    InvNextChosenValImpliesProposeOnlyVal(c, v, v');
    assume ChosenValImpliesPromiseQuorumSeesBal(c, v');
    assume ChosenValImpliesLeaderOnlyHearsVal(c, v');
    assume ChosenValImpliesLargerAcceptMsgsHoldsVal(c, v');
    // assume ChosenValImpliesLargerAcceptorsHoldsVal(c, v');
    // assume ChosenValImpliesPromiseVBOnlyVal(c, v');
    AtMostOneChosenValNext(c, v, v');
    AtMostOneChosenImpliesAgreement(c, v');
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
    ensures ChosenValImpliesProposeOnlyVal(c, v')
  {
    var ac, a, a' := c.acceptorConstants[dsStep.actor], v.acceptors[dsStep.actor], v'.acceptors[dsStep.actor];
    var propVal, propBal := dsStep.msgOps.recv.value.val, dsStep.msgOps.recv.value.bal;
    var doAccept := a.promised.None? || (a.promised.Some? && a.promised.value <= propBal);
    if doAccept {
      /* This is a point where something can suddenly be chosen.
      * Proof by contradiction. Suppose vb is newly chosen in this step, and there 
      * is a Propose message p in the pre state such that p.bal 
      * >= vb.b and p.val != vb.v. 
      * There are two cases:
      * 1. p's promise quorum has seen vb accepted. Because vb.v != p.val, it must (need promised implies proposed here)
      * have saw some vb' such that vb.b < vb'.b < p.b. Then we keep recursing down
      * until we get a contradiction??? I.e. by the finite ballots lemma.
      * 2. p's promise quorum has not seen vb accepted. Then the current acceptor
      *    must have aready promised b', but accepted v in this step. Contradiction.
      */
      var vb := VB(propVal, propBal);
      if Chosen(c, v', vb) && !Chosen(c, v, vb) {
        if !ChosenValImpliesProposeOnlyVal(c, v') {
          var p :|
            && p in v'.network.sentMsgs
            && p.Propose?
            && p.bal >= vb.b
            && p.val != vb.v;
          assert p in v.network.sentMsgs;
          assert p.bal > vb.b;



          assume false;
          


          assert false;
        }
        assert ChosenValImpliesProposeOnlyVal(c, v');
      }
    }
  }


  lemma InvNextChosenValImpliesProposeOnlyVal(c: Constants, v: Variables, v': Variables) 
    requires Inv(c, v)
    requires Next(c, v, v')
    requires MessageInv(c, v')
    ensures ChosenValImpliesProposeOnlyVal(c, v')
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.LeaderStep? {
      /* This case is trivial. This is because if something has already been chosen, then
      * then leader can only propose same val by ChosenValImpliesPromiseQuorumSeesBal.
      * Otherwise, the post-condition is vacuously true */
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor];
      var step :| LeaderHost.NextStep(lc, l, l', step, msgOps);
    } else if dsStep.AcceptorStep? {
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var ac, a, a' := c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor];
      var step :| AcceptorHost.NextStep(ac, a, a', step, msgOps);
      if step.ReceiveStep? && msgOps.recv.value.Propose? {
        InvNextChosenValImpliesProposeOnlyValAcceptorRecvStep(c, v, v', dsStep, step);
      }
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
    var accQuorum := QuorumFromReceivedAccepts(l.receivedAccepts[vb], vb);  // witness
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
}  // end module PaxosProof

