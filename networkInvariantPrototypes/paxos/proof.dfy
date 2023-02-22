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

  predicate MessageInv(c: Constants, v: Variables) 
  {
    && v.WF(c)
    && ValidMessageSrc(c, v)
    && LeaderValidHighestHeard(c, v)
    && AcceptorValidPromised(c, v)
    && AcceptorValidAcceptedVB(c, v)
    && LearnerValidReceivedAccepts(c, v)
    && LearnMsgsValid(c, v)
  }

  lemma InitImpliesMessageInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

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

  // Util
  // A quorum of Accept messages of the same vb
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


  predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
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


    assume AtMostOneChosenVal(c, v');
    AtMostOneChosenImpliesAgreement(c, v');
    assert Agreement(c, v');
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
}  // end module PaxosProof

