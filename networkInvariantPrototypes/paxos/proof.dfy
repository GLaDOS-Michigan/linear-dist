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
      case Learn(_) => true
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

  predicate MessageInv(c: Constants, v: Variables) 
  {
    && v.WF(c)
    && ValidMessageSrc(c, v)
    && LeaderValidHighestHeard(c, v)
    && AcceptorValidPromised(c, v)
    && AcceptorValidAcceptedVB(c, v)
  }

  lemma InitImpliesMessageInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

  lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
    requires MessageInv(c, v)
    requires Next(c, v, v')
    ensures MessageInv(c, v')
  {
    // assert false;
  }


  /***************************************************************************************
  *                                Application Invariants                                *
  ***************************************************************************************/

  predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    true
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
    assume false;
  }
}  // end module PaxosProof

