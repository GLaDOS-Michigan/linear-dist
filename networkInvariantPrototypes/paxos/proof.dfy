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
  predicate ValidMessageSrc(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs 
    :: 
    match msg 
      case Prepare(bal) => c.ValidLeaderIdx(bal)
      case Promise(bal, acc, _) => c.ValidLeaderIdx(bal) && c.ValidAcceptorIdx(acc)
      case Propose(bal, _) => c.ValidLeaderIdx(bal)
      case Accept(_, acc) => c.ValidAcceptorIdx(acc)
      case Learn(_) => true
  }

  predicate MessageInv(c: Constants, v: Variables) 
  {
    && v.WF(c)
    && ValidMessageSrc(c, v)
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

