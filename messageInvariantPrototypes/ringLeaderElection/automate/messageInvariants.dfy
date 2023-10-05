// Network-level "boilerplate" invariants that are application-independent

include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// All msg have a valid ringPos as src
ghost predicate VoteMsgValidSrc(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs
  :: c.ValidIdx(msg.src)
}

// Every message is sent according to a fixed function
ghost predicate TransmissionValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires VoteMsgValidSrc(c, v)
{
  forall msg | msg in v.network.sentMsgs
  :: 
  (exists i ::
      && v.ValidHistoryIdx(i)
      && Host.SendMsg(c.hostConstants[msg.src], v.History(i).hosts[msg.src], msg)
  )
}

// Every host state on receive step is updated according to a fixed function
ghost predicate ReceiveValidity(c: Constants, v: Variables) 
  requires v.WF(c)
  requires ValidHistory(c, v)
{
  reveal_ValidHistory();
  forall i, idx, msg | 
    && 1 <= i < |v.history|
    && c.ValidIdx(idx)
    && IsReceiveStepByActor(c, v, i, idx, msg)
  :: 
    && msg in v.network.sentMsgs 
    && Host.ReceiveMsg(c.hostConstants[idx], v.History(i-1).hosts[idx], v.History(i).hosts[idx], msg)
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidHistory(c, v)
  && VoteMsgValidSrc(c, v)
  && TransmissionValidity(c, v)
  && ReceiveValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidHistory(c, v);
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidHistory(c, v, v');
  InvNextTransmissionValidity(c, v, v');
  InvNextReceiveValidity(c, v, v');
}


/***************************************************************************************
*                                         Proofs                                       *
***************************************************************************************/

lemma InvNextTransmissionValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires VoteMsgValidSrc(c, v)
  requires TransmissionValidity(c, v)
  requires Next(c, v, v')
  ensures TransmissionValidity(c, v')
{
  VariableNextProperties(c, v, v');
}

lemma InvNextReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c) && v'.WF(c)
  requires ValidHistory(c, v) && ValidHistory(c, v')
  requires ReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures ReceiveValidity(c, v')
{
  VariableNextProperties(c, v, v');
}
} // end module MessageInvariants

