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
  (exists i, src ::
      && v.ValidHistoryIdx(i)
      && c.ValidIdx(src)
      && Host.SendMsg(c.hostConstants[src], v.History(i).hosts[src], msg)
  )
}

// For each host, if its highestHeard is >-1, then it must have gotten it from a message
// from its predecessor
ghost predicate ReceiveValidity(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall i, idx | 
    && v.ValidHistoryIdx(i)
    && c.ValidIdx(idx)
    && -1 < v.History(i).hosts[idx].highestHeard
  :: 
    (exists msg :: 
        && msg in v.network.sentMsgs 
        && Host.ReceiveMsg(c.hostConstants[idx], v.History(i).hosts[idx], msg)
    )
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && VoteMsgValidSrc(c, v)
  && TransmissionValidity(c, v)
  && ReceiveValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
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
  requires v.WF(c)
  requires ReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures ReceiveValidity(c, v')
{
  VariableNextProperties(c, v, v');
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
} // end module MessageInvariants

