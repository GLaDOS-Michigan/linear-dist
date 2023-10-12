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
      && v.ValidHistoryIdxStrict(i)
      && Host.SendMsg(c.hostConstants[msg.src], v.History(i).hosts[msg.src], v.History(i+1).hosts[msg.src], msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidHistory(c, v)
  && VoteMsgValidSrc(c, v)
  && TransmissionValidity(c, v)
  // && ReceiveValidity(c, v)
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
  forall msg | msg in v'.network.sentMsgs
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && Host.SendMsg(c.hostConstants[msg.src], v'.History(i).hosts[msg.src], v'.History(i+1).hosts[msg.src], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.SendMsg(c.hostConstants[msg.src], v'.History(i).hosts[msg.src], v'.History(i+1).hosts[msg.src], msg);
    }
  }
}
} // end module MessageInvariants

