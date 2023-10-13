include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// Every message is sent according to a fixed function
ghost predicate SendMsgValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs
  :: 
  (exists i ::
      && v.ValidHistoryIdxStrict(i)
      && Host.SendMsg(c.hosts[msg.src], v.History(i).hosts[msg.src], v.History(i+1).hosts[msg.src], msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && SendMsgValidity(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidVariables(c, v, v');
  InvNextSendMsgValidity(c, v, v');
}


/***************************************************************************************
*                                         Proofs                                       *
***************************************************************************************/

lemma InvNextSendMsgValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendMsgValidity(c, v)
  requires Next(c, v, v')
  ensures SendMsgValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs
  ensures
  (exists i ::
      && v'.ValidHistoryIdxStrict(i)
      && Host.SendMsg(c.hosts[msg.src], v'.History(i).hosts[msg.src], v'.History(i+1).hosts[msg.src], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.SendMsg(c.hosts[msg.src], v'.History(i).hosts[msg.src], v'.History(i+1).hosts[msg.src], msg);
    }
  }
}
} // end module MessageInvariants

