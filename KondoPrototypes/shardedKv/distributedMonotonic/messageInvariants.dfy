include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate SendReconfValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Reconf?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && Host.SendReconf(c.hosts[msg.Src()], v.History(i).hosts[msg.Src()], v.History(i+1).hosts[msg.Src()], msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && SendReconfValidity(c, v)
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidVariables(c, v, v');
  InvNextSendReconfValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/


lemma InvNextSendReconfValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendReconfValidity(c, v)
  requires Next(c, v, v')
  ensures SendReconfValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Reconf?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && Host.SendReconf(c.hosts[msg.Src()], v'.History(i).hosts[msg.Src()], v'.History(i+1).hosts[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.SendReconf(c.hosts[msg.Src()], v'.History(i).hosts[msg.Src()], v'.History(i+1).hosts[msg.Src()], msg);
    }
  }
}

} // end module MessageInvariants