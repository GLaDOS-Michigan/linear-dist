/// This file is auto-generated from /Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/messageInvariantPrototypes/lockServer/distributedMonotonic/distributedSystem.dfy
include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

// All msg have a valid source
ghost predicate ValidMessages(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs
  ::
  if msg.Release? then 0 <= msg.Src() < |c.clients|
  else if msg.Grant? then 0 <= msg.Src() < |c.server|
  else true
}

ghost predicate SendReleaseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Release?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && ClientHost.SendRelease(c.clients[msg.Src()], v.History(i).clients[msg.Src()], v.History(i+1).clients[msg.Src()], msg)
  )
}

ghost predicate SendGrantValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Grant?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && ServerHost.SendGrant(c.server[msg.Src()], v.History(i).server[msg.Src()], v.History(i+1).server[msg.Src()], msg)
  )
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && ValidMessages(c, v)
  && SendReleaseValidity(c, v)
  && SendGrantValidity(c, v)
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
  InvNextSendReleaseValidity(c, v, v');
  InvNextSendGrantValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/

lemma InvNextSendReleaseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendReleaseValidity(c, v)
  requires Next(c, v, v')
  ensures SendReleaseValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Release?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && ClientHost.SendRelease(c.clients[msg.Src()], v'.History(i).clients[msg.Src()], v'.History(i+1).clients[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ClientHost.SendRelease(c.clients[msg.Src()], v'.History(i).clients[msg.Src()], v'.History(i+1).clients[msg.Src()], msg);
    }
  }
}

lemma InvNextSendGrantValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendGrantValidity(c, v)
  requires Next(c, v, v')
  ensures SendGrantValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Grant?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && ServerHost.SendGrant(c.server[msg.Src()], v'.History(i).server[msg.Src()], v'.History(i+1).server[msg.Src()], msg)
  ) {
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ServerHost.SendGrant(c.server[msg.Src()], v'.History(i).server[msg.Src()], v'.History(i+1).server[msg.Src()], msg);
    }
  }
}

} // end module MessageInvariants
