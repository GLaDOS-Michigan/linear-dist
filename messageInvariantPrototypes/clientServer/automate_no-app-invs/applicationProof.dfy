include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations

ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  true
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ApplicationInv(c, v)
  && Safety(c, v)
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
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
  VariableNextProperties(c, v, v');
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  SafetyProof(c, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma SafetyProof(c: Constants, v: Variables) 
  requires v.WF(c)
  requires MessageInv(c, v)
  requires MonotonicityInv(c, v)
  requires ApplicationInv(c, v)
  ensures Safety(c, v)
{
  forall cidx:nat | c.ValidClientIdx(cidx)
  ensures SafetySingleClient(v.Last().clients[cidx])
  {
    reveal_ReceiveRequestValidity();
    reveal_ReceiveResponseValidity();
    if !SafetySingleClient(v.Last().clients[cidx]) {
      var client := v.Last().clients[cidx];
      var rogue_req :| rogue_req in client.responses && rogue_req !in client.requests.s;
      assert ClientHost.ReceiveResponseTrigger(c.clients[cidx], v.Last().clients[cidx], rogue_req);  // trigger
      var j, resp_msg :|  // witness
        && j < |v.history|-1
        && v.ValidHistoryIdxStrict(j)
        && resp_msg in v.network.sentMsgs
        && !ClientHost.ReceiveResponseTrigger(c.clients[cidx], v.History(j).clients[cidx], rogue_req)
        && ClientHost.ReceiveResponseTrigger(c.clients[cidx], v.History(j+1).clients[cidx], rogue_req)
        && ClientHost.ReceiveResponse(c.clients[cidx], v.History(j).clients[cidx], v.History(j+1).clients[cidx], resp_msg);
      var k :|  // witness
        && v.ValidHistoryIdxStrict(k)
        && ServerHost.SendResponseMsg(c.servers[resp_msg.Src()], v.History(k).servers[resp_msg.Src()], v.History(k+1).servers[resp_msg.Src()], resp_msg);
      assert ServerHost.ReceiveRequestTrigger(c.GetServer(), v.History(k).GetServer(c), resp_msg.r);  // trigger
      assert false;
    }
  }
}

}  // end module ClientServerProof

