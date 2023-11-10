using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using Newtonsoft.Json;

namespace Microsoft.Dafny
{
  public static class MsgInvPrinter {

    private static readonly string[] includes = {"spec.dfy"};
    private static readonly string[] imports = {"Types", "UtilitiesLibrary", "MonotonicityLibrary", "DistributedSystem"};
    private static readonly string templatePath = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Source/DafnyCore/MessageInvariants/templates.json";

    private static readonly Dictionary<string, string[]> Template = JsonConvert.DeserializeObject<Dictionary<string, string[]>>(File.ReadAllText(templatePath));

    private static string GetFromTemplate(string key, int indent) {
    var lines = Template[key];
    var res = new StringBuilder();
    foreach (var l in lines) {
      res.AppendLine(new string(' ', indent) + l);
    }
    return res.ToString();
  }

    public static string PrintMonotonicityInvariants(MonotonicityInvariantsFile file) {
      var res = new StringBuilder();

      // Module preamble 
      foreach (string i in includes) {
        res.AppendLine(String.Format("include \"{0}\"", i));
      }
      res.AppendLine();
      res.AppendLine("module MonotonicityInvariants {"); // begin MonotinicityInvariants module
      foreach (string i in imports) {
        res.AppendLine(String.Format("import opened {0}", i));
      }
      res.AppendLine();

      foreach (var monoInv in file.GetInvariants()) {
        res.AppendLine(monoInv.ToPredicate());
      }

      // Main monotonicity invariant
      res.AppendLine("ghost predicate MonotonicityInv(c: Constants, v: Variables)");
      res.AppendLine("{");
      res.AppendLine("  && v.WF(c)");
      foreach (var inv in file.GetInvariants()) {
        res.AppendLine(String.Format("  && {0}(c, v)", inv.GetPredicateName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      // Proof obligations
      res.AppendLine("// Base obligation");
      res.AppendLine(GetFromTemplate("InitImpliesMonotonicityInv", 0));
      
      res.AppendLine("// Inductive obligation");
      res.AppendLine(GetFromTemplate("MonotonicityInvInductive", 0));
      // Footer
      res.AppendLine("} // end module MonotonicityInvariants");
      return res.ToString();
    } // end function PrintMonotonicityInvariants
    

    public static string PrintMessageInvariants(MessageInvariantsFile file) {
      var res = new StringBuilder();

      // Module preamble 
      foreach (string i in includes) {
        res.AppendLine(String.Format("include \"{0}\"", i));
      }
      res.AppendLine();
      res.AppendLine("module MessageInvariants {"); // begin MessageInvariants module
      foreach (string i in imports) {
        res.AppendLine(String.Format("import opened {0}", i));
      }
      res.AppendLine();

      // Declar ValidMessges
      res.AppendLine("// All msg have a valid source");
      res.AppendLine("ghost predicate ValidMessages(c: Constants, v: Variables)");
      res.AppendLine("  requires v.WF(c)");
      res.AppendLine("{");
      res.AppendLine("  forall msg | msg in v.network.sentMsgs");
      res.AppendLine("  ::");
      res.Append("  ");
      foreach (var si in file.GetSendInvariants()) {
        res.Append("if ");
        res.Append($"msg.{si.GetMessageType()}? ");
        res.AppendLine($"then 0 <= msg.Src() < |c.{si.GetVariableField()}|");
        res.Append("  else ");
      } 
      res.AppendLine("true");
      res.AppendLine("}");
      res.AppendLine();

      // List Send Invariants
      foreach (var sendInv in file.GetSendInvariants()) {
        res.AppendLine(sendInv.ToPredicate());
      }

      // List Receive Invariants
      foreach (var recvInv in file.GetReceiveInvariants()) {
        res.AppendLine(recvInv.ToPredicate());
      }

      // Main message invariant
      res.AppendLine("ghost predicate MessageInv(c: Constants, v: Variables)");
      res.AppendLine("{");
      res.AppendLine("  && v.WF(c)");
      res.AppendLine("  && ValidVariables(c, v)");
      res.AppendLine("  && ValidMessages(c, v)");
      foreach (var inv in file.GetSendInvariants()) {
        res.AppendLine(String.Format("  && {0}(c, v)", inv.GetPredicateName()));
      }
      foreach (var inv in file.GetReceiveInvariants()) {
        res.AppendLine(String.Format("  && {0}(c, v)", inv.GetPredicateName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      // Proof obligations
      res.AppendLine("// Base obligation");
      res.Append(GetFromTemplate("InitImpliesMessageInvHeader", 0));
      foreach (var ri in file.GetReceiveInvariants().Where(x => x.isOpaque())) {
        // reveal opaqued receive invariants
        res.AppendLine(string.Format("  reveal_{0}();", ri.GetPredicateName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      res.AppendLine("// Inductive obligation");
      res.AppendLine(GetFromTemplate("MessageInvInductiveHeader", 0)); 
      res.AppendLine("{");
      res.AppendLine("  InvNextValidVariables(c, v, v');");
      foreach (var inv in file.GetSendInvariants()) {
        res.AppendLine(String.Format("  {0}(c, v, v');", inv.GetLemmaName()));
      }
      foreach (var inv in file.GetReceiveInvariants()) {
        res.AppendLine(String.Format("  {0}(c, v, v');", inv.GetLemmaName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      // Begin proofs section
      res.AppendLine(GetFromTemplate("AuxProofsSeparator", 0));

      // InvNextProofs
      foreach (var pred in file.GetSendInvariants()) {
        res.AppendLine(pred.ToLemma());
      }
      foreach (var pred in file.GetReceiveInvariants()) {
        res.AppendLine(pred.ToLemma());
      }

      // Footer
      res.AppendLine("} // end module MessageInvariants");
      return res.ToString();
    } // end function PrintMessageInvariants

    public static string PrintOwnershipInvariants(OwnershipInvariantsFile file) {
      return @"include ""spec.dfy""

module OwnershipInvariants {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

/***************************************************************************************
*                                   Definitions                                        *
***************************************************************************************/

  ghost predicate UniqueKeyInFlight(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    exists msg :: KeyInFlightByMessage(c, v, msg, k)
  }

  ghost predicate KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: UniqueKey) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && (0 <= msg.Dst() < |c.hosts| ==>
      Host.UniqueKeyInFlightForHost(c.hosts[msg.Dst()], v.Last().hosts[msg.Dst()], k, msg)
    )
  }

  ghost predicate NoHostOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    forall idx | c.ValidIdx(idx) :: !Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k)
  }

/***************************************************************************************
*                                    Invariants                                        *
***************************************************************************************/


  ghost predicate AtMostOneInFlightMessagePerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k) 
    :: m1 == m2
  }

  ghost predicate HostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoHostOwnsKey(c, v, k)
    ::
    !UniqueKeyInFlight(c, v, k)
  }

  ghost predicate AtMostOwnerPerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && c.ValidIdx(h1) 
      && c.ValidIdx(h2)
      && Host.HostOwnsUniqueKey(c.hosts[h1], v.Last().hosts[h1], k) 
      && Host.HostOwnsUniqueKey(c.hosts[h2], v.Last().hosts[h2], k) 
    ::
     h1 == h2
  }
  
  
  ghost predicate OwnershipInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && AtMostOneInFlightMessagePerKey(c, v)
    && AtMostOwnerPerKey(c, v)
    && HostOwnsKeyImpliesNotInFlight(c, v)
  }

  // Base obligation
  lemma InitImpliesOwnershipInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures OwnershipInv(c, v)
  {}

  // Inductive obligation
  lemma OwnershipInvInductive(c: Constants, v: Variables, v': Variables)
    requires OwnershipInv(c, v)
    requires Next(c, v, v')
    ensures OwnershipInv(c, v')
  {
    InvNextAtMostOneInFlightMessagePerKey(c, v, v');
    InvNextHostOwnsKeyImpliesNotInFlight(c, v, v');
    InvNextAtMostOwnerPerKey(c, v, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


lemma InvNextAtMostOneInFlightMessagePerKey(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneInFlightMessagePerKey(c, v')
{
  forall k, m1, m2 | KeyInFlightByMessage(c, v', m1, k) && KeyInFlightByMessage(c, v', m2, k) 
  ensures m1 == m2
  {
    if m1 != m2 {
      if KeyInFlightByMessage(c, v, m1, k) {
        InvNextAtMostOneInFlightHelper(c, v, v', m1, m2, k);
      } else {
        InvNextAtMostOneInFlightHelper(c, v, v', m2, m1, k);
      }
    }
  }
}

lemma InvNextAtMostOneInFlightHelper(c: Constants, v: Variables, v': Variables, m1: Message, m2: Message, k: UniqueKey)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  // input constraints
  requires m1 != m2
  requires KeyInFlightByMessage(c, v, m1, k)
  requires !KeyInFlightByMessage(c, v, m2, k)
  // postcondition
  ensures !KeyInFlightByMessage(c, v', m2, k)
{
  assert UniqueKeyInFlight(c, v, k);
}

lemma InvNextHostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsKeyImpliesNotInFlight(c, v')
{
  forall k | !NoHostOwnsKey(c, v', k)
  ensures !UniqueKeyInFlight(c, v', k)
  {
    forall msg | msg in v'.network.sentMsgs
    ensures !KeyInFlightByMessage(c, v', msg, k) {
      var idx :| c.ValidIdx(idx) && Host.HostOwnsUniqueKey(c.hosts[idx], v'.Last().hosts[idx], k);
      if Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k){
        // triggers
        assert !UniqueKeyInFlight(c, v, k);
        assert !KeyInFlightByMessage(c, v, msg, k);

      } else {
        if msg in v.network.sentMsgs && KeyInFlightByMessage(c, v, msg, k){
          var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
          // triggers
          assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
          assert UniqueKeyInFlight(c, v, k);
        }
        assert !KeyInFlightByMessage(c, v', msg, k);
      }
    }
  }
}

lemma InvNextAtMostOwnerPerKey(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOwnerPerKey(c, v')
{
  forall h1, h2, k | 
      && c.ValidIdx(h1) 
      && c.ValidIdx(h2)
      && Host.HostOwnsUniqueKey(c.hosts[h1], v'.Last().hosts[h1], k) 
      && Host.HostOwnsUniqueKey(c.hosts[h2], v'.Last().hosts[h2], k) 
  ensures
     h1 == h2
  {
    if h1 != h2 {
      if Host.HostOwnsUniqueKey(c.hosts[h1], v.Last().hosts[h1], k) {
        AtMostOneHostOwnsKey(c, v, v', k, h1, h2);
      } else if Host.HostOwnsUniqueKey(c.hosts[h2], v.Last().hosts[h2], k) {
        AtMostOneHostOwnsKey(c, v, v', k, h2, h1);
      }
    }
  }
}

lemma AtMostOneHostOwnsKey(c: Constants, v: Variables, v': Variables, k: UniqueKey, idx: HostId, other: HostId)
  requires v.WF(c) && v'.WF(c)
  requires OwnershipInv(c, v)
  requires c.ValidIdx(idx)
  requires c.ValidIdx(other)
  requires idx != other
  requires Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k) 
  requires !Host.HostOwnsUniqueKey(c.hosts[other], v.Last().hosts[other], k) 
  requires Next(c, v, v')
  ensures !Host.HostOwnsUniqueKey(c.hosts[other], v'.Last().hosts[other], k) 
{
  var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
  var actor, msgOps := dsStep.actor, dsStep.msgOps;
  if actor == other {
    var cs, s, s' := c.hosts[other], v.Last().hosts[other], v'.Last().hosts[other];
    var step :| Host.NextStep(cs, s, s', step, msgOps);
    if step.ReceiveStep? && Host.HostOwnsUniqueKey(c.hosts[other], v'.Last().hosts[other], k) {
      // triggers
      assert KeyInFlightByMessage(c, v, msgOps.recv.value, k);  
      assert UniqueKeyInFlight(c, v, k);
      assert false;
    }    
  }
}
} // end module OwnershipInvariants";
    }
  } // end class MessageInvariantsFile
}