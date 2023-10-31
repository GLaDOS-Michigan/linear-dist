using System;

namespace Microsoft.Dafny
{
  public class MsgInvPrinter {

    private static readonly string[] includes = {"spec.dfy"};
    private static readonly string[] imports = {"Types", "UtilitiesLibrary", "MonotonicityLibrary", "DistributedSystem"};

    private static readonly string InitImpliesMonotonicityInv = 
      "lemma InitImpliesMonotonicityInv(c: Constants, v: Variables)\n" +
      "  requires Init(c, v)\n" +
      "  ensures MonotonicityInv(c, v)\n" +
      "{}\n";
    
    private static readonly string InitImpliesMessageInvHeader = 
      "lemma InitImpliesMessageInv(c: Constants, v: Variables)\n" +
      "  requires Init(c, v)\n" +
      "  ensures MessageInv(c, v)\n" +
      "{\n" +
      "  InitImpliesValidVariables(c, v);\n";
      
    private static readonly string MonotonicityInvInductive = 
       "lemma MonotonicityInvInductive(c: Constants, v: Variables, v': Variables)\n" +
        "  requires MonotonicityInv(c, v)\n" +
        "  requires Next(c, v, v')\n" +
        "  ensures MonotonicityInv(c, v')\n" +
        "{\n" +
        "  VariableNextProperties(c, v, v');\n" +
        "}\n";

    private static readonly string MessageInvInductiveHeader = 
      "lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)\n" +
      "  requires MessageInv(c, v)\n" +
      "  requires Next(c, v, v')\n" +
      "  ensures MessageInv(c, v')\n";

    private static readonly string VariableNextProperties =
    "lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)\n" + 
    "  requires v.WF(c)\n" +
    "  requires Next(c, v, v')\n" +
    "  ensures 1 < |v'.history|\n" +
    "  ensures |v.history| == |v'.history| - 1\n" +
    "  ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)\n" +
    "  ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)\n" +
    "{\n" +
    "  assert 0 < |v.history|;\n" +
    "  assert 1 < |v'.history|;\n" +
    "}\n";

    public static string PrintMonotonicityInvariants(MonotonicityInvariantsFile file) {
      string res = "";

      // Module preamble 
      foreach (string i in includes) {
        res += String.Format("include \"{0}\"\n", i);
      }
      res += "\n";
      res += "module MonotonicityInvariants {\n"; // begin MonotinicityInvariants module
      foreach (string i in imports) {
        res += String.Format("import opened {0}\n", i);
      }
      res += "\n";

      foreach (var monoInv in file.GetInvariants()) {
        res += monoInv.ToPredicate() + "\n";
      }

      // Main monotonicity invariant
      res += "ghost predicate MonotonicityInv(c: Constants, v: Variables)\n" +
             "{\n" +
             "  && v.WF(c)\n";
      foreach (var inv in file.GetInvariants()) {
        res += String.Format("  && {0}(c, v)\n", inv.GetPredicateName());
      }
      res += "}\n\n";

      // Proof obligations
      res += "// Base obligation\n";
      res += InitImpliesMonotonicityInv;
      
      res += "\n";
      res += "// Inductive obligation\n";

      res += MonotonicityInvInductive;
      // Footer
      res += "} // end module MonotonicityInvariants";
      return res;
    }
    

    public static string PrintMessageInvariants(MessageInvariantsFile file) {
      string res = "";

      // Module preamble 
      foreach (string i in includes) {
        res += String.Format("include \"{0}\"\n", i);
      }
      res += "\n";
      res += "module MessageInvariants {\n"; // begin MessageInvariants module
      foreach (string i in imports) {
        res += String.Format("import opened {0}\n", i);
      }
      res += "\n";

      // List Send Invariants
      foreach (var sendInv in file.GetSendInvariants()) {
        res += sendInv.ToPredicate() + "\n";
      }

      // List Receive Invariants
      foreach (var recvInv in file.GetReceiveInvariants()) {
        res += recvInv.ToPredicate() + "\n";
      }

      // Main message invariant
      res += "ghost predicate MessageInv(c: Constants, v: Variables)\n" +
             "{\n" +
             "  && v.WF(c)\n" +
             "  && ValidVariables(c, v)\n";
      foreach (var inv in file.GetSendInvariants()) {
        res += String.Format("  && {0}(c, v)\n", inv.GetPredicateName());
      }
      foreach (var inv in file.GetReceiveInvariants()) {
        res += String.Format("  && {0}(c, v)\n", inv.GetPredicateName());
      }
      res += "}\n\n";

      // Proof obligations
      res += "// Base obligation\n";
      res += InitImpliesMessageInvHeader;
      foreach (var ri in file.GetReceiveInvariants()) {
        // reveal opaqued receive invariants
        if (ri.isOpaque()) {
          res += string.Format("  reveal_{0}();\n", ri.GetPredicateName());
        }
      }
      res += "}\n";
      
      res += "\n";
      res += "// Inductive obligation\n";

      res += MessageInvInductiveHeader + 
            "{\n" + 
            "  InvNextValidVariables(c, v, v');\n";
      foreach (var inv in file.GetSendInvariants()) {
        res += String.Format("  {0}(c, v, v');\n", inv.GetLemmaName());
      }
      foreach (var inv in file.GetReceiveInvariants()) {
        res += String.Format("  {0}(c, v, v');\n", inv.GetLemmaName());
      }
      res += "}\n";

      res += "\n" +
@"/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/";
      res += "\n\n\n";

      // InvNextProofs
      foreach (var pred in file.GetSendInvariants()) {
        res += pred.ToLemma();
        res += "\n";
      }
      foreach (var pred in file.GetReceiveInvariants()) {
        res += pred.ToLemma();
        res += "\n";
      }

      // Footer
      // res += VariableNextProperties + "\n";
      res += "} // end module MessageInvariants";
      return res;
    } // end function Print

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