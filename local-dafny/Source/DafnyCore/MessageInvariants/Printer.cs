using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
  public class MsgInvPrinter {

    private static readonly string[] includes = {"spec.dfy"};
    private static readonly string[] imports = {"Types", "UtilitiesLibrary", "DistributedSystem", "Obligations"};

    private static readonly string InitImpliesMessageInvHeader = 
      "lemma InitImpliesMessageInv(c: Constants, v: Variables)\n" +
      "  requires Init(c, v)\n" +
      "  ensures MessageInv(c, v)\n" +
      "{\n" +
      "  InitImpliesValidVariables(c, v);\n";
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

    public static string Print(MessageInvariantsFile file) {
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
  } // end class MessageInvariantsFile
}