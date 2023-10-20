using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{

  public class MessageInvariantsFileBwoken {


    public static readonly string InitImpliesMessageInv = 
      "lemma InitImpliesMessageInv(c: Constants, v: Variables)\n" +
      "  requires Init(c, v)\n" +
      "  ensures MessageInv(c, v)\n" +
      "{}\n";
    public static readonly string MessageInvInductiveHeader = 
       "lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)\n" +
        "  requires MessageInv(c, v)\n" +
        "  requires Next(c, v, v')\n" +
        "  ensures MessageInv(c, v')\n";

    public static readonly string VariableNextProperties =
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

    public static readonly string[] includes = {"spec.dfy"};
    public static readonly string[] imports = {"Types", "UtilitiesLibrary", "DistributedSystem", "Obligations"};

    // List of invariants
    public List<MsgInvPredicate> invariants;

    // Constructor
    public MessageInvariantsFileBwoken()
    {
      this.invariants = new List<MsgInvPredicate> {
        new MsgInvPredicate("TestPredicate1"),
        new MsgInvPredicate("TestPredicate2")};
    }

    // Generate Message Invariant dafny file contents
    override public string ToString()
    {
      var res = "";

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

      // List invariants
      foreach (var pred in this.invariants) {
        res += pred.ToString();
        res += "\n";
      }

      // Main message invariant
      res += "ghost predicate MessageInv(c: Constants, v: Variables)\n" +
             "{\n" +
             "  && v.WF(c)\n";
      foreach (var inv in this.invariants) {
        res += String.Format("  && {0}(c, v)\n", inv.Name());
      }
      res += "}\n\n";

      // Proof obligations
      res += "// Base obligation\n";
      res += InitImpliesMessageInv + "\n";
      res += "// Inductive obligation\n";

      res += MessageInvInductiveHeader + 
            "{\n";
      foreach (var inv in this.invariants) {
        res += String.Format("  {0}(c, v, v');\n", inv.LemmaName());
      }
      res += "}\n";

      res += 
@"/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/";
      res += "\n\n";

      // InvNextProofs
      foreach (var pred in this.invariants) {
        res += pred.ToLemma();
        res += "\n";
      }

      // Footer
      res += VariableNextProperties + "\n";
      res += "} // end module MessageInvariants\n"; // close MessageInvariants module
      return res;
    }  // end function ToString
  } // end class MessageInvariantsFile


  public class MsgInvPredicate {
    private string name;

    public MsgInvPredicate(string name) {
      this.name = name;
    }

    public string Name() {
      return this.name;
    } 

    public string LemmaName() {
      return String.Format("InvNext{0}", this.name);
    }

    // Generates the InvNext lemma for this predicate
    public string ToLemma() {
      var res = String.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", this.LemmaName());
      res += 
            "  requires MessageInv(c, v)\n" +
            "  requires Next(c, v, v')\n" +
            String.Format("  ensures {0}(c, v')\n", this.name) +
            "{\n" +
            "  VariableNextProperties(c, v, v');\n" +
            "}\n";
      return res;
    }

    // Generates this predicate declaration in dafny
    override public string ToString() {
      var res = String.Format("ghost predicate {0}(c: Constants, v: Variables)\n", this.name);
      res += "  requires v.WF(c)\n" +
             "{\n" +
             "  && true\n" +
             "}\n";
      return res;
    }
  }
}