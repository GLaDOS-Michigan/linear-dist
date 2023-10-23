using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny
{

  public class ReceiveInvariant {

    private bool opaque;
    private string functionName;    // name of the receive predicate
    private string module;          // name of the module this function belongs
    private string variableField;   // which field in distributedSystem.Hosts?
    private List<string> args;      // additional arguments to trigger

    public ReceiveInvariant(string functionName, string module, string variableField, List<string> args) {
      this.opaque = true;
      this.functionName = functionName;
      this.module = module;
      this.variableField = variableField;
      this.args = args;
    }

    public static ReceiveInvariant FromTriggerFunction(string baseName, Function receivePredicateTrigger, DatatypeDecl dsHosts) {
      // Extract module and msgType
      var module = ExtractReceiveInvariantModule(receivePredicateTrigger);
      
      // extract field name in DistributedSystem.Hosts of type seq<[module].Variables>
      string variableField = null;
      foreach (var formal in dsHosts.GetGroundingCtor().Formals) {
        if (formal.DafnyName.Contains(string.Format("{0}.Variables", module))) {
          variableField = formal.CompileName;
          break;
        }
      }
      Debug.Assert(variableField != null, "variableField should not be null");

      // extract args
      var args = new List<string>();
      int startIndex = 2; //set the desired index you want to start from
      for (int i = startIndex; i < receivePredicateTrigger.Formals.Count; i++)
      {
        args.Add(receivePredicateTrigger.Formals[i].Name);
      }
      
      Console.WriteLine(string.Format("Found recv predicate [{0}] with [{1}] args in module [{2}], in Hosts.[{3}]\n", baseName, args.Count, module, variableField));
    
      var recvInv = new ReceiveInvariant(baseName, module, variableField, args);
      return recvInv;
    }

    // Get the Module in Module.ReceivePredicate
    private static string ExtractReceiveInvariantModule(Function func) {
      return func.FullDafnyName.Substring(0, func.FullDafnyName.IndexOf('.'));
    }

    public bool isOpaque() {
      return opaque;
    }

    public string GetName() {
      return functionName;
    }

    public string GetTriggerName() {
      return string.Format("{0}Trigger", functionName);
    }

    public string GetConclusionName() {
      return string.Format("{0}Conclusion", functionName);
    }

    public string GetPredicateName() {
      return string.Format("{0}Validity", functionName);
    }

    public string GetLemmaName() {
      return string.Format("InvNext{0}Validity", functionName);
    }

    public string ToPredicate() {
      var res = "";
      if (opaque) {
        res += "ghost predicate {:opaque} " + string.Format("{0}(c: Constants, v: Variables)\n", GetPredicateName());
      } else {
        res += "ghost predicate " + string.Format("{0}(c: Constants, v: Variables)\n", GetPredicateName());
      }
      res += "  requires v.WF(c)\n" +
             "{\n" +
             string.Format("  forall idx, i, {0} |\n", string.Join(",", args.ToArray())) +
             "    && v.ValidHistoryIdx(i)\n" +
             string.Format("    && 0 <= idx < |c.{0}|\n", variableField) +
             string.Format("    && {0}.{1}(c.{2}[idx], v.History(i).{2}[idx], {3})\n", module, GetTriggerName(), variableField, string.Join(",", args.ToArray())) +
             "  ::\n" + 
             "    (exists msg ::\n" +
             "      && msg in v.network.sentMsgs\n" +
             string.Format("      && {0}.{1}(c.{2}[idx], v.History(i).{2}[idx], {3}, msg)\n", module, GetConclusionName(), variableField, string.Join(",", args.ToArray())) +
             "    )\n" +
             "}\n";
      return res;
    }

    public string ToLemma() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", GetLemmaName());
      res += "  requires v.WF(c)\n" +
             string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
             "  requires Next(c, v, v')\n" +
             string.Format("  ensures {0}(c, v')\n", GetPredicateName()) +
             "{\n" +
             "  assume false;\n" +
             "}\n";
      return res;
    }

    public override string ToString(){
      return string.Format("Receive predicate [{0}] in module [{1}], in DistributedSystem.[Hosts.{3}]", functionName, module, variableField);
    }  
  }
}