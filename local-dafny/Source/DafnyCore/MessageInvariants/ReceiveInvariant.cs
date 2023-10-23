using System.Collections.Generic;

namespace Microsoft.Dafny
{

  public class ReceiveInvariant {

    private string functionName;    // name of the send predicate
    private string module;          // name of the module this function belongs
    private string variableField;   // which field in distributedSystem.Hosts?
    private List<string> args;      // additional arguments to trigger

    public ReceiveInvariant(string functionName, string module, string variableField, List<string> args) {
      this.functionName = functionName;
      this.module = module;
      this.variableField = variableField;
      this.args = args;
    }

    public string GetName() {
      return functionName;
    }

    public string GetPredicateName() {
      return string.Format("{0}Validity", functionName);
    }

    public string GetLemmaName() {
      return string.Format("InvNext{0}Validity", functionName);
    }

    public string ToPredicate() {
      var res = string.Format("ghost predicate {0}(c: Constants, v: Variables)\n", GetPredicateName());
      res += "  requires v.WF(c)\n" +
             "  requires ValidMessages(c, v)\n" +
             "{\n" +
             "  true" +
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
             "  assume false" +
             "}\n";
      return res;
    }

    public override string ToString(){
      return string.Format("Receive predicate [{0}] in module [{1}], in DistributedSystem.[Hosts.{3}]", functionName, module, variableField);
    }  
  }
}