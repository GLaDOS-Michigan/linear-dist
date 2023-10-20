using System;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny
{
public class MessageInvariantsDriver {

  public Program program;
  public MessageInvariantsFile msgInvFile;

  // Constructor
  public MessageInvariantsDriver(Program program)
  {
    this.program = program;
    msgInvFile = new MessageInvariantsFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Deriving message invariants for file {0}\n", program.FullName));

    // Find distributedSystem.Hosts
    DatatypeDecl dsHosts = null;
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllTypesWithMembers(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.FullDafnyName.Equals("DistributedSystem.Hosts")) {
          Console.WriteLine(topLevelDecl.FullDafnyName);
          dsHosts = (DatatypeDecl) topLevelDecl;
          break;
        }
      }
    }
    Debug.Assert(dsHosts != null, "dsHosts should not be null");

    // Find Send invariants
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.Name.StartsWith("Send")) {  // identifying marker for Send Predicate
          // Extract module and msgType
          var module = ExtractSendInvariantModule(topLevelDecl);
          var msgType = ExtractSendInvariantMsgType(topLevelDecl);
          
          // extract field name in DistributedSystem.Hosts of type seq<[module].Variables>
          string variableField = null;
          foreach (var formal in dsHosts.GetGroundingCtor().Formals) {
            if (formal.DafnyName.Contains(string.Format("{0}.Variables", module))) {
              variableField = formal.CompileName;
              break;
            }
          }
          Debug.Assert(variableField != null, "variableField should not be null");

          Console.WriteLine(string.Format("Found send predicate [{0}] in module [{1}] for msg type [{2}], in DistributedSystem.[Hosts.{3}]\n", topLevelDecl.Name, module, msgType, variableField));
        }
      }
    }
  }

  // Message invariant function is of format "Send<MsgType>"
  private string ExtractSendInvariantMsgType(Function func) {
    return func.Name.Substring(4);
  }

  private string ExtractSendInvariantModule(Function func) {
    return func.FullDafnyName.Substring(0, func.FullDafnyName.IndexOf('.'));
  }

  public void WriteToFile() {
    string dafnyString = MsgInvPrinter.Print(msgInvFile);
    string outputFullname = Path.GetDirectoryName(program.FullName) + "/messageInvariantsAutogen.dfy";
    Console.WriteLine(string.Format("Writing message invariants to {0}", outputFullname));
    File.WriteAllText(outputFullname, dafnyString);
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny