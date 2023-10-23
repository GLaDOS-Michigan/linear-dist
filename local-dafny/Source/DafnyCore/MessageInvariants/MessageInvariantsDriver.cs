using System;
using System.Collections.Generic;
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
    Console.WriteLine(String.Format("Resolving message invariants for {0}\n", program.FullName));

    // Find distributedSystem.Hosts
    DatatypeDecl dsHosts = null;
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllTypesWithMembers(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.FullDafnyName.Equals("DistributedSystem.Hosts")) {
          dsHosts = (DatatypeDecl) topLevelDecl;
          break;
        }
      }
    }
    Debug.Assert(dsHosts != null, "dsHosts should not be null");

    // Find Send Predicate definitions
    var sendPredicateDefs = new List<Function>();
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.Name.StartsWith("Send")) {  // identifying marker for Send Predicate
          sendPredicateDefs.Add(topLevelDecl);
        }
      }
    }

    // Create SendInvariant objects
    foreach (var sp in sendPredicateDefs) {   
      var sendInv = SendInvariant.FromFunction(sp, dsHosts);
      msgInvFile.AddSendInvariant(sendInv);
    }

    // Find Receive Predicate definitions -- have a list of predicate names, and a map to 
    // Trigger and Conclusion definitions
    var receivePredicateNames = new List<string>();
    var receivePredicateDefs = new Dictionary<string, Function>();
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.Name.StartsWith("Receive")) {  // identifying marker for Receive Predicate
          if (topLevelDecl.Name.EndsWith("Trigger")) {
            var baseName = topLevelDecl.Name.Substring(0, topLevelDecl.Name.Length-"Trigger".Length);
            receivePredicateNames.Add(baseName);
          }
          receivePredicateDefs.Add(topLevelDecl.Name, topLevelDecl);
        }
      }
    }

    // Create ReceiveInvariant objects
    foreach (var rp in receivePredicateNames) {   
      var recvInv = ReceiveInvariant.FromTriggerFunction(rp, receivePredicateDefs[rp + "Trigger"], dsHosts);
      msgInvFile.AddReceiveInvariant(recvInv);
    }
  } // end method Resolve()

  public void WriteToFile() {
    string dafnyString = MsgInvPrinter.Print(msgInvFile);
    string outputFullname = Path.GetDirectoryName(program.FullName) + "/messageInvariantsAutogen.dfy";
    Console.WriteLine(string.Format("Writing message invariants to {0}", outputFullname));
    File.WriteAllText(outputFullname, dafnyString);
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny