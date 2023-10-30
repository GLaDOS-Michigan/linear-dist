using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny
{
public class MessageInvariantsDriver {

  public DafnyOptions options;
  public Program program;
  public MessageInvariantsFile msgInvFile;
  public MonotonicityInvariantsFile monoInvFile;

  // Constructor
  public MessageInvariantsDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    msgInvFile = new MessageInvariantsFile();
    monoInvFile = new MonotonicityInvariantsFile();
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

    if (options.msgInvs) {
      ResolveMonotonicityInvariants(dsHosts, program);
      ResolveSendInvariants(dsHosts, program);
      ResolveReceiveInvariants(dsHosts, program);
    } 
    if (options.ownershipInvs) {
      // TODO
    }
  } // end method Resolve()

  private void ResolveMonotonicityInvariants(DatatypeDecl dsHosts, Program program) {
    foreach (var kvp in program.ModuleSigs) {
      var module = kvp.Value.ModuleDef;
      if (module.DafnyName.Contains("Host")) {

        // Find Variable type definition
        foreach (var decl in module.SourceDecls) {
          if (decl.Name.Equals("Variables")) {
            var monoInvs = MonotonicityInvariant.FromVariableDecl((DatatypeDecl) decl, dsHosts);
            foreach (var mi in monoInvs) {
              monoInvFile.AddInvariant(mi);
            }
            break;
          }
        }
      }
    }
  }

  private void ResolveSendInvariants(DatatypeDecl dsHosts, Program program) {
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
  }

  private void ResolveReceiveInvariants(DatatypeDecl dsHosts, Program program) {
    // Find Receive Predicate trigger definitions
    // Trigger and Conclusion definitions
    var receivePredicateTriggers = new List<Function>();
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.Name.StartsWith("Receive") && topLevelDecl.Name.EndsWith("Trigger"))  {  // identifying marker for Receive Predicate
          receivePredicateTriggers.Add(topLevelDecl);
        }
      }
    }

    // Create ReceiveInvariant objects
    foreach (var rpt in receivePredicateTriggers) {
      var recvInv = ReceiveInvariant.FromTriggerFunction(rpt, dsHosts);
      msgInvFile.AddReceiveInvariant(recvInv);
    }
  }

  public void WriteToFile() {
    if (options.msgInvs) {
      // Write monotonicity invariants
      string monoInvString = MsgInvPrinter.PrintMonotonicityInvariants(monoInvFile);
      string monoInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/monotonicityInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing monotonicity invariants to {0}", monoInvOutputFullname));
      File.WriteAllText(monoInvOutputFullname, monoInvString);

      // Write message invariants
      string msgInvString = MsgInvPrinter.PrintMessageInvariants(msgInvFile);
      string msgInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/messageInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing message invariants to {0}", msgInvOutputFullname));
      File.WriteAllText(msgInvOutputFullname, msgInvString);
    } if (options.ownershipInvs) {
      
    }
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny