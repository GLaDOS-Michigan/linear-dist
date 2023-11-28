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
  public OwnershipInvariantsFile ownerInvFile;

  // Constructor
  public MessageInvariantsDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    msgInvFile = new MessageInvariantsFile();
    monoInvFile = new MonotonicityInvariantsFile();
    ownerInvFile = new OwnershipInvariantsFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Resolving invariants for {0}\n", program.FullName));

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
      // Nothing to do here actually
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
        if (topLevelDecl.Name.StartsWith("Send") && !topLevelDecl.FullDafnyName.StartsWith("Types.")) {  // identifying marker for Send Predicate
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
        if (topLevelDecl.Name.StartsWith("Receive") && topLevelDecl.Name.Contains("Trigger"))  {  // identifying marker for Receive Predicate
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
      string monoInvString = MsgInvPrinter.PrintMonotonicityInvariants(monoInvFile, program.FullName);
      string monoInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/monotonicityInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing monotonicity invariants to {0}", monoInvOutputFullname));
      File.WriteAllText(monoInvOutputFullname, monoInvString);

      // Write message invariants
      string msgInvString = MsgInvPrinter.PrintMessageInvariants(msgInvFile, program.FullName);
      string msgInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/messageInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing message invariants to {0}", msgInvOutputFullname));
      File.WriteAllText(msgInvOutputFullname, msgInvString);
    } 
    if (options.ownershipInvs) {
      // Write ownership invariants
      string ownerInvString = MsgInvPrinter.PrintOwnershipInvariants(ownerInvFile, program.FullName);
      string ownerInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/ownershipInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing ownership invariants to {0}", ownerInvOutputFullname));
      File.WriteAllText(ownerInvOutputFullname, ownerInvString);
    }
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny