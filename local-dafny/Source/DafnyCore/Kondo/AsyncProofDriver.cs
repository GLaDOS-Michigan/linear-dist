using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny
{
public class AsyncProofDriver {

  private readonly DafnyOptions options;
  private readonly Program program;
  private readonly AsyncProofFile proofFile;

  // Constructor
  public AsyncProofDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    proofFile = new AsyncProofFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Resolving invariants for {0}\n", program.FullName));

    var centralizedProof = GetProofModule();
    ResolveApplicationInvariants(centralizedProof);
    ResolveHelperFunctions(centralizedProof);

  } // end method Resolve()

  // Resolve list of application invariant predicates
  private void ResolveApplicationInvariants(ModuleDefinition centralizedProof) {

    // get the app inv bundle from centralized
    var appInv = GetPredicate(centralizedProof, "ApplicationInv");  
    
    // extract the conjunct names, and add Function to proofFile
    foreach (var exp in Expression.Conjuncts(appInv.Body)) {
      var predName = exp.ToString().Split('(')[0];  // this is janky
      proofFile.AddAppInv(GetPredicate(centralizedProof, predName));
    }
  }


  // Returns the Dafny predicate with the given name in given module
  private Function GetPredicate(ModuleDefinition centralizedProof, string predicateName) {
    Function res = null;
    foreach (var topLevelDecl in ModuleDefinition.AllFunctions(centralizedProof.TopLevelDecls.ToList())) {
      if (topLevelDecl.Name.Equals(predicateName)) {  // identifying marker for Send Predicate
        res = topLevelDecl;
      }
    }
    Debug.Assert(res != null, String.Format("Predicate {0} not found ", predicateName));
    return res;
  }

  // Resolve list of non-invariant functions and predicates
  private void ResolveHelperFunctions(ModuleDefinition centralizedProof) {

    // get the app inv bundle from centralized
    // var appInv = GetPredicate(centralizedProof, "ApplicationInv");  
    
    // // extract the conjunct names, and add Function to proofFile
    // foreach (var exp in Expression.Conjuncts(appInv.Body)) {
    //   var predName = exp.ToString().Split('(')[0];  // this is janky
    //   proofFile.AddAppInv(GetPredicate(predName));
    // }
  }


  // Returns the centralized Proof module
  private ModuleDefinition GetProofModule() {
    ModuleDefinition res = null;
    foreach (var kvp in program.ModuleSigs) {
      var moduleDef = kvp.Value.ModuleDef;
      if (moduleDef.DafnyName.Contains("Proof")) {
        res = moduleDef;
      }
    }
    Debug.Assert(res != null, "Proof module not found ");
    return res;
  }


  public void WriteToFile() {
    string proofString = AsyncProofPrinter.PrintAsyncProof(proofFile, options, program.FullName);
    string proofOutputFullname = Path.GetDirectoryName(program.FullName) + "/../automate_full/applicationProofDraftAutogen.dfy";
    Console.WriteLine(string.Format("Writing async proof draft to {0}", proofOutputFullname));
    File.WriteAllText(proofOutputFullname, proofString);
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny