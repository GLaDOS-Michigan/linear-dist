using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny
{
public class AsyncProofDriver {

  private readonly DafnyOptions options;
  private readonly Program program;
  private AsyncProofFile proofFile;

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

  } // end method Resolve()

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
    
    // var wr = new StringWriter();
    // var printer = new Printer(wr, options);
    // printer.PrintModuleDefinition(program.Compilation, centralizedProof, null, 0, null, "dummy string");
    
    File.WriteAllText(proofOutputFullname, proofString);
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny