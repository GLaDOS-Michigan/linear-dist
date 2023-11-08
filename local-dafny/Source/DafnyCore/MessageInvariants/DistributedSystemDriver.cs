using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny
{
public class GenAsyncDriver {

  private readonly DafnyOptions options;
  private readonly Program program;
  private DistributedSystemFile dsFile;

  // Constructor
  public GenAsyncDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    dsFile = new DistributedSystemFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Generating asynchronous distributed system for {0}\n", program.FullName));
    var systemModule = GetModule("System");

    // find imports
    foreach (var decl in systemModule.TopLevelDecls.Where(x => x.Name.Contains("Host"))) {
      dsFile.AddHostImport(decl.Name);
    }
  } // end method Resolve()

  private ModuleDefinition GetModule(string moduleName) {
    ModuleDefinition res = null;
    foreach (var kvp in program.ModuleSigs) {
      var moduleDef = kvp.Value.ModuleDef;
      if (moduleDef.DafnyName.Equals(moduleName)) {
        res = moduleDef;
      }
    }
    Debug.Assert(res != null, String.Format("Module {0} not found ", moduleName));
    return res;
  } 



  public void WriteToFile() {
    string dsString = DistributedSystemPrinter.PrintDistributedSystem(dsFile);
    string dsOutputFullname = Path.GetDirectoryName(program.FullName) + "/distributedSystemAutogen.dfy";
    Console.WriteLine(string.Format("Writing distributed system to {0}", dsOutputFullname));
    File.WriteAllText(dsOutputFullname, dsString);
  }
}  // end class GenAsyncDriver
} // end namespace Microsoft.Dafny