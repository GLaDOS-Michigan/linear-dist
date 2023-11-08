using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny {

public class DistributedSystemFile {
  private List<string> hostImports;  // host modules to import
  private DatatypeDecl constants;
  private DatatypeDecl variables;

  // Constructor
  public DistributedSystemFile()
  {
    hostImports = new List<string>();
    constants = null;
  }

  public void AddHostImport(string moduleName) {
    hostImports.Add(moduleName);
  }

   public List<string> GetHostImports() {
    return hostImports;
  }

  public void AddConstants(DatatypeDecl constants) {
    Debug.Assert(this.constants == null, "Constants already non-null!");
    this.constants = constants;
  }

  public DatatypeDecl GetConstants() {
    Debug.Assert(constants != null, "Constants is null!");
    return constants;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny