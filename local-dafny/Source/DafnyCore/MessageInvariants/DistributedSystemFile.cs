using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny {

public class DistributedSystemFile {
  private List<string> hostImports;  // host modules to import
  private IndDatatypeDecl constants;
  private IndDatatypeDecl variables;

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

  public void AddConstants(IndDatatypeDecl constants) {
    Debug.Assert(this.constants == null, "Constants already non-null!");
    this.constants = constants;
  }

  public DatatypeDecl GetConstants() {
    Debug.Assert(constants != null, "Constants is null!");
    return constants;
  }

  public void AddVariables(IndDatatypeDecl variables) {
    Debug.Assert(this.variables == null, "Variables already non-null!");
    this.variables = variables;
  }

  public DatatypeDecl GetVariables() {
    Debug.Assert(variables != null, "Variables is null!");
    return variables;
  }

} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny