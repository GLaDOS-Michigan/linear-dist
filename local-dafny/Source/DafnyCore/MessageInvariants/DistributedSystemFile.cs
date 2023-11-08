using System;
using System.Collections.Generic;

namespace Microsoft.Dafny {

public class DistributedSystemFile {
  private List<string> hostImports;  // host modules to import

  // Constructor
  public DistributedSystemFile()
  {
    hostImports = new List<string>();
  }

  public void AddHostImport(string moduleName) {
    hostImports.Add(moduleName);
  }

  public List<string> GetHostImports() {
    return hostImports;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny