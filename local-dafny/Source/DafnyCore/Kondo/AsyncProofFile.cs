// using System;
using System.Collections.Generic;
// using System.Diagnostics;
// using System.Runtime.CompilerServices;

namespace Microsoft.Dafny {

public class AsyncProofFile {
  private readonly List<Function> appInvPredicates;  // ApplicationInv predicates
  private readonly List<Function> helperFunctions;   // functions and predicates that are not invariants

  // Constructor
  public AsyncProofFile()
  {
    appInvPredicates = new List<Function>();
    helperFunctions = new List<Function>();
  }

  public void AddAppInv(Function predicate) {
    appInvPredicates.Add(predicate);
  }

   public List<Function> GetAppInvPredicates() {
    return appInvPredicates;
  }

  public void AddHelperFunction(Function f) {
    helperFunctions.Add(f);
  }

  public List<Function> GetHelperFunctions() {
    return helperFunctions;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny