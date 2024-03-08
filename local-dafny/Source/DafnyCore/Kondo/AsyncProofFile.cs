using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny {

public class AsyncProofFile {
  private List<Function> appInvPredicates;  // ApplicationInv predicates

  // Constructor
  public AsyncProofFile()
  {
    appInvPredicates = new List<Function>();
  }

  public void AddAppInv(Function predicate) {
    appInvPredicates.Add(predicate);
  }

   public List<Function> GetAppInvPredicates() {
    return appInvPredicates;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny