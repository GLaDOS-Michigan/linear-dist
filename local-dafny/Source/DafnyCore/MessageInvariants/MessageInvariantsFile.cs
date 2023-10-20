using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
  public class MessageInvariantsFile {

    // List of invariants
    private List<SendInvariant> sendInvariants;

    // Constructor
    public MessageInvariantsFile()
    {
      this.sendInvariants = new List<SendInvariant>{};
    }

    public void AddSendInvariant(SendInvariant si) {
      sendInvariants.Add(si);
    }

    public List<SendInvariant> GetSendInvariants() {
      return this.sendInvariants;
    }

  } // end class MessageInvariantsFile
}