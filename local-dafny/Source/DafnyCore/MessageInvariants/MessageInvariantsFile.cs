using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
  public class MessageInvariantsFile {

    // List of invariants
    public List<SendInvariant> sendInvariants;

    // Constructor
    public MessageInvariantsFile()
    {
      this.sendInvariants = new List<SendInvariant>{};
    }

    public void AddSendInvariant(SendInvariant si) {
      sendInvariants.Add(si);
    }


  } // end class MessageInvariantsFile
}