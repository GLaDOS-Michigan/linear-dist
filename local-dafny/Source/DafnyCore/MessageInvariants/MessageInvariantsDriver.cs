using System;
using System.IO;

namespace Microsoft.Dafny
{
public class MessageInvariantsDriver {

  public Program program;
  public MessageInvariantsFile msgInvFile;

  // Constructor
  public MessageInvariantsDriver(Program program)
  {
    this.program = program;
    msgInvFile = new MessageInvariantsFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Deriving message invariants for file {0}", program.FullName));
    
  }

  public void WriteToFile() {
    string dafnyString = MsgInvPrinter.Print(msgInvFile);
    string outputFullname = Path.GetDirectoryName(program.FullName) + "/automate/messageInvariantsAutogen.dfy";
    Console.WriteLine(String.Format("Writing message invariants to {0}", outputFullname));
    File.WriteAllText(outputFullname, dafnyString);
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny