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
  } // end method Resolve()



  public void WriteToFile() {
    string dsString = DistributedSystemPrinter.PrintDistributedSystem(dsFile);
    string dsOutputFullname = Path.GetDirectoryName(program.FullName) + "/distributedSystemAutogen.dfy";
    Console.WriteLine(string.Format("Writing distributed system to {0}", dsOutputFullname));
    File.WriteAllText(dsOutputFullname, dsString);
  }
}  // end class GenAsyncDriver
} // end namespace Microsoft.Dafny