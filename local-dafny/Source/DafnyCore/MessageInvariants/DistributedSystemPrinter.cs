using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Newtonsoft.Json;

namespace Microsoft.Dafny
{
public static class DistributedSystemPrinter {

  private static readonly string[] Includes = {"../hosts.dfy"};
  private static readonly string[] Imports = {"Types", "UtilitiesLibrary", "Network"};
  private static readonly string TemplatePath = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Source/DafnyCore/MessageInvariants/templates.json";

  private static readonly Dictionary<string, string[]> Template = JsonConvert.DeserializeObject<Dictionary<string, string[]>>(File.ReadAllText(TemplatePath));

  private static string GetFromTemplate(string key) {
    return string.Join("\n", Template[key]) + "\n";
  }

  public static string PrintDistributedSystem(DistributedSystemFile file, DafnyOptions options) {
    var res = new StringBuilder();

    // Dafny files to include
    foreach (string i in Includes) {
      res.AppendLine(String.Format("include \"{0}\"", i));
    }
    res.AppendLine();

    // Define Network module
    res.AppendLine(GetFromTemplate("NetworkModule"));
    
    // Define DistributedSystem module
    res.AppendLine("module DistributedSystem {");
    res.AppendLine(PrintDistributedSystemModuleBody(file, options));
    res.AppendLine("} // end module DistributedSystem");
    return res.ToString();
  } // end function PrintDistributedSystem

  private static string PrintDistributedSystemModuleBody(DistributedSystemFile file, DafnyOptions options) {
    var res = new StringBuilder();

    // Import dependencies
    foreach (string i in Imports) {
      res.AppendLine(String.Format("  import opened {0}", i));
    }
    foreach (string i in file.GetHostImports()) {
      res.AppendLine(String.Format("  import {0}", i));
    }
    res.AppendLine();
    
    // Declare datatype Constants
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintDatatype(file.GetConstants(), 2, "dummy string");
    res.AppendLine(wr.ToString());

    return res.ToString();
  } // end function PrintDistributedSystemModuleBody

} // end class MessageInvariantsFile
} //end namespace Microsoft.Dafny