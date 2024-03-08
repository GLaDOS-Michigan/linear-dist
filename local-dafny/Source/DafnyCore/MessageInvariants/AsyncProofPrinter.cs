using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Newtonsoft.Json;

namespace Microsoft.Dafny
{
public static class AsyncProofPrinter {

  private static readonly string[] Includes = {"../hosts.dfy"};
  private static readonly string[] Imports = {"Types", "UtilitiesLibrary", "Network"};
  private static readonly string TemplatePath = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Source/DafnyCore/MessageInvariants/templates.json";

  private static readonly Dictionary<string, string[]> Template = JsonConvert.DeserializeObject<Dictionary<string, string[]>>(File.ReadAllText(TemplatePath));

  private static string GetFromTemplate(string key, int indent) {
    var lines = Template[key];
    var res = new StringBuilder();
    foreach (var l in lines) {
      res.AppendLine(new string(' ', indent) + l);
    }
    return res.ToString();
  }

  public static string PrintAsyncProof(AsyncProofFile file, DafnyOptions options, string sourceFileName) {
    var res = new StringBuilder();

    // Header
    res.AppendLine($"/// This file is auto-generated from {sourceFileName}");

    // Dafny files to include
    foreach (string i in Includes) {
      res.AppendLine(String.Format("include \"{0}\"", i));
    }
    res.AppendLine();

    return res.ToString();
  } // end function PrintDistributedSystemModuleBody


  private static string StripTriggerAnnotations(string input) {
    // Define the pattern to remove
    string pattern = @"\{:trigger [^\}]*\} ";
    // Use Regex.Replace to remove all occurrences of the pattern
    string resultString = Regex.Replace(input, pattern, "");
    return resultString;
  }

  private static string ValidActorIdx(string actor, string field) {
    return string.Format("0 <= {0} < |h.{1}|", actor, field);
  }
} // end class MessageInvariantsFile
} //end namespace Microsoft.Dafny