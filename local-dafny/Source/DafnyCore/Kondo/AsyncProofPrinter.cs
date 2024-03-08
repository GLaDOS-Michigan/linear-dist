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

  private static readonly string[] Includes = {"monotonicityInvariantsAutogen.dfy", "messageInvariantsAutogen.dfy"};
  private static readonly string[] Imports = {"Types", "UtilitiesLibrary", "DistributedSystem", "MonotonicityInvariants", "MessageInvariants", "Obligations"};
  private static readonly string TemplatePath = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Source/DafnyCore/Kondo/templates.json";

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
    res.AppendLine($"/// Generated {DateTime.Now.ToString("MM/dd/yyyy HH:mm")} {TimeZoneInfo.Local.StandardName}");

    // Dafny files to include
    foreach (string i in Includes) {
      res.AppendLine(String.Format("include \"{0}\"", i));
    }
    res.AppendLine();

    res.AppendLine("module ProofDraft {");
    res.AppendLine(PrintAsyncProofModuleBody(file, options));
    res.AppendLine("} // end module DistributedSystem");
    return res.ToString();
  }

  private static string PrintAsyncProofModuleBody(AsyncProofFile file, DafnyOptions options) {
    var res = new StringBuilder();
    foreach (string i in Imports) {
      res.AppendLine(String.Format("  import opened {0}", i));
    }
    res.AppendLine();

    // Print Application Invariant predicates
    foreach (Function appInv in file.GetAppInvPredicates()) {
      res.AppendLine(PrintInvariantPredicate(appInv, options));
    }

    // Print Application Invariant bundle
    res.Append(GetFromTemplate("ApplicationInvHeader", 0));
    foreach (Function appInv in file.GetAppInvPredicates()) {
      res.AppendLine("  && " + appInv.Name + "(c, v)");
    }
    res.AppendLine("}");
    res.AppendLine();

    // Print Inv bundle
    res.AppendLine(GetFromTemplate("Inv", 0));

    // Print proof obligations
    res.AppendLine(GetFromTemplate("ObligationsSeparator", 0));
    res.AppendLine(GetFromTemplate("InvImpliesSafety", 0));
    res.AppendLine(GetFromTemplate("InitImpliesInv", 0));
    
    res.Append(GetFromTemplate("InvInductiveHeader", 0));
    // Print InvNext Lemma calls
    foreach (Lemma lemma in file.GetInvNextLemmas()) {
      res.AppendLine($"  {lemma.Name}(c, v, v');");
    }
    res.AppendLine("}");

    // Print InvNext Lemmas 
    if (file.GetInvNextLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("InvNextLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetInvNextLemmas()) {
        var wr = new StringWriter();
        var printer = new Printer(wr, options);
        printer.PrintMethod(lemma, 0, false, true);
        res.AppendLine(wr.ToString());
      }
    }

    // Print helper functions
    if (file.GetHelperFunctions().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperFunctionsSeparator", 0));
      foreach (Function f in file.GetHelperFunctions()) {
        var wr = new StringWriter();
        var printer = new Printer(wr, options);
        printer.PrintFunction(f, 0, false, false);
        res.AppendLine(wr.ToString());
      }
    }
    return res.ToString();
  } // end function PrintAsyncProofModuleBody 
  
  // Transform a centralized predicate into async one
  private static string PrintInvariantPredicate(Function centralizedAppPred, DafnyOptions options) {
    var res = new StringBuilder();
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintFunction(centralizedAppPred, 0, false, true);
    var pred = wr.ToString();

    pred = pred.Replace("History(i).WF(c)", "WF(c)");  // hacky

    // TODO: Ignore triggers for now
    pred = StripTriggerAnnotations(pred);
    pred = StripTriggerAnnotations(pred);

    res.Append(pred);
    return res.ToString();
  }

  private static string StripTriggerAnnotations(string input) {
    // Define the pattern to remove
    string pattern = @"\{:trigger [^\}]*\}";
    // Use Regex.Replace to remove all occurrences of the pattern
    string resultString = Regex.Replace(input, pattern, "");
    return resultString;
  }

  private static string ValidActorIdx(string actor, string field) {
    return string.Format("0 <= {0} < |h.{1}|", actor, field);
  }
} // end class MessageInvariantsFile
} //end namespace Microsoft.Dafny