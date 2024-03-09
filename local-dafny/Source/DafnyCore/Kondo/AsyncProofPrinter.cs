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
  private static readonly string[] Imports = {"Types", "UtilitiesLibrary", "MonotonicityLibrary", "DistributedSystem", "MonotonicityInvariants", "MessageInvariants", "Obligations"};
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
    
    // Print InvInductive proof body. Get directly from Sync
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(file.invInductiveLemma, 0, false, 0);
    var invInductive = wr.ToString();
    // insert VariableNextProperties(c, v, v') into string
    int index = invInductive.IndexOf("{");
    invInductive = invInductive.Insert(index+2, "  VariableNextProperties(c, v, v');\n  MonotonicityInvInductive(c, v, v');\n  MessageInvInductive(c, v, v');\n");
    res.AppendLine(invInductive);

    // Print InvNext Lemmas 
    if (file.GetInvNextLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("InvNextLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetInvNextLemmas()) {
        wr = new StringWriter();
        printer = new Printer(wr, options);
        printer.PrintMethod(lemma, 0, false, 1);
        res.AppendLine(wr.ToString());
      }
    }

    // Print helper lemmas
    if (file.GetHelperLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetHelperLemmas()) {
        wr = new StringWriter();
        printer = new Printer(wr, options);
        printer.PrintMethod(lemma, 0, false, 2);
        var linesList = wr.ToString().Split("\n").ToList();
        // hacky way to transform requires clauses, as I only wanna transform "v." and not "v"
        for (int i = 0; i < linesList.Count; i++) {
          if (linesList[i].Contains("decreases")) {
            break;
          } 
          linesList[i] = linesList[i].Replace("v.", "v.Last().");
          linesList[i] = linesList[i].Replace("v'.", "v'.Last().");
        }
        var lemmaStr = String.Join("\n", linesList);
        lemmaStr = lemmaStr.Replace("Last().WF(c)", "WF(c)");  // hacky
        lemmaStr = lemmaStr.Replace("Safety(c, v.Last())", "Safety(c, v)");  // hacky
        lemmaStr = StripTriggerAnnotations(lemmaStr);
        res.AppendLine(lemmaStr);
      }
    }

    // Print helper functions
    if (file.GetHelperFunctions().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperFunctionsSeparator", 0));
      foreach (Function f in file.GetHelperFunctions()) {
        wr = new StringWriter();
        printer = new Printer(wr, options);
        printer.PrintFunction(f, 0, false, 2);
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
    printer.PrintFunction(centralizedAppPred, 0, false, 1);
    var pred = wr.ToString();

    pred = pred.Replace("History(i).WF(c)", "WF(c)");  // hacky

    // Format Kondo triggers
    string pattern = @"\{:trigger [^\}]*\}";
    var syncTriggers = Regex.Matches(pred, pattern).Cast<Match>().Select(match => match.Value).ToList();;
    foreach (var st in syncTriggers) {
      pred = pred.Replace(st, TransformTrigger(st));
    }

    res.Append(pred);
    return res.ToString();
  }

  // Transform sync trigger into corresponding async trigger
  private static string TransformTrigger(string trigger) {
    // add v.ValidHistoryIdx(i) if i not present
    var res = trigger;
    if (!res.Contains("History(i)")) {
      int indexToInsert = res.Length - 1;
      res = res.Insert(indexToInsert, ", v.ValidHistoryIdx(i)");
    }
    return res;
  }

  private static string StripTriggerAnnotations(string input) {
    // Define the pattern to remove
    string pattern = @"\{:trigger [^\}]*\}";
    // Use Regex.Replace to remove all occurrences of the pattern
    string resultString = Regex.Replace(input, pattern, "");
    return resultString;
  }

  // private static string ValidActorIdx(string actor, string field) {
  //   return string.Format("0 <= {0} < |h.{1}|", actor, field);
  // }
} // end class MessageInvariantsFile
} //end namespace Microsoft.Dafny