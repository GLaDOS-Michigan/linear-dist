using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Intrinsics.X86;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Dafny.ProofObligationDescription;
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
      res.AppendLine(FormatInvariantPredicate(appInv, options));
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
    res.AppendLine(FormatInvInductive(file.invInductiveLemma, options));

    // Print InvNext Lemmas 
    if (file.GetInvNextLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("InvNextLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetInvNextLemmas()) {
        res.AppendLine(FormatInvNextLemma(lemma, options));
      }
    }

    // Print helper lemmas
    if (file.GetHelperLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetHelperLemmas()) {
        res.AppendLine(FormatHelperLemma(lemma, options));
      }
    }

    // Print helper functions
    if (file.GetHelperFunctions().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperFunctionsSeparator", 0));
      foreach (Function f in file.GetHelperFunctions()) {
        res.AppendLine(FormatHelperFunction(f, options));
      }
    }

    // Print special helper functions
    if (file.GetSpecialHelperFunctions().Count != 0) {
      res.AppendLine();
      foreach (Function f in file.GetSpecialHelperFunctions()) {
        res.AppendLine(FormatSpecialHelperFunction(f, options));
      }
    }
    return res.ToString();
  } // end function PrintAsyncProofModuleBody 
  
  // Transform a sync predicate into async one
  private static string FormatInvariantPredicate(Function syncAppPred, DafnyOptions options) {
    var res = new StringBuilder();
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintFunction(syncAppPred, 0, false, 1);
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

  // Transform sync InvInductive lemma into async one
  private static string FormatInvInductive(Lemma syncInvInductive, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(syncInvInductive, 0, false, 0);
    var invInductive = wr.ToString();
    // insert VariableNextProperties(c, v, v') into string
    int index = invInductive.IndexOf("{");
    invInductive = invInductive.Insert(index+2, "  VariableNextProperties(c, v, v');\n  MonotonicityInvInductive(c, v, v');\n  MessageInvInductive(c, v, v');\n");
    return invInductive;
  }

  // Transform a sync InvNext lemma into async one
  private static string FormatInvNextLemma(Lemma syncLemma, DafnyOptions options) {
    if (IsAsyncCompatible(syncLemma, options)) {
      var wr = new StringWriter();
      var printer = new Printer(wr, options);
      printer.PrintMethod(syncLemma, 0, false, 1);
      var res = wr.ToString();
      // If Inv(c, v) requirement is missing, it means that specific AppInvs are used.
      // Insert Msg and Mono Invs
      if (!res.Contains("requires Inv(c, v)")) {
        var pattern = "requires v.WF(c)";
        var insertIdx = res.IndexOf(pattern) + pattern.Length + 1;
        res = res.Insert(insertIdx, "  requires MonotonicityInv(c, v)\n  requires MessageInv(c, v)\n");
      }
      return res.ToString();
    }
    return FormatSyncSpecificLemma(syncLemma, options);
  }

  // Identifies case 2 sync lemmas
  private static bool IsAsyncCompatible(Lemma syncLemma, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(syncLemma, 0, false, 0);
    var lemmaStr = wr.ToString();
    return !lemmaStr.Contains("sysStep");
  }

  // Format a case 2 sync lemma
  private static string FormatSyncSpecificLemma(Lemma syncLemma, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(syncLemma, 0, true, 0);
    wr.WriteLine(GetFromTemplate("SyncSpecificLemma", 2));
    var res = wr.ToString();

    // Comment out lines with sync-Specific syntax
    string pattern = @"requires.*Step?|decreases.*Step";
    var synclines = Regex.Matches(res, pattern).Cast<Match>().Select(match => match.Value).ToList();
    foreach (var sl in synclines) {
      res = res.Replace(sl, "// " + sl);
    }
    return res.ToString();
  }

  // Transform sync helper lemma into async one
  private static string FormatHelperLemma(Lemma syncLemma, DafnyOptions options) {
    if (IsAsyncCompatible(syncLemma, options)) {
      var wr = new StringWriter();
      var printer = new Printer(wr, options);
      printer.PrintMethod(syncLemma, 0, false, 2);
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
      return lemmaStr;
    } 
    return FormatSyncSpecificLemma(syncLemma, options);
  }

  private static string FormatHelperFunction(Function function, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintFunction(function, 0, false, 2);
    return wr.ToString();
  }

  private static string FormatSpecialHelperFunction(Function function, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    wr.WriteLine("// I am special");
    printer.PrintFunction(function, 0, false, 0);
    var res = wr.ToString();
    res = res.Replace("v: Variables", "v: Hosts");  // hacky
    return res;
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