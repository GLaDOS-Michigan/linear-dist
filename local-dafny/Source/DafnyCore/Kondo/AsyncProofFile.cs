using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny {

public class AsyncProofFile {
  private readonly List<Function> appInvPredicates;  // ApplicationInv predicates
  private readonly List<Function> helperFunctions;   // functions and predicates that are not invariants, and not special
  private readonly List<Function> specialHelperFunctions;   // these are called by appInvPredicates, e.g. Chosen in paxos
  private readonly List<Lemma> invNextLemmas;
  private readonly List<Lemma> helperLemmas;     
  public Lemma invInductiveLemma;  // InvInductive from sync

  // Constructor
  public AsyncProofFile()
  {
    appInvPredicates = new List<Function>();
    helperFunctions = new List<Function>();
    specialHelperFunctions = new List<Function>();
    invNextLemmas = new List<Lemma>();
    helperLemmas = new List<Lemma>();
  }

  public void AddAppInv(Function predicate) {
    appInvPredicates.Add(predicate);
  }

   public List<Function> GetAppInvPredicates() {
    return appInvPredicates;
  }

  public void AddHelperFunction(Function f) {
    helperFunctions.Add(f);
  }

  public List<Function> GetHelperFunctions() {
    return helperFunctions;
  }

  public void AddSpecialHelperFunction(Function f) {
    specialHelperFunctions.Add(f);
  }

  public List<Function> GetSpecialHelperFunctions() {
    return specialHelperFunctions;
  }

  public void AddInvNextLemma(Lemma lemma) {
    Debug.Assert(lemma.Name.Contains("InvNext"), String.Format("Lemma {0} is not an InvNext lemma", lemma.Name));
    invNextLemmas.Add(lemma);
  }

  public List<Lemma> GetInvNextLemmas() {
    return invNextLemmas;
  }

  public void AddHelperLemma(Lemma lemma) {
    helperLemmas.Add(lemma);
  }

  public List<Lemma> GetHelperLemmas() {
    return helperLemmas;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny