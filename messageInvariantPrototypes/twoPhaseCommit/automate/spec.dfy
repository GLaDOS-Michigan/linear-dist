//#title Two Phase Commit Safety Specification ghost predicate
//#desc Express the English Atomic Commit safety properties as ghost predicates
//#desc over the compound state machine model from exercise01.

// 2PC should satisfy the Atomic Commit specification. English design doc:
//
// AC-1: All processes that reach a decision reach the same one.
// AC-3: The Commit decision can only be reached if all processes prefer Yes.
// AC-4: If all processes prefer Yes, then the decision must be Commit.
//
// Note that the full Atomic Commit spec includes these additional properties,
// but you should ignore them for this exercise:
// AC-2: (stability) A process cannot reverse its decision after it has reached one.
//       (best modeled with refinement)
// AC-5: (liveness) All processes eventually decide.

include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  // AC-1: All processes that reach a decision reach the same one.
  ghost predicate SafetyAC1(c: Constants, v: Variables)
    requires v.WF(c)
  {
    // All hosts that reach a decision reach the same one
    var n := |v.Last().hosts|;
    forall i, j | 0 <= i < n && 0 <= j < n && HostHasDecided(v.Last().hosts[i]) && HostHasDecided(v.Last().hosts[j])
    :: HostsReachSameDecision(v.Last().hosts[i], v.Last().hosts[j])
  }


  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  ghost predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.Last().hosts|;
    (exists i :: 0 <= i < n && HostDecidedCommit(v.Last().hosts[i]))
    ==>
    AllPreferYes(c)
  }

  // This one is easier to prove
  ghost predicate AC3Contrapos(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.Last().hosts|;
    (! AllPreferYes(c)) 
    ==> forall i | 0 <= i < n && HostHasDecided(v.Last().hosts[i]) 
        :: HostDecidedAbort(v.Last().hosts[i])
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.Last().hosts|;
    AllPreferYes(c)
    ==> 
    forall i | 0 <= i < n && HostHasDecided(v.Last().hosts[i]) :: HostDecidedCommit(v.Last().hosts[i])
  }

  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }




  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/

  ghost predicate HostHasDecided(h: Host.Variables) {
    match h
      case CoordinatorVariables(c) => c.decision.Some?
      case ParticipantVariables(p) => p.decision.Some?
  }

  ghost predicate HostDecidedCommit(h: Host.Variables) {
    match h
      case CoordinatorVariables(c) => c.decision == Some(Commit)
      case ParticipantVariables(p) => p.decision == Some(Commit)
  }

  ghost predicate HostDecidedAbort(h: Host.Variables) {
    match h
      case CoordinatorVariables(c) => c.decision == Some(Abort)
      case ParticipantVariables(p) => p.decision == Some(Abort)
  }

  ghost predicate HostsReachSameDecision(h1: Host.Variables, h2: Host.Variables) 
    requires HostHasDecided(h1)
    requires HostHasDecided(h2)
  {
    (HostDecidedCommit(h1) && HostDecidedCommit(h2)) || (HostDecidedAbort(h1) && HostDecidedAbort(h2))
  }

  ghost predicate AllPreferYes(c: Constants) 
    requires c.WF()
  {
    var n := |c.hosts|;
    forall j | 0 <= j < n-1 :: c.hosts[j].participant.preference == Yes
  }
}