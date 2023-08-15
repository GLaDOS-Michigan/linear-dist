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

include "system.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened System

  // AC-1: All processes that reach a decision reach the same one.
  ghost predicate SafetyAC1(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.hosts|;
    forall i, j | 0 <= i < n && 0 <= j < n && HostHasDecided(v.hosts[i]) && HostHasDecided(v.hosts[j])
    :: HostsReachSameDecision(v.hosts[i], v.hosts[j])
  }

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  ghost predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.hosts|;
    (exists i :: 0 <= i < n && HostDecidedCommit(v.hosts[i]))
    ==>
    AllPreferYes(c, v)
  }

  // This one is easier to prove
  ghost predicate AC3Contrapos(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.hosts|;
    (! AllPreferYes(c, v)) 
    ==> forall i | 0 <= i < n && HostHasDecided(v.hosts[i]) 
        :: HostDecidedAbort(v.hosts[i])
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(c: Constants, v: Variables)
    requires v.WF(c)
  {
    var n := |v.hosts|;
    AllPreferYes(c, v)
    ==> 
    forall i | 0 <= i < n && HostHasDecided(v.hosts[i]) :: HostDecidedCommit(v.hosts[i])
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

  ghost function GetCoordinator(c: Constants, v: Variables) : CoordinatorHost.Variables
    requires v.WF(c)
  {
    Last(v.hosts).coordinator
  }

  ghost function GetParticipant(c: Constants, v: Variables, i: int) : ParticipantHost.Variables
    requires v.WF(c)
    requires 0 <= i < |v.hosts|-1
  {
    v.hosts[i].participant
  }

  ghost function GetParticipantPreference(c: Constants, i: int) : Vote
    requires c.WF()
    requires 0 <= i < |c.hosts|-1
  {
    c.hosts[i].participant.preference
  }

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

  ghost predicate AllPreferYes(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    var n := |c.hosts|;
    forall j | 0 <= j < n-1 :: c.hosts[j].participant.preference == Yes
  }
}
