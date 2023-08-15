// Network-level "boilerplate" invariants that are application-independent

include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// All VoteMsg have a valid participant HostId as src
ghost predicate VoteMsgValidSrc(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
  :: 0 <= msg.src < |c.hosts|-1
}

// VoteMsg reflects the preference of the voter 
// Note that "0 <= msg.src < |c.hosts|-1" is prereq of GetParticipantPreference
ghost predicate VoteMsgAgreeWithVoter(c: Constants, v: Variables)
  requires v.WF(c)
  requires VoteMsgValidSrc(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.VoteMsg? 
  :: GetParticipantPreference(c, msg.src) == msg.v
}

// DecideMsgs should reflect the decision of the leader
// Note that this hinges on fact that leader does not equivocate
ghost predicate DecisionMsgsAgreeWithLeader(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.DecideMsg? 
  :: GetCoordinator(c, v).decision.Some? && msg.d == GetCoordinator(c, v).decision.value
}

// If a participant has decided, then there must be a corresponding DecideMsg
ghost predicate ParticipantsDecisionImpliesDecideMsg(c: Constants, v: Variables) 
  requires v.WF(c)
{
  var n := |v.hosts|;
  forall i | 0 <= i < n && HostHasDecided(v.hosts[i]) :: 
    && (HostDecidedCommit(v.hosts[i]) ==> DecideMsg(Commit) in v.network.sentMsgs)
    && (HostDecidedAbort(v.hosts[i]) ==> DecideMsg(Abort) in v.network.sentMsgs)
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && VoteMsgValidSrc(c, v)
  && VoteMsgAgreeWithVoter(c, v)
  && DecisionMsgsAgreeWithLeader(c, v)
  && ParticipantsDecisionImpliesDecideMsg(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{}
}

