include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// certified self-inductive
// Every message in the network has a valid source
predicate ValidMessageSrc(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: 
  match msg 
    case Prepare(bal) => c.ValidLeaderIdx(bal)
    case Promise(_, acc, _) => c.ValidAcceptorIdx(acc)
    case Propose(bal, _) => c.ValidLeaderIdx(bal)
    case Accept(_, acc) => c.ValidAcceptorIdx(acc)
    case Learn(lnr, _, _) => c.ValidLearnerIdx(lnr)
}

// certified self-inductive
// Leader updates its highestHeard and value based on a Promise message carrying that
// ballot and value
predicate LeaderValidHighestHeard(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, b| c.ValidLeaderIdx(idx) && v.leaders[idx].highestHeardBallot == Some(b)
  :: (exists prom: Message ::
        && IsPromiseMessage(v, prom)
        && prom.bal == idx
        && prom.vbOpt == Some(VB(v.leaders[idx].value, b))
    )
}

// certified self-inductive
// Leader updates receivedPromises based on Promise messages
predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, src | c.ValidLeaderIdx(idx) && src in v.leaders[idx].receivedPromises
  :: (exists prom: Message ::
        && IsPromiseMessage(v, prom)
        && prom.bal == idx
    )
} 

// certified self-inductive
// Acceptor updates its promised ballot based on a Prepare/Propose message carrying 
// that ballot
predicate AcceptorValidPromised(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, b | c.ValidAcceptorIdx(idx) && v.acceptors[idx].promised == Some(b)
  :: (exists m: Message ::
        && (IsPromiseMessage(v, m) || IsProposeMessage(v, m))
        && m.bal == b
    )
}

// certified self-inductive
// Acceptor updates its acceptedVB based on a Propose message carrying that ballot 
// and value
predicate AcceptorValidAcceptedVB(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, val, bal | 
    && c.ValidAcceptorIdx(idx) 
    && v.acceptors[idx].acceptedVB == Some(VB(val, bal))
  :: 
    Propose(bal, val) in v.network.sentMsgs
}

// TODO: This is self-inductive, but doesn't feel to be in the spirit of message invariants.
// It feels like an application invariant, but leaving this here for now. 
// I think in the full monotonic protocol, this would become an invariant on the acceptor 
//local state.
// Every Promise message in the network has a ballot upper-bounded by the promised ballot
// of the source acceptor
predicate AcceptorPromisedMonotonic(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, prom | 
    && c.ValidAcceptorIdx(idx) 
    && IsPromiseMessage(v, prom)
    && prom.acc == c.acceptorConstants[idx].id
  ::
    && v.acceptors[idx].promised.Some?
    && prom.bal <= v.acceptors[idx].promised.value
}

// certified self-inductive
// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
predicate LearnerValidReceivedAccepts(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc | 
    && c.ValidLearnerIdx(idx)
    && vb in v.learners[idx].receivedAccepts
    && acc in v.learners[idx].receivedAccepts[vb]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}

// certified self-inductive, modulo ValidMessageSrc(c, v)
// For every Learn(lnr, val) message in the network, the learner must have a quorum of
// accepts for that val, at some common ballot
predicate LearnMsgsValid(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
{
  forall lnr:LearnerId, bal, val | 
    Learn(lnr, bal, val) in v.network.sentMsgs
  :: 
    && var vb := VB(val, bal);
    && vb in v.learners[lnr].receivedAccepts
    && |v.learners[lnr].receivedAccepts[vb]| >= c.f+1
}

// Message bundle
predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessageSrc(c, v)
  && LeaderValidHighestHeard(c, v)
  && LeaderValidReceivedPromises(c, v)
  && AcceptorValidPromised(c, v)
  && AcceptorValidAcceptedVB(c, v)
  && AcceptorPromisedMonotonic(c, v)
  && LearnerValidReceivedAccepts(c, v)
  && LearnMsgsValid(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{}

/***************************************************************************************
*                                        Utils                                         *
***************************************************************************************/

predicate IsPrepareMessage(v: Variables, m: Message) {
  && m.Prepare?
  && m in v.network.sentMsgs
}

predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}

predicate IsLearnMessage(v: Variables, m: Message) {
  && m.Learn?
  && m in v.network.sentMsgs
} 
}  // end module PaxosProof

