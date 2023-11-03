include "../hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import LeaderHost
  import AcceptorHost
  import LearnerHost

datatype Constants = Constants(
  p1Quorum: nat,
  p2Quorum: nat,
  n: nat,
  leaderConstants: seq<LeaderHost.Constants>,
  acceptorConstants: seq<AcceptorHost.Constants>,
  learnerConstants: seq<LearnerHost.Constants>
)
{
  ghost predicate WF() {
    && p1Quorum + p2Quorum == n+1  // quorum overlap rule
    && UniqueIds()
  }
  
  ghost predicate UniqueIds() {
    && UniqueLeaderIds()
    && UniqueAcceptorIds()
    && UniqueLearnerIds()
  }

  ghost predicate ValidLeaderIdx(id: int) {
    0 <= id < |leaderConstants|
  }

  ghost predicate ValidAcceptorIdx(id: int) {
    0 <= id < |acceptorConstants|
  }

  ghost predicate ValidLearnerIdx(id: int) {
    0 <= id < |learnerConstants|
  }
  
  ghost predicate UniqueLeaderIds() {
    forall i, j | ValidLeaderIdx(i) && ValidLeaderIdx(j) && leaderConstants[i].id == leaderConstants[j].id :: i == j
  }

  ghost predicate UniqueAcceptorIds() {
    forall i, j | ValidAcceptorIdx(i) && ValidAcceptorIdx(j) && acceptorConstants[i].id == acceptorConstants[j].id :: i == j
  }

  ghost predicate UniqueLearnerIds() {
    forall i, j | ValidLearnerIdx(i) && ValidLearnerIdx(j) && learnerConstants[i].id == learnerConstants[j].id :: i == j
  }
} // end datatype Constants

datatype Variables = Variables(
  leaders: seq<LeaderHost.Variables>,
  acceptors: seq<AcceptorHost.Variables>,
  learners: seq<LearnerHost.Variables>
)
{
  ghost predicate WF(c: Constants) {
    && c.WF()
    && LeaderHost.GroupWF(c.leaderConstants, leaders, c.p1Quorum)
    && AcceptorHost.GroupWF(c.acceptorConstants, acceptors, c.n)
    && LearnerHost.GroupWF(c.learnerConstants, learners, c.p2Quorum)
  }

  ghost predicate LeaderCanPropose(c: Constants, ldr: LeaderId) 
    requires WF(c)
    requires c.ValidLeaderIdx(ldr)
  {
    leaders[ldr].CanPropose(c.leaderConstants[ldr])
  }
} // end datatype Variables


//// System Transitions ////

ghost predicate Init(c: Constants, v: Variables) {
  && v.WF(c)
  && LeaderHost.GroupInit(c.leaderConstants, v.leaders, c.p1Quorum)
  && AcceptorHost.GroupInit(c.acceptorConstants, v.acceptors, c.n)
  && LearnerHost.GroupInit(c.learnerConstants, v.learners, c.p2Quorum)
}

datatype Step = 
  | P1aStep(leader: LeaderId, acceptor: AcceptorId, transmit: Transmit)
  | P1bStep(acceptor: AcceptorId, leader: LeaderId, transmit: Transmit)
  | P2aStep(leader: LeaderId, acceptor: AcceptorId, transmit: Transmit)
  | P2bStep(acceptor: AcceptorId, learner: LearnerId, transmit: Transmit)
  | LearnerInternalStep(learner: LearnerId)
  | StutterStep()


// Leader sends Prepare message to Acceptor. Acceptor buffers it in its pendingPrepare field 
ghost predicate NextP1aStep(c: Constants, v: Variables, v': Variables, ldr: LeaderId, acc: AcceptorId, transmit: Transmit) 
  requires v.WF(c) && v'.WF(c)
{
  // Leader action
  && c.ValidLeaderIdx(ldr)
  && transmit.m.Prepare?
  && LeaderHost.Next(c.leaderConstants[ldr], v.leaders[ldr], v'.leaders[ldr], transmit.Send())
  // Acceptor action
  && c.ValidAcceptorIdx(acc)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], transmit.Recv())
  // All others unchanged
  && AcceptorsUnchangedExcept(c, v, v', acc)
  && LeadersUnchangedExcept(c, v, v', ldr)
  && LearnersUnchanged(v, v')
}

// Acceptor processes its pendingPrepare, and maybe sends a Promise to the leader
ghost predicate NextP1bStep(c: Constants, v: Variables, v': Variables, 
    ldr: LeaderId, acc: AcceptorId, transmit: Transmit) 
  requires v.WF(c) && v'.WF(c)
{
  // Decide whether to send promise
  && c.ValidAcceptorIdx(acc)
  && v.acceptors[acc].pendingPrepare.Some?
  && var doPromise := v.acceptors[acc].promised.MNSome? ==> v.acceptors[acc].promised.value <  v.acceptors[acc].pendingPrepare.value.bal;
  && if doPromise then
      // Acceptor action
      && transmit.m.Promise?
      && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], transmit.Send())
      // Leader action
      && c.ValidLeaderIdx(ldr)
      && LeaderHost.Next(c.leaderConstants[ldr], v.leaders[ldr], v'.leaders[ldr], transmit.Recv())
      // All others unchanged
      && LeadersUnchangedExcept(c, v, v', ldr)
      && AcceptorsUnchangedExcept(c, v, v', acc)
      && LearnersUnchanged(v, v')
  else
      // Acceptor action
      && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], MessageOps(None, None))
      // Leader action
      && c.ValidLeaderIdx(ldr)
      && LeadersUnchanged(v, v')
      // All others unchanged
      && LeadersUnchangedExcept(c, v, v', ldr)
      && AcceptorsUnchangedExcept(c, v, v', acc)
      && LearnersUnchanged(v, v')
}

// Leader sends Proposal to an acceptor. The acceptor processes the proposal
ghost predicate NextP2aStep(c: Constants, v: Variables, v': Variables, 
    ldr: LeaderId, acc: AcceptorId, transmit: Transmit) 
  requires v.WF(c) && v'.WF(c)
{
  // Leader action
  && c.ValidLeaderIdx(ldr)
  && transmit.m.Propose?
  && LeaderHost.Next(c.leaderConstants[ldr], v.leaders[ldr], v'.leaders[ldr], transmit.Send())
  // Acceptor action
  && c.ValidAcceptorIdx(acc)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], transmit.Recv())
  // All others unchanged
  && LeadersUnchangedExcept(c, v, v', ldr)
  && AcceptorsUnchangedExcept(c, v, v', acc)
  && LearnersUnchanged(v, v')
}

// Acceptor sends acceptedVB to some Learner
ghost predicate NextP2bStep(c: Constants, v: Variables, v': Variables, 
    acc: AcceptorId, lnr: LearnerId, transmit: Transmit)
  requires v.WF(c) && v'.WF(c)
{
  // Acceptor action
  && c.ValidAcceptorIdx(acc)
  && transmit.m.Accept?
  && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], transmit.Send())
  // Learner action
  && c.ValidLearnerIdx(lnr)
  && LearnerHost.Next(c.learnerConstants[lnr], v.learners[lnr], v'.learners[lnr], transmit.Recv())
  // All others unchanged
  && LearnersUnchangedExcept(c, v, v', lnr)
  && AcceptorsUnchangedExcept(c, v, v', acc)
  && LeadersUnchanged(v, v')
}

ghost predicate NextLearnerInternalStep(c: Constants, v: Variables, v': Variables, lnr: LearnerId)
  requires v.WF(c) && v'.WF(c)
{
  // Learner action
  && c.ValidLearnerIdx(lnr)
  && LearnerHost.Next(c.learnerConstants[lnr], v.learners[lnr], v'.learners[lnr], MessageOps(None, None))
  // All others unchanged
  && LearnersUnchangedExcept(c, v, v', lnr)
  && LeadersUnchanged(v, v')
  && AcceptorsUnchanged(v, v')
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
    case P1aStep(ldr, acc, transmit) => NextP1aStep(c, v, v', ldr, acc, transmit)
    case P1bStep(acc, ldr, transmit) => NextP1bStep(c, v, v', ldr, acc, transmit)
    case P2aStep(ldr, acc, transmit) => NextP2aStep(c, v, v', ldr, acc, transmit)
    case P2bStep(acc, lnr, transmit) => NextP2bStep(c, v, v', acc, lnr, transmit)
    case LearnerInternalStep(lnr) => NextLearnerInternalStep(c, v, v', lnr)
    case StutterStep => v' == v
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && exists step :: NextStep(c, v, v', step)
}


//// Helper Functions ////

ghost predicate LeadersUnchanged(v: Variables, v': Variables) {
  v'.leaders == v.leaders
}

ghost predicate LeadersUnchangedExcept(c: Constants, v: Variables, v': Variables, ldr: LeaderId)
  requires v.WF(c) && v'.WF(c)
  requires c.ValidLeaderIdx(ldr)
{
  forall id:nat | c.ValidLeaderIdx(id) && id != ldr
  :: v.leaders[id] == v'.leaders[id]
}

ghost predicate AcceptorsUnchanged(v: Variables, v': Variables) {
  v'.acceptors == v.acceptors
}

ghost predicate AcceptorsUnchangedExcept(c: Constants, v: Variables, v': Variables, acc: AcceptorId)
  requires v.WF(c) && v'.WF(c)
  requires c.ValidAcceptorIdx(acc)
{
  forall id:nat | c.ValidAcceptorIdx(id) && id != acc
  :: v.acceptors[id] == v'.acceptors[id]
}

ghost predicate LearnersUnchanged(v: Variables, v': Variables) {
  v'.learners == v.learners
}

ghost predicate LearnersUnchangedExcept(c: Constants, v: Variables, v': Variables, lnr: LearnerId)
  requires v.WF(c) && v'.WF(c)
  requires c.ValidLearnerIdx(lnr)
{
  forall id:nat | c.ValidLearnerIdx(id) && id != lnr
  :: v.learners[id] == v'.learners[id]
}


} // end module System