include "hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import LeaderHost
  import AcceptorHost
  import LearnerHost

datatype Constants = Constants(
  f: nat,
  leaderConstants: seq<LeaderHost.Constants>,
  acceptorConstants: seq<AcceptorHost.Constants>,
  learnerConstants: seq<LearnerHost.Constants>
)
{
  ghost predicate WF() {
    && 0 < f
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

datatype Hosts = Hosts(
  leaders: seq<LeaderHost.Variables>,
  acceptors: seq<AcceptorHost.Variables>,
  learners: seq<LearnerHost.Variables>
) {
  ghost predicate WF(c: Constants) {
    && LeaderHost.GroupWF(c.leaderConstants, leaders, c.f)
    && AcceptorHost.GroupWF(c.acceptorConstants, acceptors, c.f)
    && LearnerHost.GroupWF(c.learnerConstants, learners, c.f)
  }

  ghost predicate LeaderCanPropose(c: Constants, ldr: LeaderId) 
    requires WF(c)
    requires c.ValidLeaderIdx(ldr)
  {
    leaders[ldr].CanPropose(c.leaderConstants[ldr])
  }
}

datatype Variables = Variables(
  history: seq<Hosts>
)
{
  ghost predicate ValidHistoryIdx(i: int) {
    0 <= i < |history|
  }

  ghost predicate WF(c: Constants) {
    && c.WF()
    && 0 < |history|
    && (forall i | ValidHistoryIdx(i) :: history[i].WF(c))
  }

  ghost function Last() : Hosts 
    requires 0 < |history|
  {
    UtilitiesLibrary.Last(history)
  }
} // end datatype Variables


//// System Transitions ////

ghost predicate Init(c: Constants, v: Variables) {
  && v.WF(c)
  && |v.history| == 1
  && LeaderHost.GroupInit(c.leaderConstants, v.history[0].leaders, c.f)
  && AcceptorHost.GroupInit(c.acceptorConstants, v.history[0].acceptors, c.f)
  && LearnerHost.GroupInit(c.learnerConstants, v.history[0].learners, c.f)
}

datatype Step = 
  | P1aStep(leader: LeaderId, acceptor: AcceptorId)
  | P1bStep(acceptor: AcceptorId, leader: LeaderId, balOpt:Option<LeaderId>, vbOptOpt:Option<Option<ValBal>>)
  | P2aStep(leader: LeaderId, acceptor: AcceptorId, val: Value)
  | P2bStep(acceptor: AcceptorId, learner: LearnerId, acceptedVb: ValBal)
  | LearnerInternalStep(learner: LearnerId)
  | StutterStep()


// Leader sends Prepare message to Acceptor. Acceptor buffers it in its pendingPrepare field 
ghost predicate NextP1aStep(c: Constants, v: Variables, v': Variables, ldr: LeaderId, acc: AcceptorId) 
  requires v.WF(c) && v'.WF(c)
{
  var ldrLbl := LeaderHost.PrepareLbl();
  var accLbl := AcceptorHost.ReceivePrepareLbl(ldr);
  && c.ValidLeaderIdx(ldr)
  && c.ValidAcceptorIdx(acc)
  && IsSeqExtension(v.history, v'.history)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.Last().acceptors[acc], v'.Last().acceptors[acc], accLbl)
  && AcceptorsUnchangedExcept(c, v.Last(), v'.Last(), acc)
  && LeaderHost.Next(c.leaderConstants[ldr], v.Last().leaders[ldr], v'.Last().leaders[ldr], ldrLbl)
  && LeadersUnchangedExcept(c, v.Last(), v'.Last(), ldr)
  && LearnersUnchanged(v.Last(), v'.Last())
}

// Acceptor processes its pendingPrepare, and maybe sends a Promise to the leader
ghost predicate NextP1bStep(c: Constants, v: Variables, v': Variables, 
    ldr: LeaderId, acc: AcceptorId,
    balOpt: Option<LeaderId>, vbOptOpt: Option<Option<ValBal>>) 
  requires v.WF(c) && v'.WF(c)
{
  var accLbl := AcceptorHost.MaybePromiseLbl(balOpt, vbOptOpt);
  && c.ValidLeaderIdx(ldr)
  && c.ValidAcceptorIdx(acc)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.Last().acceptors[acc], v'.Last().acceptors[acc], accLbl)
  && AcceptorsUnchangedExcept(c, v.Last(), v'.Last(), acc)
  && LearnersUnchanged(v.Last(), v'.Last())
  && if balOpt.Some? then
        // assert vbOptOpt.Some?;
        && var ldrLbl := LeaderHost.ReceivePromiseLbl(acc, vbOptOpt.value);
        && ldr == balOpt.value
        && LeaderHost.Next(c.leaderConstants[ldr], v.Last().leaders[ldr], v'.Last().leaders[ldr], ldrLbl)
        && LeadersUnchangedExcept(c, v.Last(), v'.Last(), ldr)
      else 
        LeadersUnchanged(v.Last(), v'.Last())
}

// Leader sends Proposal to an acceptor. The acceptor processes the proposal
ghost predicate NextP2aStep(c: Constants, v: Variables, v': Variables, 
    ldr: LeaderId, acc: AcceptorId,
    val: Value) 
  requires v.WF(c) && v'.WF(c)
{
  var ldrLbl := LeaderHost.ProposeLbl(val);
  var accLbl := AcceptorHost.MaybeAcceptLbl(ldr, val);
  && c.ValidLeaderIdx(ldr)
  && c.ValidAcceptorIdx(acc)
  && LeaderHost.Next(c.leaderConstants[ldr], v.Last().leaders[ldr], v'.Last().leaders[ldr], ldrLbl)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.Last().acceptors[acc], v'.Last().acceptors[acc], accLbl)
  && LeadersUnchangedExcept(c, v.Last(), v'.Last(), ldr)
  && AcceptorsUnchangedExcept(c, v.Last(), v'.Last(), acc)
  && LearnersUnchanged(v.Last(), v'.Last())
}

// Acceptor sends acceptedVB to some Learner
ghost predicate NextP2bStep(c: Constants, v: Variables, v': Variables, 
    acc: AcceptorId, lnr: LearnerId,
    acceptedVb: ValBal)
  requires v.WF(c) && v'.WF(c)
{
  var accLbl := AcceptorHost.BroadcastAcceptedLbl(acceptedVb);
  var lnrLbl := LearnerHost.ReceiveAcceptLbl(acceptedVb, acc);
  && c.ValidAcceptorIdx(acc)
  && c.ValidLearnerIdx(lnr)
  // acceptor simply stutters
  && AcceptorHost.Next(c.acceptorConstants[acc], v.Last().acceptors[acc], v'.Last().acceptors[acc], accLbl)
  && AcceptorsUnchangedExcept(c, v.Last(), v'.Last(), acc)
  && LeadersUnchanged(v.Last(), v'.Last())
  // learner receives accepted vb from acceptor
  && LearnerHost.Next(c.learnerConstants[lnr], v.Last().learners[lnr], v'.Last().learners[lnr], lnrLbl)
  && LearnersUnchangedExcept(c, v.Last(), v'.Last(), lnr)
}

ghost predicate NextLearnerInternalStep(c: Constants, v: Variables, v': Variables, lnr: LearnerId)
  requires v.WF(c) && v'.WF(c)
{
  var lnrLbl := LearnerHost.InternalLbl();
  && c.ValidLearnerIdx(lnr)
  && LearnerHost.Next(c.learnerConstants[lnr], v.Last().learners[lnr], v'.Last().learners[lnr], lnrLbl)
  && LearnersUnchangedExcept(c, v.Last(), v'.Last(), lnr)
  && LeadersUnchanged(v.Last(), v'.Last())
  && AcceptorsUnchanged(v.Last(), v'.Last())
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
    case P1aStep(ldr, acc) => NextP1aStep(c, v, v', ldr, acc)
    case P1bStep(acc, ldr, balOpt, vbOptOpt) => NextP1bStep(c, v, v', ldr, acc, balOpt, vbOptOpt)
    case P2aStep(ldr, acc, val) => NextP2aStep(c, v, v', ldr, acc, val)
    case P2bStep(acc, lnr, vb) => NextP2bStep(c, v, v', acc, lnr, vb)
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

ghost predicate LeadersUnchanged(h: Hosts, h': Hosts) {
  h'.leaders == h.leaders
}

ghost predicate LeadersUnchangedExcept(c: Constants, h: Hosts, h': Hosts, ldr: LeaderId)
  requires h.WF(c) && h'.WF(c)
  requires c.ValidLeaderIdx(ldr)
{
  forall id:nat | c.ValidLeaderIdx(id) && id != ldr
  :: h.leaders[id] == h'.leaders[id]
}

ghost predicate AcceptorsUnchanged(h: Hosts, h': Hosts) {
  h'.acceptors == h.acceptors
}

ghost predicate AcceptorsUnchangedExcept(c: Constants, h: Hosts, h': Hosts, acc: AcceptorId)
  requires h.WF(c) && h'.WF(c)
  requires c.ValidAcceptorIdx(acc)
{
  forall id:nat | c.ValidAcceptorIdx(id) && id != acc
  :: h.acceptors[id] == h'.acceptors[id]
}

ghost predicate LearnersUnchanged(h: Hosts, h': Hosts) {
  h'.learners == h.learners
}

ghost predicate LearnersUnchangedExcept(c: Constants, h: Hosts, h': Hosts, lnr: LearnerId)
  requires h.WF(c) && h'.WF(c)
  requires c.ValidLearnerIdx(lnr)
{
  forall id:nat | c.ValidLearnerIdx(id) && id != lnr
  :: h.learners[id] == h'.learners[id]
}


} // end module System