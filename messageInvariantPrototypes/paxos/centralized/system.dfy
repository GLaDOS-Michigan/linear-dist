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

datatype Variables = Variables(
  leaders: seq<LeaderHost.Variables>,
  acceptors: seq<AcceptorHost.Variables>,
  learners: seq<LearnerHost.Variables>
)
{
  ghost predicate WF(c: Constants) {
    && c.WF()
    && LeaderHost.GroupWF(c.leaderConstants, leaders, c.f)
    && AcceptorHost.GroupWF(c.acceptorConstants, acceptors, c.f)
    && LearnerHost.GroupWF(c.learnerConstants, learners, c.f)
  }
} // end datatype Variables


//// System Transitions ////

ghost predicate Init(c: Constants, v: Variables) {
  && v.WF(c)
  && LeaderHost.GroupInit(c.leaderConstants, v.leaders, c.f)
  && AcceptorHost.GroupInit(c.acceptorConstants, v.acceptors, c.f)
  && LearnerHost.GroupInit(c.learnerConstants, v.learners, c.f)
}

datatype Step = 
  | P1aStep(leader: LeaderId, acceptor: AcceptorId)
  | P1bStep(acceptor: AcceptorId, leader: LeaderId, balOpt:Option<LeaderId>, vbOptOpt:Option<Option<ValBal>>)
  | P2aStep(leader: LeaderId, acceptor: AcceptorId, val: Value)
  | P2bStep(acceptor: AcceptorId, learner: LearnerId, vbOpt: Option<ValBal>)
  | StutterStep()

ghost predicate NextP1aStep(c: Constants, v: Variables, v': Variables, ldr: LeaderId, acc: AcceptorId) 
  requires v.WF(c) && v'.WF(c)
{
  var ldrLbl := LeaderHost.InternalLbl();
  var accLbl := AcceptorHost.ReceivePrepareLbl(ldr);
  && c.ValidLeaderIdx(ldr)
  && c.ValidAcceptorIdx(acc)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], accLbl)
  && AcceptorsUnchangedExcept(c, v, v', acc)
  && LeadersUnchanged(v, v')
  && LearnersUnchanged(v, v')
}

ghost predicate NextP1bStep(c: Constants, v: Variables, v': Variables, 
    ldr: LeaderId, acc: AcceptorId,
    balOpt: Option<LeaderId>, vbOptOpt: Option<Option<ValBal>>) 
  requires v.WF(c) && v'.WF(c)
{
  var accLbl := AcceptorHost.MaybePromiseLbl(balOpt, vbOptOpt);
  && c.ValidLeaderIdx(ldr)
  && c.ValidAcceptorIdx(acc)
  && AcceptorHost.Next(c.acceptorConstants[acc], v.acceptors[acc], v'.acceptors[acc], accLbl)
  && AcceptorsUnchangedExcept(c, v, v', acc)
  && LearnersUnchanged(v, v')
  && if balOpt.Some? then
        && assert vbOptOpt.Some?;  // Tony: I am surprised Dafny sees this
        && var ldrLbl := LeaderHost.ReceivePromiseLbl(acc, vbOptOpt.value);
        && ldr == balOpt.value
        && LeaderHost.Next(c.leaderConstants[ldr], v.leaders[ldr], v'.leaders[ldr], ldrLbl)
        && LeadersUnchangedExcept(c, v, v', ldr)
      else 
        LeadersUnchanged(v, v')
}





ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
    case P1aStep(ldr, acc) => NextP1aStep(c, v, v', ldr, acc)
    case P1bStep(acc, ldr, balOpt, vbOptOpt) => NextP1bStep(c, v, v', acc, ldr, balOpt, vbOptOpt)
    case P2aStep(ldr, acc, val) => v' == v
    case P2bStep(acc, lnr, vbOpt) => v' == v
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