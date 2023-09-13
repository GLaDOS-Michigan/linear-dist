include "hosts.dfy"

module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
} // end module Network


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import opened Network
  import LeaderHost
  import AcceptorHost
  import LearnerHost

  datatype Constants = Constants(
    f: nat,
    leaderConstants: seq<LeaderHost.Constants>,
    acceptorConstants: seq<AcceptorHost.Constants>,
    learnerConstants: seq<LearnerHost.Constants>)
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
  }

  datatype Hosts = Hosts(
    leaders: seq<LeaderHost.Variables>,
    acceptors: seq<AcceptorHost.Variables>,
    learners: seq<LearnerHost.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
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
    history: seq<Hosts>,
    network: Network.Variables
  ) {

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
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && LeaderHost.GroupInit(c.leaderConstants, v.history[0].leaders, c.f)
    && AcceptorHost.GroupInit(c.acceptorConstants, v.history[0].acceptors, c.f)
    && LearnerHost.GroupInit(c.learnerConstants, v.history[0].learners, c.f)

    && Network.Init(v.network)
  }
  
  datatype Step = 
    LeaderStep(actor: nat, msgOps: MessageOps)
    | AcceptorStep(actor: nat, msgOps: MessageOps)
    | LearnerStep(actor: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step 
      case LeaderStep(actor, msgOps) => NextLeaderStep(c, h, h', actor, msgOps)
      case AcceptorStep(actor, msgOps) => NextAcceptorStep(c, h, h', actor, msgOps)
      case LearnerStep(actor, msgOps) => NextLearnerStep(c, h, h', actor, msgOps)
  }

  ghost predicate NextLeaderStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps) 
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidLeaderIdx(actor)
    && LeaderHost.Next(c.leaderConstants[actor], h.leaders[actor], h'.leaders[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall other| c.ValidLeaderIdx(other) && other != actor :: h'.leaders[other] == h.leaders[other])
    && h'.acceptors == h.acceptors
    && h'.learners == h.learners
  }

  ghost predicate NextAcceptorStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps) 
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidAcceptorIdx(actor)
    && AcceptorHost.Next(c.acceptorConstants[actor], h.acceptors[actor], h'.acceptors[actor], msgOps)
    // all other hosts UNCHANGED
    && h'.leaders == h.leaders
    && (forall other| c.ValidAcceptorIdx(other) && other != actor :: h'.acceptors[other] == h.acceptors[other])
    && h'.learners == h.learners
  }

  ghost predicate NextLearnerStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps) 
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidLearnerIdx(actor)
    && LearnerHost.Next(c.learnerConstants[actor], h.learners[actor], h'.learners[actor], msgOps)
    // all other hosts UNCHANGED
    && h'.leaders == h.leaders
    && h'.acceptors == h.acceptors
    && (forall other| c.ValidLearnerIdx(other) && other != actor :: h'.learners[other] == h.learners[other])
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && IsSeqExtension(v.history, v'.history)
    && exists step :: NextStep(c, v.Last(), v'.Last(), v.network, v'.network, step)
  }
}  // end module DistributedSystem