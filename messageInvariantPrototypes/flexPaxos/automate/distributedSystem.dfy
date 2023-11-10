include "../hosts.dfy"

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
    p1Quorum: nat,
    p2Quorum: nat,
    n: nat,
    leaders: seq<LeaderHost.Constants>,
    acceptors: seq<AcceptorHost.Constants>,
    learners: seq<LearnerHost.Constants>
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
      0 <= id < |leaders|
    }

    ghost predicate ValidAcceptorIdx(id: int) {
      0 <= id < |acceptors|
    }

    ghost predicate ValidLearnerIdx(id: int) {
      0 <= id < |learners|
    }
    
    ghost predicate UniqueLeaderIds() {
      forall i, j | ValidLeaderIdx(i) && ValidLeaderIdx(j) && leaders[i].id == leaders[j].id :: i == j
    }

    ghost predicate UniqueAcceptorIds() {
      forall i, j | ValidAcceptorIdx(i) && ValidAcceptorIdx(j) && acceptors[i].id == acceptors[j].id :: i == j
    }

    ghost predicate UniqueLearnerIds() {
      forall i, j | ValidLearnerIdx(i) && ValidLearnerIdx(j) && learners[i].id == learners[j].id :: i == j
    }
  }

  datatype Hosts = Hosts(
    leaders: seq<LeaderHost.Variables>,
    acceptors: seq<AcceptorHost.Variables>,
    learners: seq<LearnerHost.Variables>
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && LeaderHost.GroupWF(c.leaders, leaders, c.p1Quorum)
      && AcceptorHost.GroupWF(c.acceptors, acceptors, c.n)
      && LearnerHost.GroupWF(c.learners, learners, c.p2Quorum)
    }

    ghost predicate LeaderCanPropose(c: Constants, ldr: LeaderId) 
      requires WF(c)
      requires c.ValidLeaderIdx(ldr)
    {
      leaders[ldr].CanPropose(c.leaders[ldr])
    }
  }

  datatype Variables = Variables(
    history: seq<Hosts>,
    network: Network.Variables
  ) {

    ghost predicate ValidHistoryIdx(i: int) {
      0 <= i < |history|
    }

    ghost predicate ValidHistoryIdxStrict(i: int) {
      0 <= i < |history|-1
    }

    ghost predicate WF(c: Constants) {
      && c.WF()
      && 0 < |history|
      && (forall i | ValidHistoryIdx(i) :: history[i].WF(c))
    }

    ghost function Last() : (h: Hosts)
      requires 0 < |history|
      ensures h == history[|history|-1]
      ensures h == History(|history|-1)
    {
      UtilitiesLibrary.Last(history)
    }

    ghost function History(i: int) : (h: Hosts)
      requires ValidHistoryIdx(i)
      ensures h == history[i]
    {
      history[i]
    }

    ghost function Truncate(c: Constants, i: int) : (v : Variables)
      requires WF(c)
      requires ValidHistoryIdx(i)
      ensures v.WF(c)
      ensures v.Last() == History(i)
    {
      Variables.Variables(history[..i+1], network)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  ghost predicate InitHosts(c: Constants, h: Hosts) 
    requires h.WF(c)
  {
    && LeaderHost.GroupInit(c.leaders, h.leaders, c.p1Quorum)
    && AcceptorHost.GroupInit(c.acceptors, h.acceptors, c.n)
    && LearnerHost.GroupInit(c.learners, h.learners, c.p2Quorum)
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
    && LeaderHost.Next(c.leaders[actor], h.leaders[actor], h'.leaders[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall other| c.ValidLeaderIdx(other) && other != actor :: h'.leaders[other] == h.leaders[other])
    && h'.acceptors == h.acceptors
    && h'.learners == h.learners
  }

  ghost predicate NextAcceptorStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps) 
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidAcceptorIdx(actor)
    && AcceptorHost.Next(c.acceptors[actor], h.acceptors[actor], h'.acceptors[actor], msgOps)
    // all other hosts UNCHANGED
    && h'.leaders == h.leaders
    && (forall other| c.ValidAcceptorIdx(other) && other != actor :: h'.acceptors[other] == h.acceptors[other])
    && h'.learners == h.learners
  }

  ghost predicate NextLearnerStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps) 
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidLearnerIdx(actor)
    && LearnerHost.Next(c.learners[actor], h.learners[actor], h'.learners[actor], msgOps)
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


/***************************************************************************************
*                                Variable properties                                   *
***************************************************************************************/

  ghost predicate {:opaque} ValidHistory(c: Constants, v: Variables)
    requires v.WF(c)
  {
    InitHosts(c, v.History(0))
  }
  
  ghost predicate ValidVariables(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    && ValidHistory(c, v)
  }

  lemma InitImpliesValidVariables(c: Constants, v: Variables)
    requires Init(c, v)
    ensures ValidHistory(c, v)
  {
    reveal_ValidHistory();
  }


  lemma InvNextValidVariables(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires ValidHistory(c, v)
    requires Next(c, v, v')
    ensures ValidHistory(c, v')
  {
    reveal_ValidHistory();
    VariableNextProperties(c, v, v');
  }

  lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires Next(c, v, v')
    ensures 1 < |v'.history|
    ensures |v.history| == |v'.history| - 1
    ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)
    ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)
  {
    assert 0 < |v.history|;
    assert 1 < |v'.history|;
  }
}  // end module DistributedSystem