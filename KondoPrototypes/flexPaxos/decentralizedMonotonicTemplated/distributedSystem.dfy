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
  }

  datatype Hosts = Hosts(
    leaders: seq<LeaderHost.Variables>,
    acceptors: seq<AcceptorHost.Variables>,
    learners: seq<LearnerHost.Variables>
  ) {
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
    && LeaderHost.GroupInit(c.leaderConstants, h.leaders, c.p1Quorum)
    && AcceptorHost.GroupInit(c.acceptorConstants, h.acceptors, c.n)
    && LearnerHost.GroupInit(c.learnerConstants, h.learners, c.p2Quorum)
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


/***************************************************************************************
*                                 History properties                                   *
***************************************************************************************/

  ghost predicate {:opaque} ValidHistory(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && InitHosts(c, v.History(0))
    && forall i | v.ValidHistoryIdxStrict(i)
      ::
      Next(c, v.Truncate(c, i), v.Truncate(c, i+1))
  }

  ghost predicate IsReceiveStepByActor(c: Constants, v: Variables, i:int, actor: int, msg: Message)
    requires v.WF(c)
    requires v.ValidHistoryIdxStrict(i)
    requires Next(c, v.Truncate(c, i), v.Truncate(c, i+1))
  {
    var step :| NextStep(c, v.Truncate(c, i).Last(), v.Truncate(c, i+1).Last(), v.network, v.network, step);
    && step.msgOps.recv == Some(msg)
    && step.actor == actor
  }

  lemma InitImpliesValidHistory(c: Constants, v: Variables)
    requires Init(c, v)
    ensures ValidHistory(c, v)
  {
    reveal_ValidHistory();
  }

  lemma InvNextValidHistory(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires ValidHistory(c, v)
    requires Next(c, v, v')
    ensures ValidHistory(c, v')
  {
    reveal_ValidHistory();
    VariableNextProperties(c, v, v');
    forall i | v'.ValidHistoryIdxStrict(i)
    ensures Next(c, v'.Truncate(c, i), v'.Truncate(c, i+1))
    {
      if i == |v'.history| - 2 {
        MessageContainmentPreservesNext(c, v, v', v'.Truncate(c, i), v'.Truncate(c, i+1));
        assert Next(c, v'.Truncate(c, i), v'.Truncate(c, i+1));
      } else {
        assert Next(c, v.Truncate(c, i), v.Truncate(c, i+1));
        assert v.Truncate(c, i).network.sentMsgs <= v'.Truncate(c, i).network.sentMsgs;
        MessageContainmentPreservesNext(c, v.Truncate(c, i), v.Truncate(c, i+1), v'.Truncate(c, i), v'.Truncate(c, i+1));
        assert Next(c, v'.Truncate(c, i), v'.Truncate(c, i+1));
      }
    }
  }

  lemma MessageContainmentPreservesNext(c: Constants, v: Variables, v': Variables, s: Variables, s': Variables)
    requires v.WF(c)
    requires s.WF(c)
    requires Next(c, v, v')
    requires v.history == s.history
    requires v'.history == s'.history
    requires v'.network.sentMsgs <= s'.network.sentMsgs
    requires s.network.sentMsgs == s'.network.sentMsgs
    ensures Next(c, s, s')
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    assert NextStep(c, s.Last(), s'.Last(), s.network, s'.network, dsStep); // trigger
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