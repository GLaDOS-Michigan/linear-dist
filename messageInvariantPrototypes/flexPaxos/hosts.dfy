include "types.dfy"


/***************************************************************************************
*                                      Leader Host                                     *
***************************************************************************************/

module LeaderHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LeaderId, p1Quorum: nat, preferredValue: Value)

  ghost predicate ConstantsValidForLeader(c: Constants, id: LeaderId, p1Quorum: nat) {
    && c.id == id
    && c.p1Quorum == p1Quorum
  }

  datatype Variables = Variables(
    receivedPromises: set<AcceptorId>, 
    value: Value, 
    highestHeardBallot: Option<LeaderId>) 
  {

    // My highestHeardBallot >= b
    ghost predicate HeardAtLeast(b: LeaderId) {
      highestHeardBallot.Some? && highestHeardBallot.value >= b
    }
    
    // My highestHeardBallot < b
    ghost predicate HeardAtMost(b: LeaderId) {
      highestHeardBallot.None? || highestHeardBallot.value < b
    }

    ghost predicate CanPropose(c: Constants) {
      && |receivedPromises| >= c.p1Quorum
      // Enabling condition that my hightest heard 
      // is smaller than my own ballot. Not a safety issue, but can probably simplify proof.
      // It is equivalent to being preempted
      && HeardAtMost(c.id)
    }
  } // end datatype Variables (Leader)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, p1Quorum: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLeader(grp_c[idx], idx, p1Quorum))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, p1Quorum: nat) {
    && 0 < p1Quorum
    && GroupWFConstants(grp_c, p1Quorum)
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, p1Quorum: nat) 
    requires GroupWF(grp_c, grp_v, p1Quorum)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedPromises == {}
    && v.value == c.preferredValue
    && v.highestHeardBallot == None
  }

  datatype Step =
    PrepareStep() | ReceiveStep() | ProposeStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case PrepareStep => NextPrepareStep(c, v, v', msgOps)
      case ReceiveStep => NextReceivePromiseStep(c, v, v', msgOps)
      case ProposeStep => NextProposeStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextPrepareStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendPrepare(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendPrepare(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && true
    // send message and update v'
    && msg == Prepare(c.id)
    && v' == v
  }

  ghost predicate NextReceivePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && ReceivePromise(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceivePromise(c: Constants, v: Variables, v': Variables, msg: Message) {
    && msg.Promise?
    && var bal := msg.bal;
    && var acc := msg.acc;
    && var vbOpt := msg.vbOpt;
    && bal == c.id  // message is meant for me
    // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
    // probably simplify proof, preventing the leader from potentially equivocating
    // on its proposed value after receiving extraneous straggling promises.
    && |v.receivedPromises| < c.p1Quorum
    && acc !in v.receivedPromises
    && var doUpdate := 
          && vbOpt.Some? 
          && v.HeardAtMost(vbOpt.value.b);
    v' == v.(
              receivedPromises := v.receivedPromises + {acc},
              value :=  if doUpdate then vbOpt.value.v else v.value,
              highestHeardBallot := if doUpdate then Some(vbOpt.value.b) else v.highestHeardBallot
            )
  }

  // Receive predicate trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceivePromiseTrigger(c: Constants, v: Variables, acc: AcceptorId) {
    && acc in v.receivedPromises
  }

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendPropose(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendPropose(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.CanPropose(c)
    // send message and update v'
    && msg == Propose(c.id, v.value)
    && v' == v
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
    && msgOps.recv == None
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LeaderHost


/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/

module AcceptorHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: AcceptorId)

  ghost predicate ConstantsValidForAcceptor(c: Constants, id: AcceptorId) {
    && c.id == id
  }

  datatype PendingPrepare = Prepare(bal:LeaderId)

  datatype Variables = Variables(
    pendingPrepare: Option<PendingPrepare>,
    promised: Option<LeaderId>,
    acceptedVB: Option<ValBal>) 
  {

    ghost predicate HasAccepted(vb: ValBal) {
      && acceptedVB.Some?
      && acceptedVB.value == vb
    }

    ghost predicate HasAcceptedValue(v: Value) {
      && acceptedVB.Some?
      && acceptedVB.value.v == v
    }

    ghost predicate HasPromisedAtLeast(b: LeaderId) {
      && promised.Some?
      && b <= promised.value
    }

    ghost predicate HasPromised(b: LeaderId) {
      && promised.Some?
      && b == promised.value
    }

    ghost predicate HasAcceptedAtLeastBal(b: LeaderId) {
      && acceptedVB.Some?
      && b <= acceptedVB.value.b
    }

    ghost predicate HasAcceptedAtMostBal(b: LeaderId) {
      acceptedVB.Some? ==> acceptedVB.value.b < b
    }
  } // end datatype Variables (acceptor)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForAcceptor(grp_c[idx], idx))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, n: nat) {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c| == n
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, n: nat) 
    requires GroupWF(grp_c, grp_v, n)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.promised == None
    && v.acceptedVB == None
    && v.pendingPrepare == None
  }

  datatype Step =
    ReceivePrepareStep() 
    | MaybePromiseStep() 
    | MaybeAcceptStep() 
    | BroadcastAcceptedStep() 
    | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceivePrepareStep => NextReceivePrepareStep(c, v, v', msgOps)
      case MaybePromiseStep => NextMaybePromiseStep(c, v, v', msgOps)
      case MaybeAcceptStep => NextMaybeAcceptStep(c, v, v', msgOps)
      case BroadcastAcceptedStep => NextBroadcastAcceptedStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextReceivePrepareStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && msgOps.recv.value.Prepare?
    && v.pendingPrepare.None?
    && v' == v.(
      pendingPrepare := Some(PendingPrepare.Prepare(msgOps.recv.value.bal))
    )
  }

  ghost predicate NextMaybePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.None?
    && v.pendingPrepare.Some?
    && var bal := v.pendingPrepare.value.bal;
    && var doPromise := v.promised.None? || (v.promised.Some? && v.promised.value < bal);
    && if doPromise then
          && msgOps.send.Some?
          && SendPromise(c, v, v', msgOps.send.value)
        else
          && v' == v.(pendingPrepare := None)
          && msgOps.send == None
  }

  // Send predicate
  ghost predicate SendPromise(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.pendingPrepare.Some?
    && var bal := v.pendingPrepare.value.bal;
    && var doPromise := v.promised.None? || (v.promised.Some? && v.promised.value < bal);
    && doPromise
    // send message and update v'
    && v' == v.(
            promised := Some(bal),
            pendingPrepare := None)
    && msg == Promise(bal, c.id, v.acceptedVB)
  }

  ghost predicate NextMaybeAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && msgOps.recv.value.Propose?
    && v.pendingPrepare.None?
    && var bal := msgOps.recv.value.bal;
    && var val := msgOps.recv.value.val;
    && var doAccept := v.promised.None? || (v.promised.Some? && v.promised.value <= bal);
    &&  if doAccept then
          && v' == v.(
                promised := Some(bal), 
                acceptedVB := Some(VB(val, bal)))
        else
          && v' == v
  }

  ghost predicate NextBroadcastAcceptedStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv == None
    && msgOps.send.Some?
    && SendAccept(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendAccept(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.pendingPrepare.None?
    && v.acceptedVB.Some?
    && v.promised == Some(v.acceptedVB.value.b)
    // send message and update v'
    && msg == Accept(v.acceptedVB.value, c.id)
    && v' == v
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send == None
    && msgOps.recv == None
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }

  lemma UpdateReceiveAcceptedStep(c: Constants, v: Variables, v': Variables, 
    step: Step, msgOps: MessageOps)
    requires NextStep(c, v, v', step, msgOps)
    requires !step.MaybeAcceptStep?
    ensures v'.acceptedVB == v.acceptedVB
  {}
}  // end module AcceptorHost


/***************************************************************************************
*                                     Learner Host                                     *
***************************************************************************************/

module LearnerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LearnerId, p2Quorum: nat)

  ghost predicate ConstantsValidForLearner(c: Constants, id: LearnerId, p2Quorum: nat) {
    && c.id == id
    && c.p2Quorum == p2Quorum
  }

  datatype Variables = Variables(
    // maps ValBal to acceptors that accepted such pair
    receivedAccepts: map<ValBal, set<AcceptorId>>,
    learned: Option<Value>
  ) {
    
    ghost predicate HasLearnedValue(v: Value) {
      learned == Some(v)
    }
  } // end datatype Variables (Learner)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, p2Quorum: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLearner(grp_c[idx], idx, p2Quorum))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, p2Quorum: nat) {
    && 0 < p2Quorum
    && GroupWFConstants(grp_c, p2Quorum)
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, p2Quorum: nat) 
    requires GroupWF(grp_c, grp_v, p2Quorum)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedAccepts == map[]
    && v.learned == None
  }

  datatype Step =
    ReceiveStep() | LearnStep(vb: ValBal) | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveAcceptStep(c, v, v', msgOps)
      case LearnStep(vb) => NextLearnStep(c, v, v', vb, msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  function UpdateReceivedAccepts(receivedAccepts: map<ValBal, set<AcceptorId>>, 
    vb: ValBal, acc: AcceptorId) : (out: map<ValBal, set<AcceptorId>>)
    // Tony: ensures clauses are exactly how I can prove to the user, and tell dafny, that 
    // data structures annotated as monotonic actually are monotonic --- cool!
    ensures vb in receivedAccepts ==> vb in out
    ensures vb in receivedAccepts ==> |receivedAccepts[vb]| <= |out[vb]|
  {
    if vb in receivedAccepts then 
      UnionIncreasesCardinality(receivedAccepts[vb], {acc});
      receivedAccepts[vb := receivedAccepts[vb] + {acc}]
    else 
      receivedAccepts[vb := {acc}]
  }

  ghost predicate NextReceiveAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && ReceiveAccept(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveAccept(c: Constants, v: Variables, v': Variables, msg: Message) {
    && msg.Accept?
    && v' == v.(
      receivedAccepts := UpdateReceivedAccepts(v.receivedAccepts, msg.vb, msg.acc)
    )
  }

  // Receive predicate trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveAcceptTrigger(c: Constants, v: Variables, acc: AcceptorId, vb: ValBal) {
    && vb in v.receivedAccepts
    && acc in v.receivedAccepts[vb]
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.None?
    && vb in v.receivedAccepts                  // enabling
    && |v.receivedAccepts[vb]| >= c.p2Quorum    // enabling
    && v' == v.(learned := Some(vb.v))          // learn new value
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.None?
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LearnerHost