include "types.dfy"


/***************************************************************************************
*                                      Leader Host                                     *
***************************************************************************************/

module LeaderHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LeaderId, f: nat, preferredValue: Value)

  ghost predicate ConstantsValidForLeader(c: Constants, id: LeaderId, f: nat) {
    && c.id == id
    && c.f == f
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
      && |receivedPromises| >= c.f+1
      // Enabling condition that my hightest heard 
      // is smaller than my own ballot. Not a safety issue, but can probably simplify proof.
      // It is equivalent to being preempted
      && HeardAtMost(c.id)
    }
  } // end datatype Variables (Leader)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLeader(grp_c[idx], idx, f))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
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
    && msgOps.send == Some(Prepare(c.id))
    && v' == v
  }

  ghost predicate NextReceivePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && msgOps.recv.value.Promise?
    && var bal := msgOps.recv.value.bal;
    && var acc := msgOps.recv.value.acc;
    && var vbOpt := msgOps.recv.value.vbOpt;
    && bal == c.id  // message is meant for me
    // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
    // probably simplify proof, preventing the leader from potentially equivocating
    // on its proposed value after receiving extraneous straggling promises.
    && |v.receivedPromises| <= c.f
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

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && v.CanPropose(c)
    && msgOps.send == Some(Propose(c.id, v.value))
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

    ghost predicate HasAcceptedAtLeastBal(b: LeaderId) {
      && acceptedVB.Some?
      && b <= acceptedVB.value.b
    }

    ghost predicate HasAcceptedAtMostBal(b: LeaderId) {
      && acceptedVB.Some?
      && acceptedVB.value.b < b
    }
  } // end datatype Variables (acceptor)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForAcceptor(grp_c[idx], idx))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c| == 2*f+1
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
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
          && v' == v.(
            promised := Some(bal),
            pendingPrepare := None)
          && msgOps.send == Some(Promise(bal, c.id, v.acceptedVB)) 
        else
          && v' == v.(pendingPrepare := None)
          && msgOps.send == None
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
    && v.pendingPrepare.None?
    && v.acceptedVB.Some?
    && msgOps.send == Some(Accept(v.acceptedVB.value, c.id))
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
}  // end module AcceptorHost


/***************************************************************************************
*                                     Learner Host                                     *
***************************************************************************************/

module LearnerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LearnerId, f: nat)

  ghost predicate ConstantsValidForLearner(c: Constants, id: LearnerId, f: nat) {
    && c.id == id
    && c.f == f
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

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLearner(grp_c[idx], idx, f))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
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
    && msgOps.recv.value.Accept?
    && v' == v.(
      receivedAccepts := UpdateReceivedAccepts(v.receivedAccepts, msgOps.recv.value.vb, msgOps.recv.value.acc)
    )
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.None?
    && vb in v.receivedAccepts              // enabling
    && |v.receivedAccepts[vb]| >= c.f + 1   // enabling
    && v' == v.(learned := Some(vb.v))      // learn new value
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