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
    receivedPromises: set<LeaderId>, 
    value: Value, 
    highestHeardBallot: Option<LeaderId>
  )

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

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedPromises == {}
    && v.value == c.preferredValue
    && v.highestHeardBallot == None
  }

  datatype TransitionLabel =
    | ReceivePromiseLbl(acc: AcceptorId, vbOpt:Option<ValBal>) 
    | ProposeLbl(val:Value) 
    | InternalLbl()

  datatype Step =
    PrepareStep() | ReceiveStep() | ProposeStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case PrepareStep => NextPrepareStep(c, v, v', lbl)
      case ReceiveStep => NextReceivePromiseStep(c, v, v', lbl)
      case ProposeStep => NextProposeStep(c, v, v', lbl)
      case StutterStep => NextStutterStep(c, v, v', lbl)
  }

  ghost predicate NextPrepareStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v' == v
  }

  ghost predicate NextReceivePromiseStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceivePromiseLbl?
    && var acc := lbl.acc;
    && var vbOpt := lbl.vbOpt;
    // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
    // probably simplify proof, preventing the leader from potentially equivocating
    // on its proposed value after receiving extraneous straggling promises.
    && |v.receivedPromises| <= c.f
    && acc !in v.receivedPromises
    && var doUpdate := 
          && vbOpt.Some? 
          && (|| v.highestHeardBallot.None?
              || (v.highestHeardBallot.Some? && vbOpt.value.b > v.highestHeardBallot.value));
    && v' == v.(
        receivedPromises := v.receivedPromises + {acc},
        value :=  if doUpdate then vbOpt.value.v else v.value,
        highestHeardBallot := if doUpdate then Some(vbOpt.value.b) else v.highestHeardBallot
      )
  }

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ProposeLbl?
    && lbl.val == v.value
    && |v.receivedPromises| >= c.f+1  // enabling condition
    // Enabling condition that my hightest heard 
    // is smaller than my own ballot. Not a safety issue, but can probably simplify proof.
    // It is equivalent to being preempted
    && (v.highestHeardBallot.None? || v.highestHeardBallot.value <= c.id)
    && v' == v
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
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

  datatype PendingMsg = Prepare(bal:LeaderId) | Propose(bal:LeaderId, val:Value)

  datatype Variables = Variables(
    pendingMsg: Option<PendingMsg>,
    promised: Option<LeaderId>,
    acceptedVB: Option<ValBal>
  )

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForAcceptor(grp_c[idx], idx))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c| == 2*f+1
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.promised == None
    && v.acceptedVB == None
    && v.pendingMsg == None
  }

  datatype TransitionLabel =
    | ReceivePrepareLbl(bal:LeaderId)
    | ReceiveProposeLbl(bal:LeaderId, val:Value)
    | MaybePromiseLbl(balOpt:Option<LeaderId>, vbOptOpt:Option<Option<ValBal>>)
    | MaybeAcceptLbl(vb:Option<ValBal>)
    | InternalLbl()

  datatype Step =
    ReceivePrepareStep() | ReceiveProposeStep() | MaybePromiseStep() | MaybeAcceptStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case ReceivePrepareStep => NextReceivePrepareStep(c, v, v', lbl)
      case ReceiveProposeStep => NextReceiveProposeStep(c, v, v', lbl)
      case MaybePromiseStep => NextMaybePromiseStep(c, v, v', lbl)
      case MaybeAcceptStep => NextMaybeAcceptStep(c, v, v', lbl)
      case StutterStep => NextStutterStep(c, v, v', lbl)
  }

  ghost predicate NextReceivePrepareStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceivePrepareLbl?
    && v.pendingMsg.None?
    && v' == v.(pendingMsg := Some(Prepare(lbl.bal)))
  }

  ghost predicate NextReceiveProposeStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceiveProposeLbl?
    && v.pendingMsg.None?
    && v' == v.(pendingMsg := Some(Propose(lbl.bal, lbl.val)))
  }

  ghost predicate NextMaybePromiseStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.MaybePromiseLbl?
    && v.pendingMsg.Some?
    && v.pendingMsg.value.Prepare?
    && var bal := v.pendingMsg.value.bal;
    && var doPromise := v.promised.None? || (v.promised.Some? && v.promised.value < bal);
    && if doPromise then
          && v' == v.(
            promised := Some(bal),
            pendingMsg := None)
          && lbl == MaybePromiseLbl(Some(bal), Some(v.acceptedVB))
        else
          && v' == v.(pendingMsg := None)
          && lbl == MaybePromiseLbl(None, None)
  }

  ghost predicate NextMaybeAcceptStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.MaybeAcceptLbl?
    && v.pendingMsg.Some?
    && v.pendingMsg.value.Propose?
    && var bal := v.pendingMsg.value.bal;
    && var val := v.pendingMsg.value.val;
    && var doAccept := v.promised.None? || (v.promised.Some? && v.promised.value <= bal);
    &&  if doAccept then
          && v' == v.(
                promised := Some(bal), 
                acceptedVB := Some(VB(val, bal)),
                pendingMsg := None)
          && lbl == MaybeAcceptLbl(Some(VB(val, bal)))
        else
          && v' == v.(pendingMsg := None)
          && lbl == MaybeAcceptLbl(None)
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
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
  )

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

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedAccepts == map[]
    && v.learned == None
  }

  datatype TransitionLabel =
    | ReceiveAcceptLbl(vb:ValBal, acc:AcceptorId)
    | InternalLbl()

  datatype Step =
    ReceiveStep() | LearnStep(vb: ValBal) | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case ReceiveStep => NextReceiveAcceptStep(c, v, v', lbl)
      case LearnStep(vb) => NextLearnStep(c, v, v', vb, lbl)
      case StutterStep => NextStutterStep(c, v, v', lbl)
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

  ghost predicate NextReceiveAcceptStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceiveAcceptLbl?
    && v' == Variables(UpdateReceivedAccepts(v.receivedAccepts, lbl.vb, lbl.acc), v.learned)
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && vb in v.receivedAccepts              // enabling
    && |v.receivedAccepts[vb]| >= c.f + 1   // enabling
    && v' == v.(learned := Some(vb.v))      // learn new value
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
  }
}  // end module LearnerHost