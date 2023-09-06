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

  datatype Inner = Inner(
    receivedPromises: set<AcceptorId>, 
    value: Value, 
    highestHeardBallot: Option<LeaderId>) 

  datatype Variables = Variables(h: seq<Inner>)
  {
    ghost predicate WF() {
      0 < |h|
    }

    // My highestHeardBallot >= b
    ghost predicate HeardAtLeast(b: LeaderId) 
      requires WF()
    {
      var vi := Last(h);
      vi.highestHeardBallot.Some? && vi.highestHeardBallot.value >= b
    }
    
    // My highestHeardBallot < b
    ghost predicate HeardAtMost(b: LeaderId) 
      requires WF()
    {
      var vi := Last(h);
      vi.highestHeardBallot.None? || vi.highestHeardBallot.value < b
    }

    ghost predicate CanPropose(c: Constants) 
      requires WF()
    {
      && |Last(h).receivedPromises| >= c.f+1
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
    && forall i | 0 <= i < |grp_v| :: grp_v[i].WF()
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    v == Variables(
      [Inner( {}, c.preferredValue, None ) ]
    )
  }

  datatype TransitionLabel =
    | ReceivePromiseLbl(acc: AcceptorId, vbOpt:Option<ValBal>) 
    | ProposeLbl(val:Value) 
    | InternalLbl()

  datatype Step =
    ReceiveStep() | ProposeStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
    requires v.WF()
  {
    match step
      case ReceiveStep => NextReceivePromiseStep(c, v, v', lbl)
      case ProposeStep => NextProposeStep(c, v, v', lbl)
      case StutterStep => NextStutterStep(c, v, v', lbl)
  }


  ghost predicate NextReceivePromiseStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    && lbl.ReceivePromiseLbl?
    && var acc := lbl.acc;
    && var vbOpt := lbl.vbOpt;
    // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
    // probably simplify proof, preventing the leader from potentially equivocating
    // on its proposed value after receiving extraneous straggling promises.
    && var vi := Last(v.h);
    && |vi.receivedPromises| <= c.f
    && acc !in vi.receivedPromises
    && var doUpdate := 
          && vbOpt.Some? 
          && v.HeardAtMost(vbOpt.value.b);
    && var vi' := Inner(
      vi.receivedPromises + {acc},
      if doUpdate then vbOpt.value.v else vi.value,
      if doUpdate then Some(vbOpt.value.b) else vi.highestHeardBallot
    );
    && v' == v.(h := v.h + [vi])
  }

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    && var vi := Last(v.h);
    && lbl.ProposeLbl?
    && lbl.val == vi.value
    && v.CanPropose(c)
    && v' == Variables(StutterSeq(v.h))
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && exists step :: NextStep(c, v, v', step, lbl)
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

  datatype Inner = Inner(
    pendingPrepare: Option<PendingPrepare>,
    promised: Option<LeaderId>,
    acceptedVB: Option<ValBal>
  )

  datatype Variables = Variables(h: seq<Inner>)
  {

    ghost predicate WF() {
      0 < |h|
    }

    ghost predicate HasAccepted(vb: ValBal) 
      requires WF()
    {
      var vi := Last(h);
      && vi.acceptedVB.Some?
      && vi.acceptedVB.value == vb
    }

    ghost predicate HasAcceptedValue(v: Value) 
      requires WF()
    {
      var vi := Last(h);
      && vi.acceptedVB.Some?
      && vi.acceptedVB.value.v == v
    }

    ghost predicate HasPromisedAtLeast(b: LeaderId) 
      requires WF()
    {
      var vi := Last(h);
      && vi.promised.Some?
      && b <= vi.promised.value
    }

    ghost predicate HasAcceptedAtLeastBal(b: LeaderId) 
      requires WF()
    {
      var vi := Last(h);
      && vi.acceptedVB.Some?
      && b <= vi.acceptedVB.value.b
    }

    ghost predicate HasAcceptedAtMostBal(b: LeaderId) 
      requires WF()
    {
      var vi := Last(h);
      && vi.acceptedVB.Some?
      && vi.acceptedVB.value.b < b
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
    && forall i | 0 <= i < |grp_v| :: grp_v[i].WF()
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    v == Variables(
      [Inner(None, None, None)]
    )
  }

  datatype TransitionLabel =
    | ReceivePrepareLbl(bal:LeaderId)
    | MaybePromiseLbl(balOpt:Option<LeaderId>, vbOptOpt:Option<Option<ValBal>>)
    | MaybeAcceptLbl(bal:LeaderId, val:Value)
    | BroadcastAcceptedLbl(vb: ValBal)
    | InternalLbl()

  datatype Step =
    ReceivePrepareStep() 
    | MaybePromiseStep() 
    | MaybeAcceptStep() 
    | BroadcastAcceptedStep() 
    | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
    requires v.WF()
  {
    match step
      case ReceivePrepareStep => NextReceivePrepareStep(c, v, v', lbl)
      case MaybePromiseStep => NextMaybePromiseStep(c, v, v', lbl)
      case MaybeAcceptStep => NextMaybeAcceptStep(c, v, v', lbl)
      case BroadcastAcceptedStep => NextBroadcastAcceptedStep(c, v, v', lbl)
      case StutterStep => NextStutterStep(c, v, v', lbl)
  }

  ghost predicate NextReceivePrepareStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    && var vi := Last(v.h);
    && lbl.ReceivePrepareLbl?
    && vi.pendingPrepare.None?
    && v' == v.(
      h := v.h + [vi.(pendingPrepare := Some(Prepare(lbl.bal)))]
    )
  }

  ghost predicate NextMaybePromiseStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
    requires v.WF()
  {
    && var vi := Last(v.h);
    && lbl.MaybePromiseLbl?
    && vi.pendingPrepare.Some?
    && var bal := vi.pendingPrepare.value.bal;
    && var doPromise := vi.promised.None? || (vi.promised.Some? && vi.promised.value < bal);
    && if doPromise then
          var vi' := vi.(promised := Some(bal),
            pendingPrepare := None);
          && v' == v.(h := v.h + [vi'])
          && lbl == MaybePromiseLbl(Some(bal), Some(vi.acceptedVB))
        else
          var vi' := vi.(pendingPrepare := None);
          && v' == v.(h := v.h + [vi'])
          && lbl == MaybePromiseLbl(None, None)
  }

  ghost predicate NextMaybeAcceptStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    && var vi := Last(v.h);
    && lbl.MaybeAcceptLbl?
    && vi.pendingPrepare.None?
    && var bal := lbl.bal;
    && var val := lbl.val;
    && var doAccept := vi.promised.None? || (vi.promised.Some? && vi.promised.value <= bal);
    &&  if doAccept then
          var vi' := vi.(
                  promised := Some(bal), 
                  acceptedVB := Some(VB(val, bal)));
          && v' == v.(h := v.h + [vi'])
        else
          && v' == Variables(StutterSeq(v.h))
  }

  ghost predicate NextBroadcastAcceptedStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
    requires v.WF()
  {
    && var vi := Last(v.h);
    && lbl.BroadcastAcceptedLbl?
    && vi.pendingPrepare.None?
    && vi.acceptedVB.Some?
    && lbl.vb == vi.acceptedVB.value
    && v' == Variables(StutterSeq(v.h))
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    && lbl.InternalLbl?
    && v' == Variables(StutterSeq(v.h))
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && exists step :: NextStep(c, v, v', step, lbl)
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

  datatype Inner = Inner(
    // maps ValBal to acceptors that accepted such pair
    receivedAccepts: map<ValBal, set<AcceptorId>>,
    learned: Option<Value>
  )

  datatype Variables = Variables(h: seq<Inner>) 
  {

    ghost predicate WF() {
      0 < |h|
    }

    ghost predicate HasLearnedSome()
      requires WF()
    {
      Last(h).learned.Some?
    }
    
    ghost predicate HasLearnedValue(v: Value) 
      requires WF()
    {
      Last(h).learned == Some(v)
    }

    ghost function GetLearnedValue() : (learned: Value)
      requires WF()
      requires HasLearnedSome()
    {
      Last(h).learned.value
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
    && forall i | 0 <= i < |grp_v| :: grp_v[i].WF()
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    v == Variables(
      [Inner(map[], None)]
    )
  }

  datatype TransitionLabel =
    | ReceiveAcceptLbl(vb:ValBal, acc:AcceptorId)
    | InternalLbl()

  datatype Step =
    ReceiveStep() | LearnStep(vb: ValBal) | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
    requires v.WF()
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

  ghost predicate NextReceiveAcceptStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    var vi := Last(v.h);
    && lbl.ReceiveAcceptLbl?
    && var vi' := Inner(UpdateReceivedAccepts(vi.receivedAccepts, lbl.vb, lbl.acc), vi.learned);
    && v' == v.(h := v.h + [vi'])
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, lbl: TransitionLabel) 
    requires v.WF()
  {
    var vi := Last(v.h);
    && lbl.InternalLbl?
    && vb in vi.receivedAccepts              // enabling
    && |vi.receivedAccepts[vb]| >= c.f + 1   // enabling
    && var vi' := vi.(learned := Some(vb.v));  // learn new value
    && v' == v.(h := v.h + [vi'])
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF()
  {
    && lbl.InternalLbl?
    && v' == Variables(StutterSeq(v.h))
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && exists step :: NextStep(c, v, v', step, lbl)
  }
}  // end module LearnerHost