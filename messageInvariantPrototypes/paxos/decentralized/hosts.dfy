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
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case ProposeStep => NextProposeStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextPrepareStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send == Some(Prepare(c.id))
    && v' == v
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Promise(bal, acc, vbOpt) => 
        // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
        // probably simplify proof, preventing the leader from potentially equivocating
        // on its proposed value after receiving extraneous straggling promises.
        && |v.receivedPromises| <= c.f
        && acc !in v.receivedPromises
        && if bal == c.id then
            var doUpdate := 
              && vbOpt.Some? 
              && (|| v.highestHeardBallot.None?
                  || (v.highestHeardBallot.Some? && vbOpt.value.b > v.highestHeardBallot.value));
            v' == v.(
              receivedPromises := v.receivedPromises + {acc},
              value :=  if doUpdate then vbOpt.value.v else v.value,
              highestHeardBallot := if doUpdate then Some(vbOpt.value.b) else v.highestHeardBallot
            )
          else 
            // this promise is not for me
            NextStutterStep(c, v, v', msgOps)
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && |v.receivedPromises| >= c.f+1  // enabling condition
    // Enabling condition that my hightest heard 
    // is smaller than my own ballot. Not a safety issue, but can probably simplify proof.
    // It is equivalent to being preempted
    && (v.highestHeardBallot.None? || v.highestHeardBallot.value <= c.id)
    
    // Tony: This is a target for monotonic transformation -- it would allow me to say that
    // Propose messages are from some value once held by the leader
    && msgOps.send == Some(Propose(c.id, v.value))
    && v' == v
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
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

  datatype Variables = Variables(
    pendingMsg: Option<Message>,
    promised: Option<LeaderId>,
    acceptedVB: Option<ValBal>
  ) {
    ghost predicate WF() {
      pendingMsg.Some? ==> (pendingMsg.value.Prepare? || pendingMsg.value.Propose?)
    }
  }

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
    && v.promised == None
    && v.acceptedVB == None
    && v.pendingMsg == None
  }

  datatype Step =
    ReceiveStep() | MaybePromiseStep() | MaybeAcceptStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case MaybePromiseStep => NextMaybePromiseStep(c, v, v', msgOps)
      case MaybeAcceptStep => NextMaybeAcceptStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v.pendingMsg.None?
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
        case Prepare(_) =>
          v' == v.(pendingMsg := Some(msgOps.recv.value))
        case Propose(bal, val) =>
          v' == v.(pendingMsg := Some(msgOps.recv.value))
        case _ =>
          NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextMaybePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && v.pendingMsg.Some?
    && v.pendingMsg.value.Prepare?
    && var bal := v.pendingMsg.value.bal;
    && var doPromise := v.promised.None? || (v.promised.Some? && v.promised.value < bal);
    && if doPromise then
          && v' == v.(
            promised := Some(bal),
            pendingMsg := None)
          && msgOps.send == Some(Promise(bal, c.id, v.acceptedVB)) 
        else
          && v' == v.(pendingMsg := None)
          && msgOps.send == None
  }

  ghost predicate NextMaybeAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
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
          && msgOps.send == Some(Accept(VB(val, bal), c.id))
        else
          && v' == v.(pendingMsg := None)
          && msgOps.send == None
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
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
    receivedAccepts: map<ValBal, set<AcceptorId>>
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

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    v.receivedAccepts == map[]
  }

  datatype Step =
    ReceiveStep() | LearnStep(vb: ValBal) | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case LearnStep(vb) => NextLearnStep(c, v, v', msgOps, vb)
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

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Accept(vb, acc) => 
        v' == Variables(UpdateReceivedAccepts(v.receivedAccepts, vb, acc))
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, vb: ValBal) {
    && msgOps.recv.None?
    && vb in v.receivedAccepts  // enabling
    && |v.receivedAccepts[vb]| >= c.f + 1  // enabling
    && msgOps.send == Some(Learn(c.id, vb.b, vb.v))
    && v' == v  // local state unchanged
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LearnerHost