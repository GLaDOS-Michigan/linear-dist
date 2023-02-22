include "types.dfy"


module LeaderHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LeaderId, f: nat, preferredValue: Value)

  predicate ConstantsValidForLeader(c: Constants, id: LeaderId, f: nat) {
    && c.id == id
    && c.f == f
  }

  datatype Variables = Variables(
    receivedPromises: set<LeaderId>, 
    value: Value, 
    highestHeardBallot: Option<LeaderId>
  )

  predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLeader(grp_c[idx], idx, f))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables) {
    && v.receivedPromises == {}
    && v.value == c.preferredValue
    && v.highestHeardBallot == None
  }

  datatype Step =
    PrepareStep() | ReceiveStep() | ProposeStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case PrepareStep => NextPrepareStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case ProposeStep => NextProposeStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  predicate NextPrepareStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send == Some(Prepare(c.id))
    && v' == v
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Promise(bal, acc, vbOpt) => 
        if bal == c.id then
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

  predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && |v.receivedPromises| >= c.f+1  // enabling condition
    // Tony: This is a target for monotonic transformation -- it would allow me to say that
    // Propose messages are from some value once held by the leader
    && msgOps.send == Some(Propose(c.id, v.value))
    && v' == v
  }

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LeaderHost


module AcceptorHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: AcceptorId)

  predicate ConstantsValidForAcceptor(c: Constants, id: AcceptorId) {
    && c.id == id
  }

  datatype Variables = Variables(
    promised: Option<LeaderId>,
    acceptedVB: Option<ValBal>
  )

  predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForAcceptor(grp_c[idx], idx))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c|
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables) {
    && v.promised == None
    && v.acceptedVB == None
  }

  datatype Step =
    ReceiveStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && match msgOps.recv.value
        case Prepare(bal) => 
          var doPromise := v.promised.None? || (v.promised.Some? && v.promised.value < bal);
          if doPromise then
            && v' == v.(promised := Some(bal))
            && msgOps.send == Some(Promise(bal, c.id, v.acceptedVB)) 
          else
            NextStutterStep(c, v, v', msgOps)  // ignore smaller ballots
        case Propose(bal, val) =>
          var doAccept := v.promised.None? || (v.promised.Some? && v.promised.value < bal);
          if doAccept then
            && v' == v.(
                  promised := Some(bal), 
                  acceptedVB := Some(VB(val, bal)))
            // Tony: This is a target for monotonic transformation -- it would allow me to say that
            // Accept messages are from some acceptedVB once held by the acceptor
            && msgOps.send == Some(Accept(VB(val, bal), c.id))
          else
            NextStutterStep(c, v, v', msgOps)  // ignore smaller ballots
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module AcceptorHost


module LearnerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(f: nat)

  predicate ConstantsValidForLearner(c: Constants, f: nat) {
    && c.f == f
  }

  datatype Variables = Variables(
    // maps ValBal to acceptors that accepted such pair
    receivedAccepts: map<ValBal, set<AcceptorId>>
  )

  predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLearner(grp_c[idx], f))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables) {
    v.receivedAccepts == map[]
  }

  datatype Step =
    ReceiveStep() | LearnStep(vb: ValBal) | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case LearnStep(vb) => NextLearnStep(c, v, v', msgOps, vb)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  function updateReceivedAccepts(receivedAccepts: map<ValBal, set<AcceptorId>>, 
    vb: ValBal, acc: AcceptorId) : (out: map<ValBal, set<AcceptorId>>) 
  {
    if vb in receivedAccepts then 
      receivedAccepts[vb := receivedAccepts[vb] + {acc}]
    else 
      receivedAccepts[vb := {acc}]
    }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Accept(vb, acc) => 
        v' == v.(receivedAccepts := updateReceivedAccepts(v.receivedAccepts, vb, acc))
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  predicate NextLearnStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, vb: ValBal) {
    && msgOps.recv.None?
    && vb in v.receivedAccepts  // enabling
    && |v.receivedAccepts[vb]| >= c.f + 1  // enabling
    && msgOps.send == Some(Learn(vb.v))
  }

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LearnerHost