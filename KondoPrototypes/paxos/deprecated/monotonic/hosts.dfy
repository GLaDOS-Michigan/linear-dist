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
    receivedPromises: seq<set<Message>>, 
    highestHeardBal: seq<Option<LeaderId>>,
    value: seq<Value>,
    proposed: seq<Value>
  ) {
    ghost predicate WF() {
      && 0 < |receivedPromises|
      && |value| == |highestHeardBal| == |receivedPromises|
      && (forall i, p | 0 <= i < |receivedPromises| && p in receivedPromises[i] :: p.Promise?)
    }

    ghost predicate HighestHeardNone() 
      requires WF()
    {
      Last(highestHeardBal) == None
    }

    ghost function GetHighestHeard() : LeaderId 
      requires WF()
      requires !HighestHeardNone()
    {
      Last(highestHeardBal).value
    }

    ghost function GetValue() : Value 
      requires WF()
    {
      Last(value)
    }

    ghost predicate NewAcceptorPromise(c: Constants, bal: LeaderId, acc: AcceptorId) 
      requires WF()
    {
      && bal == c.id
      && (forall p | p in Last(receivedPromises) :: p.acc != acc)
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLeader(grp_c[idx], idx, f))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF())
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedPromises == [{}]
    && v.value == [c.preferredValue]
    && v.highestHeardBal == [None]
    && v.proposed == []
  }

  datatype Step =
    PrepareStep() | ReceiveStep() | ProposeStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF()
    && match step
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

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF()
  {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Promise(bal, acc, vbOpt) => 
        // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
        // probably simplify proof, preventing the leader from potentially equivocating
        // on its proposed value after receiving extraneous straggling promises.
        && |Last(v.receivedPromises)| <= c.f
        && if v.NewAcceptorPromise(c, bal, acc) then
            var doUpdate := && vbOpt.Some? 
                            && (v.HighestHeardNone() || vbOpt.value.b > v.GetHighestHeard());
            v' == v.(
              receivedPromises := v.receivedPromises + [Last(v.receivedPromises) + {msgOps.recv.value}],
              value := if doUpdate then v.value + [vbOpt.value.v] else StutterSeq(v.value),
              highestHeardBal := 
                if doUpdate then v.highestHeardBal + [Some(vbOpt.value.b)] else StutterSeq(v.highestHeardBal)
            )
          else 
            // this promise is not for me
            NextStutterStep(c, v, v', msgOps)
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF()
  {
    && msgOps.recv.None?
    && |Last(v.receivedPromises)| >= c.f+1  // enabling condition
    // Enabling condition that my hightest heard 
    // is smaller than my own ballot. Not a safety issue, but can probably simplify proof.
    // It is equivalent to being preempted
    && (v.HighestHeardNone() || v.GetHighestHeard() <= c.id)
    && msgOps.send == Some(Propose(c.id, v.GetValue()))
    && v' == v.(
      proposed := v.proposed + [v.GetValue()]
    )
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

  // The sentPromises set is introduced so that I can maintain an application invariant
  // that for all Promise messages, the accepted ballot must be strictly less than the 
  // accepted ballot. It can also be maintained using a boolean seq that marks when a promise
  // message is sent out. But I am not sure which is "better"
  datatype Variables = Variables(
    promised: seq<LeaderId>,          // monotonic seq
    acceptedVB: seq<Option<ValBal>>,  // monotonic seq
    sentPromises: set<Message>        // monotonic set
  ) {

    // Tony: This is a minor application property that is swept under WF(). However,
    // the same can be achieved if we bundle promised-accepted pairs into the same seq,
    // which removes the need for this WF.
    // On second thought, this is not really an application property. It is something we 
    // enforce during monotonic transformation, which we should have the freedom to do.
    ghost predicate WF() {
      |promised| == |acceptedVB|
    }
    
    ghost predicate PromisedNone() {
      promised == []
    }

    ghost function GetPromised() : LeaderId 
      requires !PromisedNone()
    {
      Last(promised)
    }
    
    ghost predicate AcceptedNone() {
      acceptedVB == []
    }

    ghost function GetAccepted() : Option<ValBal> 
    {
      if AcceptedNone() then None
      else Last(acceptedVB)
    }

    // This is defined as such because at the moment an acceptor accepts a value, its
    // promised ballot is the same as the accepted valbal
    ghost predicate HasAccepted(vb: ValBal) 
      requires WF()
    {
      exists i :: 
        && 0 <= i < |acceptedVB| 
        && Some(vb) == acceptedVB[i]
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
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF())
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.promised == []
    && v.acceptedVB == []
    && v.sentPromises == {}
  }

  datatype Step =
    ReceiveStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && match msgOps.recv.value
        case Prepare(bal) => (
          var doPromise := v.PromisedNone() || v.GetPromised() < bal;
          if doPromise then
            && var outPromise := Promise(bal, c.id, v.GetAccepted());
            && v' == v.(
              promised := v.promised + [bal],
              acceptedVB := v.acceptedVB + [v.GetAccepted()],
              sentPromises := v.sentPromises + {outPromise}
            )
            && msgOps.send == Some(outPromise)
          else
            NextStutterStep(c, v, v', msgOps)  // ignore smaller ballots
        )
        case Propose(bal, val) => (
          var doAccept := v.PromisedNone() || v.GetPromised() <= bal;
          if doAccept then
            && v' == v.(
                  promised := v.promised + [bal], 
                  acceptedVB := v.acceptedVB + [Some(VB(val, bal))])
            && msgOps.send == Some(Accept(VB(val, bal), c.id))
          else
            NextStutterStep(c, v, v', msgOps)  // ignore smaller ballots
        )
        case _ => (
          NextStutterStep(c, v, v', msgOps)
        )
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
    receivedAccepts: map<ValBal, seq<set<AcceptorId>>>,  // each vb maps to monotonic seq
    learned: seq<ValBal>                                  // monotonic seq
  ) {
    
    ghost predicate Learned(vb: ValBal) {
      vb in learned
    }
  }

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
    && v.learned == []
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

  ghost function UpdateReceivedAccepts(receivedAccepts: map<ValBal, seq<set<AcceptorId>>>, 
    vb: ValBal, acc: AcceptorId) : (out: map<ValBal, seq<set<AcceptorId>>>)
  {
    if vb in receivedAccepts && 0 < |receivedAccepts[vb]| then 
      receivedAccepts[vb := receivedAccepts[vb] + [Last(receivedAccepts[vb]) + {acc}]]
    else 
      receivedAccepts[vb := [{acc}]]
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Accept(vb, acc) => 
        v' == Variables(UpdateReceivedAccepts(v.receivedAccepts, vb, acc), v.learned)
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, vb: ValBal) {
    && msgOps.recv.None?
    && v.learned == []
    && vb in v.receivedAccepts  // enabling
    && 0 < |v.receivedAccepts[vb]|
    && |Last(v.receivedAccepts[vb])| >= c.f + 1  // enabling
    && msgOps.send == Some(Learn(c.id, vb.b, vb.v))
    && v' == v.(
      learned := v.learned + [vb]
    )
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