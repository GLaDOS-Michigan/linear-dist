include "types.dfy"


/***************************************************************************************
*                                      Leader Host                                     *
***************************************************************************************/

module LeaderHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LeaderId, f: nat, preferredValue: Value)

  predicate ConstantsValidForLeader(c: Constants, id: LeaderId, f: nat) {
    && c.id == id
    && c.f == f
  }

  datatype Variables = Variables(
    receivedPromises: seq<set<Message>>, 
    highestHeardBal: seq<Option<LeaderId>>,
    value: seq<Value>,
    proposed: seq<Value>
  ) {
    predicate WF() {
      && 0 < |receivedPromises|
      && |value| == |highestHeardBal| == |receivedPromises|
      && (forall i, p | 0 <= i < |receivedPromises| && p in receivedPromises[i] :: p.Promise?)
    }

    predicate HighestHeardNone() 
      requires WF()
    {
      Last(highestHeardBal) == None
    }

    function GetHighestHeard() : LeaderId 
      requires WF()
      requires !HighestHeardNone()
    {
      Last(highestHeardBal).value
    }

    function GetValue() : Value 
      requires WF()
    {
      Last(value)
    }

    predicate NewAcceptorPromise(c: Constants, bal: LeaderId, acc: AcceptorId) 
      requires WF()
    {
      && bal == c.id
      && (forall p | p in Last(receivedPromises) :: p.acc != acc)
    }
  }

  predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLeader(grp_c[idx], idx, f))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF())
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables) {
    && v.receivedPromises == [{}]
    && v.value == [c.preferredValue]
    && v.highestHeardBal == [None]
    && v.proposed == []
  }

  datatype Step =
    PrepareStep() | ReceiveStep() | ProposeStep() | StutterStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF()
    && match step
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

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
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

  predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
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

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
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

  predicate ConstantsValidForAcceptor(c: Constants, id: AcceptorId) {
    && c.id == id
  }

  datatype Variables = Variables(
    promised: seq<LeaderId>,          // monotonic seq
    acceptedVB: seq<Option<ValBal>>   // monotonic seq
  ) {

    // Tony: This is a minor application property that is swept under WF(). However,
    // the same can be achieved if we bundle promised-accepted pairs into the same seq,
    // which removes the need for this WF.
    // On second thought, this is not really an application property. It is something we 
    // enforce during monotonic transformation, which we should have the freedom to do.
    predicate WF() {
      |promised| == |acceptedVB|
    }
    
    predicate PromisedNone() {
      promised == []
    }

    function GetPromised() : LeaderId 
      requires !PromisedNone()
    {
      Last(promised)
    }
    
    predicate AcceptedNone() {
      acceptedVB == []
    }

    function GetAccepted() : Option<ValBal> 
    {
      if AcceptedNone() then None
      else Last(acceptedVB)
    }

    predicate HasAccepted(vb: ValBal) {
      exists i :: 0 <= i < |acceptedVB| && Some(vb) == acceptedVB[i]
    }
  }

  predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForAcceptor(grp_c[idx], idx))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c| == 2*f+1
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF())
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWF(grp_c, grp_v, f)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables) {
    && v.promised == []
    && v.acceptedVB == []
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
        case Prepare(bal) => (
          var doPromise := v.PromisedNone() || v.GetPromised() < bal;
          if doPromise then
            && v' == v.(
              promised := v.promised + [bal],
              acceptedVB := v.acceptedVB + [v.GetAccepted()]
            )
            && msgOps.send == Some(Promise(bal, c.id, v.GetAccepted()))
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

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
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

  predicate ConstantsValidForLearner(c: Constants, id: LearnerId, f: nat) {
    && c.id == id
    && c.f == f
  }

  datatype Variables = Variables(
    // maps ValBal to acceptors that accepted such pair
    receivedAccepts: map<ValBal, seq<set<AcceptorId>>>,  // each vb maps to monotonic seq
    learned: seq<ValBal>                                  // monotonic seq
  ) {
    
    predicate Learned(vb: ValBal) {
      vb in learned
    }
  }

  predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLearner(grp_c[idx], idx, f))
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
    && v.receivedAccepts == map[]
    && v.learned == []
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

  function UpdateReceivedAccepts(receivedAccepts: map<ValBal, seq<set<AcceptorId>>>, 
    vb: ValBal, acc: AcceptorId) : (out: map<ValBal, seq<set<AcceptorId>>>)
  {
    if vb in receivedAccepts && 0 < |receivedAccepts[vb]| then 
      receivedAccepts[vb := receivedAccepts[vb] + [Last(receivedAccepts[vb]) + {acc}]]
    else 
      receivedAccepts[vb := [{acc}]]
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && match msgOps.recv.value
      case Accept(vb, acc) => 
        v' == Variables(UpdateReceivedAccepts(v.receivedAccepts, vb, acc), v.learned)
      case _ =>
        NextStutterStep(c, v, v', msgOps)
  }

  predicate NextLearnStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, vb: ValBal) {
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

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LearnerHost