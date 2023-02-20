include "types.dfy"


module LeaderHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LeaderId, f: nat, preferredValue: Value)

  predicate ConstantsValidForLeader(c: Constants, id: LeaderId, f: nat)
  {
    && c.id == id
    && c.f == f
  }

  datatype Variables = Variables(receivedPromises: set<LeaderId>, value: Value, highestHeardBallot: Option<LeaderId>)
  {
    predicate WF(c: Constants) {
      true
    }
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
          && v' == v
      case _ =>
        && v' == v
  }

  predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && |v.receivedPromises| >= c.f+1  // enabling condition
    && msgOps.send == Some(Propose(c.id, v.value))
    && v' == v
  }

  predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == msgOps.recv == None
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LeaderHost
