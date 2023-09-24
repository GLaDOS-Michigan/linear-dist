include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message = Msg(val: nat, src: nat)  // A host can receive if its ringPos == succ(src)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types


module Host {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(numParticipants:nat, ringPos: nat, hostId: HostId)

  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat, ringPos: HostId)
  {
    && c.numParticipants == participantCount
    && c.ringPos == ringPos
  }

  datatype Variables = Variables(
    highestHeardSeq: seq<nat>
  )
  {
    ghost predicate WF(c: Constants) {
      && 0 < c.numParticipants
    }

    ghost function highestHeard(): int {
      if highestHeardSeq == [] then -1
      else Last(highestHeardSeq)
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall ringPos: nat | ringPos < |grp_c|
        :: ConstantsValidForGroup(grp_c[ringPos], |grp_c|, ringPos))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.highestHeardSeq == []
  }

  datatype Step =
    TransmissionStep() | ReceiveStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case TransmissionStep => NextTransmissionStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
  }

  ghost predicate NextTransmissionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF(c)
  {
    var payload := max(v.highestHeard(), c.hostId); // max of what I heard vs my own hostId
    var msg := Msg(payload, c.ringPos);
    && msgOps.recv.None?
    && msgOps.send == Some(msg)
    && v == v'
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && msgOps.recv.value.src < c.numParticipants
    && c.ringPos == Successor(c.numParticipants, msgOps.recv.value.src)
    && if msgOps.recv.value.val >= v.highestHeard() then 
          v' == v.(highestHeardSeq := v.highestHeardSeq + [msgOps.recv.value.val])
       else
          v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host



