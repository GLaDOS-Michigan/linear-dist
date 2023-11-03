include "types.dfy"

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
    highestHeard: int   // monotonic int
  )
  {
    ghost predicate WF(c: Constants) {
      && 0 < c.numParticipants
      && highestHeard >= -1  // not really useful, but just for fun :)
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
    && v.highestHeard == -1
  }

  // Label definitions
  datatype TransitionLabel =
    SendLbl(myHighest: int) | ReceiveLbl(previousHighest: int) | InternalLbl()

  datatype Step =
    TransmissionStep() | ReceiveStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    && v.WF(c)
    && match step
      case TransmissionStep => NextTransmissionStep(c, v, v', lbl)
      case ReceiveStep => NextReceiveStep(c, v, v', lbl)
  }

  ghost predicate NextTransmissionStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) 
    requires v.WF(c)
  {
    var payload := max(v.highestHeard, c.hostId); // max of what I heard vs my own hostId
    && lbl.SendLbl?
    && lbl.myHighest == payload
    && v == v'
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ReceiveLbl?
    && v.highestHeard < lbl.previousHighest   // max of what I heard vs incoming
    && v' == v.(highestHeard := lbl.previousHighest)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
  }
}  // end module Host
