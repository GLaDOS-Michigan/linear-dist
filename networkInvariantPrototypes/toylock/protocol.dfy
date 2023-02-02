include "../UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message = Grant(epoch: nat, dst: HostId) 

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types


module Host {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(numParticipants:nat, hostId: HostId)

  predicate ConstantsValidForGroup(c: Constants, participantCount: nat, hostId: HostId)
  {
    && c.numParticipants == participantCount
    && c.hostId == hostId
  }

  datatype Variables = Variables(
    myEpoch: nat,
    hasLock: bool
  )
  {
    predicate WF(c: Constants) {
      && 0 < c.numParticipants
      && c.hostId < c.numParticipants
    }
  }

  predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall hostId: nat | hostId < |grp_c|
        :: ConstantsValidForGroup(grp_c[hostId], |grp_c|, hostId))
  }

  predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
  }

  predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && if c.hostId == 0 then
        && v.myEpoch == 1
        && v.hasLock 
      else 
        && v.myEpoch == 0
        && !v.hasLock
  }

  datatype Step =
    TransmissionStep() | ReceiveStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case TransmissionStep => NextTransmissionStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
  }

  predicate NextTransmissionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF(c)
  {
    if v.hasLock then 
      && msgOps.recv.None?
      && msgOps.send == Some(Grant(v.myEpoch + 1, Successor(c.numParticipants, c.hostId)))
      && v' == v.(hasLock := false)
    else
      && msgOps.send == msgOps.recv == None 
      && v == v'
  }

  predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && msgOps.recv.value.epoch > v.myEpoch
    && msgOps.recv.value.dst > c.hostId
    && v' == v.(hasLock := true, myEpoch := msgOps.recv.value.epoch)
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host

module Network {
  import opened Types
  datatype Variables = Variables(sentMsgs:set<Message>)

  predicate Init(v: Variables)
  {
    && v.sentMsgs == {}
  }

  predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
} // end module Network


module DistributedSystem {
  import opened Types
  import Network
  import Host

  datatype Constants = Constants(
    hostConstants: seq<Host.Constants>)
  {
    predicate ValidIdx(id: int) {
      0 <= id < |hostConstants|
    }

    predicate UniqueIds() {
      forall i, j | ValidIdx(i) && ValidIdx(j) && hostConstants[i].hostId == hostConstants[j].hostId :: i == j
    }

    predicate WF() {
      && 0 < |hostConstants|
      && UniqueIds()
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hostConstants, hosts)
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hostConstants, v.hosts)
    && Network.Init(v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, actorIdx: int, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidIdx(actorIdx)
    && Host.Next(c.hostConstants[actorIdx], v.hosts[actorIdx], v'.hosts[actorIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHostIdx | c.ValidIdx(otherHostIdx) && otherHostIdx != actorIdx :: v'.hosts[otherHostIdx] == v.hosts[otherHostIdx])
  }

  datatype Step = HostActionStep(actorIdx: int, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.actorIdx, step.msgOps)
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}  // end module DistributedSystem


