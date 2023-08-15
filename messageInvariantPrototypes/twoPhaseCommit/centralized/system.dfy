
include "hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }

    ghost predicate ValidParticipantId(id: HostId) {
      id < |hosts|-1
    }

    ghost predicate ValidCoordinatorId(id: HostId) {
      id == |hosts|-1
    }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
  }

  datatype Step =
    | VoteReqStep(coordinator: HostId)
    | SendVoteStep(participant: HostId, coordinator: HostId, vote: Vote)
    | DecideStep(coordinator: HostId, decision: Decision)
    | StutterStep()

    
  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, cidx: HostId) 
    requires v.WF(c) && v'.WF(c)
  {
    var cLbl := CoordinatorHost.VoteReqLbl();
    var pLbl := ParticipantHost.VoteReqLbl();
    && c.ValidCoordinatorId(cidx)
    && Host.Next(c.hosts[cidx], v.hosts[cidx], v'.hosts[cidx], Host.CL(cLbl))
    && (forall pidx:nat | c.ValidParticipantId(pidx)
        :: Host.Next(c.hosts[pidx], v.hosts[pidx], v'.hosts[pidx], Host.PL(pLbl))
    )
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, pidx: HostId, cidx: HostId, vote: Vote) 
    requires v.WF(c) && v'.WF(c)
  {
    var cLbl := CoordinatorHost.ReceiveVoteLbl(vote, pidx);
    var pLbl := ParticipantHost.SendVoteLbl(vote);
    && c.ValidCoordinatorId(cidx)
    && c.ValidParticipantId(pidx)
    && Host.Next(c.hosts[cidx], v.hosts[cidx], v'.hosts[cidx], Host.CL(cLbl))
    && Host.Next(c.hosts[pidx], v.hosts[pidx], v'.hosts[pidx], Host.PL(pLbl))
    && (forall id:nat | c.ValidHostId(id) && id != cidx && id != pidx
        :: v.hosts[id] == v'.hosts[id]
    )
  }

  ghost predicate NextDecideStep(c: Constants, v: Variables, v': Variables, cidx: HostId, decision: Decision)
    requires v.WF(c) && v'.WF(c)
  {
    var cLbl := CoordinatorHost.DecideLbl(decision);
    var pLbl := ParticipantHost.DecideLbl(decision);
    && c.ValidCoordinatorId(cidx)
    && Host.Next(c.hosts[cidx], v.hosts[cidx], v'.hosts[cidx], Host.CL(cLbl))
    && (forall pidx:nat | c.ValidParticipantId(pidx)
        :: Host.Next(c.hosts[pidx], v.hosts[pidx], v'.hosts[pidx], Host.PL(pLbl))
    )
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
  {
    match step
      case VoteReqStep(cidx) => NextVoteReqStep(c, v, v', cidx)
      case SendVoteStep(pidx, cidx, vote) => NextSendVoteStep(c, v, v', pidx, cidx, vote)
      case DecideStep(cidx, decision) => NextDecideStep(c, v, v', cidx, decision)
      case StutterStep => && v == v'
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }

  function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
      case CoordinatorVariables(coordinator) => coordinator.decision
      case ParticipantVariables(participant) => participant.decision
  }
}


