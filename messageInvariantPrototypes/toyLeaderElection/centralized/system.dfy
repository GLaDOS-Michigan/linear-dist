include "hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import Host

  datatype Constants = Constants(hostConstants: seq<Host.Constants>)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hostConstants)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hostConstants|
    }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hostConstants, hosts)
    }

    ghost predicate IsLeader(c: Constants, h: HostId) 
      requires WF(c)
      requires c.ValidHostId(h)
    {
      hosts[h].isLeader
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hostConstants, v.hosts)
  }

  datatype Step =
    | HostLocalStep(host: HostId)   // host can be nominated, or declare victory in this step
    | VoteReqStep(nominee: HostId, receiver: HostId)
    | VoteStep(voter: HostId, nominee: HostId)
    | StutterStep()

  
  ghost predicate NextHostLocalStep(c: Constants, v: Variables, v': Variables, host: HostId) 
    requires v.WF(c) && v'.WF(c)
  {
    && var lbl := Host.InternalLbl();
    && c.ValidHostId(host)
    && Host.Next(c.hostConstants[host], v.hosts[host], v'.hosts[host], lbl)
    && (forall idx: HostId | c.ValidHostId(idx) && idx != host
        :: v'.hosts[idx] == v.hosts[idx]
    )
  }

  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, nominee: HostId, receiver: HostId)
    requires v.WF(c) && v'.WF(c)
  {
    && var nomineeLbl := Host.SendVoteReqLbl(nominee);
    && var receiverLbl := Host.RecvVoteReqLbl(nominee);
    && nominee != receiver  // important to not introduce false
    && c.ValidHostId(nominee)
    && c.ValidHostId(receiver)
    && Host.Next(c.hostConstants[nominee], v.hosts[nominee], v'.hosts[nominee], nomineeLbl)
    && Host.Next(c.hostConstants[receiver], v.hosts[receiver], v'.hosts[receiver], receiverLbl)
    && (forall idx: HostId | c.ValidHostId(idx) && idx != nominee && idx != receiver
        :: v'.hosts[idx] == v.hosts[idx]
    )
  }

  ghost predicate NextVoteStep(c: Constants, v: Variables, v': Variables, voter: HostId, nominee: HostId)
    requires v.WF(c) && v'.WF(c)
  {
    && var voterLbl := Host.SendVoteLbl(voter, nominee);
    && var nomineeLbl := Host.RecvVoteLbl(voter, nominee);
    && nominee != voter  // important to not introduce false
    && c.ValidHostId(voter)
    && c.ValidHostId(nominee)
    && Host.Next(c.hostConstants[voter], v.hosts[voter], v'.hosts[voter], voterLbl)
    && Host.Next(c.hostConstants[nominee], v.hosts[nominee], v'.hosts[nominee], nomineeLbl)
    && (forall idx: HostId | c.ValidHostId(idx) && idx != nominee && idx != voter
        :: v'.hosts[idx] == v.hosts[idx]
    )
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
  {
    match step
      case HostLocalStep(host) => NextHostLocalStep(c, v, v', host)
      case VoteReqStep(nominee, receiver) => NextVoteReqStep(c, v, v', nominee, receiver)
      case VoteStep(voter, nominee) => NextVoteStep(c, v, v', voter, nominee)
      case StutterStep => v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }

}