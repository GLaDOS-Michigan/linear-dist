
include "hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(
    coordinator: seq<CoordinatorHost.Constants>,
    participants: seq<ParticipantHost.Constants>)
  {
    ghost predicate WF() {
      && CoordinatorHost.GroupWFConstants(coordinator, |participants|)
      && ParticipantHost.GroupWFConstants(participants)
    }

    ghost predicate ValidParticipantId(id: HostId) {
      id < |participants|
    }

    ghost function GetCoordinator() : CoordinatorHost.Constants 
      requires WF()
    {
      coordinator[0]
    }
  }

  datatype Variables = Variables(
    coordinator: seq<CoordinatorHost.Variables>,
    participants: seq<ParticipantHost.Variables>
  )
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && CoordinatorHost.GroupWF(c.coordinator, coordinator, |c.participants|)
      && ParticipantHost.GroupWF(c.participants, participants)
    }

    ghost function GetCoordinator(c: Constants) : CoordinatorHost.Variables 
      requires WF(c)
    {
      coordinator[0]
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && CoordinatorHost.GroupInit(c.coordinator, v.coordinator)
    && ParticipantHost.GroupInit(c.participants, v.participants)
  }

  datatype Step =
    | VoteReqStep(coordinator: HostId)
    | SendVoteStep(participant: HostId, vote: Vote)
    | DecideStep(decision: Decision)
    | StutterStep()

    
  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, pidx: HostId) 
    requires v.WF(c) && v'.WF(c)
  {
    var cLbl := CoordinatorHost.VoteReqLbl();
    var pLbl := ParticipantHost.VoteReqLbl();
    && c.ValidParticipantId(pidx)
    && ParticipantHost.Next(c.participants[pidx], v.participants[pidx], v'.participants[pidx], pLbl)
    && CoordinatorHost.Next(c.GetCoordinator(), v.GetCoordinator(c), v'.GetCoordinator(c), cLbl)
    && (forall x:nat | c.ValidParticipantId(x)
        ::  v.participants[pidx] == v'.participants[pidx])
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, pidx: HostId, vote: Vote) 
    requires v.WF(c) && v'.WF(c)
  {
    var cLbl := CoordinatorHost.ReceiveVoteLbl(vote, pidx);
    var pLbl := ParticipantHost.SendVoteLbl(vote);
    && c.ValidParticipantId(pidx)
    && CoordinatorHost.Next(c.GetCoordinator(), v.GetCoordinator(c), v'.GetCoordinator(c), cLbl)
    && ParticipantHost.Next(c.participants[pidx], v.participants[pidx], v'.participants[pidx], pLbl)
    && (forall x:HostId | c.ValidParticipantId(x)
        ::  v.participants[x] == v'.participants[x])
  }

  ghost predicate NextDecideStep(c: Constants, v: Variables, v': Variables, decision: Decision)
    requires v.WF(c) && v'.WF(c)
  {
    var cLbl := CoordinatorHost.DecideLbl(decision);
    var pLbl := ParticipantHost.DecideLbl(decision);
    && CoordinatorHost.Next(c.GetCoordinator(), v.GetCoordinator(c), v'.GetCoordinator(c), cLbl)
    && (forall x:nat | c.ValidParticipantId(x)
        :: ParticipantHost.Next(c.participants[x], v.participants[x], v'.participants[x], pLbl))
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
  {
    match step
      case VoteReqStep(pidx) => NextVoteReqStep(c, v, v', pidx)
      case SendVoteStep(pidx, vote) => NextSendVoteStep(c, v, v', pidx, vote)
      case DecideStep(decision) => NextDecideStep(c, v, v', decision)
      case StutterStep => v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }
}


