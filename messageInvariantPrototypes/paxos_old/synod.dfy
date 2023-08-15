include "types.dfy"
include "network.dfy"
include "agents.dfy"

module Synod {
import opened Network
import opened Agents
import opened Types


datatype Constants = Constants(f:nat, ldr_ids:seq<Id>, ldr_vals:seq<Value>, acc_ids:seq<Id>) {
    ghost predicate WF() {
        && f >= 1
        && |ldr_ids| >= 1
        && |acc_ids| == 2*f+1
        && ValidLdrVals()
        && ValidTypes()
        && ValidIds()
        && UniqueIds()
    }

    ghost predicate ValidLdrIdx(i:int) {
        0<=i<|ldr_ids|
    }

    ghost predicate ValidAccIdx(i:int) {
        0<=i<|acc_ids|
    }

    ghost predicate ValidLdrId(id:Id) {
        id.agt == Ldr && ValidLdrIdx(id.idx)
    }

    ghost predicate ValidAccId(id:Id) {
        id.agt == Acc && ValidAccIdx(id.idx)
    }

    ghost predicate ValidTypes() {
        && (forall l | l in ldr_ids :: l.agt.Ldr?)
        && (forall l | l in acc_ids :: l.agt.Acc?)
    }

    ghost predicate ValidLdrVals() {
        && |ldr_vals| == |ldr_ids|
        && forall i | ValidLdrIdx(i) :: ldr_vals[i] != Nil
    }

    ghost predicate UniqueIds() {
        && seqIsUnique(ldr_ids)
        && seqIsUnique(acc_ids)
        // && (forall i, j | ValidLdrIdx(i) && ValidLdrIdx(j) && ldr_ids[i]==ldr_ids[j] :: i == j)
        // && (forall i, j | ValidAccIdx(i) && ValidAccIdx(j) && acc_ids[i]==acc_ids[j] :: i == j)
    }

    ghost predicate ValidIds() {
        && (forall i | ValidLdrIdx(i) :: ldr_ids[i].idx == i)
        && (forall i | ValidAccIdx(i) :: acc_ids[i].idx == i)
    }
}

datatype DistrSys = DistrSys(
    network: Environment,
    leaders: seq<Leader>,
    acceptors: seq<Acceptor>
) {
    ghost predicate WF(c: Constants)
        requires c.WF()
    {
        && |leaders| == |c.ldr_ids|
        && |acceptors| == |c.acc_ids|
        && (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.id == c.ldr_ids[i])
        && (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.initval == c.ldr_vals[i])
        && (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.accConf == c.acc_ids)
        && (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.f == c.f)
        && (forall i | c.ValidAccIdx(i) :: acceptors[i].consts.id == c.acc_ids[i])
    }
}


/*****************************************************************************************
*                                        DS Init                                         *
*****************************************************************************************/
ghost predicate Init(c:Constants, s:DistrSys) 
{
    && c.WF()
    && s.WF(c)
    && EnvironmentInit(s.network)
    && |s.leaders| == |c.ldr_ids|
    && |s.acceptors| == |c.acc_ids|
    && (forall i | c.ValidLdrIdx(i) :: LeaderInit(s.leaders[i], c.ldr_ids[i], c.acc_ids, c.f, c.ldr_vals[i]))
    && (forall i | c.ValidAccIdx(i) :: AcceptorInit(s.acceptors[i], c.acc_ids[i]))
}


/*****************************************************************************************
*                                        DS Next                                         *
*****************************************************************************************/

ghost predicate Next(c:Constants, s:DistrSys, s':DistrSys) {
    && c.WF()
    && s.WF(c)
    && s'.WF(c)
    && exists actor, recvIos, sendIos :: PaxosNextOneAgent(c, s, s', actor, recvIos, sendIos)
}


ghost predicate PaxosNextOneAgent(c:Constants, s:DistrSys, s':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires c.WF() && s.WF(c) && s'.WF(c)
{
    && ValidActor(c, actor)
    && PaxosNextOneAgent_Agent(c, s, s', actor, recvIos, sendIos)
    && s.network.nextStep == IoStep(actor, recvIos, sendIos)
    && EnvironmentNext(s.network, s'.network)
}

ghost predicate PaxosNextOneAgent_Agent(c:Constants, s:DistrSys, s':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires c.WF() && s.WF(c) && s'.WF(c)
    requires ValidActor(c, actor)
{
    match actor.agt {
        case Ldr => 
            && s'.acceptors == s.acceptors
            && |s'.leaders| == |s.leaders|
            && s'.leaders == s.leaders[actor.idx := s'.leaders[actor.idx]]
            && LeaderNext(s.leaders[actor.idx], s'.leaders[actor.idx], recvIos, sendIos)
        case Acc => 
            && s'.leaders == s.leaders
            && |s'.acceptors| == |s.acceptors|
            && s'.acceptors == s.acceptors[actor.idx := s'.acceptors[actor.idx]]
            && AcceptorNext(s.acceptors[actor.idx], s'.acceptors[actor.idx], recvIos, sendIos)
    }
}

ghost predicate ValidActor(c:Constants, actor:Id) 
    requires c.WF()
{
     match actor.agt {
        case Ldr => c.ValidLdrIdx(actor.idx)
        case Acc => c.ValidAccIdx(actor.idx)
    }
}


/*****************************************************************************************
*                                        Utils                                           *
*****************************************************************************************/


ghost predicate Chosen(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
{
    exists qrm :: 
        && QuorumOfAcceptMsgs(c, ds, qrm, b) 
        && AccPacketsHaveValueV(qrm, v)
}

ghost predicate AccPacketsHaveValueV(S:set<Packet>, v:Value) 
    requires forall p | p in S :: p.msg.Accept?
{   
    forall p:Packet | p in S :: p.msg.val == v
}


ghost predicate SomeValueChosen(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
{
    exists v, b :: Chosen(c, ds, b, v)
}


ghost predicate QuorumOfAcceptors(c:Constants, q:set<int>) 
    requires c.WF() 
{
    && |q| >= c.f + 1
    && forall idx | idx in q :: c.ValidAccIdx(idx)
}

ghost predicate UniqueSources(qrm:set<Packet>) {
    forall p1, p2 | p1 in qrm && p2 in qrm 
    :: p1.src == p2.src ==> p1 == p2
}

ghost predicate SameDest(qrm:set<Packet>) {
    forall p1, p2 | p1 in qrm && p2 in qrm :: p1.dst == p2.dst
}

/* qrm is a quorum of promise messages with ballot b */
ghost predicate QuorumOfPromiseMsgs(c:Constants, ds:DistrSys, qrm:set<Packet>, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    && |qrm| >= c.f + 1
    && UniqueSources(qrm)
    // && SameDest(qrm)
    && (forall p | p in qrm :: 
            && isPromisePkt(ds, p)
            && p.msg.bal == b
    )
}

/* acc_qrm is a quorum of acceptors with promised ballot >= b */
ghost predicate QuorumOfAcceptorsPromised(c:Constants, ds:DistrSys, acc_qrm:set<Id>, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    && |acc_qrm| >= c.f + 1
    && (forall id | id in acc_qrm :: 
            && c.ValidAccId(id)
            && BalLtEq(b, ds.acceptors[id.idx].promised)
    )
}

/* acc_qrm is a quorum of acceptors with accepted (b, _) */
ghost predicate QuorumOfAcceptorsAccepted(c:Constants, ds:DistrSys, acc_qrm:set<Id>, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    && |acc_qrm| >= c.f + 1
    && (forall id | id in acc_qrm :: 
            && c.ValidAccId(id)
            && BalLtEq(b, ds.acceptors[id.idx].accepted.b)
    )
}

/* qrm is a quorum of accept messages with ballot b, value v */
ghost predicate QuorumOfAcceptMsgs(c:Constants, ds:DistrSys, qrm:set<Packet>, b:Ballot) 
    requires c.WF()
{
    && |qrm| >= c.f + 1
    && SetOfAcceptMsgs(c, ds, qrm, b)
}

/* S is a set of accept messages with ballot b, value v */
ghost predicate SetOfAcceptMsgs(c:Constants, ds:DistrSys, S:set<Packet>, b:Ballot) 
    requires c.WF()
{
    && UniqueSources(S)
    && (forall p | p in S :: 
            && isAcceptPkt(ds, p)
            && p.msg.bal == b
    )
}


ghost predicate AllPacketsValid(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets
    :: ValidPacketSourceDest(c, ds, p)
}


ghost predicate ValidPacketSourceDest(c:Constants, ds:DistrSys, p:Packet) 
    requires c.WF() && ds.WF(c)
{
    match p.msg {
        case Prepare(b) => 
            && ValidLeaderSource(c, ds, p)
            && ValidAcceptorDest(c, ds, p)
        case Promise(b, vb) => 
            && ValidAcceptorSource(c, ds, p)
            && ValidLeaderDest(c, ds, p)
        case Propose(b, v) => 
            && ValidLeaderSource(c, ds, p)
            && ValidAcceptorDest(c, ds ,p)
        case Accept(b, v) => 
            && ValidAcceptorSource(c, ds, p)
            && ValidLeaderDest(c, ds, p)
        case Preempt(b) => 
            && ValidAcceptorSource(c, ds, p)
            && ValidLeaderDest(c, ds, p)
    }
}

ghost predicate ValidAcceptorSource(c:Constants, ds:DistrSys, p:Packet) 
    requires c.WF() && ds.WF(c)
{
    && p.src.agt == Acc 
    && c.ValidAccIdx(p.src.idx)
}

ghost predicate ValidLeaderSource(c:Constants, ds:DistrSys, p:Packet) 
    requires c.WF() && ds.WF(c)
{
    && p.src.agt == Ldr 
    && c.ValidLdrIdx(p.src.idx)
}

ghost predicate ValidAcceptorDest(c:Constants, ds:DistrSys, p:Packet) 
    requires c.WF() && ds.WF(c)
{
    && p.dst.agt == Acc 
    && c.ValidAccIdx(p.dst.idx)
}

ghost predicate ValidLeaderDest(c:Constants, ds:DistrSys, p:Packet) 
    requires c.WF() && ds.WF(c)
{
    && p.dst.agt == Ldr 
    && c.ValidLdrIdx(p.dst.idx)
}

ghost predicate LeaderInPhase1(c:Constants, ds:DistrSys, idx:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    ds.leaders[idx].state == P1a || ds.leaders[idx].state == P1b
}


ghost predicate LeaderInPhase2(c:Constants, ds:DistrSys, idx:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    ds.leaders[idx].state == P2a || ds.leaders[idx].state == P2b
}

ghost predicate LeaderHasDecided(c:Constants, ds:DistrSys, idx:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    ds.leaders[idx].state == Decided
}

ghost predicate LeaderHasBallotB(c:Constants, ds:DistrSys, idx:int, b:Ballot) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    ds.leaders[idx].ballot == b
}

ghost predicate LeaderHasValueV(c:Constants, ds:DistrSys, idx:int, v:Value) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    ds.leaders[idx].val == v
}

ghost predicate AcceptorHasValueV(c:Constants, ds:DistrSys, idx:int, v:Value) 
    requires c.WF() && ds.WF(c)
    requires c.ValidAccIdx(idx)
{
    ds.acceptors[idx].accepted.v == v
}

ghost predicate TwoLeadersHaveSameV(c:Constants, ds:DistrSys, i1:int, i2:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i1) && c.ValidLdrIdx(i2)
{
    LeaderHasValueV(c, ds, i1, ds.leaders[i2].val)
}

ghost predicate LeaderIdxDecidedV(c:Constants, ds:DistrSys, idx:int, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    && LeaderHasDecided(c, ds, idx)
    && LeaderHasValueV(c, ds, idx,v)
    && LeaderHasBallotB(c, ds, idx, b)
}

ghost predicate SomeLeaderHasDecided(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    exists i :: c.ValidLdrIdx(i) && LeaderHasDecided(c, ds, i)
}

ghost predicate isPreparePkt(ds:DistrSys, p:Packet)
{
    p in ds.network.sentPackets && p.msg.Prepare?
}

ghost predicate isPromisePkt(ds:DistrSys, p:Packet)
{
    p in ds.network.sentPackets && p.msg.Promise?
}

ghost predicate isAcceptPkt(ds:DistrSys, p:Packet)
{
    p in ds.network.sentPackets && p.msg.Accept?
}

ghost predicate isProposePkt(ds:DistrSys, p:Packet)
{
    p in ds.network.sentPackets && p.msg.Propose?
}

}