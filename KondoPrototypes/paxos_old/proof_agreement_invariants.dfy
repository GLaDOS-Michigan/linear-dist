include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"

module Proof_Agreement_Invs {
import opened Network
import opened Agents
import opened Types
import opened Synod


/* All correct processes decide the same value */
ghost predicate Agreement(c:Constants, ds:DistrSys) 
    requires c.WF()
    requires ds.WF(c)
{
    forall i1, i2 | 
        && c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1) 
        && c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds, i2) 
    :: TwoLeadersHaveSameV(c, ds, i1, i2)
}


/* Only one value can be chosen */
ghost predicate Agreement_Chosen_Safety(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
{
    forall b1, b2, v1, v2 | Chosen(c, ds, b1, v1) && Chosen(c, ds, b2, v2)
    :: v1 == v2
}


ghost predicate Trivialities(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && BallotBottomness_ValueNilness(c, ds)
    && AllPacketsValid(c, ds)
}


/* Invariants for establishing Agreement */
ghost predicate Agreement_Chosen_Inv(c:Constants, ds:DistrSys) 
{
    && c.WF()
    && ds.WF(c)
    && Trivialities(c, ds)
    && Agreement_Chosen_Inv_Common(c, ds)
    // Chosen
    && Agreement_Chosen_Inv_ChosenProperties(c, ds)
    && Agreement_Chosen_Safety(c, ds)
}

ghost predicate Agreement_Chosen_Inv_ChosenProperties(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
{
    forall b, v | Chosen(c, ds, b, v) 
        :: Agreement_Chosen_Inv_SomeValChosen(c, ds, b, v)
}

/* Things that are always true */
ghost predicate Agreement_Chosen_Inv_Common(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
{
    && OneValuePerBallot(c, ds)

    // Leader state
    && LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
    && LdrPromisesSetCorrespondToPromiseMsg(c, ds)
    && LdrPromisesSetHaveLeaderBallot(c, ds)
    && LdrPromisesSetHaveUniqueSrc(c, ds)
    && LdrBallotBelongsToItself(c, ds)

    // Acceptor state
    && AccPromisedBallotLargerThanAccepted(c, ds)
    && PromiseMsgImpliesPromised(c, ds)
    && AcceptMsgImpliesAccepted(c, ds)

    // Messages
    && PromiseMsgBalLargerThanAcceptedItSees(c, ds)
    && PromiseVBImpliesAcceptMsg(c, ds)
    && PromisedImpliesNoMoreAccepts(c, ds)
    && ProposeMsgImpliesQuorumOfPromise(c, ds)
    && ProposeMsgHasBalIdxAsSource(c, ds)
    && AcceptedImpliesAcceptMsg(c, ds)
    && AcceptMsgImpliesProposeMsg(c, ds)
    && LeaderP1ImpliesAllProposeHasLtBal(c, ds)
    && LeaderP2ImpliesAllProposeHasLtEqBal(c, ds)
    && LeaderP2ImpliesQuorumOfPromise(c, ds)    
}


/* Things that are true if v is chosen with ballot b. */
ghost predicate Agreement_Chosen_Inv_SomeValChosen(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
    requires Chosen(c, ds, b, v) 
{
    && LargerBallotPhase2LeadersV(c, ds, b, v)
    && LargerBallotAcceptors(c, ds, b, v)
    && LargerBallotAcceptMsgs(c, ds, b, v)
    && LargerBallotPromiseMsgs(c, ds, b, v)
    && LargerBallotProposeMsgs(c, ds, b, v)
    && LargerBallotsPromiseQrms(c, ds, b)
    && SameBallotLeaderNotInPhase1(c, ds, b)
}


/* Only one value can be associated with each ballot */
ghost predicate OneValuePerBallot(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && OneValuePerBallot_UniqueLdrBals(c, ds)
    && OneValuePerBallot_PromiseMsg(c, ds)
    && OneValuePerBallot_ProposeMsg(c, ds)
    && OneValuePerBallot_AcceptMsg(c, ds)
    && OneValuePerBallot_ProposeMsgAndLeader(c, ds)
}

ghost predicate OneValuePerBallot_UniqueLdrBals(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall l1, l2 | c.ValidLdrIdx(l1) && c.ValidLdrIdx(l2) && l1!=l2 
    :: ds.leaders[l1].ballot != ds.leaders[l2].ballot
}

ghost predicate OneValuePerBallot_PromiseMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prom_p1, prom_p2 | 
        && isPromisePkt(ds, prom_p1) && isPromisePkt(ds, prom_p2) 
        && prom_p1.msg.vb.b == prom_p2.msg.vb.b
    :: 
        prom_p1.msg.vb.v == prom_p2.msg.vb.v
}

ghost predicate OneValuePerBallot_ProposeMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prop_p1, prop_p2 | 
        && isProposePkt(ds, prop_p1) && isProposePkt(ds, prop_p2)
        && prop_p1.msg.bal == prop_p2.msg.bal
    :: 
        prop_p1.msg.val == prop_p2.msg.val
}

ghost predicate OneValuePerBallot_AcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall acc_p1, acc_p2 | 
        && isAcceptPkt(ds, acc_p1) && isAcceptPkt(ds, acc_p2)
        && acc_p1.msg.bal == acc_p2.msg.bal
    :: 
        acc_p1.msg.val == acc_p2.msg.val
}

ghost predicate OneValuePerBallot_ProposeMsgAndLeader(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall l_idx, prop | 
        && c.ValidLdrIdx(l_idx)
        && LeaderInPhase2(c, ds, l_idx) 
        && isProposePkt(ds, prop)
        && prop.msg.bal == ds.leaders[l_idx].ballot
    :: 
        prop.msg.val == ds.leaders[l_idx].val
}


/* For each promise message Promise(b', (b, v)), we have b' > b */
ghost predicate PromiseMsgBalLargerThanAcceptedItSees(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prom_p | isPromisePkt(ds, prom_p)
    :: BalLt(prom_p.msg.vb.b, prom_p.msg.bal)
}


/* For each promise message p, if it contains an accepted (v, b), then there is an 
* Accept(b) in the network from the same source */
ghost predicate PromiseVBImpliesAcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prom_p | 
        && isPromisePkt(ds, prom_p)
        && prom_p.msg.vb.b != Bottom
    :: 
    (exists acc_p :: 
        && isAcceptPkt(ds, acc_p)
        && acc_p.src == prom_p.src
        && acc_p.msg == Accept(prom_p.msg.vb.b, prom_p.msg.vb.v)
    )
}

/* If an Promise msg in network with ballot b, then acceptor x 
* has promise >= b */
ghost predicate PromiseMsgImpliesPromised(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p:Packet | c.ValidAccIdx(p.src.idx) && isPromisePkt(ds, p)
    :: BalLtEq(p.msg.bal, ds.acceptors[p.src.idx].promised)
}

/* If an Accept msg in network with src x, ballot b, then balval of acceptor x 
* has ballot >= b */
ghost predicate AcceptMsgImpliesAccepted(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p:Packet | c.ValidAccIdx(p.src.idx) && isAcceptPkt(ds, p)
    :: BalLtEq(p.msg.bal, ds.acceptors[p.src.idx].accepted.b)
}

/* If an acceptor has currently accepted (b, v), then there must be an Accept(b, v) message in the network
* from that acceptor */
ghost predicate AcceptedImpliesAcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall idx | 
        && c.ValidAccIdx(idx) 
        && ds.acceptors[idx].accepted.b != Bottom
    :: (
    exists p ::
        && isAcceptPkt(ds, p)
        && p.msg == Accept(ds.acceptors[idx].accepted.b, ds.acceptors[idx].accepted.v)
        && p.src == Id(Acc, idx)
    )
}

/* For each Accept(b,v) message, there is a corresponding Propose message Propose(b,v) 
* in the network */
ghost predicate AcceptMsgImpliesProposeMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall acc_p | isAcceptPkt(ds, acc_p)
    :: (
    var b, v := acc_p.msg.bal, acc_p.msg.val;
    var ldr := acc_p.dst;
    var acc := acc_p.src;
    exists prop_p :: 
        && isProposePkt(ds, prop_p)
        && prop_p.src == ldr
        && prop_p.dst == acc
        && prop_p.msg == Propose(b, v)
    )
}

/* For each leader in phase 1, all proposals in the network has ballot strictly less than
* current ballot */
ghost predicate LeaderP1ImpliesAllProposeHasLtBal(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall id | c.ValidLdrId(id) && LeaderInPhase1(c, ds, id.idx)
    :: AllProposalsFromSourceBalLt(c, ds, id) 
}

ghost predicate AllProposalsFromSourceBalLt(c:Constants, ds:DistrSys, id:Id) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrId(id)
{
    forall p | isProposePkt(ds, p) && p.src == id 
    :: BalLt(p.msg.bal, ds.leaders[id.idx].ballot)
}

/* For each leader in phase 2, all proposals in the network has ballot strictly less than
* current ballot */
ghost predicate LeaderP2ImpliesAllProposeHasLtEqBal(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall id | c.ValidLdrId(id) && LeaderInPhase2(c, ds, id.idx)
    :: AllProposalsFromSourceBalLtEq(c, ds, id) 
}

ghost predicate AllProposalsFromSourceBalLtEq(c:Constants, ds:DistrSys, id:Id) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrId(id)
{
    forall p | isProposePkt(ds, p) && p.src == id 
    :: BalLtEq(p.msg.bal, ds.leaders[id.idx].ballot)
}


/* For each leader in phase 2, there is a corresponding quorum of Promise packets 
* in the network supporting it's ballot */
ghost predicate LeaderP2ImpliesQuorumOfPromise(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall idx | c.ValidLdrIdx(idx) && LeaderInPhase2(c, ds, idx)
    :: (exists qrm  
        :: QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val))
}

ghost predicate QrmHighestBallotNilOrV(c:Constants, ds:DistrSys, qrm:set<Packet>, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
{
    && QuorumOfPromiseMsgs(c, ds, qrm, b)
    && (|| PromisePktWithHighestBallot(qrm).msg.vb.v == v
        || PromisePktWithHighestBallot(qrm).msg.vb.v == Nil
    )
}


/* For each Propose(v, b) message, there is a corresponding quorum of Promise packets 
* in the network */
// TONY: I think this is actually implied by LdrPromisesSetCorrespondToPromiseMsg
ghost predicate ProposeMsgImpliesQuorumOfPromise(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prop_p | isProposePkt(ds, prop_p)
    :: (
    var b := prop_p.msg.bal;
    var v := prop_p.msg.val;
    exists qrm  :: 
        && QuorumOfPromiseMsgs(c, ds, qrm, b)
        && (|| PromisePktWithHighestBallot(qrm).msg.vb.v == v
            || PromisePktWithHighestBallot(qrm).msg.vb.v == Nil
        )
    )
}

/* For each Propose(v, b) message, the ballot b identifies the sender */
ghost predicate ProposeMsgHasBalIdxAsSource(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p | isProposePkt(ds, p) && p.msg.bal.Ballot? :: p.src == Id(Ldr, p.msg.bal.idx)
}



/* All l.accepts collected by l came from network */
ghost predicate LdrAcceptsSetCorrespondToAcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: AcceptsSetCorrespondToAcceptMsg(c, ds, i) 
}

ghost predicate AcceptsSetCorrespondToAcceptMsg(c:Constants, ds:DistrSys, i:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i)
{
    forall s | s in ds.leaders[i].accepts
    :: Packet(s, Id(Ldr, i), Accept(ds.leaders[i].ballot, ds.leaders[i].val)) in ds.network.sentPackets
}

/* All l.promises collected by l came from network */
ghost predicate LdrPromisesSetCorrespondToPromiseMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: PromisesSetCorrespondToPromiseMsg(c, ds, i)
}

ghost predicate PromisesSetCorrespondToPromiseMsg(c:Constants, ds:DistrSys, i:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i)
{
    forall p | p in ds.leaders[i].promises :: isPromisePkt(ds, p)
}


/* All l.promises collected by l have same ballot as l */
ghost predicate LdrPromisesSetHaveLeaderBallot(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: PromisesSetHaveBallotB(c, ds, i)
}

/* All l.promises collected by l has unique source */
ghost predicate LdrPromisesSetHaveUniqueSrc(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: UniqueSources(ds.leaders[i].promises)
}

/* Leader ballots have its own idx as identifier */
ghost predicate LdrBallotBelongsToItself(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i:nat | c.ValidLdrIdx(i) && ds.leaders[i].ballot != Bottom 
    :: ds.leaders[i].ballot.idx == i
}


ghost predicate PromisesSetHaveBallotB(c:Constants, ds:DistrSys, i:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i) 
{
    forall p | p in ds.leaders[i].promises && p.msg.Promise? :: p.msg.bal == ds.leaders[i].ballot
}


/* Acceptor promised ballot always at least as large as accepted ballot */
ghost predicate AccPromisedBallotLargerThanAccepted(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidAccIdx(i) 
    :: BalLtEq(ds.acceptors[i].accepted.b, ds.acceptors[i].promised)
}


/* If a promised packet promised b', with previously accepted (v, b), then 
*   - there can be no accept messages in network, from the same acceptor, 
*       with ballot x such that b < x < b' 
*   - the acceptor either has (v, b) accepted, or accepted some ballot >= b'
*/
ghost predicate PromisedImpliesNoMoreAccepts(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds) 
{
    forall prom_p | 
        && prom_p in ds.network.sentPackets 
        && prom_p.msg.Promise?
    :: 
    var p1_promised_bal := prom_p.msg.bal;
    var p1_accepted_bal := prom_p.msg.vb.b;
    && AcceptorConstraint(c, ds, prom_p.src, p1_promised_bal, p1_accepted_bal)
    && AcceptMessageConstraint(c, ds, prom_p.src, p1_promised_bal, p1_accepted_bal)
}

ghost predicate AcceptorConstraint(c:Constants, ds:DistrSys, src:Id, p1_promised_bal:Ballot, p1_accepted_bal:Ballot) 
    requires c.WF() && ds.WF(c)
    requires src.agt == Acc && c.ValidAccIdx(src.idx)
{
    var acc := ds.acceptors[src.idx];
    && BalLtEq(p1_promised_bal, acc.promised)
    && (|| acc.accepted.b == p1_accepted_bal
        || BalLtEq(p1_promised_bal, acc.accepted.b)
    )
}

ghost predicate AcceptMessageConstraint(c:Constants, ds:DistrSys, src:Id, p1_promised_bal:Ballot, p1_accepted_bal:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall acc_p | 
        && isAcceptPkt(ds, acc_p)
        && acc_p.src == src
    :: 
        || BalLtEq(acc_p.msg.bal, p1_accepted_bal)
        || BalLtEq(p1_promised_bal, acc_p.msg.bal)
}



ghost predicate BallotBottomness_ValueNilness(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && BallotBottomness_ValueNilness_Packets(c, ds)
    && BallotBottomness_ValueNilness_Agents(c, ds)
}

ghost predicate BallotBottomness_ValueNilness_Packets(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p ::
    if isPreparePkt(ds, p) then p.msg.bal != Bottom
    else if isPromisePkt(ds, p) then p.msg.vb.v == Nil <==> p.msg.vb.b == Bottom
    else if isAcceptPkt(ds, p) then p.msg.val != Nil && p.msg.bal != Bottom
    else if isProposePkt(ds, p) then p.msg.val != Nil && p.msg.bal != Bottom
    else true
}

ghost predicate BallotBottomness_ValueNilness_Agents(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && (forall l | l in ds.leaders :: l.ballot != Bottom && l.val != Nil)
    && (forall a | a in ds.acceptors :: a.accepted.b == Bottom <==> a.accepted.v == Nil)
}



/* If v is chosen with ballot b, then all phase 2 leaders with ballots
* b' >= b must be of v */
ghost predicate LargerBallotPhase2LeadersV(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
{
    forall i' | 
        && c.ValidLdrIdx(i') 
        && BalLtEq(b, ds.leaders[i'].ballot) 
        && LeaderInPhase2(c, ds, i') 
    :: LeaderHasValueV(c, ds, i', v)
}

/* If v is chosen with ballot b, then for any acceptor that accepted a ballot b'>=b, 
* the accepted value is v */
ghost predicate LargerBallotAcceptors(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
{
    forall i' | c.ValidAccIdx(i') && BalLtEq(b, ds.acceptors[i'].accepted.b)
    :: AcceptorHasValueV(c, ds, i', v)
}

/* If v is chosen with ballot b, then for any Accept msgs with ballot b'>=b, 
* the value is v */
ghost predicate LargerBallotAcceptMsgs(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
{
    forall p | isAcceptPkt(ds, p) && BalLtEq(b, p.msg.bal)
    :: p.msg.val == v
}


/* If v is chosen with ballot b, then for any Promise msgs with valbal ballot b'>=b, 
* the valbal value is v */
ghost predicate LargerBallotPromiseMsgs(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
{
    forall p | isPromisePkt(ds, p) && BalLtEq(b, p.msg.vb.b)
    :: p.msg.vb.v == v
}

/* If v is chosen with ballot b, then for any Propose msgs with ballot b'>=b, 
* the value is v */
ghost predicate LargerBallotProposeMsgs(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
{
    forall p | isProposePkt(ds, p) && BalLtEq(b, p.msg.bal)
    :: p.msg.val == v
}

/* If v is chosen with ballot b, then all Promise quorums for ballots
* b' >= b must come from an acceptor that accepted (b, v) */
ghost predicate LargerBallotsPromiseQrms(c:Constants, ds:DistrSys, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall b' | BalLt(b, b') 
    :: LargerBalQuorumHasSeenB(c, ds, b, b')
}

ghost predicate LargerBalQuorumHasSeenB(c:Constants, ds:DistrSys, b:Ballot, b':Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds, qrm, b') 
    :: QuorumHasSeenB(c, qrm, b)
}

ghost predicate QuorumHasSeenB(c:Constants, qrm:set<Packet>, b:Ballot) 
    requires forall p | p in qrm :: p.msg.Promise?
{
    exists p :: p in qrm && BalLtEq(b, p.msg.vb.b)
}


/* If v is chosen with ballot b, then the leader with current ballot b cannot be in Phase1 */
ghost predicate SameBallotLeaderNotInPhase1(c:Constants, ds:DistrSys, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) && ds.leaders[i].ballot == b
    :: !LeaderInPhase1(c, ds, i)
}

// ghost predicate LeaderHasQuorumOfAccepts(c:Constants, ds:DistrSys, i:int) 
//     requires c.WF() && ds.WF(c)
//     requires c.ValidLdrIdx(i)
// {
//     |ds.leaders[i].accepts| == c.f + 1
// }

}