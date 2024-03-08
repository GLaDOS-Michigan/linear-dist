include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_helper.dfy"
include "proof_axioms.dfy"
include "proof_agreement_invariants.dfy"
include "proof_agreement_chosenProperties1.dfy"
include "proof_agreement_chosenProperties2.dfy"

module Proof_Agreement {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Helper
import opened Proof_Axioms
import opened Proof_Agreement_Invs
import opened Proof_Agreement_ChosenProperties_1
import opened Proof_Agreement_ChosenProperties_2



/* Init ==> Agreement_Chosen_Inv */
lemma InitImpliesAgreementChosenInv(c:Constants, ds:DistrSys) 
    requires Init(c, ds)
    ensures Agreement_Chosen_Inv(c, ds)
{}


lemma NextPreservesTrivialities(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires c.WF() && ds.WF(c)
    requires Next(c, ds, ds')
    requires Trivialities(c, ds)
    ensures Trivialities(c, ds')
    ensures ds'.WF(c)
{
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Acc {
        assert recvIos[0] in ds.network.sentPackets;
    }
    forall p | p in ds'.network.sentPackets
    ensures ValidPacketSourceDest(c, ds', p)
    {}    
}


/* Agreement_Chosen_Inv && Next ==> Agreement_Chosen_Inv' */
lemma NextPreservesAgreementChosenInv(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires Next(c, ds, ds')
    ensures Agreement_Chosen_Inv(c, ds')
{
    NextPreservesTrivialities(c, ds, ds');
    AgreementChosenInv_Common(c, ds, ds');

    if SomeValueChosen(c, ds) {
        AgreementChosenInv_SomeChosen(c, ds, ds');
    } else {
        AgreementChosenInv_NoneChosen(c, ds, ds');
    }
    AgreementChosenInv_Safety(c, ds, ds');
}

lemma AgreementChosenInv_Safety(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c)
    requires Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Agreement_Chosen_Inv_ChosenProperties(c, ds')
    requires Next(c, ds, ds')
    ensures Agreement_Chosen_Safety(c, ds')
{
    forall b1, b2, v1, v2 | Chosen(c, ds', b1, v1) && Chosen(c, ds', b2, v2)
    ensures v1 == v2
    {
        if b1 != b2 {
            if BalLt(b1, b2) {
                assert v1 == v2;
            } else if BalLt(b2, b1) {
                assert v1 == v2;
            } else {
                assert b1 == b2;
                assert false;
            }
        }
    }
}

////////////////          Agreement Sub-Lemma: Common Invariants          ////////////////

lemma AgreementChosenInv_Common(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    ensures Agreement_Chosen_Inv_Common(c, ds')
{
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        AgreementChosenInv_LdrAction(c, ds, ds', actor, recvIos, sendIos);
    } else {
        AgreementChosenInv_AccAction(c, ds, ds', actor, recvIos, sendIos);
    }
}

lemma {:timeLimitMultiplier 3} AgreementChosenInv_LdrAction(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    ensures Agreement_Chosen_Inv_Common(c, ds')
{
    AgreementChosenInv_LdrAction_LdrAcceptsSetCorrespondToAcceptMsg(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_LdrAction_LdrPromisesSetHaveUniqueSrc(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_LdrAction_LeaderAndProposeBals(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_LdrAction_LeaderP2ImpliesQuorumOfPromise(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_LdrAction_OneValuePerBallot(c, ds, ds', actor, recvIos, sendIos);
}

lemma AgreementChosenInv_AccAction(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures Agreement_Chosen_Inv_Common(c, ds')
{
    lemma_NetworkMonotoneIncreasing(c, ds, ds'); 
    AgreementChosenInv_AccAction_PromiseMsgBalLargerThanAcceptedItSees(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_AccAction_PromiseVBImpliesAcceptMsg(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_AccAction_AcceptMsgImpliesAccepted(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_AccAction_AcceptMsgImpliesProposeMsg(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_AccAction_LeaderP2ImpliesQuorumOfPromise(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_AccAction_PromisedImpliesNoMoreAccepts(c, ds, ds', actor, recvIos, sendIos);
    AgreementChosenInv_AccAction_OneValuePerBallot(c, ds, ds', actor, recvIos, sendIos);
}


lemma AgreementChosenInv_LdrAction_LdrAcceptsSetCorrespondToAcceptMsg(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    ensures LdrAcceptsSetCorrespondToAcceptMsg(c, ds')
{
    lemma_NetworkMonotoneIncreasing(c, ds, ds');
    forall i | c.ValidLdrIdx(i) 
    ensures AcceptsSetCorrespondToAcceptMsg(c, ds', i) 
    {}
}

lemma AgreementChosenInv_LdrAction_LdrPromisesSetHaveUniqueSrc(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    ensures LdrPromisesSetHaveUniqueSrc(c, ds')
{
    forall idx | c.ValidLdrIdx(idx) 
    ensures UniqueSources(ds'.leaders[idx].promises)
    {}
}


lemma AgreementChosenInv_LdrAction_LeaderAndProposeBals(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires c.WF() && ds.WF(c)
    requires LeaderP1ImpliesAllProposeHasLtBal(c, ds)
    requires LeaderP2ImpliesAllProposeHasLtEqBal(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    ensures LeaderP1ImpliesAllProposeHasLtBal(c, ds')
    ensures LeaderP2ImpliesAllProposeHasLtEqBal(c, ds')
{}


lemma {:timeLimitMultiplier 5} AgreementChosenInv_LdrAction_LeaderP2ImpliesQuorumOfPromise(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires LdrPromisesSetCorrespondToPromiseMsg(c, ds')
    ensures LeaderP2ImpliesQuorumOfPromise(c, ds')
{
    lemma_NetworkMonotoneIncreasing(c, ds, ds');
    forall idx | c.ValidLdrIdx(idx) && LeaderInPhase2(c, ds', idx)
    ensures exists q :: QrmHighestBallotNilOrV(c, ds', q, ds'.leaders[idx].ballot, ds'.leaders[idx].val)
    {
        if idx == actor.idx {
            var l, l' := ds.leaders[idx], ds'.leaders[idx];
            match l.state {
                case P1a => 
                    lemma_LdrP1aGoToP1(c, ds, ds', actor, recvIos, sendIos);
                    assert false;
                case P1b => {
                    if recvIos[0].msg.Promise? {
                        var src, msg := recvIos[0].src, recvIos[0].msg;
                        if msg.bal == l.ballot && !exists p :: p in l.promises && p.src == src {
                            assert LeaderProcessValidPromise(l, l', recvIos[0], sendIos);
                            if |l.promises| == 2*l.consts.f {
                                var promises := l.promises + {recvIos[0]};
                                assert QrmHighestBallotNilOrV(c, ds', promises, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                            } else {
                                assert l'.state == l.state;
                                assert !LeaderInPhase2(c, ds', idx);
                            }
                        } else {
                            assert LeaderStutter(l, l', sendIos);
                            assert !LeaderInPhase2(c, ds', idx);
                        }
                    } else if recvIos[0].msg.Preempt? {
                        if BalLt(l.ballot, recvIos[0].msg.bal) {
                            assert l'.state == P1a;
                            assert !LeaderInPhase2(c, ds', idx);
                        } else {
                            assert LeaderStutter(l, l', sendIos);
                            var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
                            assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                        }
                    }
                }
                case P2a => {
                    var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
                    assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                }
                case P2b => {
                    match recvIos[0].msg {
                        case Accept(bal, val) => 
                            if recvIos[0].msg.bal == l.ballot && recvIos[0].src !in l.accepts {
                                var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
                                assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                            } else {
                                assert LeaderStutter(l, l', sendIos);
                                var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
                                assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                            }
                        case Preempt(bal) => 
                            if BalLt(l.ballot, recvIos[0].msg.bal) {
                                assert l'.state == P1a;
                                assert !LeaderInPhase2(c, ds', idx);
                            } else {
                                assert LeaderStutter(l, l', sendIos);
                                var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
                                assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                            }
                        case _ => 
                            assert LeaderStutter(l, l', sendIos);
                            var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
                            assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
                    }
                } 
                case Decided => {
                    assert LeaderStutter(l, l', sendIos);
                    assert !LeaderInPhase2(c, ds', idx);
                }
            }
        } else {
            assert ds'.leaders[idx] == ds.leaders[idx];
            var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
            assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
        }
    }
}


lemma AgreementChosenInv_LdrAction_OneValuePerBallot(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires c.WF() && ds.WF(c)
    requires OneValuePerBallot(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires LdrBallotBelongsToItself(c, ds)
    requires LeaderP1ImpliesAllProposeHasLtBal(c, ds)
    requires ProposeMsgHasBalIdxAsSource(c, ds)
    requires c.ValidLdrId(actor)
    ensures OneValuePerBallot(c, ds')
{
    AgreementChosenInv_LdrAction_OneValuePerBallot_ProposeMsgAndLeader(c, ds, ds', actor, recvIos, sendIos);
}


lemma AgreementChosenInv_LdrAction_OneValuePerBallot_ProposeMsgAndLeader(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires c.WF() && ds.WF(c)
    requires OneValuePerBallot(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires LeaderP1ImpliesAllProposeHasLtBal(c, ds)
    requires LdrBallotBelongsToItself(c, ds)
    requires ProposeMsgHasBalIdxAsSource(c, ds)
    requires c.ValidLdrId(actor)
    ensures OneValuePerBallot_ProposeMsgAndLeader(c, ds')
{
    forall l_idx, prop | 
        && c.ValidLdrIdx(l_idx)
        && LeaderInPhase2(c, ds', l_idx) 
        && isProposePkt(ds', prop)
        && prop.msg.bal == ds'.leaders[l_idx].ballot
    ensures prop.msg.val == ds'.leaders[l_idx].val
    {
        if l_idx == actor.idx {
            var l, l' := ds.leaders[l_idx], ds'.leaders[l_idx];
            match l.state {
                case P1a => 
                    lemma_LdrP1aGoToP1(c, ds, ds', actor, recvIos, sendIos);
                    assert false;
                case P1b => {
                    match recvIos[0].msg 
                        case Promise(bal, valbal) => 
                            if recvIos[0].msg .bal == l.ballot && !exists p :: p in l.promises && p.src == recvIos[0].src {
                                if |l.promises| == 2*l.consts.f {
                                    // This is where we need LeaderP1ImpliesAllProposeHasLtBal
                                    lemma_NewPacketsComeFromSendIos(c, ds, ds', actor, recvIos, sendIos);
                                    assert prop.src == Id(Ldr, prop.msg.bal.idx);
                                    assert false;
                                } else {
                                    assert l'.state == l.state;
                                    assert false;
                                }
                            } else {
                                assert l' == l;
                                assert false;
                            }
                        case Preempt(bal) => 
                            if BalLt(l.ballot, recvIos[0].msg.bal) {
                                assert l'.state == P1a;
                                assert false;
                            } else {
                                assert l' == l;
                                assert prop.msg.val == l'.val;
                            }
                        case _ => 
                            assert l' == l;
                            assert prop.msg.val == l'.val;
                }
                case P2a => 
                    if prop in ds.network.sentPackets {
                        assert prop.msg.val == l'.val;
                    } else {
                        lemma_NewPacketsComeFromSendIos(c, ds, ds', actor, recvIos, sendIos);
                        assert prop.msg.val == l'.val;
                    }
                case P2b => {
                    match recvIos[0].msg {
                        case Accept(bal, val) => 
                            if recvIos[0].msg.bal == l.ballot && recvIos[0].src !in l.accepts {
                                if |l.accepts| == 2*l.consts.f {
                                    assert l'.state == Decided;
                                    assert false;
                                } else {
                                    assert prop.msg.val == l'.val;
                                }
                            } else {
                                assert l' == l;
                                assert prop.msg.val == l'.val;
                            }
                        case Preempt(bal) => 
                            if BalLt(l.ballot, recvIos[0].msg.bal) {
                                assert l'.state == P1a;
                                assert !LeaderInPhase2(c, ds', l_idx);
                            } else {
                                assert l' == l;
                                assert prop.msg.val == l'.val;
                            }
                        case _ => 
                            assert l' == l;
                            assert prop.msg.val == l'.val;
                    }
                } 
                case Decided => 
                    assert !LeaderInPhase2(c, ds', l_idx);
                    assert false;
            }
        } else {
            assert ds'.leaders[l_idx].val == ds.leaders[l_idx].val;
            assert LeaderInPhase2(c, ds, l_idx);
            if prop in ds.network.sentPackets {
                    assert isProposePkt(ds, prop);
                    assert prop.msg.val == ds.leaders[l_idx].val;
                    assert prop.msg.val == ds'.leaders[l_idx].val;
            } else {
                assert prop.src == Id(Ldr, prop.msg.bal.idx);
                assert prop.src != actor;
                lemma_NewPacketsComeFromSendIos(c, ds, ds', actor, recvIos, sendIos);
                assert false;
            }
        }
    }
    assert OneValuePerBallot_ProposeMsgAndLeader(c, ds');
}


lemma AgreementChosenInv_AccAction_PromiseMsgBalLargerThanAcceptedItSees(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures PromiseMsgBalLargerThanAcceptedItSees(c, ds')
{
    var a, a' := ds.acceptors[actor.idx], ds'.acceptors[actor.idx];
    if recvIos[0].msg.Prepare? {
        lemma_NewPacketsComeFromSendIos(c, ds, ds', actor, recvIos, sendIos);
        if BalLt(a.promised, recvIos[0].msg.bal) {
            assert BalLtEq(a.accepted.b, a.promised);
            var newProm := sendIos[0];
            assert newProm.msg.bal == recvIos[0].msg.bal && newProm.msg.vb.b == a.accepted.b;
            lemma_BalLtTransitivity2(newProm.msg.vb.b, a.promised, newProm.msg.bal);
            lemma_SingleElemList1(sendIos, newProm);
        } 
    } else {
        lemma_NoPromiseSentInNonPromiseStep(c, ds, ds', actor, recvIos, sendIos);
    }
}


lemma AgreementChosenInv_AccAction_PromiseVBImpliesAcceptMsg(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures PromiseVBImpliesAcceptMsg(c, ds')
{
    var a, a' := ds.acceptors[actor.idx], ds'.acceptors[actor.idx];
    if recvIos[0].msg.Prepare? {
        if BalLt(a.promised, recvIos[0].msg.bal) {
            var outPkt := sendIos[0];
            if outPkt.msg.vb.b != Bottom {
                var p :|    && isAcceptPkt(ds, p)   // by AcceptedImpliesAcceptMsg
                            && p.src == actor
                            && p.msg == Accept(a.accepted.b, a.accepted.v);
                lemma_SingleElemList1(sendIos, outPkt);
            }
        }
    } else {
        lemma_NoPromiseSentInNonPromiseStep(c, ds, ds', actor, recvIos, sendIos);
    }
}


lemma AgreementChosenInv_AccAction_AcceptMsgImpliesAccepted(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures AcceptMsgImpliesAccepted(c, ds')
{
    lemma_NetworkMonotoneIncreasing(c, ds, ds');
    forall p:Packet | c.ValidAccIdx(p.src.idx) && isAcceptPkt(ds', p)
    ensures BalLtEq(p.msg.bal, ds'.acceptors[p.src.idx].accepted.b)
    {
        if p !in ds.network.sentPackets { 
            lemma_NewAcceptPktImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, p);
        }
    }
}


lemma AgreementChosenInv_AccAction_AcceptMsgImpliesProposeMsg(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures AcceptMsgImpliesProposeMsg(c, ds')
{
    lemma_NetworkMonotoneIncreasing(c, ds, ds');
    forall p:Packet | c.ValidAccIdx(p.src.idx) && isAcceptPkt(ds', p)
    ensures exists prop_p :: 
        && isProposePkt(ds, prop_p)
        && prop_p.src == p.dst
        && prop_p.dst == p.src
        && prop_p.msg == Propose(p.msg.bal, p.msg.val)
    {
        if p !in ds.network.sentPackets { 
            lemma_NewAcceptPktImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, p);
        }
    }
}

lemma AgreementChosenInv_AccAction_LeaderP2ImpliesQuorumOfPromise(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures LeaderP2ImpliesQuorumOfPromise(c, ds')
{
    lemma_NetworkMonotoneIncreasing(c, ds, ds');
    forall idx | c.ValidLdrIdx(idx) && LeaderInPhase2(c, ds', idx)
    ensures exists qrm  
        :: QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val)
    {
        assert ds'.leaders[idx] == ds.leaders[idx];
        var qrm :| QrmHighestBallotNilOrV(c, ds, qrm, ds.leaders[idx].ballot, ds.leaders[idx].val);
        assert QrmHighestBallotNilOrV(c, ds', qrm, ds'.leaders[idx].ballot, ds'.leaders[idx].val);
    }
}


/* If a promised packet promised b', with previously accepted (v, b), then 
*   - there can be no accept messages in network, from the same acceptor, 
*       with ballot x such that b < x < b' 
*   - the acceptor either has (v, b) accepted, or accepted some ballot >= b'
*/
lemma AgreementChosenInv_AccAction_PromisedImpliesNoMoreAccepts(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    ensures PromisedImpliesNoMoreAccepts(c, ds')
{
    forall prom_p | 
        && prom_p in ds'.network.sentPackets 
        && prom_p.msg.Promise?
    ensures && AcceptorConstraint(c, ds', prom_p.src, prom_p.msg.bal, prom_p.msg.vb.b)
            && AcceptMessageConstraint(c, ds', prom_p.src, prom_p.msg.bal, prom_p.msg.vb.b)
    {
        var prom_promised_bal, prom_accepted_bal := prom_p.msg.bal, prom_p.msg.vb.b;
        
        if prom_p in ds.network.sentPackets {
            assert AcceptorConstraint(c, ds', prom_p.src, prom_p.msg.bal, prom_p.msg.vb.b);
            forall acc_p | isAcceptPkt(ds', acc_p) && acc_p.src == prom_p.src
            ensures|| BalLtEq(acc_p.msg.bal, prom_accepted_bal)
                   || BalLtEq(prom_promised_bal, acc_p.msg.bal)
            {
                if acc_p !in ds.network.sentPackets {
                    /* This step is an accept step. So we have a.promised >= prom_promised_bal.
                    * acc_p has ballot a'.accepted.b == a'.promised. 
                    * And prom_promised_bal <= a.promised <= a'.promised;
                    */ 
                    lemma_NewAcceptPktImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, acc_p);
                    var a, a' := ds.acceptors[actor.idx], ds'.acceptors[actor.idx];
                    lemma_BalLtEqTransitivity(prom_promised_bal, a.promised, a'.promised);
                } 
            }       
        } else {
            lemma_NewAcceptPktImpliesPromiseStep(c, ds, ds', actor, recvIos, sendIos, prom_p);
        }
    }
}

           

lemma AgreementChosenInv_AccAction_OneValuePerBallot(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires c.WF() && ds.WF(c)
    requires OneValuePerBallot(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires LdrBallotBelongsToItself(c, ds')
    requires AcceptMsgImpliesProposeMsg(c, ds')
    requires PromiseVBImpliesAcceptMsg(c, ds')
    requires c.ValidAccId(actor)
    ensures OneValuePerBallot(c, ds')
{}

}