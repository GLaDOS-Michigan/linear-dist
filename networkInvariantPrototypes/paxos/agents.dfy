include "types.dfy"

module Agents {
import opened Types


/*****************************************************************************************
*                                Acceptor State Machine                                  *
*****************************************************************************************/

datatype AcceptorConstants = AConsts(id:Id)

datatype Acceptor = Acceptor(
    consts:AcceptorConstants, 
    promised:Ballot, 
    accepted:ValBal)

/* Acceptor initial state */
predicate AcceptorInit(a:Acceptor, id:Id) {
    && a.consts == AConsts(id)
    && a.promised == Bottom
    && a.accepted == VB(Nil, Bottom)
}

/* Acceptor next state */
predicate AcceptorNext(a:Acceptor, a':Acceptor, recvIos:seq<Packet>, sendIos:seq<Packet>) {
    && a'.consts == a.consts
    && |recvIos| == 1
    && match recvIos[0].msg {
        case Prepare(bal) => AcceptorNext_RcvPrepare(a, a', recvIos[0], sendIos)
        case Propose(bal, val) => AcceptorNext_RcvPropose(a, a', recvIos[0], sendIos)
        case _ => a == a' && sendIos == []
    }
}

/* Acceptor next state, process Prepare message */
predicate AcceptorNext_RcvPrepare(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Prepare?
{   
    if BalLt(a.promised, recvIo.msg.bal) then
        AcceptorPromise(a, a', recvIo, sendIos)
    else 
        AcceptorPreempt(a, a', recvIo, sendIos)
}

/* Acceptor next state, process Accept message */
predicate AcceptorNext_RcvPropose(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Propose?
{
    if BalLtEq(a.promised, recvIo.msg.bal)  then
        AcceptorAccept(a, a', recvIo, sendIos)
    else 
        AcceptorPreempt(a, a', recvIo, sendIos)
}

/* Acceptor send Promise */
predicate AcceptorPromise(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Prepare?
{
    && a'.promised == recvIo.msg.bal
    && a'.accepted == a.accepted
    && |sendIos| == 1
    && sendIos[0].src == a.consts.id
    && sendIos[0].dst == recvIo.src
    && sendIos[0].msg == Promise(recvIo.msg.bal, a.accepted)
}

/* Acceptor send Accept */
predicate AcceptorAccept(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Propose?
{
    && a'.promised == recvIo.msg.bal 
    && a'.accepted == VB(recvIo.msg.val, recvIo.msg.bal)
    && |sendIos| == 1
    && sendIos[0].src == a.consts.id
    && sendIos[0].dst == recvIo.src
    && sendIos[0].msg == Accept(recvIo.msg.bal, recvIo.msg.val)
}

/* Acceptor send Preempt */
predicate AcceptorPreempt(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Prepare? || recvIo.msg.Propose?
{
    && |sendIos| == 1
    && sendIos[0].src == a.consts.id
    && sendIos[0].dst == recvIo.src
    && sendIos[0].msg == Preempt(a.promised)
    && a'.promised == a.promised
    && a'.accepted == a.accepted
    // Bug 1: a'.promised and a'.accepted unspecified
}


/*****************************************************************************************
*                                 Leader State Machine                                   *
*****************************************************************************************/

datatype LeaderState = P1a | P1b | P2a | P2b | Decided
datatype LeaderConstants = LConsts(id:Id, accConf:seq<Id>, f:nat, initval:Value)

datatype Leader = Leader(
    consts:LeaderConstants,    
    state:LeaderState,
    ballot:Ballot,
    val:Value,
    promises:set<Packet>,
    accepts:set<Id>
)

/* Leader initial state */
predicate LeaderInit(l:Leader, id:Id, accConf:seq<Id>, f:nat, initval:Value) {
    && l.consts == LConsts(id, accConf, f, initval)
    && l.state == P1a
    && l.ballot == Ballot(0, id.idx)
    && l.val == initval
    && l.promises == {}     // Bug 8: This line was omitted
    && l.accepts == {}      // Bug 12: This line was omitted
}

/* Leader next state */
predicate LeaderNext(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) {
    && l'.consts == l.consts
    && match l.state {
        case P1a => LeaderNext_P1a(l, l', recvIos, sendIos)
        case P1b => LeaderNext_P1b(l, l', recvIos, sendIos)
        case P2a => LeaderNext_P2a(l, l', recvIos, sendIos)
        case P2b => LeaderNext_P2b(l, l', recvIos, sendIos)
        case Decided => LeaderStutter(l, l', sendIos)
    }
}


/* Leader next state, broadcast Prepare messages */
predicate LeaderNext_P1a(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P1a
{
    && l'.state == P1b
    && l'.ballot == l.ballot
    && l'.val == l.val
    && l'.promises == l.promises
    && l'.accepts == l.accepts
    && recvIos == []
    && LeaderSendPrepare(l, sendIos)
}

predicate LeaderSendPrepare(l:Leader, sendIos:seq<Packet>) {
    && |sendIos| == |l.consts.accConf|
    && forall i | 0 <= i < |sendIos| 
        :: sendIos[i] == Packet(l.consts.id, l.consts.accConf[i], Prepare(l.ballot))
}


/* Leader next state, wait for quorum of Promise messages */
predicate LeaderNext_P1b(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P1b
{
    && |recvIos| == 1 
    && match recvIos[0].msg {
        case Prepare(bal) => LeaderStutter(l, l', sendIos)
        case Promise(bal, valbal) => LeaderProcessPromise(l, l', recvIos[0], sendIos)
        case Propose(bal, val) => LeaderStutter(l, l', sendIos)
        case Accept(bal, val) =>  LeaderStutter(l, l', sendIos)
        case Preempt(bal) => LeaderProcessPreempt(l, l', recvIos[0].msg, sendIos)
    }
}

predicate LeaderStutter(l:Leader, l':Leader, sendIos:seq<Packet>) {
    l' == l && sendIos == []
}

predicate LeaderProcessPromise(l:Leader, l':Leader, pkt:Packet, sendIos:seq<Packet>) 
    requires pkt.msg.Promise?
    requires l.state == P1b
{
    var src, msg := pkt.src, pkt.msg;
    if msg.bal == l.ballot && !exists p :: p in l.promises && p.src == src then
        LeaderProcessValidPromise(l, l', pkt, sendIos)
    else 
        // This is a stale promise
        LeaderStutter(l, l', sendIos)
}

predicate LeaderProcessValidPromise(l:Leader, l':Leader, pkt:Packet, sendIos:seq<Packet>) 
    requires pkt.msg.Promise?
    requires l.state == P1b
    requires pkt.msg.bal == l.ballot
    requires !exists p :: p in l.promises && p.src == pkt.src
{
    // Bug 6: The leader is supposed to propose the value accepted with the highest prior 
    // ballot from its quorum of Promise messages. However, in this case, I just pick the 
    // value of the last Promise I receive. This violates correctness the same way as Sam 
    // Sillydoodle in Problem Set 2. 

    && sendIos == []    // Bug 2: left out this line, so sendIos was unspecified
    && if |l.promises| == 2*l.consts.f then 
        // Go to phase 2a
        var promises := l.promises + {pkt};
        && l'.state == P2a
        && l'.ballot == l.ballot
        // && l'.val == (if msg.val == Nil then l.val else msg.val)  // Bug 6
        && l'.val == (if PromisePktWithHighestBallot(promises).msg.vb.v == Nil 
                    then l.val 
                    else PromisePktWithHighestBallot(promises).msg.vb.v)
        && l'.promises == {}
        && l'.accepts == {}
    else 
        && l'.state == l.state
        && l'.ballot == l.ballot
        && l'.val == l.val
        && l'.promises == l.promises + {pkt}
        && l'.accepts == l.accepts
}

predicate LeaderProcessPreempt(l:Leader, l':Leader, msg:Message, sendIos:seq<Packet>) 
    requires msg.Preempt?
{
    && sendIos == []    // Bug 2: left out this line, so sendIos was unspecified
    && if BalLt(l.ballot, msg.bal) then 
        // I am preempted
        && l'.state == P1a
        && l'.ballot == NextBallot(msg.bal, l.consts.id.idx)
        && l'.promises == {}
        && l'.accepts == {}
        && l'.val == l.val
    else 
        // False alarm, msg is stale
        LeaderStutter(l, l', sendIos)
}


/* Leader next state, broadcast Propose messages */
predicate LeaderNext_P2a(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P2a
{
    && l'.state == P2b
    && l'.ballot == l.ballot
    && l'.val == l.val
    && l'.promises == l.promises
    && l'.accepts == l.accepts
    && recvIos == []
    && LeaderSendPropose(l, sendIos)
}

predicate LeaderSendPropose(l:Leader, sendIos:seq<Packet>) 
    requires l.state == P2a
{
    && |sendIos| == |l.consts.accConf|
    && forall i | 0 <= i < |sendIos| 
        :: sendIos[i] == Packet(l.consts.id, l.consts.accConf[i], Propose(l.ballot, l.val))
}


/* Leader next state, wait for quorum of Accept messages */
predicate LeaderNext_P2b(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P2b
{
    && |recvIos| == 1 
    && match recvIos[0].msg {
        case Prepare(bal) => LeaderStutter(l, l', sendIos)
        case Promise(bal, valbal) => LeaderStutter(l, l', sendIos)
        case Propose(bal, val) => LeaderStutter(l, l', sendIos)
        case Accept(bal, val) =>  LeaderProcessAccept(l, l', recvIos[0], sendIos)
        case Preempt(bal) => LeaderProcessPreempt(l, l', recvIos[0].msg, sendIos)
    }
}

predicate LeaderProcessAccept(l:Leader, l':Leader, pkt:Packet, sendIos:seq<Packet>) 
    requires pkt.msg.Accept?
    requires l.state == P2b
{
    var src, msg := pkt.src, pkt.msg;
    if msg.bal == l.ballot && src !in l.accepts then
        LeaderProcessValidAccept(l, l', src, msg, sendIos)
    else 
        // This is a stale Accept
        LeaderStutter(l, l', sendIos)
}

predicate LeaderProcessValidAccept(l:Leader, l':Leader, src:Id, msg:Message, sendIos:seq<Packet>) 
    requires msg.Accept?
    requires l.state == P2b
{
    && sendIos == []    // Bug 3: left out this line, so sendIos was unspecified
    && if |l.accepts| == 2*l.consts.f then 
        // Go to Decided state
        && l'.state == Decided
        && l'.ballot == l.ballot
        && l'.val == l.val
        && l'.promises == l.promises
        && l'.accepts == l.accepts
    else 
        && l'.state == l.state
        && l'.ballot == l.ballot
        && l'.val == l.val
        && l'.promises == l.promises
        && l'.accepts == l.accepts + {src}
}


/*****************************************************************************************
*                                        Utils                                           *
*****************************************************************************************/


// function {:opaque} PromFromPromiseMessage(src:Id, msg:Message) : (p:Promise)
//     requires msg.Promise?
//     ensures p.src == src
//     ensures p.vb == msg.vb
// {
//     Pro(src, msg.vb)
// }


function PromisePktWithHighestBallot(pset:set<Packet>) : (p:Packet)
    requires |pset| > 0
    // requires forall p | p in pset :: p.msg.Promise?
    ensures p.msg.Promise? && p in pset
    ensures forall p' | p' in pset && p'.msg.Promise? :: BalLtEq(p'.msg.vb.b, p.msg.vb.b)
}