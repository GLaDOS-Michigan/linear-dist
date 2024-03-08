include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"

module Proof_Validity {
import opened Network
import opened Agents
import opened Types
import opened Synod


/*****************************************************************************************
*                                       Validity                                         *
*****************************************************************************************/

/* If all processes propose v, then every process that decides a value decides v */
ghost predicate Validity(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> AllDecidedProcessesDecidesV(c, ds, v)
}

ghost predicate AllProcessesInitV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: c.ldr_vals[i] == v
}

ghost predicate AllDecidedProcessesDecidesV(c:Constants, ds:DistrSys, v:Value)
    requires c.WF()
    requires ds.WF(c)
{
    forall l | l in ds.leaders && l.state == Decided :: l.val == v
}


/* Invariants for establishing Validity */
ghost predicate Validity_Inv(c:Constants, ds:DistrSys, v:Value) 
{
    && c.WF()
    && ds.WF(c)
    && Validity(c, ds, v)
    && Validity_Inv_AllLdrProposeV(c, ds, v)
    && Validity_Inv_AllAccAcceptsV(c, ds, v)
    && Validity_Inv_AllMessegesContainV(c, ds, v)
}

ghost predicate Validity_Inv_AllMessegesContainV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> forall pkt | pkt in ds.network.sentPackets :: MessageContainsV(pkt.msg, v)
}

ghost predicate MessageContainsV(m: Message, v:Value) {
    match m {
        case Prepare(bal) => true
        case Promise(bal, vb) => vb.v != v ==> vb.v == Nil
        case Propose(bal, val) => val == v
        case Accept(bal, val) =>  true
        case Preempt(bal) => true
    }
}

ghost predicate Validity_Inv_AllAccAcceptsV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> forall i | c.ValidAccIdx(i) :: ds.acceptors[i].accepted.v != v ==> ds.acceptors[i].accepted.v == Nil 
}

ghost predicate Validity_Inv_AllLdrProposeV(c:Constants, ds:DistrSys, v:Value)
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> 
    && (forall i | c.ValidLdrIdx(i) :: ds.leaders[i].val == v)
    && (forall i | c.ValidLdrIdx(i) :: 
            forall p | p in ds.leaders[i].promises  && p.msg.Promise?
            :: p.msg.vb.v != Nil ==> p.msg.vb.v == v)
}


/* Init ==> Validity_Inv */
lemma InitImpliesValidityInv(c:Constants, ds:DistrSys, v:Value) 
    requires Init(c, ds)
    ensures Validity_Inv(c, ds, v)
{}


/* Validity_Inv && Next ==> Validity_Inv' */
lemma NextPreservesVakidityInv(c:Constants, v:Value, ds:DistrSys, ds':DistrSys) 
    requires Validity_Inv(c, ds, v)
    requires Next(c, ds, ds')
    ensures Validity_Inv(c, ds', v)
{}

}