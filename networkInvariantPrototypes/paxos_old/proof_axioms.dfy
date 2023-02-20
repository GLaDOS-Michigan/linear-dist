include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_agreement_invariants.dfy"

module Proof_Axioms {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Agreement_Invs


lemma {:axiom} axiom_FiniteBallots(b1:Ballot, b2:Ballot) returns (s:seq<Ballot>)
    requires BalLtEq(b1, b2)
    ensures |s| > 0
    ensures b1 == s[0]
    ensures b2 == s[|s|-1]
    ensures TotalOrderBal(s)

predicate TotalOrderBal(s:seq<Ballot>) 
    requires |s| > 0
{
    && (forall i, j | 0 <= i < j < |s| :: BalLt(s[i], s[j]))
    && (forall b' | BalLtEq(s[0], b') && BalLtEq(b', s[|s|-1]) :: b' in s)
    && seqIsUnique(s)
}


lemma {:axiom} axiom_Set_Cover<T>(S1:set<T>, S2:set<T>, U:set<T>)
    requires S1 <= U 
    requires S2 <= U
    requires S1 * S2 == {}
    requires |S1| + |S2| >= |U|
    ensures S1 + S2 == U


lemma {:axiom} axiom_Set_DisjointSets<T>(S1:set<T>, S2:set<T>)
    requires forall e | e in S1 :: e !in S2
    ensures S1 * S2 == {}


lemma {:axiom} axiom_Set_Intersection(S1:set<Id>, S2:set<Id>, U:set<Id>) returns (e:Id)
    requires |S1| > |U|/2
    requires |S2| > |U|/2
    requires forall id | id in S1 :: id in U
    requires forall id | id in S2 :: id in U
    ensures e in U && e in S1 && e in S2

}