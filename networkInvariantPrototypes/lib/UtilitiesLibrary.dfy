module UtilitiesLibrary {
  datatype Option<T> = Some(value:T) | None

  function max(x: int, y: int) : (res: int) 
    ensures res == x || res == y
    ensures res >= x && res >= y
  {
    if x > y then x else y
  }

  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  function Successor(mod: nat, idx: nat) : (ret:nat)
    requires 0 < mod
    requires idx < mod
  {
    if idx == mod-1 then 0 else idx+1
  }

  function Predecessor(mod: nat, idx: nat) : (ret:nat)
    requires 0 < mod
    requires idx < mod
  {
    if idx == 0 then mod-1 else idx-1
  }

  predicate StrictOrdering(s: seq<nat>) {
    forall i , j | 
      && 0 <= i < |s| 
      && 0 <= j < |s| 
      && i < j
    :: s[i] < s[j]
  }

  predicate SeqIsComplete(s: seq<nat>, x: nat, y: nat) {
    && 2 <= |s|
    && s[0] == x
    && s[|s|-1] == y
    && (forall n | x <= n <= y :: n in s)
  }
  
  lemma SetComprehensionSize(n: nat) 
    ensures |(set x | 0 <= x < n)| == n
    decreases n
  {
    var s := (set x | 0 <= x < n);
    if n == 0 {
      assert |s| == 0;
    } else {
      SetComprehensionSize(n-1);
      assert s == (set x | 0 <= x < n-1) + {n-1};  // trigger
    }
  }

  lemma UnionIncreasesCardinality<T>(s1: set<T>, s2: set<T>) 
    ensures |s1 + s2| >= |s1|
    ensures |s1 + s2| >= |s2|
  {
    assume false;  // TODO
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {
    if |theSets| == 0 then {} else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  // As you can see, Dafny's recursion heuristics easily complete the recursion
  // induction proofs, so these two statements could easily be ensures of
  // UnionSeqOfSets. However, the quantifiers combine with native map axioms
  // to be a bit trigger-happy, so we've pulled them into independent lemmas
  // you can invoke only when needed.
  // Suggestion: hide calls to this lemma in a an
  //   assert P by { SetsAreSubsetsOfUnion(...) }
  // construct so you can get your conclusion without "polluting" the rest of the
  // lemma proof context with this enthusiastic forall.
  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
  }

  // Convenience function for learning a particular index (invoking Hilbert's
  // Choose on the exists in EachUnionMemberBelongsToASet).
  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {
    EachUnionMemberBelongsToASet(theSets);
    var chosenIdx :| 0<=chosenIdx<|theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }

  predicate SetIsQuorum<T>(clusterSize: nat, S: set<T>) {
    |S| > clusterSize / 2
  }

  lemma QuorumIntersection<T>(cluster: set<T>, S1: set<T>, S2: set<T>) returns (e: T) 
    requires SetIsQuorum(|cluster|, S1)
    requires SetIsQuorum(|cluster|, S2)
    requires S1 <= cluster
    requires S2 <= cluster
    ensures e in S1 && e in S2
  {
    assume false;  // TODO
    e :| e in S1 && e in S2;
  }

  function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    assert m'.Keys == m.Keys - {key};
    m'
  }

  function StutterSeq<T>(s: seq<T>) : (s': seq<T>)
    requires 0 < |s|
    ensures |s'| == |s|+1
  {
    s + [Last(s)]
  }
}
