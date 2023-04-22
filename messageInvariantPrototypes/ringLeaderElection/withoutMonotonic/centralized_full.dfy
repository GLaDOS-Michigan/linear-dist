datatype Constants = Constants(ids: seq<nat>) {
    predicate ValidIdx(i: nat) {
        0 <= i < |ids|
    }

    predicate UniqueIds() {
        forall i:nat, j:nat | ValidIdx(i) && ValidIdx(j) && ids[i] == ids[j] :: i == j
    }

    predicate WellFormed() {
        && 0 < |ids|
        && UniqueIds()
    }

}

datatype Variables = Variables(highest_heard: seq<int>) {
    predicate WellFormed(c: Constants) {
        && c.WellFormed()
        && |highest_heard| == |c.ids|
    }
}

predicate Init(c: Constants, v: Variables) {
    && v.WellFormed(c)
    && forall idx:nat | c.ValidIdx(idx) :: v.highest_heard[idx] == -1
}

function max(a: int, b:int) : (ret:int) 
    ensures ret >= a && ret >= b
{
    if a >= b then a else b
}

function Successor(c:Constants, idx: nat) : (ret:nat)
    requires c.ValidIdx(idx)
{
    if idx == |c.ids|-1 then 0 else idx+1
}

predicate Transmission(c: Constants, v: Variables, v':Variables, actor: nat) {
    && v.WellFormed(c)
    && v'.WellFormed(c)
    && c.ValidIdx(actor)
    && (var msg := max(v.highest_heard[actor], c.ids[actor]);
       var new_highest_heard := max(msg, v.highest_heard[Successor(c, actor)]);
       v' == v.(highest_heard := v.highest_heard[Successor(c, actor) := new_highest_heard]))
}

datatype Step = TransmissionStep(actor: nat)

predicate NextStep(c:Constants, v: Variables, v': Variables, step: Step) {
    match step {
        case TransmissionStep(actor) => Transmission(c, v, v', actor)
    }
}

predicate Next(c: Constants, v: Variables, v': Variables) {
    exists step :: NextStep(c, v, v', step)
}

// Model ends here. Below is the definition of safety
predicate IsLeader(c: Constants, v: Variables, idx: nat) 
    requires v.WellFormed(c)
    requires c.ValidIdx(idx)
{
    v.highest_heard[idx] == c.ids[idx]
}

predicate Safety(c: Constants, v: Variables) 
    requires v.WellFormed(c)
{
    forall idx1, idx2 | 
        && c.ValidIdx(idx1) 
        && c.ValidIdx(idx2) 
        && IsLeader(c, v, idx1)
        && IsLeader(c, v, idx2)
        :: idx1 == idx2
}

// Safety definition ends here. Below comes the proof of safety

predicate Between(start: nat, node: nat, end: nat) 
{
    if start < end then
        start < node < end else
        node < end || start < node
}

predicate ChordDominates(c: Constants, v: Variables) 
    requires v.WellFormed(c)
{
    forall src:nat, dst:nat, mid:nat | 
        && c.ValidIdx(src)
        && c.ValidIdx(dst)
        && c.ValidIdx(mid)
        && v.highest_heard[dst] == c.ids[src]
        && Between(src, mid, dst)
            :: c.ids[mid] < c.ids[src]
}

predicate Inv(c: Constants, v: Variables) {
    && v.WellFormed(c)
    && ChordDominates(c, v)
    && Safety(c, v)
}

lemma InvImpliesSafety(c: Constants, v: Variables) 
    requires Init(c, v)
    ensures Safety(c, v)
{
}

lemma InitImpliesInv(c: Constants, v: Variables) 
    requires Init(c, v)
    ensures Inv(c, v)
{
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{
}

