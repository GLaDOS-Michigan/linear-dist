include "../lib/UtilitiesLibrary.dfy"

module Types {
import opened UtilitiesLibrary

type LeaderId = nat
type AcceptorId = nat
type LearnerId = nat
type Value(!new)
datatype ValBal = VB(v:Value, b:LeaderId)

datatype Message = Prepare(bal:LeaderId)
                | Promise(bal:LeaderId, acc:AcceptorId, vbOpt:Option<ValBal>)  //valbal is the value-ballot pair with which the value was accepted
                | Propose(bal:LeaderId, val:Value)
                | Accept(vb:ValBal, acc:AcceptorId)                 
{
  ghost function Src() : nat {
    if this.Prepare? then bal
    else if this.Promise? then acc
    else if this.Propose? then bal
    else acc
  }
}

datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

// Lemma: Given b1 < b2, there is a finite, strictly ordered sequence 
// [b1, b_a, b_b, ... , b_2] such that for all ballots b where b1 < b < b2, b in seq
lemma FiniteBallots(b1: LeaderId, b2: LeaderId) returns (res: seq<LeaderId>)
  requires b1 < b2
  ensures SeqIsComplete(res, b1, b2)
{
  if b1 == b2 - 1 {
    return [b1, b2];
  } else {
    var sub := FiniteBallots(b1, b2-1);
    return sub + [b2];
  }
}
}