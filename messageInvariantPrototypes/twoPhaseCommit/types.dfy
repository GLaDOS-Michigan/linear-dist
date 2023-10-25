include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Vote = Yes | No

  datatype Decision = Commit | Abort

  datatype Message =
    VoteReqMsg | VoteMsg(v: Vote, src: HostId) | DecideMsg(decision: Decision)
  {
    ghost function Src() : nat {
      if this.VoteMsg? then src else 0
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}
