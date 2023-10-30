include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type UniqueKey = int

  datatype Message = Grant(src: nat, dst: HostId, epoch: nat) {
    ghost function Src() : nat {
      src
    }

    ghost function Dst() : nat {
      dst
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types