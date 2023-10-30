include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type OwnedKey = int
  datatype Entry = Entry(live: bool, version: nat)

  datatype Message = Reconf(src: nat, dst: nat, key: OwnedKey, version: nat) {
    function Src() : nat {
      src
    }

    function Dst() : nat {
      dst
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types