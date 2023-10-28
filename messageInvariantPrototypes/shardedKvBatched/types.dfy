include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type UniqueKey = int
  datatype Entry = Entry(live: bool, version: nat)
  type VersionedKeys = map<UniqueKey, nat>

  datatype Message = Reconf(src: nat, dst: nat, vks: VersionedKeys) {
    ghost function Src() : nat {
      src
    }

    ghost function Dst() : nat {
      dst
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types