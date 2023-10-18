include "../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type Key = int
  datatype Entry = Entry(live: bool, version: nat)
  type VersionedKeys = map<Key, nat>

  datatype Message = Reconf(src: nat, dst: nat, vks: VersionedKeys) 

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types