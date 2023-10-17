include "../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type Key = int
  datatype Entry = Entry(key: Key, version: nat)

  datatype Message = Reconf(src: nat, dst: nat, key: Entry) 

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types