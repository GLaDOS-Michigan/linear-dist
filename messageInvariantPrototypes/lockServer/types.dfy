include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type UniqueKey = int

  datatype Message = 
    | Grant(src: nat, dst: nat, epoch: nat) 
    | Release(src: nat, epoch: nat)
  {
    function Src() : nat {
      src
    }

    function Dst() : nat {
      if this.Grant? then dst else 0
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
} // end module Types