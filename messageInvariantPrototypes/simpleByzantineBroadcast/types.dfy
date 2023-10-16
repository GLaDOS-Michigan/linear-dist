include "../lib/UtilitiesLibrary.dfy"

module Types {
import opened UtilitiesLibrary

type HostId = nat
type Value(==,!new)

datatype Message = Vote(src: HostId)
                // | Promise(bal:LeaderId, acc:AcceptorId, vbOpt:Option<ValBal>)  //valbal is the value-ballot pair with which the value was accepted
                // | Propose(bal:LeaderId, val:Value)
                // | Accept(vb:ValBal, acc:AcceptorId)

datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

}