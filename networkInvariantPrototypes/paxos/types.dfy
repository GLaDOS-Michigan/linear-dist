include "../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type LeaderId = nat
  type AcceptorId = nat
  type Value
  datatype ValBal = VB(v:Value, b:LeaderId)

  datatype Message = Prepare(bal:LeaderId)
                  | Promise(bal:LeaderId, acc:AcceptorId, vbOpt:Option<ValBal>)  //valbal is the value-ballot pair with which the value was accepted
                  | Propose(bal:LeaderId, val:Value)
                  | Accept(bal:LeaderId, val:Value)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}