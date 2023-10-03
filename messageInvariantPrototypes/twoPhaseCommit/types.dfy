include "../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Vote = Yes | No

  datatype Decision = Commit | Abort

  datatype Message =
    VoteReqMsg | VoteMsg(v: Vote, src: HostId) | DecideMsg(d: Decision)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}
