include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  // How a particular participant feels.
  datatype Vote = Yes | No
  // What decision has been reached by the protocol.
  datatype Decision = Commit | Abort

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
    VoteReqMsg | VoteMsg(v: Vote, src: HostId) | DecideMsg(d: Decision)

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}
