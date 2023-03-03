#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::option::*;
use pervasive::modes::*;
use pervasive::map::*;
use pervasive::seq::*;
use pervasive::prelude::*;

verus!{

// Network that might duplicate

// TODO how do we implement & verify this spec in terms of an actual network model?

trait IsMessage {
    pub spec fn is_valid(&self) -> bool;
}

#[verifier(external_body)]
struct Network<T> { t: PhantomData<T> }

impl<T: Copy + IsMessage> Network<T> {
    #[verifier(external_body)]
    fn send(&self, t: T)
        requires t.is_valid(),
    { }

    #[verifier(external_body)]
    fn recv(&self) -> (t: T)
        ensures t.is_valid(),
    { }
}


// Network that can't duplicate

// TODO should parameterize over these with generics / traits

type Msg = u64;                 // physical message the user sends
struct MsgGhost { val: u64 }    // (non-duplicable) ghost object they send with the message

spec fn msg_inv(m: Msg, mg: MsgGhost) -> bool { mg.val == m }

tokenized_state_machine!{ Net
    fields {
        #[sharding(variable)]
        seq_src: nat,

        #[sharding(variable)]
        seq_dst: nat,

        #[sharding(persistent_map)]
        valid_msg: Map<nat, Msg>,

        #[sharding(storage_map)]
        user_ghosts: Map<nat, MsgGhost>,
    }

    init!{
        initialize() {
            init seq_src = 0;
            init seq_dst = 0;
            init msgs = Map::empty();
            init user_ghosts = Map::empty();
        }
    }

    transition!{
        send(msg: Msg, msg_ghost: MsgGhost) {
            require(msg_inv(msg, msg_ghost));

            update seq_src = pre.seq_src + 1;
            add valid_msg (union)= [ pre.seq_src => msg ];
            deposit user_ghosts += [ pre.seq_src => msg_ghost ];
        }
    }

    transition!{
        recv() {
            let seq_num = pre.seq_dst;
            have msgs >= [ seq_num => let msg ];

            update seq_dst = pre.seq_dst + 1;

            withdraw user_msgs -= [ seq_num => let msg_ghost ];

            assert(msg_inv(msg, msg_ghost));
        }
    }


    //      0     1     2     3     4
    //      m0    m1    m2    m3    m4        valid_msg
    //                  g2    g3    g4        user_ghosts
    //
    //                  ^               ^
    //                  |               |
    //                seq_dst         seq_src

    #[invariant]
    fn the_inv(&self) {
        self.seq_dst <= self.seq_src
        && (forall |i| self.seq_dst <= i < self.seq_src
            ==>
            && self.valid_msg.dom().contains(i)
                self.user_ghosts.dom().contains(i) && 
                msg_inv(self.valid_msg.index(i), self.user_ghosts.index(i))
        )
    }
}

// Message type that the wrapper library uses
//
// Note that this needs to be Copy so that it can be sent through the
// more primitive Network library.

struct WrapperMsg {
    msg: Msg,
    seq: usize,
    #[proof] token: Net::valid_msg,
}

impl IsMessage for WrapperMessage {
    pub spec fn is_valid(&self) -> bool {
        self.token@.key == self.seq as int
        && self.token@.value == self.msg
    }
}

struct UserSender {
    seq: usize,

    #[proof] token: Net::seq_src,
    #[proof] instance: Net::Instance,

    network: Network<WrapperMsg>,
}

struct UserReceiver {
    seq: usize,

    #[proof] token: Net::seq_dst,
    #[proof] instance: Net::Instance,

    network: Network<WrapperMsg>,
}

// TODO how do two nodes initialize?

impl UserSender {
    fn wf(&self) -> bool {
        &&& self.token@.value == seq as int
        &&& self.token@.instance == instance
    }

    fn do_send(&mut self, m: Msg, #[proof] mg: MsgGhost)
        requires self.seq < 1000000,
            old(self).wf(),
            msg_inv(m, mg),
        ensures
            self.wf(),
    {
        proof {
            // Obtain a valid_msg_token
            #[proof] let Trk(valid_msg_token) = self.instance.send(m, mg,
                // Update the token (increment it by 1)
                &mut self.token,
                // deposit the ghost state
                mg);
        }

        self.seq += 1;

        self.network.send(WrapperMsg { msg: m, token: valid_msg_token });
    }
}

impl UserReceiver {
    fn wf(&self) -> bool {
        &&& self.token@.value == seq as int
        &&& self.token@.instance == instance
    }

    fn do_recv(&mut self) -> (pair: (Msg, Tracked<MsgGhost>))
        requires self.seq < 1000000,
            old(self).wf(),
        ensures
          self.wf(),
          ({
            let (m, mg) = pair;
              msg_inv(m, mg@)
          }),
    {
        loop {
            let msg = self.network.recv();
          
            if msg.seq == self.seq + 1 {
                let m = msg.msg;

                #[proof] let mg;
                proof {
                    // Withdraw the ghost state
                    let Trk(mg0) = self.instance.recv( // proof failure TODO
                        // Update the Receiver token (increment it by 1)
                        &mut self.token,
                        // Provide the token from the message as evidence
                        &msg.token);
                    mg = mg0;
                }

                return (m, tracked(mg));
            } else if msg.seq <= self.seq {
                // do nothing - this is an old message
            } else {
                // This message is newer than the next one we're expecting
                // TODO a realistic example would put this message in a buffer
                // or something to deliver it to the user later
            }
        }
    }
}



fn main() { }

}
