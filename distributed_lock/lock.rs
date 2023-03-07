mod pervasive;
use pervasive::prelude::*;

verus! {

// How would e.g. a dist file system that uses distributed locks
// rely on the property that there's a uniquely held lock resource?

struct LockTransfer {}
type Msg = LockTransfer;
type Resource = Tracked<...>;


// Maybe use tickets and stubs to prove a refinement?
// Travis: this may be too trivial for a lock
tokenized_state_machine! { Lock {
    // bunch'o'tickets and stubs
    acquire_request:
    acquire_response:

    acquire_request:
    acquire_response:
} }


struct NodeChannel {
    net: Tracked<Net::instance>,
    send: UserSender,
    recv: UserReceiver,
}

// not planning to run this
// establishes that there is only one resource
// parties, and their pair-wise channels
pub fn global_main(parties: usize) {
    // TRUSTED
    let resource = Resource::new(); // requires false?

    //
    let channels = // set up pair-wise channels
    spawn(move || {
        let node = DistributedLockNode {
            channels: ...,
            id: ghost(0),
        };
        node_main(node, Some(resource));
    });
    for i in 1..parties {
        spawn(|| {
            let node = DistributedLockNode {
                channels: ...,
                id: ghost(i),
            };
            node_main(node, None);
        });
    }
}

pub fn node_main(node: DistributedLockNode, resource: Option<Resource>) {
    let mut node = node;
    let mut resource = resource;
    loop {
        let l = if let Some(resource) = resource.take() {
            resource
        } else {
            node.acquire()
        };
        // exercise resource
        node.release(l);
    }
}

struct DistributedLockNode<LR> {
    channels: Vec<Option<NodeChannel>>, // channel j goes to node j, channel i is None
    i: usize,
}

impl DistributedLockNode<LR> {
    pub fn acquire(&mut self) -> (res: LR)
        requires self.i != 0
    {
        let (_msg, msg_ghost) = self.channels[(self.i - 1) % self.channels.len()].as_ref().unwrap().recv.do_recv();
        // _msg has to be LockTransfer
        msg_ghost
    }

    pub fn release(&mut self, res: LR)
    {
        self.channels[(self.i + 1) % self.channels.len()].as_ref().unwrap().send.do_send(LockTransfer {}, res);
    }

}


}
