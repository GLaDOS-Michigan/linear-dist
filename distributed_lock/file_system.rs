


verus! {


pub closed spec fn get_fresh_nat(reqs: Set<ReqId>) -> nat
    recommends reqs.finite()
{
    choose |n| !reqs.contains(n)
}

// What you'd want to do in a distributed file system with file servers
// is to stick into the Lock resource the token representing the shard 
// of the system state associated with the data on some file-server
//
// then prove refinement of a distributed FileSystem to a Map

tokenized_state_machine! { FileSystem {
    #[sharding(variable)]
    data: i64,

    // bunch'o'tickets and stubs
    #[sharding(map)] // a read_request is (nat, ())
    read_request: Map<nat, ()>,
    #[sharding(map)]
    read_response: Map<nat, (i64,)>,

    write_request:
    write_response:
}

transition! {
    client_read_start() {
        birds_eye let rid = get_fresh_nat(pre.read_request.dom());
        add read_request += [ rid => () ] by { ... }
    }
}

transition! {
    read_do() {
        remove read_request -= [ rid => let () ] by { ... }
        add read_response += [ rid => (pre.data) ] by { ... }
    }
}

transition! {
    client_read_finish(rid: nat) {
        remove read_request -= [ rid => let () ] by { ... }
    }
}

transition! {
    client_write_start() {
        birds_eye let rid = get_fresh_nat(pre.write_request.dom());
        add write_request += [ rid => () ] by { ... }
    }
}

transition! {
    write_do() {
        remove write_request -= [ rid => let () ] by { ... }
        add write_response += [ rid => (pre.data) ] by { ... }
    }
}

transition! {
    client_write_finish(rid: nat) {
        remove write_request -= [ rid => let () ] by { ... }
    }
}

}
}

pub fn global_main(parties: usize) {
    let resource = FileSystem::data;
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

}

struct FileSystemClient {
    lock: DistributedLockNode<FileSystem::data>,
    instance: FileSystem::instance,
}

impl FileSystemClient {
    // as if client called let ticket = self.instance.read_start();
    pub fn read(&mut self, ticket: FileSystem::read_request) -> (i64, Tracked<ReadResponse>)
    {
        let data_token = self.lock.acquire();
        // we aren't actually exchanging the data; that seems important
        let stub = self.instance.read_do(data_token, ticket);
        stub
    }

    pub fn write(&mut self, new_v: i64, ticket: Tracked<WriteRequest>) -> Tracked<WriteResponse> {
        let data_token = self.lock.acquire();
        // we aren't actually exchanging the data; that seems important
        let stub = self.instance.write_do(data_token, ticket);
        stub
    }
}

}

