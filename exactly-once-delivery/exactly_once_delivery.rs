// rust_verify/tests/example.rs ignore
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::vec::*;
use pervasive::modes::*;
use pervasive::multiset::*;
use pervasive::map::*;
use pervasive::seq::*;
use pervasive::option::*;
use pervasive::atomic_ghost::*;

use state_machines_macros::tokenized_state_machine;
use option::Option::{Some, None};

tokenized_state_machine!{

ExactlyOnceDelivery<StoredType> {
    // StoredType may have some invariants independent of the application
    // - these are message invariants
 
    fields {
        // maps host src, dst pairs to a map from sequence
        // number to StoredType
        // in_network
        #[sharding(...)]
        pub storage: Map<(nat, nat), Map<nat, StoredType>>,
    }

    init!{
        initialize(init_value: StoredType) {
            init storage = map![];
        }
    }

    transition!{
        deposit_user_send(value: StoredType, src: HostId, dst: HostId) {
            deposit storage += todo!();
        }
    }

    transition!{
        withdraw_user_receive(dst: HostId) -> StoredType {
            withdraw storage -= todo!();
        }
    }
} //tokenized_state_machine
