

// ================================================================

Sharded key-value store

struct HasKeyValue { key: Key, value: Value }

KeyValueStore {
    fields {
        #[sharding(map)]
        pub key_values: Map<Key, HasKeyValue>,
        // one shard: subset of key_values at a host
    }
}

init!{
    initialize() {
        // get all the keys
        init key_values = 0..MAX_KEY.map(|k| HasKeyValue { key, value: key })
    }
}

transition!{
    serve_get(...) {
        // must have the key
    }
}

// these transitions never need to talk about sending/receiving shards
// in fact, they cannot

// combines with, in the implementation

ExactlyOnceDelivery<StoredType = HasKeyValue>

// the StoredType(?) can be a refinement type which is a message invariant

// ================================================================

// in the implementation,
// - sending a message deposits a HasKeyValue
//   <- ghost state, physical state connected by a predicate that couples them
//      this coupling predicate must have a global meaning
//

// ================================================================

// to have an exclusive resource we can use a contradiction lemma:
    proof fn only_one(a: tracked LockHeld, b: tracked LockHeld)
        ensures false
