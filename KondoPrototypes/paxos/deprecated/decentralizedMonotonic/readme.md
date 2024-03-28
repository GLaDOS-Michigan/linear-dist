# Readme

Monotonic version of Decentralized Paxos with global history.

This is based on centralizedMonotonic Paxos with global history. To maintain comparability,
the correctness condition is about learner state, rather than Learn messages.

This version has custom message invariants written by Tony --- the formal message invariant template is not applied.

applicationProof.dfy is deprecated for containing illegal inductive proofs over history.
applicationProof_NoTruncate.dfy is the updated version with illegal lemmas removed.
