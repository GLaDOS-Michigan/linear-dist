# Readme

Monotonic version of Decentralized Paxos.

This is based on centralizedMonotonic Paxos.

Want to compare if inductive invariants from centralizedMonotonic Paxos carry over here.

## Notes 7 Sept 2023

In this version, each node maintains its own history.
I think this does not work. Rather, the entire set of hosts should maintain a history. Otherwise, different host histories progress at different rates, and it becomes impossible to talk about a “consistent cut” of two host histories. Indeed, I am having trouble formalizing `AcceptorValidPromisedAndAccepted` as it requires talking about consistent historical states across nodes.

Instead, if the whole hosts set maintains a history, then every property that is true in the non-monotonic version is true for every historical state in the monotonic version.
