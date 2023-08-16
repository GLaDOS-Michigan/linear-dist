# Readme

The Toy Leader Election Protocol, sourced from "Modularity for Decidability of
Deductive Verification with Applications to Distributed Systems" (PLDI'18)

1. Client broadcasts StartElection. This is modeled as StartElection message existing in the network at genesis.
2. A node receiving client request broadcasts Vote-Req, if it has not already voted
3. A node receiving Vote-Req broadcasts a Vote for the sender, if it has not already voted
4. A node receiving a quorum of Votes declares itself the leader, broadcasts Leader message

Note that without Monotonic Transformation, the Application Invariant relies on network state.
