# Readme

The Toy Leader Election Protocol, sourced from "Modularity for Decidability of
Deductive Verification with Applications to Distributed Systems" (PLDI'18)

There are two favors of this protocol.

## With Atomic Recv-And-Send Steps

1. Client broadcasts StartElection. This is modeled as StartElection message existing in the network at genesis.
2. A node receiving client request broadcasts Vote-Req, if it has not already voted
3. A node receiving Vote-Req broadcasts a Vote for the sender, if it has not already voted
4. A node receiving a quorum of Votes declares itself the leader, broadcasts Leader message

## Without Atomic Recv-And-Send Steps

1. Client broadcasts StartElection. This is modeled as StartElection message existing in the network at genesis.
2. A node receiving client request nominates itself as the candidate, if it does not already have a candidate.
3. A node with itself as the nominee broadcasts Vote-Req.
4. A node receiving Vote-Req nominates the sender.
5. A node with a nominee votes for the nominee.
6. A node receiving a quorum of Votes declares itself the leader, broadcasts Leader message
