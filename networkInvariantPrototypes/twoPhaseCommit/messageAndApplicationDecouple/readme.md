Two Phase Commit while organizing for Message and Application Invariants.

Observe that there is no need for Monotonic Transformation here. This is because the 
coordinator only sends a single message -- the decision message -- and that is already 
monotonic with respect to its local decision.