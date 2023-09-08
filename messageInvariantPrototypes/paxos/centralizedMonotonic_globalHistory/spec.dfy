include "system.dfy"

module Obligations {
  import opened System

  // All learners must learn the same value
  ghost predicate Agreement(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2 |
      && c.ValidLearnerIdx(l1)
      && c.ValidLearnerIdx(l2)
      && v.learners[l1].HasLearnedSome()
      && v.learners[l2].HasLearnedSome()
    ::
      v.learners[l1].GetLearnedValue() == v.learners[l2].GetLearnedValue()
  }
}