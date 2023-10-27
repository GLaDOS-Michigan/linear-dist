include "UtilitiesLibrary.dfy"

module MonotonicityLibrary {
  import opened UtilitiesLibrary

  datatype MonotonicWriteOnceOption<T> = WOSome(value:T) | WONone
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicWriteOnceOption<T>) {
      past.WOSome? ==> past == this
    }
  }

  datatype MonotonicNatOption = MNSome(value: nat) | MNNone
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicNatOption) {
      past.MNSome? ==> (this.MNSome? && past.value <= this.value)
    }
  }

  datatype MonotonicSet<T> = MonotonicSet(s: set<T>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicSet<T>) {
      past.s <= this.s
    }
  }
}
