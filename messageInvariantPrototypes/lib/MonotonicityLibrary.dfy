include "UtilitiesLibrary.dfy"

module MonotonicityLibrary {
  import opened UtilitiesLibrary

  datatype WriteOnceOption<T> = WOSome(value:T) | WONone
  {
    ghost predicate SatisfiesWriteOnce(past: WriteOnceOption<T>) {
      past.WOSome? ==> past == this
    }
  }

  datatype MonotonicSet<T> = MonotonicSet(s: set<T>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicSet<T>) {
      past.s <= this.s
    }
  }
}
