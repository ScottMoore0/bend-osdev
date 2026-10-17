# bend-osdev-algo, binary search: the lower bound of a key in a sorted
# sequence of U32 (the index of the first element not below the key, or the
# length if every element is below it), and an index holding the key.
#
# Two implementations, as CONVENTIONS asks where speed matters:
#
#   bsearch.lower_bound, bsearch.find              the reference, on a List:
#                                                  a scan, proved correct
#   bsearch.array_lower_bound, bsearch.array_find  the fast one, on an
#                                                  Array<U32>: a binary
#                                                  search, O(log n) reads
#
# The two agree on the vectors in LAWS.bend and on the differential test in
# ref/; a proof that they agree for every input needs lemmas about
# Array.get that Base does not have yet (see the README).
import Base

# Sorted: each element is at most the next
def bsearch.sorted.pair(xs: List<&2, U32>, x: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.and(U32.is_le(x, y), bsearch.sorted.pair(t, y))

def bsearch.sorted(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      bsearch.sorted.pair(t, x)

# The reference

def bsearch.below.step(c: Bool, k: Nat) -> Nat:
  match c:
    case True{}:
      1n+k
    case False{}:
      0n

# the number of leading elements below key: on a sorted list, the index of
# the first element not below key (the length if there is none)
def bsearch.lower_bound(xs: List<&2, U32>, +key: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      bsearch.below.step(U32.is_lt(x, key), bsearch.lower_bound(t, key))

def bsearch.find.hit(c: Bool, i: Nat) -> Maybe<&2, Nat>:
  match c:
    case True{}:
      Some{i}
    case False{}:
      None{}

def bsearch.find.check(+i: Nat, m: Maybe<&2, U32>, key: U32) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      bsearch.find.hit(U32.is_eq(x, key), i)

# an index of a sorted list that holds key (the first), or None
def bsearch.find(+xs: List<&2, U32>, +key: U32) -> Maybe<&2, Nat>:
  +i = bsearch.lower_bound(xs, key)
  bsearch.find.check(i, List.get(&2, U32, xs, i), key)

# The fast implementation, on the first n slots of an Array<U32>

def bsearch.array.fin(r: Array<U32> & U32) -> Array<U32>:
  (a, x) = r
  a

def bsearch.array.val(r: Array<U32> & U32) -> U32:
  (a, x) = r
  x

# the search state: the array, and the range [lo, hi) still in question
type BsearchState is Type:
  BsearchState{a: Array<U32>, lo: U32, hi: U32}

# one halving of [lo, hi): the element at mid decides which half stays
def bsearch.array.pick(below: Bool, a: Array<U32>, +lo: U32, +hi: U32, +mid: U32) -> BsearchState:
  match below:
    case True{}:
      BsearchState{a, U32.inc(mid), hi}
    case False{}:
      BsearchState{a, lo, mid}

def bsearch.array.step(active: Bool, r: Array<U32> & U32, +key: U32, +lo: U32, +hi: U32, +mid: U32) -> BsearchState:
  match active:
    case True{}:
      (a, +x) = r
      bsearch.array.pick(U32.is_lt(x, key), a, lo, hi, mid)
    case False{}:
      (a, x) = r
      BsearchState{a, lo, hi}

def bsearch.array.advance(st: BsearchState, +key: U32) -> BsearchState:
  match st:
    case BsearchState{a, +lo, +hi}:
      +mid = U32.add(lo, U32.shr(U32.sub(hi, lo)))
      bsearch.array.step(U32.is_lt(lo, hi), Array.get(U32, a, mid), key, lo, hi, mid)

def bsearch.array.result(st: BsearchState) -> Array<U32> & U32:
  match st:
    case BsearchState{a, lo, hi}:
      (a, lo)

# fuel bounds the halvings: 33 is enough for any [lo, hi) of U32; once the
# range is empty the remaining steps change nothing
def bsearch.array.go(fuel: Nat, st: BsearchState, +key: U32) -> Array<U32> & U32:
  match fuel:
    case 0n:
      bsearch.array.result(st)
    case 1n+f:
      bsearch.array.go(f, bsearch.array.advance(st, key), key)

# the index of the first of the first n elements not below key (n if none)
def bsearch.array_lower_bound(a: Array<U32>, n: U32, key: U32) -> Array<U32> & U32:
  bsearch.array.go(33n, BsearchState{a, 0, n}, key)

def bsearch.array.found(inside: Bool, r: Array<U32> & U32, +i: U32, +key: U32) -> Array<U32> & Maybe<&2, U32>:
  match inside:
    case True{}:
      (a, +x) = r
      (a, Bool.pick(Maybe<&2, U32>, U32.is_eq(x, key), Some{i}, None{}))
    case False{}:
      (a, x) = r
      (a, None{})

def bsearch.array.find(r: Array<U32> & U32, +n: U32, +key: U32) -> Array<U32> & Maybe<&2, U32>:
  (a, +i) = r
  bsearch.array.found(U32.is_lt(i, n), Array.get(U32, a, i), i, key)

# an index of the first n elements of a sorted array that holds key, or None
def bsearch.array_find(a: Array<U32>, +n: U32, +key: U32) -> Array<U32> & Maybe<&2, U32>:
  bsearch.array.find(bsearch.array_lower_bound(a, n, key), n, key)
