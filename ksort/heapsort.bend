# bend-osdev-ksort, heapsort: the first n slots of an Array sorted in
# place, the counterpart of the kernel's sort (lib/sort.c's interface:
# heapsort, O(n log n) comparisons, no extra memory, not stable).
#
# The comparison is a template argument ~le, as for list_sort: le(a, b) says
# a may come before b. The array is a max-heap while it is built, then the
# largest element is swapped to the end of the shrinking heap, n - 1 times.
#
# Every write goes through ksort.heap.swap, which exchanges two slots and
# does nothing unless both lie below n: so the slots from n on are never
# touched, whatever the index arithmetic does, and the array's elements are
# only ever permuted.
#
# Each Array.get answers the array beside the element; the helpers below
# take that pair as a parameter (the shape bend-osdev-array's of_list laws
# follow).
import Base

# Swapping two slots below lim

def ksort.heap.swap.got2(~A: Data, r: Array<A> & A, +i: U32, +j: U32, xi: A) -> Array<A>:
  (a, xj) = r
  Array.set(A, Array.set(A, a, i, xj), j, xi)

def ksort.heap.swap.got(~A: Data, r: Array<A> & A, +i: U32, +j: U32) -> Array<A>:
  (a, xi) = r
  ksort.heap.swap.got2(~A, Array.get(A, a, j), i, j, xi)

def ksort.heap.swap.at(~A: Data, ok: Bool, a: Array<A>, +i: U32, +j: U32) -> Array<A>:
  match ok:
    case True{}:
      ksort.heap.swap.got(~A, Array.get(A, a, i), i, j)
    case False{}:
      a

# slots i and j exchanged when both are below lim; else a unchanged
def ksort.heap.swap(~A: Data, a: Array<A>, +lim: U32, +i: U32, +j: U32) -> Array<A>:
  ksort.heap.swap.at(~A, Bool.and(U32.is_lt(i, lim), U32.is_lt(j, lim)), a, i, j)

# Sifting down: the state of one sift, a step at a time

# the array, the bound lim of every swap, the heap's size n, the slot i
# being sifted, and whether the sift goes on
type KsortHeap<-A: Data> is Type:
  KsortHeap{a: Array<A>, lim: U32, n: U32, i: U32, live: Bool}

# m is i's larger child: swap them and go on from m, unless m is not above i
def ksort.heap.decide(~A: Data, stop: Bool, a: Array<A>, +lim: U32, +n: U32, +i: U32, +m: U32) -> KsortHeap<A>:
  match stop:
    case True{}:
      KsortHeap{a, lim, n, i, False{}}
    case False{}:
      KsortHeap{ksort.heap.swap(~A, a, lim, i, m), lim, n, m, True{}}

def ksort.heap.cmp.got2(~A: Data, ~le: A -> A -> Bool, r: Array<A> & A, +lim: U32, +n: U32, +i: U32, +m: U32, xi: A) -> KsortHeap<A>:
  (a, xm) = r
  ksort.heap.decide(~A, le(xm, xi), a, lim, n, i, m)

def ksort.heap.cmp.got(~A: Data, ~le: A -> A -> Bool, r: Array<A> & A, +lim: U32, +n: U32, +i: U32, +m: U32) -> KsortHeap<A>:
  (a, xi) = r
  ksort.heap.cmp.got2(~A, ~le, Array.get(A, a, m), lim, n, i, m, xi)

def ksort.heap.cmp(~A: Data, ~le: A -> A -> Bool, a: Array<A>, +lim: U32, +n: U32, +i: U32, +m: U32) -> KsortHeap<A>:
  ksort.heap.cmp.got(~A, ~le, Array.get(A, a, i), lim, n, i, m)

def ksort.heap.pick.got2(~A: Data, ~le: A -> A -> Bool, r: Array<A> & A, +lim: U32, +n: U32, +i: U32, +c: U32, +d: U32, xc: A) -> KsortHeap<A>:
  (a, xd) = r
  ksort.heap.cmp(~A, ~le, a, lim, n, i, Bool.pick(U32, le(xc, xd), d, c))

def ksort.heap.pick.got(~A: Data, ~le: A -> A -> Bool, r: Array<A> & A, +lim: U32, +n: U32, +i: U32, +c: U32, +d: U32) -> KsortHeap<A>:
  (a, xc) = r
  ksort.heap.pick.got2(~A, ~le, Array.get(A, a, d), lim, n, i, c, d, xc)

# c is i's left child: the larger of c and c + 1, if c + 1 is in the heap
def ksort.heap.pick(~A: Data, ~le: A -> A -> Bool, two: Bool, a: Array<A>, +lim: U32, +n: U32, +i: U32, +c: U32) -> KsortHeap<A>:
  match two:
    case True{}:
      ksort.heap.pick.got(~A, ~le, Array.get(A, a, c), lim, n, i, c, U32.inc(c))
    case False{}:
      ksort.heap.cmp(~A, ~le, a, lim, n, i, c)

def ksort.heap.child(~A: Data, ~le: A -> A -> Bool, has: Bool, a: Array<A>, +lim: U32, +n: U32, +i: U32, +c: U32) -> KsortHeap<A>:
  match has:
    case True{}:
      ksort.heap.pick(~A, ~le, U32.is_lt(U32.inc(c), n), a, lim, n, i, c)
    case False{}:
      KsortHeap{a, lim, n, i, False{}}

def ksort.heap.live(~A: Data, ~le: A -> A -> Bool, live: Bool, a: Array<A>, +lim: U32, +n: U32, +i: U32) -> KsortHeap<A>:
  match live:
    case True{}:
      +c = U32.inc(U32.shl(i))
      ksort.heap.child(~A, ~le, Bool.and(U32.is_lt(c, n), U32.is_lt(i, c)), a, lim, n, i, c)
    case False{}:
      KsortHeap{a, lim, n, i, False{}}

# one step of a sift: i moves down one level, or the sift stops
def ksort.heap.step(~A: Data, ~le: A -> A -> Bool, st: KsortHeap<A>) -> KsortHeap<A>:
  match st:
    case KsortHeap{a, +lim, +n, +i, live}:
      ksort.heap.live(~A, ~le, live, a, lim, n, i)

def ksort.heap.sift(~A: Data, ~le: A -> A -> Bool, fuel: Nat, st: KsortHeap<A>) -> KsortHeap<A>:
  match fuel:
    case 0n:
      st
    case 1n+f:
      ksort.heap.sift(~A, ~le, f, ksort.heap.step(~A, ~le, st))

def ksort.heap.array(~A: Data, st: KsortHeap<A>) -> Array<A>:
  match st:
    case KsortHeap{a, lim, n, i, live}:
      a

# slot i sifted down the heap of the first n slots; 33 steps reach the
# bottom of any heap, since each one at least doubles i
def ksort.heap.sift_down(~A: Data, ~le: A -> A -> Bool, a: Array<A>, +lim: U32, +n: U32, +i: U32) -> Array<A>:
  ksort.heap.array(~A, ksort.heap.sift(~A, ~le, 33n, KsortHeap{a, lim, n, i, True{}}))

# Building the heap and taking it apart

# slots i - 1 down to 0 sifted (fuel is i)
def ksort.heap.build(~A: Data, ~le: A -> A -> Bool, fuel: Nat, a: Array<A>, +lim: U32, +n: U32, +i: U32) -> Array<A>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      +j = U32.sub(i, 1)
      ksort.heap.build(~A, ~le, f, ksort.heap.sift_down(~A, ~le, a, lim, n, j), lim, n, j)

# the heap of the first m slots: its largest element swapped to slot m - 1
# and the rest sifted, until one slot is left (fuel is m - 1)
def ksort.heap.drain(~A: Data, ~le: A -> A -> Bool, fuel: Nat, a: Array<A>, +lim: U32, +m: U32) -> Array<A>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      +k = U32.sub(m, 1)
      ksort.heap.drain(~A, ~le, f, ksort.heap.sift_down(~A, ~le, ksort.heap.swap(~A, a, lim, 0, k), lim, k, 0), lim, k)

# the first n slots of a sorted by le, in place; the others unchanged (sort)
def ksort.heap_sort(~A: Data, ~le: A -> A -> Bool, a: Array<A>, +n: U32) -> Array<A>:
  +h = U32.shr(n)
  ksort.heap.drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), ksort.heap.build(~A, ~le, U32.to_nat(h), a, n, n, h), n, n)

# heap_sort by a Nat key, smallest first
def ksort.heap_sort_by(~A: Data, ~key: A -> Nat, a: Array<A>, +n: U32) -> Array<A>:
  ksort.heap_sort(~A, ~(x => y => Nat.is_le(key(x), key(y))), a, n)
