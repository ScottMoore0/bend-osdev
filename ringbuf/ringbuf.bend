# bend-osdev-ringbuf: a fixed-capacity FIFO ring buffer of U32, in the style
# of the kernel's kfifo.
#
# The slots are an Array<U32> of 2^order slots, updated in place. Two
# counters, in and out, count the elements pushed and popped; the element
# pushed when in was k sits in slot k mod 2^order (the Array's own index
# wrap-around), and the length is in - out. Push writes at in and refuses
# (RingFull) when the length is the capacity; pop reads at out and refuses
# (RingEmpty) when the length is 0.
#
# The counters are Nat, not wrapping machine words: once out reaches the
# capacity, both counters drop by the capacity, which keeps out below the
# capacity and in below twice it, so they stay small however long the ring
# runs, and every slot index stays the same.
#
# model.bend is the reference implementation of the same interface, on the
# list of the elements.
import Base
import ../array/array.bend as A

type RingError is Data:
  RingFull{}
  RingEmpty{}

type RingBuf is Type:
  RingBuf{order: Nat, ins: Nat, outs: Nat, slots: Array<U32>}

# 2^order, the number of slots
def ring.size(o: Nat) -> Nat:
  match o:
    case 0n:
      1n
    case 1n+p:
      Nat.double(ring.size(p))

# the capacity used when none is given: 2^8 = 256 slots
def ring.order_default() -> Nat:
  8n

# Tests on the counters

def ring.full.test(+o: Nat, +i: Nat, +u: Nat) -> Bool:
  Nat.is_eq(Nat.sub(i, u), ring.size(o))

def ring.empty.test(+i: Nat, +u: Nat) -> Bool:
  Nat.is_eq(i, u)

# the invariant every ring the defs below build keeps: out is below the
# capacity, out <= in, and in - out is at most the capacity
def ring.inv(+o: Nat, +i: Nat, +u: Nat) -> Bool:
  Bool.and(Nat.is_lt(u, ring.size(o)), Bool.and(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), ring.size(o))))

# Building and observing

# an empty ring of 2^order slots
def ring.new(+order: Nat) -> RingBuf:
  RingBuf{order, 0n, 0n, Array.new(U32, order, 0)}

def ring.new_default() -> RingBuf:
  ring.new(ring.order_default())

# the number of elements (kfifo_len)
def ring.len(r: RingBuf) -> RingBuf & Nat:
  match r:
    case RingBuf{o, +i, +u, a}:
      (RingBuf{o, i, u, a}, Nat.sub(i, u))

# the number of slots (kfifo_size)
def ring.capacity(r: RingBuf) -> RingBuf & Nat:
  match r:
    case RingBuf{+o, i, u, a}:
      (RingBuf{o, i, u, a}, ring.size(o))

# the number of free slots (kfifo_avail)
def ring.avail(r: RingBuf) -> RingBuf & Nat:
  match r:
    case RingBuf{+o, +i, +u, a}:
      (RingBuf{o, i, u, a}, Nat.sub(ring.size(o), Nat.sub(i, u)))

def ring.is_empty(r: RingBuf) -> RingBuf & Bool:
  match r:
    case RingBuf{o, +i, +u, a}:
      (RingBuf{o, i, u, a}, ring.empty.test(i, u))

def ring.is_full(r: RingBuf) -> RingBuf & Bool:
  match r:
    case RingBuf{+o, +i, +u, a}:
      (RingBuf{o, i, u, a}, ring.full.test(o, i, u))

# whether the counters keep the invariant (every ring built by these defs
# does: see LAWS.bend)
def ring.valid(r: RingBuf) -> RingBuf & Bool:
  match r:
    case RingBuf{+o, +i, +u, a}:
      (RingBuf{o, i, u, a}, ring.inv(o, i, u))

# Listing the elements

def ring.items.word(r: Array<U32> & U32, k: Array<U32> -> U32 -> RingBuf & List<&2, U32>) -> RingBuf & List<&2, U32>:
  (a, x) = r
  k(a, x)

# the elements pushed when in was u to u + n - 1, newest first, in front of
# acc (a tail call per element, so it runs on long rings)
def ring.items.go(n: Nat, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, acc: List<&2, U32>) -> RingBuf & List<&2, U32>:
  match n:
    case 0n:
      (RingBuf{o, i, u, a}, acc)
    case 1n+ +p:
      ring.items.word(Array.get(U32, a, U32.from_nat(Nat.add(u, p))), a2 => x => ring.items.go(p, o, i, u, a2, Con{x, acc}))

# the elements, oldest first, left in place (kfifo_out_peek of all of them)
def ring.items(r: RingBuf) -> RingBuf & List<&2, U32>:
  match r:
    case RingBuf{+o, +i, +u, a}:
      ring.items.go(Nat.sub(i, u), o, i, u, a, Nil{})

# Push and pop

def ring.push.go(full: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, x: U32) -> RingBuf & Result<&2, &2, RingError, Unit>:
  match full:
    case True{}:
      (RingBuf{o, i, u, a}, Fail{RingFull{}})
    case False{}:
      (RingBuf{o, 1n+i, u, Array.set(U32, a, U32.from_nat(i), x)}, Done{Unit{}})

# x appended; RingFull, and the ring unchanged, if there is no room (kfifo_put)
def ring.push(r: RingBuf, x: U32) -> RingBuf & Result<&2, &2, RingError, Unit>:
  match r:
    case RingBuf{+o, +i, +u, a}:
      ring.push.go(ring.full.test(o, i, u), o, i, u, a, x)

# out moved past the element read; at the capacity, both counters drop by it
def ring.pop.wrap(w: Bool, +o: Nat, +i: Nat, u1: Nat, a: Array<U32>, x: U32) -> RingBuf & Result<&2, &2, RingError, U32>:
  match w:
    case True{}:
      (RingBuf{o, Nat.sub(i, ring.size(o)), 0n, a}, Done{x})
    case False{}:
      (RingBuf{o, i, u1, a}, Done{x})

def ring.pop.read(+o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32) -> RingBuf & Result<&2, &2, RingError, U32>:
  (a, x) = ax
  ring.pop.wrap(Nat.is_eq(1n+u, ring.size(o)), o, i, 1n+u, a, x)

def ring.pop.go(empty: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>) -> RingBuf & Result<&2, &2, RingError, U32>:
  match empty:
    case True{}:
      (RingBuf{o, i, u, a}, Fail{RingEmpty{}})
    case False{}:
      ring.pop.read(o, i, u, Array.get(U32, a, U32.from_nat(u)))

# the oldest element, removed; RingEmpty, and the ring unchanged, if there
# is none (kfifo_get)
def ring.pop(r: RingBuf) -> RingBuf & Result<&2, &2, RingError, U32>:
  match r:
    case RingBuf{+o, +i, +u, a}:
      ring.pop.go(ring.empty.test(i, u), o, i, u, a)

def ring.peek.read(+o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32) -> RingBuf & Result<&2, &2, RingError, U32>:
  (a, x) = ax
  (RingBuf{o, i, u, a}, Done{x})

def ring.peek.go(empty: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>) -> RingBuf & Result<&2, &2, RingError, U32>:
  match empty:
    case True{}:
      (RingBuf{o, i, u, a}, Fail{RingEmpty{}})
    case False{}:
      ring.peek.read(o, i, u, Array.get(U32, a, U32.from_nat(u)))

# the oldest element, left in place; RingEmpty if there is none (kfifo_peek)
def ring.peek(r: RingBuf) -> RingBuf & Result<&2, &2, RingError, U32>:
  match r:
    case RingBuf{+o, +i, +u, a}:
      ring.peek.go(ring.empty.test(i, u), o, i, u, a)

# Batches

def ring.push_list.count(p: RingBuf & Result<&2, &2, RingError, Unit>, +n: Nat) -> RingBuf & Nat:
  (r, res) = p
  match res:
    case Done{u}:
      (r, 1n+n)
    case Fail{e}:
      (r, n)

def ring.push_list.step(st: RingBuf & Nat, x: U32) -> RingBuf & Nat:
  (r, +n) = st
  ring.push_list.count(ring.push(r, x), n)

def ring.push_list.go(xs: List<&2, U32>, st: RingBuf & Nat) -> RingBuf & Nat:
  match xs:
    case Nil{}:
      st
    case Con{x, t}:
      ring.push_list.go(t, ring.push_list.step(st, x))

# the elements of xs pushed in order while there is room; how many were
# pushed (kfifo_in)
def ring.push_list(r: RingBuf, xs: List<&2, U32>) -> RingBuf & Nat:
  ring.push_list.go(xs, (r, 0n))

def ring.pop_list.keep(p: RingBuf & Result<&2, &2, RingError, U32>, acc: List<&2, U32>) -> RingBuf & List<&2, U32>:
  (r, res) = p
  match res:
    case Done{x}:
      (r, List.append(&2, U32, acc, Con{x, Nil{}}))
    case Fail{e}:
      (r, acc)

def ring.pop_list.step(st: RingBuf & List<&2, U32>) -> RingBuf & List<&2, U32>:
  (r, acc) = st
  ring.pop_list.keep(ring.pop(r), acc)

def ring.pop_list.go(n: Nat, st: RingBuf & List<&2, U32>) -> RingBuf & List<&2, U32>:
  match n:
    case 0n:
      st
    case 1n+k:
      ring.pop_list.go(k, ring.pop_list.step(st))

# up to n elements popped, oldest first; fewer if the ring empties (kfifo_out)
def ring.pop_list(r: RingBuf, n: Nat) -> RingBuf & List<&2, U32>:
  ring.pop_list.go(n, (r, Nil{}))

# Specifications (for the laws; they look inside the array, so they do not
# run compiled)

# a ring as the defs above build it: valid counters, an order below 32 (so
# that every slot index fits a U32), and its slots a perfect array of 2^order
# (bend-osdev-array's Arrays.is_perfect)
def ring.sound(r: RingBuf) -> Bool:
  match r:
    case RingBuf{+o, +i, +u, a}:
      Bool.and(ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)))
