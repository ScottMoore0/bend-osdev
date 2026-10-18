# bend-osdev-textsearch, byte automata: an algorithm that reads one byte at a
# time,
#   ~step: S -> U32 -> S & Bool
# answering its new state and whether a match ends with that byte, made into
# a feed (textsearch.bend's interface). A match ending with the byte at
# offset k is reported as k + 1.
import Base
import ./textsearch.bend as T

def ts.auto.hit(h: Bool, +e: Nat, ms: List<&2, Nat>) -> List<&2, Nat>:
  match h:
    case True{}:
      Con{e, ms}
    case False{}:
      ms

def ts.auto.cons(~S: Data, h: Bool, +e: Nat, r: S & List<&2, Nat>) -> S & List<&2, Nat>:
  match r:
    case (s, ms):
      (s, ts.auto.hit(h, e, ms))

# r is the step of the byte that ends at offset pos; xs the bytes after it
def ts.auto.go(~S: Data, ~step: S -> U32 -> S & Bool, xs: List<&2, U32>, +pos: Nat, r: S & Bool) -> S & List<&2, Nat>:
  match xs:
    case Nil{}:
      match r:
        case (s, h):
          (s, ts.auto.hit(h, pos, Nil{}))
    case Con{c, t}:
      match r:
        case (s, h):
          ts.auto.cons(~S, h, pos, ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)))

# the bytes xs, the first at offset pos, fed one at a time from state s
def ts.auto.feed(~S: Data, ~step: S -> U32 -> S & Bool, s: S, +pos: Nat, xs: List<&2, U32>) -> S & List<&2, Nat>:
  match xs:
    case Nil{}:
      (s, Nil{})
    case Con{c, t}:
      ts.auto.go(~S, ~step, t, 1n+pos, step(s, c))

def ts.auto.pre(~S: Data, m1: List<&2, Nat>, r: S & List<&2, Nat>) -> S & List<&2, Nat>:
  match r:
    case (s, m2):
      (s, List.append(&2, Nat, m1, m2))

# a feed's outcome r, then the bytes ys from offset pos: the state after
# both, and the matches of both
def ts.auto.then(~S: Data, ~step: S -> U32 -> S & Bool, r: S & List<&2, Nat>, +pos: Nat, ys: List<&2, U32>) -> S & List<&2, Nat>:
  match r:
    case (s, m1):
      ts.auto.pre(~S, m1, ts.auto.feed(~S, ~step, s, pos, ys))

def ts.auto.snd(~S: Data, r: S & List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case (s, ms):
      ms

# the ends of the matches in xs (one chunk), the first byte at offset pos
def ts.auto.ends(~S: Data, ~step: S -> U32 -> S & Bool, s: S, +pos: Nat, xs: List<&2, U32>) -> List<&2, Nat>:
  ts.auto.snd(~S, ts.auto.feed(~S, ~step, s, pos, xs))

# the ends of the matches in the chunks cs (textsearch.bend's ts.run with
# this feed)
def ts.auto.run(~S: Data, ~step: S -> U32 -> S & Bool, s: S, +pos: Nat, cs: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  T.ts.run(~S, ~(s1 => p => xs => ts.auto.feed(~S, ~step, s1, p, xs)), s, pos, cs)
