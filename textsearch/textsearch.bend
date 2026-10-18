# bend-osdev-textsearch: finding a pattern in a byte stream that arrives in
# pieces, the counterpart of the kernel's textsearch framework
# (textsearch_prepare, textsearch_find, textsearch_next).
#
# A search algorithm is a state type ~S and a template argument
#   ~feed: S -> Nat -> List<&2, U32> -> S & List<&2, Nat>
# taking the state, the offset of a chunk's first byte in the stream, and
# the chunk, and answering the new state and the matches the chunk
# completes. A match is given by its end: the offset just past its last byte
# (for a pattern of fixed length m, the match starts m bytes before). The
# state carries what the algorithm needs across chunks, so a match may span
# chunk boundaries.
#
# The instances: auto.bend turns any byte automaton (a state and a step on
# one byte) into a feed; kmp.bend (Knuth-Morris-Pratt) and fsm.bend (a small
# token automaton) are automata; bm.bend (Boyer-Moore, Horspool's rule with
# the good-suffix rule as an option) searches each chunk, carrying the bytes
# a match could still need; naive.bend is the reference.
import Base
import ../bytes/bytes.bend as B

# The stream: chunks of bytes

# the bytes of every chunk, in order
def ts.concat(cs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      List.append(&2, U32, c, ts.concat(t))

# chunks given as Octets, as lists of bytes
def ts.chunks(cs: List<&2, B.Octets>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{B.Octets.to_list(c), ts.chunks(t)}

# Running an algorithm over a stream

def ts.run.go(~S: Data, ~feed: S -> Nat -> List<&2, U32> -> S & List<&2, Nat>, cs: List<&2, List<&2, U32>>, +pos: Nat, r: S & List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      match r:
        case (s, ms):
          ms
    case Con{+c, t}:
      match r:
        case (s, ms):
          List.append(&2, Nat, ms, ts.run.go(~S, ~feed, t, Nat.add(pos, List.length(&2, U32, c)), feed(s, pos, c)))

# the ends of the matches in the chunks cs, the first chunk starting at
# offset pos, from state s
def ts.run(~S: Data, ~feed: S -> Nat -> List<&2, U32> -> S & List<&2, Nat>, s: S, +pos: Nat, cs: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  ts.run.go(~S, ~feed, cs, pos, (s, Nil{}))

# the ends of the matches in a stream of Octets chunks, from its start
def ts.find_all(~S: Data, ~feed: S -> Nat -> List<&2, U32> -> S & List<&2, Nat>, s: S, cs: List<&2, B.Octets>) -> List<&2, Nat>:
  ts.run(~S, ~feed, s, 0n, ts.chunks(cs))

def ts.head(ms: List<&2, Nat>) -> Maybe<&2, Nat>:
  match ms:
    case Nil{}:
      None{}
    case Con{m, t}:
      Some{m}

# the end of the first match (textsearch_find)
def ts.find(~S: Data, ~feed: S -> Nat -> List<&2, U32> -> S & List<&2, Nat>, s: S, cs: List<&2, B.Octets>) -> Maybe<&2, Nat>:
  ts.head(ts.find_all(~S, ~feed, s, cs))

# match ends as starts, for a pattern of m bytes
def ts.starts(+m: Nat, ms: List<&2, Nat>) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{Nat.sub(e, m), ts.starts(m, t)}

# Comparing bytes, exactly or ignoring ASCII case (TS_IGNORECASE)

# a byte with ASCII upper case folded to lower case when icase
def ts.fold.up(up: Bool, +c: U32) -> U32:
  match up:
    case True{}:
      U32.add(c, 32)
    case False{}:
      c

def ts.fold(icase: Bool, +c: U32) -> U32:
  match icase:
    case True{}:
      ts.fold.up(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), c)
    case False{}:
      c

def ts.same(+icase: Bool, a: U32, b: U32) -> Bool:
  U32.is_eq(ts.fold(icase, a), ts.fold(icase, b))

# the usual choice: bytes compared exactly
def ts.exact() -> Bool:
  False{}

def ts.fold_all(+icase: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{ts.fold(icase, c), ts.fold_all(icase, t)}
