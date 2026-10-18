# bend-osdev-c842, the matcher: finds earlier copies of the 8-, 4- and
# 2-byte phrases of a chunk, for the encoder's pointers.
#
# As the paper describes the hardware (Blaner et al. 2013), each phrase size
# has its own direct-mapped hash table holding a pointer to where a phrase
# with that hash was last seen; a candidate is used only once its bytes are
# compared with the phrase (the table's entries are only hints). Here the
# tables hold positions in the input, the hash is FNV-1a over the phrase's
# bytes (the paper's XOR trees are the hardware's own), and the bytes are
# compared through the window (window.bend). A candidate must also be one the
# decoder will read for its index: no more than the history (2048 bytes for
# P8 and P4, 512 for P2) before the chunk being encoded, which starts at a
# multiple of 8 (the encoder writes short data only at the end).
#
# The strategy is a parameter: C842NoMatch (no pointers: chunks as literals,
# Z8 and RPT only), or C842Hash with each table's size (2^bits entries).
# C842Strategy.default() is C842Hash{10, 11, 10}: the hardware's table sizes
# for 8- and 4-byte phrases (1K and 2K entries) and 1K for 2-byte phrases.
import Base
import ./format.bend as F
import ./window.bend as W

type C842Strategy is Data:
  C842NoMatch{}
  C842Hash{bits8: Nat, bits4: Nat, bits2: Nat}

def C842Strategy.default() -> C842Strategy:
  C842Hash{10n, 11n, 10n}

# the tables (position + 1 of the latest phrase with each hash; 0: none),
# and each one's shift (32 - its bits); on: matching at all
type C842Matcher is Type:
  C842Matcher{on: Bool, t8: Array<U32>, t4: Array<U32>, t2: Array<U32>, s8: Nat, s4: Nat, s2: Nat}

def c842.match.new(s: C842Strategy) -> C842Matcher:
  match s:
    case C842NoMatch{}:
      C842Matcher{False{}, Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), 32n, 32n, 32n}
    case C842Hash{+b8, +b4, +b2}:
      C842Matcher{True{}, Array.new(U32, b8, 0), Array.new(U32, b4, 0), Array.new(U32, b2, 0), Nat.sub(32n, b8), Nat.sub(32n, b4), Nat.sub(32n, b2)}

# FNV-1a, 32 bits, over a phrase's bytes
def c842.match.fnv.go(xs: List<&2, U32>, h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      c842.match.fnv.go(t, U32.mul(U32.xor(h, x), 16777619))

def c842.match.hash(xs: List<&2, U32>, sh: Nat) -> U32:
  U32.shrn(c842.match.fnv.go(xs, 2166136261), sh)

# the phrase's bytes are the window's from position p on
def c842.match.same(xs: List<&2, U32>, +w: W.C842Win, +p: U32, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{x, t}:
      c842.match.same(t, w, U32.add(p, 1), Bool.and(ok, U32.is_eq(x, W.c842.win.get(w, p))))

def c842.match.log(k: F.C842Kind) -> Nat:
  match k:
    case F.C842LL{}:
      1n
    case F.C842P2{}:
      1n
    case F.C842P4{}:
      2n
    case F.C842P8{}:
      3n

def c842.match.index.at(ok: Bool, +p: U32, +k: F.C842Kind) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{U32.shrn(U32.and(p, U32.sub(F.C842Kind.history(k), 1)), c842.match.log(k))}
    case False{}:
      None{}

# the index for a candidate entry e (position + 1) of phrase xs, for the
# chunk at i
def c842.match.check.at(empty: Bool, +e: U32, +k: F.C842Kind, +i: U32, xs: List<&2, U32>, w: W.C842Win) -> Maybe<&2, U32>:
  match empty:
    case True{}:
      None{}
    case False{}:
      +p = U32.sub(e, 1)
      c842.match.index.at(Bool.and(U32.is_le(U32.sub(i, p), F.C842Kind.history(k)), c842.match.same(xs, w, p, True{})), p, k)

def c842.match.check(+e: U32, +k: F.C842Kind, +i: U32, xs: List<&2, U32>, w: W.C842Win) -> Maybe<&2, U32>:
  c842.match.check.at(U32.is_eq(e, 0), e, k, i, xs, w)

# a table and what was found in it
type C842Look is Type:
  C842Look{t: Array<U32>, found: Maybe<&2, U32>}

def c842.match.look.got(r: Array<U32> & U32, +k: F.C842Kind, +i: U32, xs: List<&2, U32>, w: W.C842Win) -> C842Look:
  (t, e) = r
  C842Look{t, c842.match.check(e, k, i, xs, w)}

def c842.match.look(t: Array<U32>, sh: Nat, +k: F.C842Kind, +i: U32, +xs: List<&2, U32>, w: W.C842Win) -> C842Look:
  c842.match.look.got(Array.get(U32, t, c842.match.hash(xs, sh)), k, i, xs, w)

# The interface (the encoder's)

# a matcher and what it found
type C842Found is Type:
  C842Found{m: C842Matcher, found: Maybe<&2, U32>}

def c842.match.put8(l: C842Look, t4: Array<U32>, t2: Array<U32>, s8: Nat, s4: Nat, s2: Nat) -> C842Found:
  match l:
    case C842Look{t, f}:
      C842Found{C842Matcher{True{}, t, t4, t2, s8, s4, s2}, f}

def c842.match.put4(l: C842Look, t8: Array<U32>, t2: Array<U32>, s8: Nat, s4: Nat, s2: Nat) -> C842Found:
  match l:
    case C842Look{t, f}:
      C842Found{C842Matcher{True{}, t8, t, t2, s8, s4, s2}, f}

def c842.match.put2(l: C842Look, t8: Array<U32>, t4: Array<U32>, s8: Nat, s4: Nat, s2: Nat) -> C842Found:
  match l:
    case C842Look{t, f}:
      C842Found{C842Matcher{True{}, t8, t4, t, s8, s4, s2}, f}

# the index of an earlier copy of the phrase xs (of kind P2, P4 or P8), for
# the chunk starting at i, if the matcher finds one the decoder will read
def c842.match.find(m: C842Matcher, +k: F.C842Kind, +i: U32, +xs: List<&2, U32>, w: W.C842Win) -> C842Found:
  match m:
    case C842Matcher{on, t8, t4, t2, +s8, +s4, +s2}:
      match on:
        case False{}:
          C842Found{C842Matcher{False{}, t8, t4, t2, s8, s4, s2}, None{}}
        case True{}:
          match k:
            case F.C842P8{}:
              c842.match.put8(c842.match.look(t8, s8, F.C842P8{}, i, xs, w), t4, t2, s8, s4, s2)
            case F.C842P4{}:
              c842.match.put4(c842.match.look(t4, s4, F.C842P4{}, i, xs, w), t8, t2, s8, s4, s2)
            case F.C842P2{}:
              c842.match.put2(c842.match.look(t2, s2, F.C842P2{}, i, xs, w), t8, t4, s8, s4, s2)
            case F.C842LL{}:
              C842Found{C842Matcher{True{}, t8, t4, t2, s8, s4, s2}, None{}}

# the matcher with the phrase xs (of kind k) seen at position j
def c842.match.add(m: C842Matcher, k: F.C842Kind, +j: U32, +xs: List<&2, U32>) -> C842Matcher:
  match m:
    case C842Matcher{on, t8, t4, t2, +s8, +s4, +s2}:
      match on:
        case False{}:
          C842Matcher{False{}, t8, t4, t2, s8, s4, s2}
        case True{}:
          match k:
            case F.C842P8{}:
              C842Matcher{True{}, Array.set(U32, t8, c842.match.hash(xs, s8), U32.add(j, 1)), t4, t2, s8, s4, s2}
            case F.C842P4{}:
              C842Matcher{True{}, t8, Array.set(U32, t4, c842.match.hash(xs, s4), U32.add(j, 1)), t2, s8, s4, s2}
            case F.C842P2{}:
              C842Matcher{True{}, t8, t4, Array.set(U32, t2, c842.match.hash(xs, s2), U32.add(j, 1)), s8, s4, s2}
            case F.C842LL{}:
              C842Matcher{True{}, t8, t4, t2, s8, s4, s2}
