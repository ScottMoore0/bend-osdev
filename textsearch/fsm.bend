# bend-osdev-textsearch, a small token automaton (the kernel's ts_fsm): the
# pattern is a list of tokens, each a class of bytes and how many of them:
# exactly one, one or none (TsPerhaps), any number (TsStar), one or more
# (TsPlus). A match is a non-empty run of bytes that the tokens, in order,
# describe; the search reports where each match ends (several matches may
# end at the same byte: it is reported once).
#
# The automaton keeps the set of token positions some match in progress has
# reached (position k: tokens 0 to k - 1 matched), and starts a new match at
# every byte, so no byte is read twice.
import Base
import ./textsearch.bend as T
import ./auto.bend as A

type TsClass is Data:
  TsIs{b: U32}
  TsRange{lo: U32, hi: U32}
  TsOneOf{bs: List<&2, U32>}
  TsAnyByte{}

type TsRecur is Data:
  TsOne{}
  TsPerhaps{}
  TsStar{}
  TsPlus{}

type TsToken is Data:
  TsToken{class: TsClass, recur: TsRecur}

# the tokens (TsPlus written as TsOne then TsStar) and, for each position 0
# to the number of tokens, whether a match in progress has reached it
type TsFsm is Data:
  TsFsm{toks: List<&2, TsToken>, active: List<&2, Bool>}

# Classes

def ts.fsm.has(bs: List<&2, U32>, +c: U32) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, t}:
      Bool.or(U32.is_eq(b, c), ts.fsm.has(t, c))

def ts.fsm.member(cl: TsClass, +c: U32) -> Bool:
  match cl:
    case TsIs{b}:
      U32.is_eq(b, c)
    case TsRange{lo, hi}:
      Bool.and(U32.is_le(lo, c), U32.is_le(c, hi))
    case TsOneOf{bs}:
      ts.fsm.has(bs, c)
    case TsAnyByte{}:
      True{}

def ts.fsm.digit() -> TsClass:
  TsRange{48, 57}

def ts.fsm.lower() -> TsClass:
  TsRange{97, 122}

def ts.fsm.upper() -> TsClass:
  TsRange{65, 90}

def ts.fsm.space() -> TsClass:
  TsOneOf{[9, 10, 11, 12, 13, 32]}

# a byte string as tokens: each byte exactly once
def ts.fsm.literal(p: List<&2, U32>) -> List<&2, TsToken>:
  match p:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{TsToken{TsIs{b}, TsOne{}}, ts.fsm.literal(t)}

# The automaton

def ts.fsm.expand(tks: List<&2, TsToken>) -> List<&2, TsToken>:
  match tks:
    case Nil{}:
      Nil{}
    case Con{TsToken{+cl, TsPlus{}}, t}:
      Con{TsToken{cl, TsOne{}}, Con{TsToken{cl, TsStar{}}, ts.fsm.expand(t)}}
    case Con{tk, t}:
      Con{tk, ts.fsm.expand(t)}

def ts.fsm.falses(tks: List<&2, TsToken>) -> List<&2, Bool>:
  match tks:
    case Nil{}:
      [False{}]
    case Con{tk, t}:
      Con{False{}, ts.fsm.falses(t)}

# the state before any text
def ts.fsm.start(tks: List<&2, TsToken>) -> TsFsm:
  +e = ts.fsm.expand(tks)
  TsFsm{e, ts.fsm.falses(e)}

def ts.fsm.optional(tk: TsToken) -> Bool:
  match tk:
    case TsToken{cl, r}:
      match r:
        case TsOne{}:
          False{}
        case TsPerhaps{}:
          True{}
        case TsStar{}:
          True{}
        case TsPlus{}:
          False{}

def ts.fsm.stays(tk: TsToken) -> Bool:
  match tk:
    case TsToken{cl, r}:
      match r:
        case TsStar{}:
          True{}
        case TsOne{}:
          False{}
        case TsPerhaps{}:
          False{}
        case TsPlus{}:
          False{}

def ts.fsm.matches(tk: TsToken, +c: U32) -> Bool:
  match tk:
    case TsToken{cl, r}:
      ts.fsm.member(cl, c)

# the positions reachable without reading: past optional tokens
def ts.fsm.close(tks: List<&2, TsToken>, act: List<&2, Bool>, carry: Bool) -> List<&2, Bool>:
  match tks act:
    case Nil{} Con{a, r}:
      [Bool.or(a, carry)]
    case Con{+tk, tt} Con{a, at}:
      +o = Bool.or(a, carry)
      Con{o, ts.fsm.close(tt, at, Bool.and(o, ts.fsm.optional(tk)))}
    case _ Nil{}:
      Nil{}

# the positions after reading byte c: a TsStar token stays, the others move
# on one position
def ts.fsm.advance(tks: List<&2, TsToken>, act: List<&2, Bool>, +c: U32, inc: Bool) -> List<&2, Bool>:
  match tks act:
    case Nil{} Con{a, r}:
      [inc]
    case Con{+tk, tt} Con{a, at}:
      +mt = Bool.and(a, ts.fsm.matches(tk, c))
      +st = ts.fsm.stays(tk)
      Con{Bool.or(inc, Bool.and(mt, st)), ts.fsm.advance(tt, at, c, Bool.and(mt, Bool.not(st)))}
    case _ Nil{}:
      Nil{}

def ts.fsm.start_here(act: List<&2, Bool>) -> List<&2, Bool>:
  match act:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{True{}, t}

def ts.fsm.last(act: List<&2, Bool>) -> Bool:
  match act:
    case Nil{}:
      False{}
    case Con{a, Nil{}}:
      a
    case Con{a, t}:
      ts.fsm.last(t)

# one byte (the automaton's step): a match may start at it; whether a match
# ends with it
def ts.fsm.step(s: TsFsm, c: U32) -> TsFsm & Bool:
  match s:
    case TsFsm{+tks, act}:
      +a0 = ts.fsm.close(tks, ts.fsm.start_here(act), False{})
      +a2 = ts.fsm.close(tks, ts.fsm.advance(tks, a0, c, False{}), False{})
      (TsFsm{tks, a2}, ts.fsm.last(a2))

# The textsearch interface

def ts.fsm.feed(s: TsFsm, pos: Nat, xs: List<&2, U32>) -> TsFsm & List<&2, Nat>:
  A.ts.auto.feed(~TsFsm, ~ts.fsm.step, s, pos, xs)

# the ends of the matches of the tokens in the text xs
def ts.fsm.ends(tks: List<&2, TsToken>, xs: List<&2, U32>) -> List<&2, Nat>:
  A.ts.auto.ends(~TsFsm, ~ts.fsm.step, ts.fsm.start(tks), 0n, xs)

# the ends of the matches in the text arriving as the chunks cs
def ts.fsm.search(tks: List<&2, TsToken>, cs: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  A.ts.auto.run(~TsFsm, ~ts.fsm.step, ts.fsm.start(tks), 0n, cs)

# The reference: the tokens tried against every run of the text

def ts.fsm.is_nil(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{c, t}:
      False{}

# whether the tokens describe exactly the bytes xs; fuel bounds the steps
# (each reads a token or a byte: their numbers plus one are enough)
def ts.fsm.full(fuel: Nat, tks: List<&2, TsToken>, xs: List<&2, U32>) -> Bool:
  match fuel tks:
    case 0n _:
      False{}
    case 1n+f Nil{}:
      ts.fsm.is_nil(xs)
    case 1n+ +f Con{TsToken{+cl, r}, +tt}:
      match r xs:
        case TsOne{} Nil{}:
          False{}
        case TsOne{} Con{c, t}:
          Bool.and(ts.fsm.member(cl, c), ts.fsm.full(f, tt, t))
        case TsPerhaps{} Nil{}:
          ts.fsm.full(f, tt, Nil{})
        case TsPerhaps{} Con{+c, +t}:
          Bool.or(ts.fsm.full(f, tt, Con{c, t}), Bool.and(ts.fsm.member(cl, c), ts.fsm.full(f, tt, t)))
        case TsStar{} Nil{}:
          ts.fsm.full(f, tt, Nil{})
        case TsStar{} Con{+c, +t}:
          Bool.or(ts.fsm.full(f, tt, Con{c, t}), Bool.and(ts.fsm.member(cl, c), ts.fsm.full(f, Con{TsToken{cl, TsStar{}}, tt}, t)))
        case TsPlus{} Nil{}:
          False{}
        case TsPlus{} Con{c, t}:
          Bool.and(ts.fsm.member(cl, c), ts.fsm.full(f, Con{TsToken{cl, TsStar{}}, tt}, t))

def ts.fsm.fuel(tks: List<&2, TsToken>, xs: List<&2, U32>) -> Nat:
  1n+Nat.add(Nat.mul(2n, List.length(&2, TsToken, tks)), List.length(&2, U32, xs))

# whether a non-empty suffix of xs matches
def ts.fsm.any_suffix(+tks: List<&2, TsToken>, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+c, +t}:
      Bool.or(ts.fsm.full(ts.fsm.fuel(tks, Con{c, t}), tks, Con{c, t}), ts.fsm.any_suffix(tks, t))

def ts.fsm.hit(h: Bool, +e: Nat, ms: List<&2, Nat>) -> List<&2, Nat>:
  match h:
    case True{}:
      Con{e, ms}
    case False{}:
      ms

def ts.fsm.naive.go(k: Nat, +tks: List<&2, TsToken>, +xs: List<&2, U32>, +i: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      ts.fsm.hit(ts.fsm.any_suffix(tks, List.take(&2, U32, xs, i)), i, ts.fsm.naive.go(r, tks, xs, 1n+i))

# the ends of the matches: every offset i where some non-empty run ending
# at i matches
def ts.fsm.naive(+tks: List<&2, TsToken>, +xs: List<&2, U32>) -> List<&2, Nat>:
  ts.fsm.naive.go(List.length(&2, U32, xs), tks, xs, 1n)
