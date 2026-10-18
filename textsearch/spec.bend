# bend-osdev-textsearch, bounded exhaustive agreement: every pattern and text
# over a small alphabet up to a length, the text whole, one byte per chunk,
# and split in two at every offset, searched by each algorithm and compared
# with the references (naive.bend, and fsm.bend's ts.fsm.naive for tokens).
# LAWS.bend states that these answer True for small bounds; check.bend runs
# larger ones.
import Base
import ./naive.bend as V
import ./kmp.bend as K
import ./bm.bend as M
import ./fsm.bend as F

def ts.spec.nat_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      Bool.and(Nat.is_eq(a, b), ts.spec.nat_eq(at, bt))
    case _ _:
      False{}

# Words

def ts.spec.prepend(+c: U32, ws: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      Con{Con{c, w}, ts.spec.prepend(c, t)}

def ts.spec.words.go(as: List<&2, U32>, +ws: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match as:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      List.append(&2, List<&2, U32>, ts.spec.prepend(a, ws), ts.spec.words.go(t, ws))

# the words of exactly n letters of the alphabet as
def ts.spec.words(+as: List<&2, U32>, n: Nat) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      [Nil{}]
    case 1n+k:
      ts.spec.words.go(as, ts.spec.words(as, k))

# the words of lo, lo + 1, ..., lo + k - 1 letters
def ts.spec.upto(k: Nat, +as: List<&2, U32>, +lo: Nat) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      List.append(&2, List<&2, U32>, ts.spec.words(as, lo), ts.spec.upto(r, as, 1n+lo))

# Chunkings of a text

def ts.spec.cuts(k: Nat, +xs: List<&2, U32>, +i: Nat) -> List<&2, List<&2, List<&2, U32>>>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      Con{[List.take(&2, U32, xs, i), List.drop(&2, U32, xs, i)], ts.spec.cuts(r, xs, 1n+i)}

def ts.spec.singles(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{[c], ts.spec.singles(t)}

# the text whole, one byte per chunk, and cut in two at every offset
def ts.spec.splits(+xs: List<&2, U32>) -> List<&2, List<&2, List<&2, U32>>>:
  Con{[xs], Con{ts.spec.singles(xs), ts.spec.cuts(1n+List.length(&2, U32, xs), xs, 0n)}}

# Plain patterns: KMP and both Boyer-Moore rules against the reference

def ts.spec.plain.cs(+icase: Bool, +p: List<&2, U32>, +want: List<&2, Nat>, ss: List<&2, List<&2, List<&2, U32>>>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{+cs, r}:
      Bool.and(Bool.and(ts.spec.nat_eq(K.ts.kmp.search(icase, p, cs), want), Bool.and(ts.spec.nat_eq(M.ts.bm.search(icase, M.TsGoodSuffix{}, p, cs), want), ts.spec.nat_eq(M.ts.bm.search(icase, M.TsHorspool{}, p, cs), want))), ts.spec.plain.cs(icase, p, want, r))

def ts.spec.plain.xs(+icase: Bool, +p: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      Bool.and(ts.spec.plain.cs(icase, p, V.ts.naive.ends(icase, p, x), ts.spec.splits(x)), ts.spec.plain.xs(icase, p, r))

# whether every algorithm finds what the reference finds, for each pattern
# of ps in each text of xs, however the text is chunked (of the chunkings
# above)
def ts.spec.plain(+icase: Bool, ps: List<&2, List<&2, U32>>, +xs: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, r}:
      Bool.and(ts.spec.plain.xs(icase, p, xs), ts.spec.plain(icase, r, xs))

# Token patterns: the automaton against its reference

def ts.spec.tokens.cs(+tks: List<&2, F.TsToken>, +want: List<&2, Nat>, ss: List<&2, List<&2, List<&2, U32>>>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{+cs, r}:
      Bool.and(ts.spec.nat_eq(F.ts.fsm.search(tks, cs), want), ts.spec.tokens.cs(tks, want, r))

def ts.spec.tokens.xs(+tks: List<&2, F.TsToken>, xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      Bool.and(ts.spec.tokens.cs(tks, F.ts.fsm.naive(tks, x), ts.spec.splits(x)), ts.spec.tokens.xs(tks, r))

def ts.spec.tokens(ps: List<&2, List<&2, F.TsToken>>, +xs: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, r}:
      Bool.and(ts.spec.tokens.xs(p, xs), ts.spec.tokens(r, xs))

# every token of a class in the four counts
def ts.spec.recurs(+cl: F.TsClass) -> List<&2, F.TsToken>:
  [F.TsToken{cl, F.TsOne{}}, F.TsToken{cl, F.TsPerhaps{}}, F.TsToken{cl, F.TsStar{}}, F.TsToken{cl, F.TsPlus{}}]

def ts.spec.toks(cs: List<&2, F.TsClass>) -> List<&2, F.TsToken>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      List.append(&2, F.TsToken, ts.spec.recurs(c), ts.spec.toks(t))

def ts.spec.with.go(+a: F.TsToken, bs: List<&2, F.TsToken>) -> List<&2, List<&2, F.TsToken>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{[a, b], ts.spec.with.go(a, t)}

def ts.spec.pairs(as: List<&2, F.TsToken>, +bs: List<&2, F.TsToken>) -> List<&2, List<&2, F.TsToken>>:
  match as:
    case Nil{}:
      Nil{}
    case Con{+a, t}:
      List.append(&2, List<&2, F.TsToken>, ts.spec.with.go(a, bs), ts.spec.pairs(t, bs))

def ts.spec.ones(tks: List<&2, F.TsToken>) -> List<&2, List<&2, F.TsToken>>:
  match tks:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{[a], ts.spec.ones(t)}

# the patterns of one token and of two, from the classes cs
def ts.spec.token_pats(cs: List<&2, F.TsClass>) -> List<&2, List<&2, F.TsToken>>:
  +tks = ts.spec.toks(cs)
  List.append(&2, List<&2, F.TsToken>, ts.spec.ones(tks), ts.spec.pairs(tks, tks))
