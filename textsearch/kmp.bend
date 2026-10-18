# bend-osdev-textsearch, Knuth-Morris-Pratt (the kernel's ts_kmp): a byte
# automaton whose state is how much of the pattern the text read so far ends
# with. On a byte that does not extend it, the prefix table says the next
# shorter prefix that the text also ends with, so no byte is read twice.
import Base
import ./textsearch.bend as T
import ./auto.bend as A

# the pattern (case-folded when icase), its prefix table, its length, and q:
# how many of its bytes the text read so far ends with (below m)
type TsKmp is Data:
  TsKmp{icase: Bool, pat: List<&2, U32>, fail: List<&2, Nat>, m: Nat, q: Nat}

def ts.kmp.at(xs: List<&2, U32>, k: Nat) -> U32:
  match xs k:
    case Nil{} _:
      0
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      ts.kmp.at(t, j)

def ts.kmp.nat_at(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs k:
    case Nil{} _:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      ts.kmp.nat_at(t, j)

def ts.kmp.back.pick(hit: Bool, +k: Nat, r: Nat) -> Nat:
  match hit:
    case True{}:
      k
    case False{}:
      r

# from a prefix of k bytes, the longest prefix along the prefix table that
# is empty or can be extended by byte b; fuel bounds the steps (k + 1 is
# enough: each step is shorter)
def ts.kmp.back(fuel: Nat, +pat: List<&2, U32>, +fail: List<&2, Nat>, +b: U32, +k: Nat) -> Nat:
  match fuel k:
    case _ 0n:
      0n
    case 0n 1n+j:
      0n
    case 1n+f 1n+j:
      ts.kmp.back.pick(U32.is_eq(ts.kmp.at(pat, 1n+j), b), 1n+j, ts.kmp.back(f, pat, fail, b, ts.kmp.nat_at(fail, j)))

def ts.kmp.ext(ok: Bool, +k: Nat) -> Nat:
  match ok:
    case True{}:
      1n+k
    case False{}:
      k

# the longest prefix the text ends with, after a prefix of k bytes and then
# byte b
def ts.kmp.next(+pat: List<&2, U32>, +fail: List<&2, Nat>, +b: U32, +k: Nat) -> Nat:
  +k1 = ts.kmp.back(1n+k, pat, fail, b, k)
  ts.kmp.ext(U32.is_eq(ts.kmp.at(pat, k1), b), k1)

def ts.kmp.pi.go(xs: List<&2, U32>, +pat: List<&2, U32>, +acc: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{b, t}:
      +k2 = ts.kmp.next(pat, acc, b, k)
      ts.kmp.pi.go(t, pat, List.append(&2, Nat, acc, [k2]), k2)

# the prefix table: entry i is the length of the longest proper prefix of
# pat[0..i] that is also its suffix
def ts.kmp.pi(+pat: List<&2, U32>) -> List<&2, Nat>:
  match pat:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      ts.kmp.pi.go(t, Con{b, t}, [0n], 0n)

# the state before any text
def ts.kmp.start(+icase: Bool, p: List<&2, U32>) -> TsKmp:
  +fp = T.ts.fold_all(icase, p)
  TsKmp{icase, fp, ts.kmp.pi(fp), List.length(&2, U32, fp), 0n}

def ts.kmp.done(+icase: Bool, +pat: List<&2, U32>, +fail: List<&2, Nat>, +m: Nat, +q: Nat, full: Bool) -> TsKmp & Bool:
  match full:
    case True{}:
      (TsKmp{icase, pat, fail, m, ts.kmp.nat_at(fail, Nat.sub(m, 1n))}, True{})
    case False{}:
      (TsKmp{icase, pat, fail, m, q}, False{})

# one byte (the automaton's step); an empty pattern never matches
def ts.kmp.step(s: TsKmp, c: U32) -> TsKmp & Bool:
  match s:
    case TsKmp{+icase, +pat, +fail, m, +q}:
      match m:
        case 0n:
          (TsKmp{icase, pat, fail, 0n, q}, False{})
        case 1n+ +k:
          +q2 = ts.kmp.next(pat, fail, T.ts.fold(icase, c), q)
          ts.kmp.done(icase, pat, fail, 1n+k, q2, Nat.is_eq(q2, 1n+k))

# The textsearch interface

# a chunk of bytes, the first at offset pos
def ts.kmp.feed(s: TsKmp, pos: Nat, xs: List<&2, U32>) -> TsKmp & List<&2, Nat>:
  A.ts.auto.feed(~TsKmp, ~ts.kmp.step, s, pos, xs)

# the ends of the occurrences of p in the text xs
def ts.kmp.ends(+icase: Bool, p: List<&2, U32>, xs: List<&2, U32>) -> List<&2, Nat>:
  A.ts.auto.ends(~TsKmp, ~ts.kmp.step, ts.kmp.start(icase, p), 0n, xs)

# the ends of the occurrences of p in the text arriving as the chunks cs
def ts.kmp.search(+icase: Bool, p: List<&2, U32>, cs: List<&2, List<&2, U32>>) -> List<&2, Nat>:
  A.ts.auto.run(~TsKmp, ~ts.kmp.step, ts.kmp.start(icase, p), 0n, cs)
