# bend-osdev-deflate: the dynamic Huffman encoder (RFC 1951, 3.2.7): code
# lengths from symbol frequencies, and a dynamic block's header.
#
# Code lengths come from the package-merge algorithm (L. L. Larmore and D. S.
# Hirschberg, "A Fast Algorithm for Optimal Length-Limited Huffman Codes",
# Journal of the ACM 37(3), 1990): the optimal prefix code whose codes are at
# most `limit` bits (15 for the literal/length and distance codes, 7 for the
# code length code, whose lengths 3.2.7 sends in 3 bits). Each code is
# complete: a code with one symbol used gets a second one, of one bit too,
# so no decoder need accept an incomplete code.
#
# The header (3.2.7): HLIT and HDIST, the code lengths of the two codes as
# one sequence ("all code lengths form a single sequence of HLIT + HDIST +
# 258 values") run-length coded with 16 (copy the previous length 3 to 6
# times), 17 (a length of 0, 3 to 10 times) and 18 (0, 11 to 138 times), and
# the code length code's own lengths in 3.2.7's order, trailing zeros
# dropped (at least 4 are sent).
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as K
import ./huffman.bend as H
import ./table.bend as T

# Code lengths from frequencies (package-merge)

# a coin: its weight and the symbols it covers (a leaf covers one)
type DflItem is Data:
  DflItem{w: U32, syms: List<&2, U32>}

def dyn.item.le(a: DflItem, b: DflItem) -> Bool:
  match a b:
    case DflItem{x, s} DflItem{y, t}:
      U32.is_le(x, y)

def dyn.leaf(zero: Bool, +f: U32, +sym: U32, acc: List<&2, DflItem>) -> List<&2, DflItem>:
  match zero:
    case True{}:
      acc
    case False{}:
      Con{DflItem{f, [sym]}, acc}

# the leaves, one per symbol with a nonzero frequency (reversed)
def dyn.leaves(fs: List<&2, U32>, +sym: U32, acc: List<&2, DflItem>) -> List<&2, DflItem>:
  match fs:
    case Nil{}:
      acc
    case Con{+f, t}:
      dyn.leaves(t, U32.add(sym, 1), dyn.leaf(U32.is_eq(f, 0), f, sym, acc))

# Merging two sorted lists (ties: the first list's item first), a step at a
# time

type DflMs is Data:
  DflMs{a: List<&2, DflItem>, b: List<&2, DflItem>, acc: List<&2, DflItem>}

def dyn.mstep.pick(first: Bool, +x: DflItem, s: List<&2, DflItem>, +y: DflItem, t: List<&2, DflItem>, acc: List<&2, DflItem>) -> DflMs:
  match first:
    case True{}:
      DflMs{s, Con{y, t}, Con{x, acc}}
    case False{}:
      DflMs{Con{x, s}, t, Con{y, acc}}

def dyn.mstep(m: DflMs) -> DflMs:
  match m:
    case DflMs{a, b, acc}:
      match a:
        case Nil{}:
          match b:
            case Nil{}:
              DflMs{Nil{}, Nil{}, acc}
            case Con{y, t}:
              DflMs{Nil{}, t, Con{y, acc}}
        case Con{+x, s}:
          match b:
            case Nil{}:
              DflMs{s, Nil{}, Con{x, acc}}
            case Con{+y, t}:
              dyn.mstep.pick(dyn.item.le(x, y), x, s, y, t, acc)

def dyn.merge.go(fuel: Nat, m: DflMs) -> List<&2, DflItem>:
  match fuel:
    case 0n:
      match m:
        case DflMs{a, b, acc}:
          List.reverse(&2, DflItem, acc)
    case 1n+f:
      dyn.merge.go(f, dyn.mstep(m))

def dyn.merge(+a: List<&2, DflItem>, +b: List<&2, DflItem>) -> List<&2, DflItem>:
  dyn.merge.go(Nat.add(List.length(&2, DflItem, a), List.length(&2, DflItem, b)), DflMs{a, b, Nil{}})

# neighbours paired into packages (an odd one left over is dropped)
def dyn.package(xs: List<&2, DflItem>) -> List<&2, DflItem>:
  match xs:
    case Con{DflItem{w1, s1}, Con{DflItem{w2, s2}, t}}:
      Con{DflItem{U32.add(w1, w2), B.append.fast(s1, s2)}, dyn.package(t)}
    case _:
      Nil{}

# limit - 1 rounds of packaging and merging with the leaves
def dyn.rounds(n: Nat, +leaves: List<&2, DflItem>, cur: List<&2, DflItem>) -> List<&2, DflItem>:
  match n:
    case 0n:
      cur
    case 1n+p:
      dyn.rounds(p, leaves, dyn.merge(leaves, dyn.package(cur)))

def dyn.count.syms(ss: List<&2, U32>, tab: T.DflTab) -> T.DflTab:
  match ss:
    case Nil{}:
      tab
    case Con{+s, t}:
      +tb = tab
      dyn.count.syms(t, T.tab.set9(s, tb, U32.add(T.tab.get9(s, tb), 1)))

def dyn.count.items(xs: List<&2, DflItem>, tab: T.DflTab) -> T.DflTab:
  match xs:
    case Nil{}:
      tab
    case Con{DflItem{w, ss}, t}:
      dyn.count.items(t, dyn.count.syms(ss, tab))

# the first n entries of a table, as a list
def dyn.read(n: Nat, +i: U32, +tab: T.DflTab, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      dyn.read(p, U32.add(i, 1), tab, Con{T.tab.get9(i, tab), acc})

def dyn.other(zero: Bool) -> U32:
  match zero:
    case True{}:
      1
    case False{}:
      0

def dyn.one(+sym: U32) -> T.DflTab:
  T.tab.set9(sym, T.tab.set9(dyn.other(U32.is_eq(sym, 0)), T.DflTNil{}, 1), 1)

def dyn.first(ss: List<&2, U32>) -> U32:
  match ss:
    case Con{h, t}:
      h
    case Nil{}:
      0

def dyn.lengths.of(leaves: List<&2, DflItem>, +limit: Nat) -> T.DflTab:
  match leaves:
    case Nil{}:
      T.DflTNil{}
    case Con{DflItem{w, ss}, t}:
      match t:
        case Nil{}:
          dyn.one(dyn.first(ss))
        case Con{y, u}:
          +sorted = List.sort(~DflItem, ~dyn.item.le, Con{DflItem{w, ss}, Con{y, u}})
          +n = List.length(&2, DflItem, sorted)
          dyn.count.items(List.take(&2, DflItem, dyn.rounds(Nat.sub(limit, 1n), sorted, sorted), Nat.sub(Nat.add(n, n), 2n)), T.DflTNil{})

# the code lengths (at most limit bits, limit at least 9 here) of an optimal
# complete prefix code for n symbols with these frequencies; all 0 if every
# frequency is 0
def dyn_lengths(+fs: List<&2, U32>, +limit: Nat) -> List<&2, U32>:
  dyn.read(List.length(&2, U32, fs), 0, dyn.lengths.of(dyn.leaves(fs, 0, Nil{}), limit), Nil{})

# The code length sequence, run-length coded (3.2.7)

# a code length symbol and its extra bits (n bits of value v)
type DflCl is Data:
  DflCl{sym: U32, n: Nat, v: U32}

def dyn.inc_if(ok: Bool, n: Nat) -> Nat:
  match ok:
    case True{}:
      1n+n
    case False{}:
      n

# how many of xs, from the start, are v (at most cap); live: those so far
# were
def dyn.run(xs: List<&2, U32>, live: Bool, +v: U32, cap: Nat, n: Nat) -> Nat:
  match xs live:
    case Con{h, t} True{}:
      match cap:
        case 0n:
          n
        case 1n+c:
          +ok = U32.is_eq(h, v)
          dyn.run(t, ok, v, c, dyn.inc_if(ok, n))
    case _ _:
      n

# the run coder's state: the lengths still to code, the previous length
# (16: none yet), the symbols so far (reversed)
type DflRl is Data:
  DflRl{xs: List<&2, U32>, prev: U32, acc: List<&2, DflCl>}

def dyn.rl.zeros(long: Bool, mid: Bool, +r: Nat, xs: List<&2, U32>, acc: List<&2, DflCl>) -> DflRl:
  match long:
    case True{}:
      DflRl{B.drop(r, xs), 0, Con{DflCl{18, 7n, U32.from_nat(Nat.sub(r, 11n))}, acc}}
    case False{}:
      match mid:
        case True{}:
          DflRl{B.drop(r, xs), 0, Con{DflCl{17, 3n, U32.from_nat(Nat.sub(r, 3n))}, acc}}
        case False{}:
          DflRl{B.drop(1n, xs), 0, Con{DflCl{0, 0n, 0}, acc}}

def dyn.rl.rep(ok: Bool, +r: Nat, +h: U32, xs: List<&2, U32>, acc: List<&2, DflCl>) -> DflRl:
  match ok:
    case True{}:
      DflRl{B.drop(r, xs), h, Con{DflCl{16, 2n, U32.from_nat(Nat.sub(r, 3n))}, acc}}
    case False{}:
      DflRl{B.drop(1n, xs), h, Con{DflCl{h, 0n, 0}, acc}}

def dyn.rl.nonzero(again: Bool, +h: U32, +xs: List<&2, U32>, acc: List<&2, DflCl>) -> DflRl:
  match again:
    case True{}:
      +r = dyn.run(xs, True{}, h, 6n, 0n)
      dyn.rl.rep(Nat.is_le(3n, r), r, h, xs, acc)
    case False{}:
      DflRl{B.drop(1n, xs), h, Con{DflCl{h, 0n, 0}, acc}}

def dyn.rl.at(zero: Bool, +h: U32, +prev: U32, +xs: List<&2, U32>, acc: List<&2, DflCl>) -> DflRl:
  match zero:
    case True{}:
      +r = dyn.run(xs, True{}, 0, 138n, 0n)
      dyn.rl.zeros(Nat.is_le(11n, r), Nat.is_le(3n, r), r, xs, acc)
    case False{}:
      dyn.rl.nonzero(U32.is_eq(h, prev), h, xs, acc)

# one symbol (and the lengths it stands for)
def dyn.rl.next(st: DflRl) -> DflRl:
  match st:
    case DflRl{xs, +prev, acc}:
      match xs:
        case Nil{}:
          DflRl{Nil{}, prev, acc}
        case Con{+h, t}:
          dyn.rl.at(U32.is_eq(h, 0), h, prev, Con{h, t}, acc)

def dyn.rl.go(fuel: Nat, st: DflRl) -> List<&2, DflCl>:
  match fuel:
    case 0n:
      match st:
        case DflRl{xs, prev, acc}:
          List.reverse(&2, DflCl, acc)
    case 1n+f:
      dyn.rl.go(f, dyn.rl.next(st))

# a code length sequence, run-length coded
def dyn_rle(+xs: List<&2, U32>) -> List<&2, DflCl>:
  dyn.rl.go(1n+List.length(&2, U32, xs), DflRl{xs, 16, Nil{}})

# The header

# 3.2.7's order of the code length code lengths
def dyn.order() -> List<&2, U32>:
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def dyn.trim.go(xs: List<&2, U32>, lead: Bool, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      +z = Bool.and(lead, U32.is_eq(h, 0))
      dyn.trim.go(t, z, dyn.inc_if(Bool.not(z), n))

# how many of a list's entries are left once its trailing zeros are dropped
def dyn.trim(xs: List<&2, U32>) -> Nat:
  dyn.trim.go(List.reverse(&2, U32, xs), True{}, 0n)

def dyn.clfreq(cls: List<&2, DflCl>, tab: T.DflTab) -> T.DflTab:
  match cls:
    case Nil{}:
      tab
    case Con{DflCl{+sym, n, v}, t}:
      +tb = tab
      dyn.clfreq(t, T.tab.set9(sym, tb, U32.add(T.tab.get9(sym, tb), 1)))

# the lengths of the symbols listed, in that order
def dyn.pick(order: List<&2, U32>, +clens: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match order:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{i, t}:
      dyn.pick(t, clens, Con{H.hf.get(clens, U32.to_nat(i)), acc})

# a dynamic block's header: the counts (HLIT + 257, HDIST + 1, HCLEN + 4),
# the code length code's lengths (in 3.2.7's order, HCLEN + 4 of them), the
# coded code lengths, and the code length code's table
type DflDynHdr is Data:
  DflDynHdr{hlit: Nat, hdist: Nat, hclen: Nat, ordered: List<&2, U32>, cls: List<&2, DflCl>, ctab: T.DflTab}

def dyn.max(+a: Nat, +b: Nat) -> Nat:
  Nat.max(a, b)

# the header for these code lengths (ll: 286 literal/length lengths, dl: 30
# distance lengths)
def dyn_header(+ll: List<&2, U32>, +dl: List<&2, U32>) -> DflDynHdr:
  +hlit = dyn.max(dyn.trim(ll), 257n)
  +hdist = dyn.max(dyn.trim(dl), 1n)
  +cls = dyn_rle(B.append.fast(List.take(&2, U32, ll, hlit), List.take(&2, U32, dl, hdist)))
  +clens = dyn_lengths(dyn.read(19n, 0, dyn.clfreq(cls, T.DflTNil{}), Nil{}), 7n)
  +ordered = dyn.pick(dyn.order(), clens, Nil{})
  +hclen = dyn.max(dyn.trim(ordered), 4n)
  DflDynHdr{hlit, hdist, hclen, List.take(&2, U32, ordered, hclen), cls, H.huff_table(clens)}

def dyn.cls.bits(cls: List<&2, DflCl>, +ctab: T.DflTab, n: Nat) -> Nat:
  match cls:
    case Nil{}:
      n
    case Con{DflCl{+sym, e, v}, t}:
      dyn.cls.bits(t, ctab, Nat.add(n, Nat.add(H.huff_len(ctab, sym), e)))

# how many bits the header takes (the block's 3 header bits included)
def dyn_header_bits(h: DflDynHdr) -> Nat:
  match h:
    case DflDynHdr{hlit, hdist, +hclen, ordered, cls, ctab}:
      dyn.cls.bits(cls, ctab, Nat.add(17n, Nat.mul(3n, hclen)))

def dyn.put.lens(xs: List<&2, U32>, w: K.DflOut) -> K.DflOut:
  match xs:
    case Nil{}:
      w
    case Con{h, t}:
      dyn.put.lens(t, K.out.put(w, h, 3n))

def dyn.put.cls(cls: List<&2, DflCl>, w: K.DflOut, +ctab: T.DflTab) -> K.DflOut:
  match cls:
    case Nil{}:
      w
    case Con{DflCl{+sym, e, v}, t}:
      dyn.put.cls(t, K.out.put(K.out.put(w, H.huff_bits(ctab, sym), H.huff_len(ctab, sym)), v, e), ctab)

# the header written: BFINAL, BTYPE 10, HLIT, HDIST, HCLEN, the code length
# code's lengths, the coded code lengths
def dyn_write_header(w: K.DflOut, final: Bool, h: DflDynHdr) -> K.DflOut:
  match h:
    case DflDynHdr{hlit, hdist, hclen, ordered, cls, +ctab}:
      +w1 = K.out.put(K.out.bit(w, final), 2, 2n)
      +w2 = K.out.put(K.out.put(K.out.put(w1, U32.from_nat(Nat.sub(hlit, 257n)), 5n), U32.from_nat(Nat.sub(hdist, 1n)), 5n), U32.from_nat(Nat.sub(hclen, 4n)), 4n)
      dyn.put.cls(cls, dyn.put.lens(ordered, w2), ctab)
