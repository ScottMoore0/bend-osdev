# bend-osdev-lzo, LZO1X compression, written from the same documentation as
# decode.bend (Documentation/staging/lzo.rst); no LZO source code was read.
#
# lzo1x_literals is the simplest valid stream: one run of literals, then the
# end marker. lzo1x_compress is an LZO1X-1-style compressor: a greedy LZ77
# matcher with a single-entry hash table keyed by the next four bytes. It
# writes M2 (distances up to 2048, lengths 3 to 8), M3 (up to 16384) and M4
# (up to 49151) matches, carries up to 3 literals after a match in its S
# bits, and writes longer literal runs as their own instruction.
#
# lzo1x_compress checks its own output: it decodes it and, should that not
# give the input back, answers lzo1x_literals instead. So a law can say, for
# every input, that what it writes decodes to the input.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./decode.bend as D

# Length bytes: a zero for each 255, then the rest (1 to 255)

# the last length byte: 255 - d (d counts down the room left in a byte)
def ext.last(d: Nat) -> U32:
  U32.from_nat(Nat.sub(255n, d))

# the length bytes for (255 - d) + r (the reference form, which the proofs
# follow): r = 0 ends with 255 - d; past a full byte (d = 0), a zero
def ext.ref(r: Nat, d: Nat) -> List<&2, U32>:
  match r:
    case 0n:
      [ext.last(d)]
    case 1n+p:
      match d:
        case 0n:
          Con{0, ext.ref(p, 254n)}
        case 1n+q:
          ext.ref(p, q)

# k zero bytes in front of acc
def ext.zeros(k: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+j:
      ext.zeros(j, Con{0, acc})

# ext.ref, tail-recursive: count the zeros (k), then lay them down in front
# of the last byte. PROOF.bend's ext_fast proves the two equal.
def ext.go(r: Nat, d: Nat, k: Nat) -> List<&2, U32>:
  match r:
    case 0n:
      ext.zeros(k, [ext.last(d)])
    case 1n+p:
      match d:
        case 0n:
          ext.go(p, 254n, 1n+k)
        case 1n+q:
          ext.go(p, q, k)

# the length bytes for v (v >= 1; nothing for 0)
def ext.bytes(v: Nat) -> List<&2, U32>:
  match v:
    case 0n:
      Nil{}
    case 1n+p:
      ext.go(p, 254n, 0n)

# The literal-only stream. lit.hK(n) is the instruction for K + n literals
# at the start of a stream: none for 0; the first byte 17 + K for 1 to 3;
# 0000LLLL with L = K - 3 for 4 to 18; 0000 0000 and length bytes beyond.

def lit.h18(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [15]
    case 1n+p:
      Con{0, ext.go(p, 254n, 0n)}

def lit.h17(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [14]
    case 1n+p:
      lit.h18(p)

def lit.h16(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [13]
    case 1n+p:
      lit.h17(p)

def lit.h15(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [12]
    case 1n+p:
      lit.h16(p)

def lit.h14(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [11]
    case 1n+p:
      lit.h15(p)

def lit.h13(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [10]
    case 1n+p:
      lit.h14(p)

def lit.h12(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [9]
    case 1n+p:
      lit.h13(p)

def lit.h11(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [8]
    case 1n+p:
      lit.h12(p)

def lit.h10(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [7]
    case 1n+p:
      lit.h11(p)

def lit.h9(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [6]
    case 1n+p:
      lit.h10(p)

def lit.h8(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [5]
    case 1n+p:
      lit.h9(p)

def lit.h7(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [4]
    case 1n+p:
      lit.h8(p)

def lit.h6(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [3]
    case 1n+p:
      lit.h7(p)

def lit.h5(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [2]
    case 1n+p:
      lit.h6(p)

def lit.h4(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [1]
    case 1n+p:
      lit.h5(p)

def lit.h3(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [20]
    case 1n+p:
      lit.h4(p)

def lit.h2(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [19]
    case 1n+p:
      lit.h3(p)

def lit.h1(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [18]
    case 1n+p:
      lit.h2(p)

def lit.h0(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      lit.h1(p)

# the end marker: M4 with distance 16384
def lzo1x_end() -> B.Octets:
  B.Octets.of_list([17, 0, 0])

# the stream holding the bytes o as literals
def lzo1x_literals(+o: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.of_list(lit.h0(B.Octets.len(o))), B.Octets.append(o, lzo1x_end()))

# Instructions, pushed onto a reversed output

# a match of len bytes (3 or more) at distance o + 1, followed by s literals
# (0 to 3): M2 when it fits, else M3, else M4
def enc.m2(+len: Nat, +o: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  +b = U32.or(U32.shln(U32.from_nat(Nat.sub(len, 1n)), 5n), U32.or(U32.shln(U32.and(o, 7), 2n), s))
  Con{U32.shrn(o, 3n), Con{b, out}}

# the two distance bytes of M3 and M4: D (14 bits) and S, little-endian
def enc.d16(+d: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  Con{U32.shrn(d, 6n), Con{U32.or(U32.shln(U32.and(d, 63), 2n), s), out}}

# an opcode with a length field of m bits (all ones: mask), or 0 and length
# bytes for longer matches; top: the length the field holds at most
def enc.len.pick(fits: Bool, +op: U32, +len: Nat, +top: Nat, out: List<&2, U32>) -> List<&2, U32>:
  match fits:
    case True{}:
      Con{U32.or(op, U32.from_nat(Nat.sub(len, 2n))), out}
    case False{}:
      B.rev_onto(ext.bytes(Nat.sub(len, top)), Con{op, out})

def enc.m3(+len: Nat, +o: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  enc.d16(o, s, enc.len.pick(Nat.is_le(len, 33n), 32, len, 33n, out))

def enc.m4(+len: Nat, +o: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  +t = U32.sub(o, 16383)
  enc.d16(U32.and(t, 16383), s, enc.len.pick(Nat.is_le(len, 9n), U32.or(16, U32.shln(U32.shrn(t, 14n), 3n)), len, 9n, out))

def enc.match.far(near: Bool, +len: Nat, +o: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  match near:
    case True{}:
      enc.m3(len, o, s, out)
    case False{}:
      enc.m4(len, o, s, out)

def enc.match.pick(m2: Bool, +len: Nat, +o: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  match m2:
    case True{}:
      enc.m2(len, o, s, out)
    case False{}:
      enc.match.far(U32.is_lt(o, 16384), len, o, s, out)

def enc.match(+len: Nat, +o: U32, +s: U32, out: List<&2, U32>) -> List<&2, U32>:
  enc.match.pick(Bool.and(U32.is_lt(o, 2048), Nat.is_le(len, 8n)), len, o, s, out)

# a literal run of k bytes (4 or more) after a match: 0000LLLL
def enc.run.pick(short: Bool, +k: Nat, out: List<&2, U32>) -> List<&2, U32>:
  match short:
    case True{}:
      Con{U32.from_nat(Nat.sub(k, 3n)), out}
    case False{}:
      B.rev_onto(ext.bytes(Nat.sub(k, 18n)), Con{0, out})

def enc.run(+k: Nat, out: List<&2, U32>) -> List<&2, U32>:
  enc.run.pick(Nat.is_le(k, 18n), k, out)

# the first literal run of a stream: the first byte 17 + k up to 238
# literals, else 0000 0000 and length bytes
def enc.first.pick(short: Bool, +k: Nat, out: List<&2, U32>) -> List<&2, U32>:
  match short:
    case True{}:
      Con{U32.from_nat(Nat.add(17n, k)), out}
    case False{}:
      B.rev_onto(ext.bytes(Nat.sub(k, 18n)), Con{0, out})

def enc.first(k: Nat, +lits: List<&2, U32>, out: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      out
    case 1n+(+j):
      B.rev_onto(lits, enc.first.pick(Nat.is_le(j, 237n), 1n+j, out))

# the match before these literals (k of them): up to 3 ride in its S bits,
# more take a literal run of their own
def enc.after(few: Bool, +k: Nat, +lits: List<&2, U32>, +len: Nat, +o: U32, out: List<&2, U32>) -> List<&2, U32>:
  match few:
    case True{}:
      B.rev_onto(lits, enc.match(len, o, U32.from_nat(k), out))
    case False{}:
      B.rev_onto(lits, enc.run(k, enc.match(len, o, 0, out)))

# the last match, not yet written: its S bits wait for the literals after it
type LzoPend is Data:
  LzoPendNone{}
  LzoPendMatch{len: Nat, o: U32}

def enc.flush.at(p: LzoPend, +k: Nat, +lits: List<&2, U32>, out: List<&2, U32>) -> List<&2, U32>:
  match p:
    case LzoPendNone{}:
      enc.first(k, lits, out)
    case LzoPendMatch{len, o}:
      enc.after(Nat.is_le(k, 3n), k, lits, len, o, out)

# the pending match and the literals since (in order)
def enc.flush(p: LzoPend, +lits: List<&2, U32>, out: List<&2, U32>) -> List<&2, U32>:
  enc.flush.at(p, B.len.fast(lits), lits, out)

# The matcher

# hash_bits: the hash table holds 2^hash_bits positions; max_dist: the
# farthest a match may reach back (49151 at most, LZO1X's largest distance)
type LzoCompressOptions is Data:
  LzoCompressOptions{hash_bits: Nat, max_dist: U32}

def LzoCompressOptions.default() -> LzoCompressOptions:
  LzoCompressOptions{14n, 49151}

# a table slot: a position + 1 (0: empty) and the input from there on
type LzoCand is Data:
  LzoCand{pos: U32, suf: List<&2, U32>}

# the matcher's state: the table; the input from position i on, which ends
# at end; the farthest distance; the hash shift; the literals since the last
# match (reversed); the match before them; the output so far (reversed)
type LzoEnc is Type:
  LzoEncGo{tab: Array<LzoCand>, cur: List<&2, U32>, i: U32, end: U32, far: U32, sh: Nat, lits: List<&2, U32>, pend: LzoPend, out: List<&2, U32>}
  LzoEncDone{out: List<&2, U32>}

# the next four bytes, hashed to the table's bits
def enc.hash(xs: List<&2, U32>, sh: Nat) -> U32:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      U32.shrn(U32.mul(U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))), 2654435761), sh)
    case _:
      0

def enc.inc_if(ok: Bool, n: Nat) -> Nat:
  match ok:
    case True{}:
      1n+n
    case False{}:
      n

# how many bytes a and b share from their starts, k at most; live: the bytes
# so far agree
def enc.common(a: List<&2, U32>, live: Bool, b: List<&2, U32>, +k: U32, n: Nat) -> Nat:
  match a live:
    case Con{x, s} True{}:
      match b:
        case Nil{}:
          n
        case Con{y, t}:
          +ok = Bool.and(U32.is_lt(0, k), U32.is_eq(x, y))
          enc.common(s, ok, t, U32.sub(k, 1), enc.inc_if(ok, n))
    case _ _:
      n

# the end: the pending match, the last literals, the end marker
def enc.done(p: LzoPend, lits: List<&2, U32>, cur: List<&2, U32>, out: List<&2, U32>) -> LzoEnc:
  LzoEncDone{Con{0, Con{0, Con{17, enc.flush(p, B.rev_onto(lits, cur), out)}}}}

# a match of ml bytes (4 or more), or one more literal
def enc.emit(ok: Bool, tab: Array<LzoCand>, +cur: List<&2, U32>, +i: U32, +ml: Nat, +o: U32, end: U32, far: U32, sh: Nat, +lits: List<&2, U32>, p: LzoPend, out: List<&2, U32>) -> LzoEnc:
  match ok:
    case True{}:
      LzoEncGo{tab, B.drop(ml, cur), U32.add(i, U32.from_nat(ml)), end, far, sh, Nil{}, LzoPendMatch{ml, o}, enc.flush(p, B.rev(lits), out)}
    case False{}:
      match cur:
        case Nil{}:
          enc.done(p, lits, Nil{}, out)
        case Con{b, t}:
          LzoEncGo{tab, t, U32.add(i, 1), end, far, sh, Con{b, lits}, p, out}

def enc.found(valid: Bool, +suf: List<&2, U32>, +cur: List<&2, U32>, +k: U32) -> Nat:
  match valid:
    case True{}:
      enc.common(suf, True{}, cur, k, 0n)
    case False{}:
      0n

# the slot for this position: its old entry is the candidate, which must be
# far bytes back at most and agree on 4 bytes or more
def enc.cand(r: Array<LzoCand> & LzoCand, +h: U32, +cur: List<&2, U32>, +i: U32, +end: U32, +far: U32, sh: Nat, lits: List<&2, U32>, p: LzoPend, out: List<&2, U32>) -> LzoEnc:
  (tab, c) = r
  match c:
    case LzoCand{+pos, suf}:
      +off = U32.sub(U32.add(i, 1), pos)
      +ml = enc.found(Bool.and(U32.is_lt(0, pos), U32.is_le(off, far)), suf, cur, U32.sub(end, i))
      enc.emit(Nat.is_le(4n, ml), Array.set(LzoCand, tab, h, LzoCand{U32.add(i, 1), cur}), cur, i, ml, U32.sub(off, 1), end, far, sh, lits, p, out)

def enc.step.at(go: Bool, tab: Array<LzoCand>, +cur: List<&2, U32>, +i: U32, end: U32, far: U32, +sh: Nat, lits: List<&2, U32>, p: LzoPend, out: List<&2, U32>) -> LzoEnc:
  match go:
    case True{}:
      +h = enc.hash(cur, sh)
      enc.cand(Array.get(LzoCand, tab, h), h, cur, i, end, far, sh, lits, p, out)
    case False{}:
      enc.done(p, lits, cur, out)

# one position: with fewer than 4 bytes left, the rest are literals
def enc.step(tab: Array<LzoCand>, cur: List<&2, U32>, +i: U32, +end: U32, far: U32, sh: Nat, lits: List<&2, U32>, p: LzoPend, out: List<&2, U32>) -> LzoEnc:
  enc.step.at(U32.is_le(U32.add(i, 4), end), tab, cur, i, end, far, sh, lits, p, out)

# every step moves on a byte or more, so fuel of the input's length + 1
# reaches the end
def enc.loop(fuel: Nat, st: LzoEnc) -> List<&2, U32>:
  match fuel:
    case 0n:
      match st:
        case LzoEncGo{tab, cur, i, end, far, sh, lits, p, out}:
          B.rev(Con{0, Con{0, Con{17, enc.flush(p, B.rev_onto(lits, cur), out)}}})
        case LzoEncDone{out}:
          B.rev(out)
    case 1n+f:
      match st:
        case LzoEncGo{tab, cur, i, end, far, sh, lits, p, out}:
          enc.loop(f, enc.step(tab, cur, i, end, far, sh, lits, p, out))
        case LzoEncDone{out}:
          B.rev(out)

def enc.cap.pick(ok: Bool, a: U32, b: U32) -> U32:
  match ok:
    case True{}:
      a
    case False{}:
      b

# a distance limit of at most 49151
def enc.cap(+far: U32) -> U32:
  enc.cap.pick(U32.is_le(far, 49151), far, 49151)

# the matcher's stream for xs
def enc.stream(opts: LzoCompressOptions, +xs: List<&2, U32>) -> List<&2, U32>:
  match opts:
    case LzoCompressOptions{+bits, far}:
      +n = B.len.fast(xs)
      enc.loop(1n+n, LzoEncGo{Array.new(LzoCand, bits, LzoCand{0, Nil{}}), xs, 0, U32.from_nat(n), enc.cap(far), Nat.sub(32n, bits), Nil{}, LzoPendNone{}, Nil{}})

# Checking a stream: decode it and compare

def enc.weq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          Bool.and(Bool.not(Bool.xor(x, y)), enc.weq(p, s, t))

def enc.u32_eq(a: U32, b: U32) -> Bool:
  match a b:
    case U32{x} U32{y}:
      enc.weq(32n, x, y)

# the same bytes, in the same order; live: the bytes so far agree (a tail
# call, so it runs on lists of any length)
def enc.same.go(xs: List<&2, U32>, ys: List<&2, U32>, live: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      live
    case Con{a, s} Con{b, t}:
      enc.same.go(s, t, Bool.and(live, enc.u32_eq(a, b)))
    case _ _:
      False{}

def enc.same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  enc.same.go(xs, ys, True{})

def enc.keep(ok: Bool, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match ok:
    case True{}:
      c
    case False{}:
      lzo1x_literals(o)

# the stream c if it decodes to o, else the literal-only stream. r is the
# decoder's own answer (its output list), compared with o as it comes out
def enc.check(r: Result<&2, &2, E.LzoError, D.LzoOut>, +c: B.Octets, +o: B.Octets) -> B.Octets:
  match r:
    case Fail{e}:
      lzo1x_literals(o)
    case Done{D.LzoOut{acc, room}}:
      enc.keep(enc.same(B.rev(acc), B.Octets.to_list(o)), c, o)

# The public interface

# the matcher's stream for o, unchecked
def lzo1x_compress_unchecked(opts: LzoCompressOptions, o: B.Octets) -> B.Octets:
  B.Octets.of_list(enc.stream(opts, B.Octets.to_list(o)))

# a stream for o: the matcher's, checked by decoding it
def lzo1x_compress_with(opts: LzoCompressOptions, +o: B.Octets) -> B.Octets:
  +c = lzo1x_compress_unchecked(opts, o)
  enc.check(D.dec.run_list(B.Octets.to_list(c), B.Octets.len(o)), c, o)

def lzo1x_compress(+o: B.Octets) -> B.Octets:
  lzo1x_compress_with(LzoCompressOptions.default(), o)

# The same on lists, for the lzop writer (no conversions to and from Octets)

def enc.lits(+xs: List<&2, U32>) -> List<&2, U32>:
  B.append.fast(lit.h0(B.len.fast(xs)), B.append.fast(xs, [17, 0, 0]))

def enc.pick(ok: Bool, +c: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      c
    case False{}:
      enc.lits(xs)

def enc.checked.at(r: Result<&2, &2, E.LzoError, D.LzoOut>, +c: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Fail{e}:
      enc.lits(xs)
    case Done{D.LzoOut{acc, room}}:
      enc.pick(enc.same(B.rev(acc), xs), c, xs)

def enc.checked(opts: LzoCompressOptions, +xs: List<&2, U32>) -> List<&2, U32>:
  +c = enc.stream(opts, xs)
  enc.checked.at(D.dec.run_list(c, B.len.fast(xs)), c, xs)
