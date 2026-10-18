# bend-osdev-crc, the table-driven fast path: one table lookup per byte
# instead of eight bit steps (about 3x faster for CRC32C on native builds).
#
# The bitwise engines in crc.bend are the reference; these must give the same
# results, which the vectors in LAWS.bend and ref/run.sh check (a law for
# every input is out of reach: it would need lemmas about Array's internals).
# The table is an Array, so it is built once per call and threaded through.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./crc.bend as C

# 32-bit tables: entry i is eight bit steps of the register i (reflected), or
# of i placed in the register's top byte (most significant bit first)

def t32.fill.r(n: Nat, a: Array<U32>, +poly: U32, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      t32.fill.r(p, Array.set(U32, a, i, C.r32.bits(8n, poly, i)), poly, U32.add(i, 1))

def t32.fill.n(n: Nat, a: Array<U32>, +poly: U32, +shift: Nat, +topbit: U32, +mask: U32, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      t32.fill.n(p, Array.set(U32, a, i, C.n32.bits(8n, poly, topbit, mask, U32.shln(i, shift))), poly, shift, topbit, mask, U32.add(i, 1))

def t32.r.fin(r: Array<U32> & U32, +c: U32) -> Array<U32> & U32:
  (t, v) = r
  (t, U32.xor(U32.shrn(c, 8n), v))

# reflected: c = (c >> 8) ^ T[(c ^ b) & 255]
def t32.r.raw(xs: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & U32:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      (tab, +c) = r
      t32.r.raw(t, t32.r.fin(Array.get(U32, tab, U32.and(U32.xor(c, h), 255)), c))

def t32.n.fin(r: Array<U32> & U32, +c: U32, +mask: U32) -> Array<U32> & U32:
  (t, v) = r
  (t, U32.and(U32.xor(U32.shln(c, 8n), v), mask))

# most significant bit first: c = ((c << 8) ^ T[((c >> (w - 8)) ^ b) & 255]) & mask
def t32.n.raw(xs: List<&2, U32>, +shift: Nat, +mask: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      (tab, +c) = r
      t32.n.raw(t, shift, mask, t32.n.fin(Array.get(U32, tab, U32.and(U32.xor(U32.shrn(c, shift), h), 255)), c, mask))

def t32.snd(r: Array<U32> & U32) -> U32:
  (t, v) = r
  v

# most significant bit first: a table for widths of 8 and up; below 8 the
# input goes in a bit at a time, so the bitwise engine serves
def t32.update.msb(small: Bool, +width: Nat, +poly: U32, c: U32, xs: List<&2, U32>) -> U32:
  match small:
    case True{}:
      C.s32.raw(xs, poly, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), c)
    case False{}:
      +shift = Nat.sub(width, 8n)
      +topbit = U32.shln(1, Nat.sub(width, 1n))
      +mask = U32.sub(U32.shln(1, width), 1)
      t32.snd(t32.n.raw(xs, shift, mask, (t32.fill.n(256n, [0 : U32*256n], poly, shift, topbit, mask, 0), c)))

def t32.update.go(reflected: Bool, +width: Nat, +poly: U32, c: U32, xs: List<&2, U32>) -> U32:
  match reflected:
    case True{}:
      +rp = C.reflect32(poly, width)
      t32.snd(t32.r.raw(xs, (t32.fill.r(256n, [0 : U32*256n], rp, 0), c)))
    case False{}:
      t32.update.msb(Nat.is_lt(width, 8n), width, poly, c, xs)

# the same as Crc32Spec.update, table-driven
def Crc32Spec.update_fast(spec: C.Crc32Spec, c: U32, o: B.Octets) -> U32:
  match spec:
    case C.Crc32Spec{+width, poly, init, reflected, xorout}:
      t32.update.go(reflected, width, poly, c, B.Octets.to_list(o))

def Crc32Spec.compute_fast(+spec: C.Crc32Spec, o: B.Octets) -> U32:
  C.Crc32Spec.finish(spec, Crc32Spec.update_fast(spec, C.Crc32Spec.start(spec), o))

# 64-bit tables

def t64.fill.r(n: Nat, a: Array<W.W64>, +poly: W.W64, +i: U32) -> Array<W.W64>:
  match n:
    case 0n:
      a
    case 1n+p:
      t64.fill.r(p, Array.set(W.W64, a, i, C.r64.bits(8n, poly, W.W64.from_u32(i))), poly, U32.add(i, 1))

def t64.fill.n(n: Nat, a: Array<W.W64>, +poly: W.W64, +i: U32) -> Array<W.W64>:
  match n:
    case 0n:
      a
    case 1n+p:
      t64.fill.n(p, Array.set(W.W64, a, i, C.n64.bits(8n, poly, W.W64.from_parts(U32.shln(i, 24n), 0))), poly, U32.add(i, 1))

def t64.r.fin(r: Array<W.W64> & W.W64, +c: W.W64) -> Array<W.W64> & W.W64:
  (t, v) = r
  (t, W.W64.xor(W.W64.shr(c, 8n), v))

def t64.r.raw(xs: List<&2, U32>, r: Array<W.W64> & W.W64) -> Array<W.W64> & W.W64:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      (tab, +c) = r
      t64.r.raw(t, t64.r.fin(Array.get(W.W64, tab, U32.and(U32.xor(W.W64.lo(c), h), 255)), c))

def t64.n.fin(r: Array<W.W64> & W.W64, +c: W.W64) -> Array<W.W64> & W.W64:
  (t, v) = r
  (t, W.W64.xor(W.W64.shl(c, 8n), v))

def t64.n.raw(xs: List<&2, U32>, r: Array<W.W64> & W.W64) -> Array<W.W64> & W.W64:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      (tab, +c) = r
      t64.n.raw(t, t64.n.fin(Array.get(W.W64, tab, U32.and(U32.xor(U32.shrn(W.W64.hi(c), 24n), h), 255)), c))

def t64.snd(r: Array<W.W64> & W.W64) -> W.W64:
  (t, v) = r
  v

def t64.update.go(reflected: Bool, poly: W.W64, c: W.W64, xs: List<&2, U32>) -> W.W64:
  match reflected:
    case True{}:
      t64.snd(t64.r.raw(xs, (t64.fill.r(256n, Array.new(W.W64, 8n, W.W64.zero()), C.reflect64(poly), 0), c)))
    case False{}:
      t64.snd(t64.n.raw(xs, (t64.fill.n(256n, Array.new(W.W64, 8n, W.W64.zero()), poly, 0), c)))

def Crc64Spec.update_fast(spec: C.Crc64Spec, c: W.W64, o: B.Octets) -> W.W64:
  match spec:
    case C.Crc64Spec{poly, init, reflected, xorout}:
      t64.update.go(reflected, poly, c, B.Octets.to_list(o))

def Crc64Spec.compute_fast(+spec: C.Crc64Spec, o: B.Octets) -> W.W64:
  C.Crc64Spec.finish(spec, Crc64Spec.update_fast(spec, C.Crc64Spec.start(spec), o))
