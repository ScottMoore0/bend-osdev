# bend-osdev-zstd, XXH64: the 64-bit xxHash, from its specification
# (xxhash_spec.md, "xxHash fast digest algorithm", version 0.1.1, by Yann
# Collet). Zstandard frames end with the low 32 bits of XXH64 (seed 0) of
# their content (RFC 8878, section 3.1.1).
#
# Usable on its own: ZstdXxh64.hash(seed, o) in one call, or start / update / digest
# for data that arrives in pieces (the state keeps at most 31 bytes that do
# not yet fill a 32-byte stripe).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

# The state: the four accumulators, the seed, the bytes so far (a count),
# and the bytes of the stripe being filled (reversed, at most 31) and their
# number
type ZstdXxh64 is Data:
  ZstdXxh64{v1: W.W64, v2: W.W64, v3: W.W64, v4: W.W64, seed: W.W64, total: Nat, buf: List<&2, U32>, nbuf: Nat}

# The five primes
def xxh.p1() -> W.W64:
  W.W64.from_parts(2654435761, 2246822535)

def xxh.p2() -> W.W64:
  W.W64.from_parts(3266489917, 668265295)

def xxh.p3() -> W.W64:
  W.W64.from_parts(374761393, 2654435833)

def xxh.p4() -> W.W64:
  W.W64.from_parts(2246822519, 3266489955)

def xxh.p5() -> W.W64:
  W.W64.from_parts(668265263, 374761413)

# rotate left by r bits (0 < r < 64)
def xxh.rotl(+x: W.W64, +r: Nat) -> W.W64:
  W.W64.or(W.W64.shl(x, r), W.W64.shr(x, Nat.sub(64n, r)))

# round(acc, lane) = rotl(acc + lane * P2, 31) * P1
def xxh.round(acc: W.W64, lane: W.W64) -> W.W64:
  W.W64.mul(xxh.rotl(W.W64.add(acc, W.W64.mul(lane, xxh.p2())), 31n), xxh.p1())

def xxh.merge(acc: W.W64, v: W.W64) -> W.W64:
  W.W64.add(W.W64.mul(W.W64.xor(acc, xxh.round(W.W64.zero(), v)), xxh.p1()), xxh.p4())

# a little-endian 32-bit word from four bytes
def xxh.le32(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(B.byte(a), U32.shln(B.byte(b), 8n)), U32.or(U32.shln(B.byte(c), 16n), U32.shln(B.byte(d), 24n)))

# Stripes: 32 bytes, four lanes of 8, one per accumulator

type ZsXLanes is Data:
  ZsXLanes{v1: W.W64, v2: W.W64, v3: W.W64, v4: W.W64}

def xxh.lane(a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32) -> W.W64:
  W.W64.from_parts(xxh.le32(e, f, g, h), xxh.le32(a, b, c, d))

# the accumulators after one stripe xs (32 bytes, in order)
def xxh.stripe(xs: List<&2, U32>, v1: W.W64, v2: W.W64, v3: W.W64, v4: W.W64) -> ZsXLanes:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, Con{d0, Con{d1, Con{d2, Con{d3, Con{d4, Con{d5, Con{d6, Con{d7, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ZsXLanes{xxh.round(v1, xxh.lane(a0, a1, a2, a3, a4, a5, a6, a7)), xxh.round(v2, xxh.lane(b0, b1, b2, b3, b4, b5, b6, b7)), xxh.round(v3, xxh.lane(c0, c1, c2, c3, c4, c5, c6, c7)), xxh.round(v4, xxh.lane(d0, d1, d2, d3, d4, d5, d6, d7))}
    case _:
      ZsXLanes{v1, v2, v3, v4}

def xxh.full(lanes: ZsXLanes, +seed: W.W64, +total: Nat) -> ZstdXxh64:
  match lanes:
    case ZsXLanes{v1, v2, v3, v4}:
      ZstdXxh64{v1, v2, v3, v4, seed, total, Nil{}, 0n}

def xxh.push(full: Bool, st: ZstdXxh64) -> ZstdXxh64:
  match full:
    case True{}:
      match st:
        case ZstdXxh64{v1, v2, v3, v4, +seed, +total, buf, nbuf}:
          xxh.full(xxh.stripe(B.rev(buf), v1, v2, v3, v4), seed, total)
    case False{}:
      st

# the state after one more byte
def xxh.byte(st: ZstdXxh64, b: U32) -> ZstdXxh64:
  match st:
    case ZstdXxh64{v1, v2, v3, v4, seed, total, buf, nbuf}:
      +n = Nat.add(nbuf, 1n)
      xxh.push(Nat.is_eq(n, 32n), ZstdXxh64{v1, v2, v3, v4, seed, 1n+total, Con{B.byte(b), buf}, n})

def xxh.bytes(xs: List<&2, U32>, st: ZstdXxh64) -> ZstdXxh64:
  match xs:
    case Nil{}:
      st
    case Con{h, t}:
      xxh.bytes(t, xxh.byte(st, h))

# The digest: the accumulators merged (32 bytes or more) or seed + P5, plus
# the length, then the bytes left over: lanes of 8, a word of 4, single bytes

def xxh.tail(xs: List<&2, U32>, h: W.W64) -> W.W64:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{k, t}}}}}}}}:
      xxh.tail(t, W.W64.add(W.W64.mul(xxh.rotl(W.W64.xor(h, xxh.round(W.W64.zero(), xxh.lane(a, b, c, d, e, f, g, k))), 27n), xxh.p1()), xxh.p4()))
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      xxh.tail(t, W.W64.add(W.W64.mul(xxh.rotl(W.W64.xor(h, W.W64.mul(W.W64.from_u32(xxh.le32(a, b, c, d)), xxh.p1())), 23n), xxh.p2()), xxh.p3()))
    case Con{a, t}:
      xxh.tail(t, W.W64.mul(xxh.rotl(W.W64.xor(h, W.W64.mul(W.W64.from_u32(B.byte(a)), xxh.p5())), 11n), xxh.p1()))
    case Nil{}:
      h

def xxh.avalanche(+h: W.W64) -> W.W64:
  +h1 = W.W64.mul(W.W64.xor(h, W.W64.shr(h, 33n)), xxh.p2())
  +h2 = W.W64.mul(W.W64.xor(h1, W.W64.shr(h1, 29n)), xxh.p3())
  W.W64.xor(h2, W.W64.shr(h2, 32n))

def xxh.start_acc(big: Bool, +v1: W.W64, +v2: W.W64, +v3: W.W64, +v4: W.W64, seed: W.W64) -> W.W64:
  match big:
    case True{}:
      +h = W.W64.add(W.W64.add(xxh.rotl(v1, 1n), xxh.rotl(v2, 7n)), W.W64.add(xxh.rotl(v3, 12n), xxh.rotl(v4, 18n)))
      xxh.merge(xxh.merge(xxh.merge(xxh.merge(h, v1), v2), v3), v4)
    case False{}:
      W.W64.add(seed, xxh.p5())

# The public interface

# the state before any byte
def ZstdXxh64.start(+seed: W.W64) -> ZstdXxh64:
  ZstdXxh64{W.W64.add(W.W64.add(seed, xxh.p1()), xxh.p2()), W.W64.add(seed, xxh.p2()), seed, W.W64.sub(seed, xxh.p1()), seed, 0n, Nil{}, 0n}

# the state after the bytes o
def ZstdXxh64.update(st: ZstdXxh64, o: B.Octets) -> ZstdXxh64:
  xxh.bytes(B.Octets.to_list(o), st)

# the same, for one byte (the low 8 bits of b)
def ZstdXxh64.update_byte(st: ZstdXxh64, b: U32) -> ZstdXxh64:
  xxh.byte(st, b)

# the hash of the bytes so far
def ZstdXxh64.digest(st: ZstdXxh64) -> W.W64:
  match st:
    case ZstdXxh64{v1, v2, v3, v4, seed, +total, buf, nbuf}:
      +h = W.W64.add(xxh.start_acc(Nat.is_le(32n, total), v1, v2, v3, v4, seed), W.W64.from_nat(total))
      xxh.avalanche(xxh.tail(B.rev(buf), h))

# XXH64 of o with this seed, in one call
def ZstdXxh64.hash(+seed: W.W64, o: B.Octets) -> W.W64:
  ZstdXxh64.digest(ZstdXxh64.update(ZstdXxh64.start(seed), o))
