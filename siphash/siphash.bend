# bend-osdev-siphash: SipHash-c-d, from J.-P. Aumasson and D. J. Bernstein,
# "SipHash: a fast short-input PRF" (2012-09-18), section 2, with the
# double-width (128-bit) output of the reference implementation (siphash.c,
# github.com/veorq/SipHash, CC0).
#
# A 128-bit key k (two little-endian 64-bit words k0, k1) sets four 64-bit
# words v0..v3 to k0, k1, k0, k1 xored with "somepseudorandomlygeneratedbytes"
# (and v1 ^= ee for the wide output). The message is cut into 64-bit
# little-endian words; the last holds the 0 to 7 bytes left over, zero
# bytes, and the message length mod 256 in its top byte. Each word m is
# compressed: v3 ^= m, c SipRounds, v0 ^= m. Then v2 ^= ff (ee for the
# wide output), d SipRounds, and the output v0 ^ v1 ^ v2 ^ v3, written
# little-endian; the wide output follows it with v1 ^= dd, d SipRounds and
# the same xor again.
#
# Streaming: SipHash.start, SipHash.update (pieces in order, any split),
# SipHash.finish. The state takes one byte at a time and compresses each
# word as its eighth byte arrives, so update over a ++ b is update over a,
# then over b (LAWS.bend: siphash_streaming), for every state.
#
# halfsiphash.bend holds HalfSipHash, the 32-bit-word variant, with the
# same parameters and key error.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

# Errors

type SipError is Data:
  SipBadKeyLength{got: Nat}

# Parameters: c compression rounds, d finalization rounds, and whether the
# output is double width (128 bits for SipHash, 64 for HalfSipHash)

type SipParams is Data:
  SipParams{c: Nat, d: Nat, wide: Bool}

# SipHash-2-4, the paper's proposal (Linux's siphash)
def SipParams.sip24() -> SipParams:
  SipParams{2n, 4n, False{}}

# SipHash-1-3 (Linux's hsiphash on 64-bit machines; bend-kit-hash's)
def SipParams.sip13() -> SipParams:
  SipParams{1n, 3n, False{}}

# SipHash-4-8, the paper's conservative proposal
def SipParams.sip48() -> SipParams:
  SipParams{4n, 8n, False{}}

# SipHash-2-4 with the double-width output
def SipParams.sip24_wide() -> SipParams:
  SipParams{2n, 4n, True{}}

def SipParams.c(p: SipParams) -> Nat:
  match p:
    case SipParams{c, d, w}:
      c

def SipParams.d(p: SipParams) -> Nat:
  match p:
    case SipParams{c, d, w}:
      d

def SipParams.wide(p: SipParams) -> Bool:
  match p:
    case SipParams{c, d, w}:
      w

# Keys

type SipKey is Data:
  SipKey{k0: W.W64, k1: W.W64}

def SipKey.of_words(k0: W.W64, k1: W.W64) -> SipKey:
  SipKey{k0, k1}

def SipKey.k0(k: SipKey) -> W.W64:
  match k:
    case SipKey{a, b}:
      a

def SipKey.k1(k: SipKey) -> W.W64:
  match k:
    case SipKey{a, b}:
      b

def sip.word(m: Maybe<&2, W.W64>) -> W.W64:
  match m:
    case Some{v}:
      v
    case None{}:
      W.W64.zero()

def sip.key.pick(ok: Bool, +o: B.Octets) -> Result<&2, &2, SipError, SipKey>:
  match ok:
    case True{}:
      Done{SipKey{sip.word(B.Octets.le64_at(o, 0n)), sip.word(B.Octets.le64_at(o, 8n))}}
    case False{}:
      Fail{SipBadKeyLength{B.Octets.len(o)}}

# the key of 16 bytes: k0 the first 8, little-endian, k1 the next 8
def SipKey.of_octets(+o: B.Octets) -> Result<&2, &2, SipError, SipKey>:
  sip.key.pick(Nat.is_eq(B.Octets.len(o), 16n), o)

# SipRound

type SipV is Data:
  SipV{v0: W.W64, v1: W.W64, v2: W.W64, v3: W.W64}

# rotate left by r, 0 < r < 32, on the halves
def sip.rotl(+x: W.W64, +r: Nat) -> W.W64:
  +h = W.W64.hi(x)
  +l = W.W64.lo(x)
  W.W64.from_parts(U32.or(U32.shln(h, r), U32.shrn(l, Nat.sub(32n, r))), U32.or(U32.shln(l, r), U32.shrn(h, Nat.sub(32n, r))))

# rotate left by 32
def sip.rotl32(+x: W.W64) -> W.W64:
  W.W64.from_parts(W.W64.lo(x), W.W64.hi(x))

# the paper's SipRound, step by step: v0 += v1; v1 <<<= 13; v1 ^= v0;
# v0 <<<= 32; v2 += v3; v3 <<<= 16; v3 ^= v2; v0 += v3; v3 <<<= 21;
# v3 ^= v0; v2 += v1; v1 <<<= 17; v1 ^= v2; v2 <<<= 32
def sip.round(s: SipV) -> SipV:
  match s:
    case SipV{v0, +v1, v2, +v3}:
      +a0 = W.W64.add(v0, v1)
      +a1 = W.W64.xor(sip.rotl(v1, 13n), a0)
      +b0 = sip.rotl32(a0)
      +a2 = W.W64.add(v2, v3)
      +a3 = W.W64.xor(sip.rotl(v3, 16n), a2)
      +c0 = W.W64.add(b0, a3)
      +b3 = W.W64.xor(sip.rotl(a3, 21n), c0)
      +b2 = W.W64.add(a2, a1)
      +b1 = W.W64.xor(sip.rotl(a1, 17n), b2)
      SipV{c0, b1, sip.rotl32(b2), b3}

def sip.rounds(n: Nat, s: SipV) -> SipV:
  match n:
    case 0n:
      s
    case 1n+p:
      sip.rounds(p, sip.round(s))

def sip.xor0(+m: W.W64, s: SipV) -> SipV:
  match s:
    case SipV{v0, v1, v2, v3}:
      SipV{W.W64.xor(v0, m), v1, v2, v3}

# one word compressed: v3 ^= m, c rounds, v0 ^= m
def sip.compress(+c: Nat, s: SipV, +m: W.W64) -> SipV:
  match s:
    case SipV{v0, v1, v2, v3}:
      sip.xor0(m, sip.rounds(c, SipV{v0, v1, v2, W.W64.xor(v3, m)}))

# The state: the parameters, v0..v3, the pending bytes (k of them, k < 8,
# little-endian in lo and then hi), and the length so far mod 2^32

type SipState is Data:
  SipState{prm: SipParams, v: SipV, lo: U32, hi: U32, k: U32, n: U32}

def sip.wide_xor(wide: Bool, +x: W.W64) -> W.W64:
  match wide:
    case True{}:
      W.W64.xor(x, W.W64.from_u32(238))
    case False{}:
      x

def sip.start(+prm: SipParams, +k0: W.W64, +k1: W.W64) -> SipState:
  +v0 = W.W64.xor(k0, W.W64.from_parts(1936682341, 1886610805))
  +v1 = sip.wide_xor(SipParams.wide(prm), W.W64.xor(k1, W.W64.from_parts(1685025377, 1852075885)))
  +v2 = W.W64.xor(k0, W.W64.from_parts(1819895653, 1852142177))
  +v3 = W.W64.xor(k1, W.W64.from_parts(1952801890, 2037671283))
  SipState{prm, SipV{v0, v1, v2, v3}, 0, 0, 0, 0}

# the state before any byte
def SipHash.start(+prm: SipParams, key: SipKey) -> SipState:
  match key:
    case SipKey{k0, k1}:
      sip.start(prm, k0, k1)

# A byte: into the pending word; the eighth compresses it

def sip.full(full: Bool, +prm: SipParams, v: SipV, +lo: U32, +hi: U32, +k: U32, +n: U32) -> SipState:
  match full:
    case True{}:
      SipState{prm, sip.compress(SipParams.c(prm), v, W.W64.from_parts(hi, lo)), 0, 0, 0, n}
    case False{}:
      SipState{prm, v, lo, hi, k, n}

def sip.put(low: Bool, +prm: SipParams, v: SipV, +lo: U32, +hi: U32, +k: U32, +n: U32, +b: U32) -> SipState:
  match low:
    case True{}:
      sip.full(False{}, prm, v, U32.or(lo, U32.shln(b, U32.to_nat(U32.mul(k, 8)))), hi, U32.add(k, 1), U32.add(n, 1))
    case False{}:
      sip.full(U32.is_eq(k, 7), prm, v, lo, U32.or(hi, U32.shln(b, U32.to_nat(U32.mul(U32.sub(k, 4), 8)))), U32.add(k, 1), U32.add(n, 1))

def sip.step(s: SipState, b: U32) -> SipState:
  match s:
    case SipState{prm, v, lo, hi, +k, n}:
      sip.put(U32.is_lt(k, 4), prm, v, lo, hi, k, n, U32.and(255, b))

def sip.go(xs: List<&2, U32>, s: SipState) -> SipState:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      sip.go(t, sip.step(s, h))

# the state after more bytes
def SipHash.update(s: SipState, o: B.Octets) -> SipState:
  sip.go(B.Octets.to_list(o), s)

# the state after one more byte (its low 8 bits)
def SipHash.update_byte(s: SipState, b: U32) -> SipState:
  sip.step(s, b)

# the parameters a state runs with
def SipHash.params(s: SipState) -> SipParams:
  match s:
    case SipState{prm, v, lo, hi, k, n}:
      prm

# Finalization

def sip.out(s: SipV) -> W.W64:
  match s:
    case SipV{v0, v1, v2, v3}:
      W.W64.xor(W.W64.xor(v0, v1), W.W64.xor(v2, v3))

def sip.xor1(+x: U32, s: SipV) -> SipV:
  match s:
    case SipV{v0, v1, v2, v3}:
      SipV{v0, W.W64.xor(v1, W.W64.from_u32(x)), v2, v3}

def sip.xor2(+x: U32, s: SipV) -> SipV:
  match s:
    case SipV{v0, v1, v2, v3}:
      SipV{v0, v1, W.W64.xor(v2, W.W64.from_u32(x)), v3}

def sip.second(+d: Nat, +s: SipV) -> B.Octets:
  B.Octets.append(B.Octets.le64(sip.out(s)), B.Octets.le64(sip.out(sip.rounds(d, sip.xor1(221, s)))))

def sip.fin(wide: Bool, +d: Nat, s: SipV) -> B.Octets:
  match wide:
    case False{}:
      B.Octets.le64(sip.out(sip.rounds(d, sip.xor2(255, s))))
    case True{}:
      sip.second(d, sip.rounds(d, sip.xor2(238, s)))

def sip.finish(prm: SipParams, v: SipV, +last: W.W64) -> B.Octets:
  match prm:
    case SipParams{+c, +d, wide}:
      sip.fin(wide, d, sip.compress(c, v, last))

# the output of the bytes so far: 8 bytes, or 16 when wide
def SipHash.finish(s: SipState) -> B.Octets:
  match s:
    case SipState{prm, v, lo, hi, k, n}:
      sip.finish(prm, v, W.W64.from_parts(U32.or(hi, U32.shln(U32.and(255, n), 24n)), lo))

# the output length of a parameter set: 8 bytes, or 16 when wide
def SipParams.out_len(p: SipParams) -> Nat:
  match p:
    case SipParams{c, d, w}:
      match w:
        case True{}:
          16n
        case False{}:
          8n

# One call

def SipHash.hash(+prm: SipParams, key: SipKey, o: B.Octets) -> B.Octets:
  SipHash.finish(SipHash.update(SipHash.start(prm, key), o))

# SipHash-2-4 and SipHash-1-3, 64-bit output
def siphash24(key: SipKey, o: B.Octets) -> B.Octets:
  SipHash.hash(SipParams.sip24(), key, o)

def siphash13(key: SipKey, o: B.Octets) -> B.Octets:
  SipHash.hash(SipParams.sip13(), key, o)

# from a raw 16-byte key (SipBadKeyLength otherwise)
def SipHash.mac(+prm: SipParams, key: B.Octets, o: B.Octets) -> Result<&2, &2, SipError, B.Octets>:
  Result.map(&2, &2, SipError, SipKey, B.Octets, k => SipHash.hash(prm, k, o), SipKey.of_octets(key))
