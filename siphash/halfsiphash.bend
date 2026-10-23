# bend-osdev-siphash: HalfSipHash-c-d, SipHash on 32-bit words, as the
# reference implementation defines it (halfsiphash.c,
# github.com/veorq/SipHash, CC0; the SipHash paper, J.-P. Aumasson and
# D. J. Bernstein, 2012-09-18, defines SipHash on 64-bit words).
#
# A 64-bit key k (two little-endian 32-bit words k0, k1) sets v0 = k0,
# v1 = k1 (^ ee for the wide output), v2 = k0 ^ 6c796765,
# v3 = k1 ^ 74656462. The message is cut into 32-bit little-endian words;
# the last holds the 0 to 3 bytes left over, zero bytes, and the length
# mod 256 in its top byte. Each word m: v3 ^= m, c rounds, v0 ^= m. Then
# v2 ^= ff (ee for the wide output), d rounds, and the output v1 ^ v3,
# written little-endian; the wide output follows it with v1 ^= dd,
# d rounds and v1 ^ v3 again. The round is SipRound on 32-bit words with
# the rotations 5, 16, 8, 7, 13, 16.
#
# Streaming as in siphash.bend: start, update (any split), finish.
# The parameters (SipParams) and the key error (SipError) are siphash.bend's.
import Base
import ../bytes/bytes.bend as B
import ./siphash.bend as S

# HalfSipHash-2-4 with 32-bit output
def HalfSipParams.hsip24() -> S.SipParams:
  S.SipParams{2n, 4n, False{}}

# HalfSipHash-1-3 (Linux's hsiphash on 32-bit machines)
def HalfSipParams.hsip13() -> S.SipParams:
  S.SipParams{1n, 3n, False{}}

# HalfSipHash-2-4 with the 64-bit output
def HalfSipParams.hsip24_wide() -> S.SipParams:
  S.SipParams{2n, 4n, True{}}

# the output length of a parameter set: 4 bytes, or 8 when wide
def HalfSipParams.out_len(p: S.SipParams) -> Nat:
  match p:
    case S.SipParams{c, d, w}:
      match w:
        case True{}:
          8n
        case False{}:
          4n

# Keys

type HsipKey is Data:
  HsipKey{k0: U32, k1: U32}

def HsipKey.of_words(k0: U32, k1: U32) -> HsipKey:
  HsipKey{k0, k1}

def HsipKey.k0(k: HsipKey) -> U32:
  match k:
    case HsipKey{a, b}:
      a

def HsipKey.k1(k: HsipKey) -> U32:
  match k:
    case HsipKey{a, b}:
      b

def hsip.word(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{v}:
      v
    case None{}:
      0

def hsip.key.pick(ok: Bool, +o: B.Octets) -> Result<&2, &2, S.SipError, HsipKey>:
  match ok:
    case True{}:
      Done{HsipKey{hsip.word(B.Octets.le32_at(o, 0n)), hsip.word(B.Octets.le32_at(o, 4n))}}
    case False{}:
      Fail{S.SipBadKeyLength{B.Octets.len(o)}}

# the key of 8 bytes: k0 the first 4, little-endian, k1 the next 4
def HsipKey.of_octets(+o: B.Octets) -> Result<&2, &2, S.SipError, HsipKey>:
  hsip.key.pick(Nat.is_eq(B.Octets.len(o), 8n), o)

# The round

type HsipV is Data:
  HsipV{v0: U32, v1: U32, v2: U32, v3: U32}

def hsip.rotl(+x: U32, +r: Nat) -> U32:
  U32.or(U32.shln(x, r), U32.shrn(x, Nat.sub(32n, r)))

# v0 += v1; v1 <<<= 5; v1 ^= v0; v0 <<<= 16; v2 += v3; v3 <<<= 8;
# v3 ^= v2; v0 += v3; v3 <<<= 7; v3 ^= v0; v2 += v1; v1 <<<= 13;
# v1 ^= v2; v2 <<<= 16
def hsip.round(s: HsipV) -> HsipV:
  match s:
    case HsipV{v0, +v1, v2, +v3}:
      +a0 = U32.add(v0, v1)
      +a1 = U32.xor(hsip.rotl(v1, 5n), a0)
      +b0 = hsip.rotl(a0, 16n)
      +a2 = U32.add(v2, v3)
      +a3 = U32.xor(hsip.rotl(v3, 8n), a2)
      +c0 = U32.add(b0, a3)
      +b3 = U32.xor(hsip.rotl(a3, 7n), c0)
      +b2 = U32.add(a2, a1)
      +b1 = U32.xor(hsip.rotl(a1, 13n), b2)
      HsipV{c0, b1, hsip.rotl(b2, 16n), b3}

def hsip.rounds(n: Nat, s: HsipV) -> HsipV:
  match n:
    case 0n:
      s
    case 1n+p:
      hsip.rounds(p, hsip.round(s))

def hsip.xor0(+m: U32, s: HsipV) -> HsipV:
  match s:
    case HsipV{v0, v1, v2, v3}:
      HsipV{U32.xor(v0, m), v1, v2, v3}

def hsip.compress(+c: Nat, s: HsipV, +m: U32) -> HsipV:
  match s:
    case HsipV{v0, v1, v2, v3}:
      hsip.xor0(m, hsip.rounds(c, HsipV{v0, v1, v2, U32.xor(v3, m)}))

# The state: the parameters, v0..v3, the pending bytes (k of them, k < 4,
# little-endian in m), and the length so far mod 2^32

type HsipState is Data:
  HsipState{prm: S.SipParams, v: HsipV, m: U32, k: U32, n: U32}

def hsip.wide_xor(wide: Bool, +x: U32) -> U32:
  match wide:
    case True{}:
      U32.xor(x, 238)
    case False{}:
      x

def hsip.start(+prm: S.SipParams, +k0: U32, +k1: U32) -> HsipState:
  HsipState{prm, HsipV{k0, hsip.wide_xor(S.SipParams.wide(prm), k1), U32.xor(k0, 1819895653), U32.xor(k1, 1952801890)}, 0, 0, 0}

def HalfSipHash.start(+prm: S.SipParams, key: HsipKey) -> HsipState:
  match key:
    case HsipKey{k0, k1}:
      hsip.start(prm, k0, k1)

def hsip.full(full: Bool, +prm: S.SipParams, v: HsipV, +m: U32, +k: U32, +n: U32) -> HsipState:
  match full:
    case True{}:
      HsipState{prm, hsip.compress(S.SipParams.c(prm), v, m), 0, 0, n}
    case False{}:
      HsipState{prm, v, m, k, n}

def hsip.step(s: HsipState, b: U32) -> HsipState:
  match s:
    case HsipState{prm, v, m, +k, n}:
      hsip.full(U32.is_eq(k, 3), prm, v, U32.or(m, U32.shln(U32.and(255, b), U32.to_nat(U32.mul(k, 8)))), U32.add(k, 1), U32.add(n, 1))

def hsip.go(xs: List<&2, U32>, s: HsipState) -> HsipState:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      hsip.go(t, hsip.step(s, h))

def HalfSipHash.update(s: HsipState, o: B.Octets) -> HsipState:
  hsip.go(B.Octets.to_list(o), s)

def HalfSipHash.update_byte(s: HsipState, b: U32) -> HsipState:
  hsip.step(s, b)

def HalfSipHash.params(s: HsipState) -> S.SipParams:
  match s:
    case HsipState{prm, v, m, k, n}:
      prm

# Finalization

def hsip.out(s: HsipV) -> U32:
  match s:
    case HsipV{v0, v1, v2, v3}:
      U32.xor(v1, v3)

def hsip.xor1(+x: U32, s: HsipV) -> HsipV:
  match s:
    case HsipV{v0, v1, v2, v3}:
      HsipV{v0, U32.xor(v1, x), v2, v3}

def hsip.xor2(+x: U32, s: HsipV) -> HsipV:
  match s:
    case HsipV{v0, v1, v2, v3}:
      HsipV{v0, v1, U32.xor(v2, x), v3}

def hsip.second(+d: Nat, +s: HsipV) -> B.Octets:
  B.Octets.append(B.Octets.le32(hsip.out(s)), B.Octets.le32(hsip.out(hsip.rounds(d, hsip.xor1(221, s)))))

def hsip.fin(wide: Bool, +d: Nat, s: HsipV) -> B.Octets:
  match wide:
    case False{}:
      B.Octets.le32(hsip.out(hsip.rounds(d, hsip.xor2(255, s))))
    case True{}:
      hsip.second(d, hsip.rounds(d, hsip.xor2(238, s)))

def hsip.finish(prm: S.SipParams, v: HsipV, +last: U32) -> B.Octets:
  match prm:
    case S.SipParams{+c, +d, wide}:
      hsip.fin(wide, d, hsip.compress(c, v, last))

# the output of the bytes so far: 4 bytes, or 8 when wide
def HalfSipHash.finish(s: HsipState) -> B.Octets:
  match s:
    case HsipState{prm, v, m, k, n}:
      hsip.finish(prm, v, U32.or(m, U32.shln(U32.and(255, n), 24n)))

def HalfSipHash.hash(+prm: S.SipParams, key: HsipKey, o: B.Octets) -> B.Octets:
  HalfSipHash.finish(HalfSipHash.update(HalfSipHash.start(prm, key), o))

def halfsiphash24(key: HsipKey, o: B.Octets) -> B.Octets:
  HalfSipHash.hash(HalfSipParams.hsip24(), key, o)

def halfsiphash13(key: HsipKey, o: B.Octets) -> B.Octets:
  HalfSipHash.hash(HalfSipParams.hsip13(), key, o)

# from a raw 8-byte key (SipBadKeyLength otherwise)
def HalfSipHash.mac(+prm: S.SipParams, key: B.Octets, o: B.Octets) -> Result<&2, &2, S.SipError, B.Octets>:
  Result.map(&2, &2, S.SipError, HsipKey, B.Octets, k => HalfSipHash.hash(prm, k, o), HsipKey.of_octets(key))
