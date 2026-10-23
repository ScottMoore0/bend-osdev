# AES-128, AES-192 and AES-256 (FIPS 197) as block ciphers for the modes:
# the named default ciphers, used as
#   ~CmAesKey, ~CmAes.encrypt, ~CmAes.decrypt
# Encryption is bend-collections' AES (bend-collections@1.0.0.0,
# src/crypto/aes/aes.bend: expand_key and encrypt_block). That library has no
# decryption, so this file adds FIPS 197's inverse cipher (section 5.3): it
# undoes bend-collections' cipher round by round, with that cipher's own
# round keys (its Schedule), the last one first. The inverse S-box is
# computed, not looked up: the inverse affine map, then the inverse in
# GF(2^8) as x^254, with masks instead of branches, so no branch or table
# index depends on a key or data byte; InvMixColumns' products by {09},
# {0b}, {0d} and {0e} are sums of doublings (xtime), likewise branch-free.
#
# Both directions use the round keys with each byte masked to its low 8
# bits (aes.sched), which changes nothing for a key made by CmAes.key (its
# bytes are below 256) and lets LAWS.bend state the round trip for every
# value of CmAesKey.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M
import bend-collections@1.0.0.0/src/crypto/aes/aes.bend as A
import bend-collections@1.0.0.0/src/crypto/aes/types.bend as T

# GF(2^8) modulo x^8 + x^4 + x^3 + x + 1

def aes.xt(+x: U32) -> U32:
  U32.and(255, U32.xor(U32.shl(x), U32.and(27, M.cm.mask(U32.shrn(x, 7n)))))

def aes.gmul.go(n: Nat, +a: U32, +b: U32, p: U32) -> U32:
  match n:
    case 0n:
      p
    case 1n+q:
      aes.gmul.go(q, aes.xt(a), U32.shr(b), U32.xor(p, U32.and(a, M.cm.mask(b))))

def aes.gmul(+a: U32, +b: U32) -> U32:
  aes.gmul.go(8n, a, b, 0)

# a := a^2 * x, n times: from a = x, six times gives x^127
def aes.inv.go(n: Nat, a: U32, +x: U32) -> U32:
  match n:
    case 0n:
      a
    case 1n+q:
      +s = a
      aes.inv.go(q, aes.gmul(aes.gmul(s, s), x), x)

# the multiplicative inverse, x^254 (0 for 0)
def aes.inv(+x: U32) -> U32:
  +a = aes.inv.go(6n, x, x)
  aes.gmul(a, a)

def aes.rotl(+b: U32, +n: Nat) -> U32:
  U32.and(255, U32.or(U32.shln(b, n), U32.shrn(b, Nat.sub(8n, n))))

# the inverse S-box: the inverse affine map, then the inverse
def aes.isbox(x: U32) -> U32:
  +b = U32.and(255, x)
  aes.inv(U32.xor(U32.xor(U32.xor(aes.rotl(b, 1n), aes.rotl(b, 3n)), aes.rotl(b, 6n)), 5))

# The state is bend-collections' (T.State: four columns T.W{r0, r1, r2, r3},
# byte 4c + r of the block in row r of column c)

# each byte's low 8 bits
def aes.mask_w(w: T.Quad) -> T.Quad:
  match w:
    case T.W{a, b, c, d}:
      T.W{U32.and(255, a), U32.and(255, b), U32.and(255, c), U32.and(255, d)}

def aes.mask(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{aes.mask_w(c0), aes.mask_w(c1), aes.mask_w(c2), aes.mask_w(c3)}

def aes.mask_keys(ks: List<&2, T.State>) -> List<&2, T.State>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      Con{aes.mask(k), aes.mask_keys(rest)}

# a schedule with every round key byte masked
def aes.sched(s: A.Schedule) -> A.Schedule:
  match s:
    case A.Schedule{nr, ks}:
      A.Schedule{nr, aes.mask_keys(ks)}

# InvSubBytes: the inverse S-box on every byte
def aes.isub_w(w: T.Quad) -> T.Quad:
  match w:
    case T.W{a, b, c, d}:
      T.W{aes.isbox(a), aes.isbox(b), aes.isbox(c), aes.isbox(d)}

def aes.inv_sub(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{aes.isub_w(c0), aes.isub_w(c1), aes.isub_w(c2), aes.isub_w(c3)}

# InvShiftRows: row r moves r columns to the right
def aes.inv_shift(s: T.State) -> T.State:
  match s:
    case T.S{T.W{p0, p1, p2, p3}, T.W{q0, q1, q2, q3}, T.W{r0, r1, r2, r3}, T.W{s0, s1, s2, s3}}:
      T.S{T.W{p0, s1, r2, q3}, T.W{q0, p1, s2, r3}, T.W{r0, q1, p2, s3}, T.W{s0, r1, q2, p3}}

# InvMixColumns: each column times {0e, 0b, 0d, 09}, rotated per row
# a byte times {09}, {0b}, {0d}, {0e}: x^3 + 1, x^3 + x + 1, x^3 + x^2 + 1,
# x^3 + x^2 + x, as sums of doublings
def aes.c9(+b: U32) -> U32:
  U32.xor(aes.xt(aes.xt(aes.xt(b))), b)

def aes.c11(+b: U32) -> U32:
  +b2 = aes.xt(b)
  U32.xor(U32.xor(aes.xt(aes.xt(b2)), b2), b)

def aes.c13(+b: U32) -> U32:
  +b4 = aes.xt(aes.xt(b))
  U32.xor(U32.xor(aes.xt(b4), b4), b)

def aes.c14(+b: U32) -> U32:
  +b2 = aes.xt(b)
  +b4 = aes.xt(b2)
  U32.xor(U32.xor(aes.xt(b4), b4), b2)

# the same products of a word's low byte
def aes.m9(a: U32) -> U32:
  aes.c9(U32.and(255, a))

def aes.m11(a: U32) -> U32:
  aes.c11(U32.and(255, a))

def aes.m13(a: U32) -> U32:
  aes.c13(U32.and(255, a))

def aes.m14(a: U32) -> U32:
  aes.c14(U32.and(255, a))

def aes.imix0(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.xor(U32.xor(aes.m14(a), aes.m11(b)), U32.xor(aes.m13(c), aes.m9(d)))

def aes.imix_w(w: T.Quad) -> T.Quad:
  match w:
    case T.W{+a, +b, +c, +d}:
      T.W{aes.imix0(a, b, c, d), aes.imix0(b, c, d, a), aes.imix0(c, d, a, b), aes.imix0(d, a, b, c)}

def aes.inv_mix(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{aes.imix_w(c0), aes.imix_w(c1), aes.imix_w(c2), aes.imix_w(c3)}

# A round undone (round key k): AddRoundKey, InvMixColumns, InvShiftRows,
# InvSubBytes; the last round has no MixColumns to undo
def aes.inv_round(c: T.State, k: T.State) -> T.State:
  aes.inv_sub(aes.inv_shift(aes.inv_mix(A.add_round_key(c, k))))

def aes.inv_last(c: T.State, k: T.State) -> T.State:
  aes.inv_sub(aes.inv_shift(A.add_round_key(c, k)))

# bend-collections' rounds (n full rounds, then the last, a round key each)
# undone, the last round key first
def aes.inv_rounds(n: Nat, ks: List<&2, T.State>, c: T.State) -> T.State:
  match n ks:
    case 0n Con{k, rest}:
      aes.inv_last(c, k)
    case 1n+p Con{k, rest}:
      aes.inv_round(aes.inv_rounds(p, rest, c), k)
    case _ _:
      aes.mask(c)

# bend-collections' cipher (AddRoundKey with the first round key, then the
# rounds) undone
def aes.inv_cipher(+nr: Nat, ks: List<&2, T.State>, c: T.State) -> T.State:
  match ks:
    case Con{k, rest}:
      aes.mask(A.add_round_key(aes.inv_rounds(Nat.sub(nr, 1n), rest, c), k))
    case Nil{}:
      aes.mask(c)

# a block's 16 bytes as a state, and back
def aes.state16(xs: List<&2, U32>) -> T.State:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{b0, Con{b1, Con{b2, Con{b3, Con{c0, Con{c1, Con{c2, Con{c3, Con{d0, Con{d1, Con{d2, Con{d3, t}}}}}}}}}}}}}}}}:
      T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}
    case _:
      T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}

def aes.state_in(b: M.CmBlock) -> T.State:
  aes.state16(M.cm.bytes_of(b))

def aes.out(s: T.State) -> M.CmBlock:
  match s:
    case T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}:
      M.cm.block16(a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3)

# The cipher

# An expanded AES key: bend-collections' schedule (the number of rounds and
# the round keys), for encryption and decryption alike. Internal; built by
# CmAes.key.
type CmAesKey is Data:
  CmAesKey{sched: A.Schedule}

def aes.key.go(m: Maybe<&2, A.Schedule>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, CmAesKey>:
  match m:
    case None{}:
      Fail{M.CmBadKeyLength{B.len(xs)}}
    case Some{s}:
      Done{CmAesKey{s}}

def aes.key.pick(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, CmAesKey>:
  match ok:
    case True{}:
      aes.key.go(A.expand_key(xs), xs)
    case False{}:
      Fail{M.CmBadKeyLength{B.len(xs)}}

# a 16-byte (AES-128) or 32-byte (AES-256) key
def CmAes.key(o: B.Octets) -> Result<&2, &2, M.CmError, CmAesKey>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  aes.key.pick(Bool.or(Nat.is_eq(n, 16n), Nat.is_eq(n, 32n)), xs)

def CmAes.key128(o: B.Octets) -> Result<&2, &2, M.CmError, CmAesKey>:
  +xs = B.Octets.to_list(o)
  aes.key.pick(Nat.is_eq(B.len(xs), 16n), xs)

def CmAes.key192(o: B.Octets) -> Result<&2, &2, M.CmError, CmAesKey>:
  +xs = B.Octets.to_list(o)
  aes.key.pick(Nat.is_eq(B.len(xs), 24n), xs)

def CmAes.key256(o: B.Octets) -> Result<&2, &2, M.CmError, CmAesKey>:
  +xs = B.Octets.to_list(o)
  aes.key.pick(Nat.is_eq(B.len(xs), 32n), xs)

def aes.of_maybe(m: Maybe<&2, List<&2, U32>>) -> M.CmBlock:
  match m:
    case None{}:
      M.CmBlock.zero()
    case Some{xs}:
      M.cm.block_of(xs)

# one block, encrypted (bend-collections' encrypt_block)
def CmAes.encrypt(k: CmAesKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case CmAesKey{sched}:
      aes.of_maybe(A.encrypt_block(aes.sched(sched), M.cm.bytes_of(b)))

# the key as it is: decryption needs nothing beyond the schedule (kept so
# that callers written for an earlier version, which computed decryption
# round keys here, still build)
def CmAes.prepare(k: CmAesKey) -> CmAesKey:
  k

def aes.decrypt_with(s: A.Schedule, b: M.CmBlock) -> M.CmBlock:
  match s:
    case A.Schedule{nr, ks}:
      aes.out(aes.inv_cipher(nr, ks, aes.state_in(b)))

# one block, decrypted (the inverse cipher above)
def CmAes.decrypt(k: CmAesKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case CmAesKey{sched}:
      aes.decrypt_with(aes.sched(sched), b)
