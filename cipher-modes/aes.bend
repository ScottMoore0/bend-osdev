# AES-128 and AES-256 (FIPS 197) as block ciphers for the modes: the named
# default ciphers, used as
#   ~CmAesKey, ~CmAes.encrypt, ~CmAes.decrypt
# Encryption is bend-collections' AES (bend-collections@1.0.0.0,
# src/crypto/aes/aes.bend: expand_key and encrypt_block). That library has no
# decryption, so this file adds FIPS 197's inverse cipher (section 5.3) and the
# key expansion it needs (section 5.2), written here from the specification.
# The inverse S-box is computed, not looked up: the inverse affine map, then
# the inverse in GF(2^8) as x^254, with masks instead of branches, so no
# branch or table index depends on a key or data byte.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M
import bend-collections@1.0.0.0/src/crypto/aes/aes.bend as A

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

# the S-box: the inverse, then the affine map
def aes.sbox(+x: U32) -> U32:
  +b = aes.inv(U32.and(255, x))
  U32.xor(U32.xor(U32.xor(U32.xor(U32.xor(b, aes.rotl(b, 1n)), aes.rotl(b, 2n)), aes.rotl(b, 3n)), aes.rotl(b, 4n)), 99)

# the inverse S-box: the inverse affine map, then the inverse
def aes.isbox(x: U32) -> U32:
  +b = U32.and(255, x)
  aes.inv(U32.xor(U32.xor(U32.xor(aes.rotl(b, 1n), aes.rotl(b, 3n)), aes.rotl(b, 6n)), 5))

# The state: 16 bytes, column by column (byte 4c + r is row r of column c)

type CmAesState is Data:
  CmAesState{s0: U32, s1: U32, s2: U32, s3: U32, s4: U32, s5: U32, s6: U32, s7: U32, s8: U32, s9: U32, s10: U32, s11: U32, s12: U32, s13: U32, s14: U32, s15: U32}

def aes.byte(+w: U32, n: Nat) -> U32:
  U32.and(255, U32.shrn(w, n))

def aes.state_of(b: M.CmBlock) -> CmAesState:
  match b:
    case M.CmBlock{+w0, +w1, +w2, +w3}:
      CmAesState{aes.byte(w0, 24n), aes.byte(w0, 16n), aes.byte(w0, 8n), aes.byte(w0, 0n), aes.byte(w1, 24n), aes.byte(w1, 16n), aes.byte(w1, 8n), aes.byte(w1, 0n), aes.byte(w2, 24n), aes.byte(w2, 16n), aes.byte(w2, 8n), aes.byte(w2, 0n), aes.byte(w3, 24n), aes.byte(w3, 16n), aes.byte(w3, 8n), aes.byte(w3, 0n)}

def aes.block_of(s: CmAesState) -> M.CmBlock:
  match s:
    case CmAesState{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15}:
      M.CmBlock{M.cm.word(a0, a1, a2, a3), M.cm.word(a4, a5, a6, a7), M.cm.word(a8, a9, a10, a11), M.cm.word(a12, a13, a14, a15)}

def aes.add(s: CmAesState, k: CmAesState) -> CmAesState:
  match s k:
    case CmAesState{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15} CmAesState{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      CmAesState{U32.xor(a0, b0), U32.xor(a1, b1), U32.xor(a2, b2), U32.xor(a3, b3), U32.xor(a4, b4), U32.xor(a5, b5), U32.xor(a6, b6), U32.xor(a7, b7), U32.xor(a8, b8), U32.xor(a9, b9), U32.xor(a10, b10), U32.xor(a11, b11), U32.xor(a12, b12), U32.xor(a13, b13), U32.xor(a14, b14), U32.xor(a15, b15)}

# InvShiftRows: row r moves r columns to the right
# InvSubBytes: the inverse S-box on every byte (both in one pass)
def aes.inv_shift_sub(s: CmAesState) -> CmAesState:
  match s:
    case CmAesState{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15}:
      CmAesState{aes.isbox(a0), aes.isbox(a13), aes.isbox(a10), aes.isbox(a7), aes.isbox(a4), aes.isbox(a1), aes.isbox(a14), aes.isbox(a11), aes.isbox(a8), aes.isbox(a5), aes.isbox(a2), aes.isbox(a15), aes.isbox(a12), aes.isbox(a9), aes.isbox(a6), aes.isbox(a3)}

# multiples of a byte by 9, 11, 13 and 14
def aes.m9(+a: U32) -> U32:
  U32.xor(aes.xt(aes.xt(aes.xt(a))), a)

def aes.m11(+a: U32) -> U32:
  +a2 = aes.xt(a)
  U32.xor(U32.xor(aes.xt(aes.xt(a2)), a2), a)

def aes.m13(+a: U32) -> U32:
  +a4 = aes.xt(aes.xt(a))
  U32.xor(U32.xor(aes.xt(a4), a4), a)

def aes.m14(+a: U32) -> U32:
  +a2 = aes.xt(a)
  +a4 = aes.xt(a2)
  U32.xor(U32.xor(aes.xt(a4), a4), a2)

def aes.mix0(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  U32.xor(U32.xor(aes.m14(a), aes.m11(b)), U32.xor(aes.m13(c), aes.m9(d)))

# InvMixColumns: each column times {0e, 0b, 0d, 09}, rotated per row
def aes.inv_mix(s: CmAesState) -> CmAesState:
  match s:
    case CmAesState{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, +a9, +a10, +a11, +a12, +a13, +a14, +a15}:
      CmAesState{aes.mix0(a0, a1, a2, a3), aes.mix0(a1, a2, a3, a0), aes.mix0(a2, a3, a0, a1), aes.mix0(a3, a0, a1, a2), aes.mix0(a4, a5, a6, a7), aes.mix0(a5, a6, a7, a4), aes.mix0(a6, a7, a4, a5), aes.mix0(a7, a4, a5, a6), aes.mix0(a8, a9, a10, a11), aes.mix0(a9, a10, a11, a8), aes.mix0(a10, a11, a8, a9), aes.mix0(a11, a8, a9, a10), aes.mix0(a12, a13, a14, a15), aes.mix0(a13, a14, a15, a12), aes.mix0(a14, a15, a12, a13), aes.mix0(a15, a12, a13, a14)}

# The inverse cipher over the round keys, last round key first:
# AddRoundKey(Nr), then Nr - 1 rounds of InvShiftRows, InvSubBytes,
# AddRoundKey, InvMixColumns, then InvShiftRows, InvSubBytes, AddRoundKey(0)
def aes.rounds(rest: List<&2, CmAesState>, k: CmAesState, s: CmAesState) -> CmAesState:
  match rest:
    case Nil{}:
      aes.add(aes.inv_shift_sub(s), k)
    case Con{k2, rest2}:
      aes.rounds(rest2, k2, aes.inv_mix(aes.add(aes.inv_shift_sub(s), k)))

def aes.decrypt(ks: List<&2, CmAesState>, s: CmAesState) -> CmAesState:
  match ks:
    case Nil{}:
      s
    case Con{k, Nil{}}:
      aes.add(s, k)
    case Con{k, Con{k2, rest}}:
      aes.rounds(rest, k2, aes.add(s, k))

# Key expansion (FIPS 197, 5.2), on big-endian words

def aes.sub_word(+w: U32) -> U32:
  M.cm.word(aes.sbox(U32.shrn(w, 24n)), aes.sbox(U32.shrn(w, 16n)), aes.sbox(U32.shrn(w, 8n)), aes.sbox(w))

def aes.rot_word(+w: U32) -> U32:
  U32.or(U32.shln(w, 8n), U32.shrn(w, 24n))

def aes.rcon.go(n: Nat, +x: U32) -> U32:
  match n:
    case 0n:
      x
    case 1n+p:
      aes.rcon.go(p, aes.xt(x))

# x^(j - 1) in GF(2^8), the round constant of word j * Nk
def aes.rcon(j: Nat) -> U32:
  match j:
    case 0n:
      0
    case 1n+p:
      aes.rcon.go(p, 1)

# Nk > 6 and i mod Nk = 4: SubWord alone
def aes.temp.big(big: Bool, +w: U32) -> U32:
  match big:
    case True{}:
      aes.sub_word(w)
    case False{}:
      w

# temp from w[i - 1], for word i
def aes.temp(first: Bool, +i: Nat, +nk: Nat, +w: U32) -> U32:
  match first:
    case True{}:
      U32.xor(aes.sub_word(aes.rot_word(w)), U32.shln(aes.rcon(Nat.div(i, nk)), 24n))
    case False{}:
      aes.temp.big(Bool.and(Nat.is_lt(6n, nk), Nat.is_eq(Nat.mod(i, nk), 4n)), w)

def aes.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

def aes.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def aes.last(xs: List<&2, U32>, d: U32) -> U32:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      aes.last(t, h)

# n more words from word i; win holds the last Nk words, oldest first, and acc
# every word so far, newest first
def aes.expand.go(n: Nat, +i: Nat, +nk: Nat, +win: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      +w = U32.xor(aes.head(win), aes.temp(Nat.is_eq(Nat.mod(i, nk), 0n), i, nk, aes.last(win, 0)))
      aes.expand.go(p, 1n+i, nk, B.append(aes.tail(win), Con{w, Nil{}}), Con{w, acc})

# the key's bytes as big-endian words
def aes.words(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Con{M.cm.word(a, b, c, d), aes.words(t)}
    case _:
      Nil{}

def aes.round_keys(ws: List<&2, U32>) -> List<&2, CmAesState>:
  match ws:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Con{aes.state_of(M.CmBlock{a, b, c, d}), aes.round_keys(t)}
    case _:
      Nil{}

# the 4 (Nr + 1) words of the schedule, Nr = Nk + 6
def aes.expand(+nk: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  +ws = aes.words(xs)
  aes.expand.go(Nat.sub(Nat.mul(4n, Nat.add(nk, 7n)), nk), nk, nk, ws, List.reverse(&2, U32, ws))

# The cipher

# An expanded AES key: bend-collections' schedule for encryption, the key's
# bytes, and the round keys for decryption, last first, once CmAes.prepare
# has computed them (Nil until then: CmAes.decrypt then derives them for each
# block). Internal; built by CmAes.key.
type CmAesKey is Data:
  CmAesKey{sched: A.Schedule, raw: List<&2, U32>, dkeys: List<&2, CmAesState>}

def aes.key.go(m: Maybe<&2, A.Schedule>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, CmAesKey>:
  match m:
    case None{}:
      Fail{M.CmBadKeyLength{B.len(xs)}}
    case Some{s}:
      Done{CmAesKey{s, xs, Nil{}}}

def aes.key.pick(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, CmAesKey>:
  match ok:
    case True{}:
      aes.key.go(A.expand_key(xs), xs)
    case False{}:
      Fail{M.CmBadKeyLength{B.len(xs)}}

# the decryption round keys: the ones computed already, or from the key bytes
def aes.dkeys(dk: List<&2, CmAesState>, +raw: List<&2, U32>) -> List<&2, CmAesState>:
  match dk:
    case Nil{}:
      List.reverse(&2, CmAesState, aes.round_keys(aes.expand(Nat.div(B.len(raw), 4n), raw)))
    case Con{h, t}:
      Con{h, t}

# a 16-byte (AES-128) or 32-byte (AES-256) key
def CmAes.key(o: B.Octets) -> Result<&2, &2, M.CmError, CmAesKey>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  aes.key.pick(Bool.or(Nat.is_eq(n, 16n), Nat.is_eq(n, 32n)), xs)

def CmAes.key128(o: B.Octets) -> Result<&2, &2, M.CmError, CmAesKey>:
  +xs = B.Octets.to_list(o)
  aes.key.pick(Nat.is_eq(B.len(xs), 16n), xs)

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
    case CmAesKey{sched, raw, dk}:
      aes.of_maybe(A.encrypt_block(sched, M.cm.bytes_of(b)))

# the key with its decryption round keys computed, for decrypting many blocks
def CmAes.prepare(k: CmAesKey) -> CmAesKey:
  match k:
    case CmAesKey{sched, +raw, dk}:
      CmAesKey{sched, raw, aes.dkeys(dk, raw)}

# one block, decrypted (the inverse cipher above)
def CmAes.decrypt(k: CmAesKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case CmAesKey{sched, raw, dk}:
      aes.block_of(aes.decrypt(aes.dkeys(dk, raw), aes.state_of(b)))
