# XTS (IEEE Std 1619-2007, XTS-AES; NIST SP 800-38E), the tweakable mode for
# storage, over any 128-bit block cipher (see mode-core.bend for the
# template arguments). A data unit (a sector) is encrypted under two keys: k1
# for the data and k2 for the tweak. With i the data unit's 128-bit sequence
# number, as 16 little-endian bytes:
#   T_0 = E(k2, i),  T_(j+1) = T_j * alpha  (in GF(2^128), below)
#   C_j = E(k1, P_j xor T_j) xor T_j
# A data unit of at least 16 bytes whose length is not a multiple of 16 ends
# with ciphertext stealing (IEEE 1619, 5.3.2): the last full block's
# ciphertext lends its tail to pad the partial block.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../mode-core/mode-core.bend as M

# Multiplication by alpha (the polynomial x) in GF(2^128) modulo
# x^128 + x^7 + x^2 + x + 1, with the block read as a little-endian number
# (IEEE 1619, 5.2): every byte shifts left one bit, taking the top bit of the
# byte before it; the top bit of byte 15 wraps round as 135 (0x87) into byte 0.

# each byte of w shifted left, with the carries between w's own bytes
def xts.shift(+w: U32) -> U32:
  U32.or(U32.and(4278124286, U32.shl(w)), U32.and(65793, U32.shrn(w, 15n)))

# the carry out of w's last byte, into the first byte of the next word
def xts.carry(w: U32) -> U32:
  U32.shln(U32.and(128, w), 17n)

def Xts.mul_alpha(t: M.CmBlock) -> M.CmBlock:
  match t:
    case M.CmBlock{+w0, +w1, +w2, +w3}:
      M.CmBlock{U32.xor(xts.shift(w0), U32.and(2264924160, M.cm.mask(U32.shrn(w3, 7n)))), U32.or(xts.shift(w1), xts.carry(w0)), U32.or(xts.shift(w2), xts.carry(w1)), U32.or(xts.shift(w3), xts.carry(w2))}

# One block under tweak t

def xts.benc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, p: M.CmBlock, +t: M.CmBlock) -> M.CmBlock:
  M.CmBlock.xor(enc(k, M.CmBlock.xor(p, t)), t)

def xts.bdec(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, c: M.CmBlock, +t: M.CmBlock) -> M.CmBlock:
  M.CmBlock.xor(dec(k, M.CmBlock.xor(c, t)), t)

# The block layer: whole blocks from tweak t (t = T_j for the first of them)

def xts.enc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      Con{xts.benc(~K, ~enc, k, p, t), xts.enc(~K, ~enc, k, rest, Xts.mul_alpha(t))}

def xts.dec(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{c, rest}:
      Con{xts.bdec(~K, ~dec, k, c, t), xts.dec(~K, ~dec, k, rest, Xts.mul_alpha(t))}

# The same, tail-recursive (the blocks so far kept reversed in acc), so a
# data unit can be of any length: PROOF.bend proves each equal to its
# structural form above for every input

def xts.enc.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock, acc: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      M.cm.blocks.rev_onto(acc, Nil{})
    case Con{p, rest}:
      xts.enc.go(~K, ~enc, k, rest, Xts.mul_alpha(t), Con{xts.benc(~K, ~enc, k, p, t), acc})

def xts.enc.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  xts.enc.go(~K, ~enc, k, bs, t, Nil{})

def xts.dec.go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock, acc: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      M.cm.blocks.rev_onto(acc, Nil{})
    case Con{c, rest}:
      xts.dec.go(~K, ~dec, k, rest, Xts.mul_alpha(t), Con{xts.bdec(~K, ~dec, k, c, t), acc})

def xts.dec.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  xts.dec.go(~K, ~dec, k, bs, t, Nil{})

def Xts.encrypt_blocks(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k1: K, t: M.CmBlock, bs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  xts.enc.fast(~K, ~enc, k1, bs, t)

def Xts.decrypt_blocks(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k1: K, t: M.CmBlock, bs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  xts.dec.fast(~K, ~dec, k1, bs, t)

# T_0: the encrypted sequence number
def Xts.tweak(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k2: K, i: M.CmBlock) -> M.CmBlock:
  enc(k2, i)

# the 16-byte sequence number of data unit n (a sector number): n in
# little-endian order, then zeros
def Xts.sector(n: W.W64) -> B.Octets:
  B.Octets.append(B.Octets.le64(n), B.Octets.zeros(8n))

# The byte layer, with ciphertext stealing (IEEE 1619, 5.3.2). A data unit
# is its whole blocks and a tail of 0 to 15 bytes. All whole blocks but the
# last go through the block layer; the last one and the tail are encrypted
# together, by steal_c (the last full ciphertext block) and steal_t (the
# final partial one), from the tweak t = T_(n-1).

# T_0 * alpha^n
def xts.alpha_n(n: Nat, +t: M.CmBlock) -> M.CmBlock:
  match n:
    case 0n:
      t
    case 1n+q:
      xts.alpha_n(q, Xts.mul_alpha(t))

def xts.steal_c.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, partial: Bool, +k: K, p: M.CmBlock, +tail: List<&2, U32>, +t: M.CmBlock) -> M.CmBlock:
  match partial:
    case False{}:
      xts.benc(~K, ~enc, k, p, t)
    case True{}:
      +cc = M.cm.bytes_of(xts.benc(~K, ~enc, k, p, t))
      xts.benc(~K, ~enc, k, M.cm.block_of(B.append(tail, B.drop(B.len(tail), cc))), Xts.mul_alpha(t))

def xts.steal_t.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, partial: Bool, +k: K, p: M.CmBlock, +tail: List<&2, U32>, +t: M.CmBlock) -> List<&2, U32>:
  match partial:
    case False{}:
      Nil{}
    case True{}:
      B.take(B.len(tail), M.cm.bytes_of(xts.benc(~K, ~enc, k, p, t)))

# the ciphertext of the last whole block p and the tail, under tweak t
def xts.steal_c(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, p: M.CmBlock, +tail: List<&2, U32>, +t: M.CmBlock) -> M.CmBlock:
  xts.steal_c.go(~K, ~enc, Nat.is_lt(0n, B.len(tail)), k, p, tail, t)

def xts.steal_t(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, p: M.CmBlock, +tail: List<&2, U32>, +t: M.CmBlock) -> List<&2, U32>:
  xts.steal_t.go(~K, ~enc, Nat.is_lt(0n, B.len(tail)), k, p, tail, t)

# the plaintext of the last whole ciphertext block c and the tail
def xts.dsteal.go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, partial: Bool, +k: K, c: M.CmBlock, +tail: List<&2, U32>, +t: M.CmBlock) -> List<&2, U32>:
  match partial:
    case False{}:
      M.cm.bytes_of(xts.bdec(~K, ~dec, k, c, t))
    case True{}:
      +pp = M.cm.bytes_of(xts.bdec(~K, ~dec, k, c, Xts.mul_alpha(t)))
      M.cm.bytes_onto(xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(tail, B.drop(B.len(tail), pp))), t), B.take(B.len(tail), pp))

def xts.dsteal(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, c: M.CmBlock, +tail: List<&2, U32>, +t: M.CmBlock) -> List<&2, U32>:
  xts.dsteal.go(~K, ~dec, Nat.is_lt(0n, B.len(tail)), k, c, tail, t)

# all but the last of p then rest; and the last
def xts.init(rest: List<&2, M.CmBlock>, p: M.CmBlock) -> List<&2, M.CmBlock>:
  match rest:
    case Nil{}:
      Nil{}
    case Con{q, r}:
      Con{p, xts.init(r, q)}

def xts.last(rest: List<&2, M.CmBlock>, p: M.CmBlock) -> M.CmBlock:
  match rest:
    case Nil{}:
      p
    case Con{q, r}:
      xts.last(r, q)

def xts.eout(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> List<&2, U32>:
  +tl = xts.alpha_n(List.length(&2, M.CmBlock, init), t)
  M.cm.join_onto(List.append(&2, M.CmBlock, xts.enc(~K, ~enc, k, init, t), Con{xts.steal_c(~K, ~enc, k, last, tail, tl), Nil{}}), xts.steal_t(~K, ~enc, k, last, tail, tl))

def xts.dout(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> List<&2, U32>:
  M.cm.join_onto(xts.dec(~K, ~dec, k, init, t), xts.dsteal(~K, ~dec, k, last, tail, xts.alpha_n(List.length(&2, M.CmBlock, init), t)))

def xts.e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match bs:
        case Nil{}:
          Fail{M.CmTooShort{n}}
        case Con{+p, +rest}:
          Done{B.Octets.of_list(xts.eout(~K, ~enc, k, t, xts.init(rest, p), xts.last(rest, p), tail))}

def xts.d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match bs:
        case Nil{}:
          Fail{M.CmTooShort{n}}
        case Con{+c, +rest}:
          Done{B.Octets.of_list(xts.dout(~K, ~dec, k, t, xts.init(rest, c), xts.last(rest, c), tail))}

def xts.e1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      xts.e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs))

def xts.d1(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      xts.d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs))

def xts.tweak.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k2: K, r: Result<&2, &2, M.CmError, M.CmBlock>) -> Result<&2, &2, M.CmError, M.CmBlock>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{enc(k2, v)}

# T_0, from the 16-byte sequence number i
def xts.tweak(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k2: K, i: B.Octets) -> Result<&2, &2, M.CmError, M.CmBlock>:
  +xs = B.Octets.to_list(i)
  xts.tweak.go(~K, ~enc, k2, M.cm.need_block(xs, M.CmBadTweakLength{B.len(xs)}))

# The byte layer, tail-recursive: what Xts.encrypt and Xts.decrypt run
# (xts.init .. xts.d1 are the structural forms; PROOF.bend: xtsp.e1_eq,
# d1_eq)

def xts.init.go(rest: List<&2, M.CmBlock>, p: M.CmBlock, acc: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match rest:
    case Nil{}:
      M.cm.blocks.rev_onto(acc, Nil{})
    case Con{q, r}:
      xts.init.go(r, q, Con{p, acc})

def xts.init.fast(rest: List<&2, M.CmBlock>, p: M.CmBlock) -> List<&2, M.CmBlock>:
  xts.init.go(rest, p, Nil{})

def xts.eout.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> List<&2, U32>:
  +tl = xts.alpha_n(M.cm.blocks.len(init), t)
  M.cm.join_onto.fast(M.cm.blocks.append(xts.enc.fast(~K, ~enc, k, init, t), Con{xts.steal_c(~K, ~enc, k, last, tail, tl), Nil{}}), xts.steal_t(~K, ~enc, k, last, tail, tl))

def xts.dout.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> List<&2, U32>:
  M.cm.join_onto.fast(xts.dec.fast(~K, ~dec, k, init, t), xts.dsteal(~K, ~dec, k, last, tail, xts.alpha_n(M.cm.blocks.len(init), t)))

def xts.e2.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match bs:
        case Nil{}:
          Fail{M.CmTooShort{n}}
        case Con{+p, +rest}:
          Done{B.Octets.of_list(xts.eout.fast(~K, ~enc, k, t, xts.init.fast(rest, p), xts.last(rest, p), tail))}

def xts.d2.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match bs:
        case Nil{}:
          Fail{M.CmTooShort{n}}
        case Con{+c, +rest}:
          Done{B.Octets.of_list(xts.dout.fast(~K, ~dec, k, t, xts.init.fast(rest, c), xts.last(rest, c), tail))}

def xts.e1.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      xts.e2.fast(~K, ~enc, k, t, M.cm.split.fast(xs), B.len.fast(xs))

def xts.d1.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      xts.d2.fast(~K, ~dec, k, t, M.cm.split.fast(xs), B.len.fast(xs))

# Xts.encrypt and Xts.decrypt through the structural forms (the laws' proofs
# reason about these; PROOF.bend proves them equal to the public defs)
def Xts.encrypt.ref(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, i: B.Octets, p: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  xts.e1(~K, ~enc, k1, xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(p))

def Xts.decrypt.ref(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, i: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  xts.d1(~K, ~dec, k1, xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(c))

# the data unit p (at least 16 bytes) with sequence number i (16 bytes)
def Xts.encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, i: B.Octets, p: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  xts.e1.fast(~K, ~enc, k1, xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(p))

# decryption needs enc too: the tweak is always encrypted
def Xts.decrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, i: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  xts.d1.fast(~K, ~dec, k1, xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(c))
