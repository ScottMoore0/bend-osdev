# LRW over any 128-bit block cipher (the block-cipher interface, block.bend):
# the tweakable block cipher of M. Liskov, R. Rivest, D. Wagner, "Tweakable
# Block Ciphers" (CRYPTO 2002), theorem 2, as the IEEE P1619 draft proposal
# "Tweakable Narrow-block Encryption" (draft 1.00, October 2004) specifies
# LRW-AES for storage: a key pair (Key1, the cipher's key; Key2, a 16-byte
# tweak key), and for the block at logical index I
#   T = Key2 (x) I,  C = E(Key1, P xor T) xor T,  P = D(Key1, C xor T) xor T
# with (x) the product in GF(2^128) modulo x^128 + x^7 + x^2 + x + 1 on
# 16-byte big-endian numbers (bend-osdev-gf's Gf128.mul_be) and I a 16-byte
# big-endian number (draft section 6.1). Consecutive blocks have consecutive
# indices. The key is Key1 followed by Key2 (the Linux kernel's "lrw"
# layout); the IV is the index of the first block.
#
# A tweak is made a block through the cipher's block format (~blk_of); a
# format that refused 16 bytes would leave the block untweaked, in both
# directions, so decryption undoes encryption whatever the format, for every
# key, tweak key, index and list of blocks wherever the cipher's decryption
# undoes its encryption: a law per 128-bit instance (gen/instances.py,
# <c>_lrw_round_trip).
import Base
import ../bytes/bytes.bend as B
import ../gf/gf128.bend as G
import ./crypto.bend as Cr
import ./modes.bend as Md

# the tweak of index i under the tweak key k2, as a block
def cr.lrw.tweak(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k2: G.Gf128, i: G.Gf128) -> Maybe<&2, Blk>:
  blk_of(G.Gf128.to_octets(G.Gf128.mul_be(k2, i)))

# one block under a tweak
def cr.lrw.benc(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, t: Maybe<&2, Blk>, p: Blk) -> Blk:
  match t:
    case None{}:
      enc(k, p)
    case Some{+x}:
      bxor(enc(k, bxor(p, x)), x)

def cr.lrw.bdec(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, t: Maybe<&2, Blk>, c: Blk) -> Blk:
  match t:
    case None{}:
      dec(k, c)
    case Some{+x}:
      bxor(dec(k, bxor(c, x)), x)

def cr.lrw.carry(z: Bool, +w: U32) -> U32:
  match z:
    case True{}:
      U32.add(w, 1)
    case False{}:
      w

# i + 1, modulo 2^128
def cr.lrw.inc(i: G.Gf128) -> G.Gf128:
  match i:
    case G.Gf128{w0, w1, w2, w3}:
      +a3 = U32.add(w3, 1)
      +c3 = U32.is_eq(a3, 0)
      +a2 = cr.lrw.carry(c3, w2)
      +c2 = Bool.and(c3, U32.is_eq(a2, 0))
      +a1 = cr.lrw.carry(c2, w1)
      +c1 = Bool.and(c2, U32.is_eq(a1, 0))
      G.Gf128{cr.lrw.carry(c1, w0), a1, a2, a3}

# Structural forms (the proofs' reference): the blocks from index i

def cr.lrw.enc(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{cr.lrw.benc(~K, ~Blk, ~enc, ~bxor, k, cr.lrw.tweak(~Blk, ~blk_of, k2, i), p), cr.lrw.enc(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, t, cr.lrw.inc(i))}

def cr.lrw.dec(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{cr.lrw.bdec(~K, ~Blk, ~dec, ~bxor, k, cr.lrw.tweak(~Blk, ~blk_of, k2, i), c), cr.lrw.dec(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, t, cr.lrw.inc(i))}

# The loops that run

def cr.lrw.enc.go(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Md.cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{p, t}:
      cr.lrw.enc.go(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, t, cr.lrw.inc(i), Con{cr.lrw.benc(~K, ~Blk, ~enc, ~bxor, k, cr.lrw.tweak(~Blk, ~blk_of, k2, i), p), acc})

def cr.lrw.dec.go(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Md.cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{c, t}:
      cr.lrw.dec.go(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, t, cr.lrw.inc(i), Con{cr.lrw.bdec(~K, ~Blk, ~dec, ~bxor, k, cr.lrw.tweak(~Blk, ~blk_of, k2, i), c), acc})

# LRW on blocks: key k, tweak key k2, the first block's index i (the next
# call's index is i plus the number of blocks)
def CrLrw.encrypt_blocks(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, +i: G.Gf128, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.lrw.enc.go(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, bs, i, Nil{})

def CrLrw.decrypt_blocks(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, +i: G.Gf128, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.lrw.dec.go(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, bs, i, Nil{})

# The key pair: the cipher's key schedule and the tweak key
type CrLrwKey<-K: Data> is Data:
  CrLrwKey{k: K, t: G.Gf128}

def cr.lrw.gf(+n: Nat, r: Result<&2, &2, G.Gf128Error, G.Gf128>) -> Result<&2, &2, Cr.CrError, G.Gf128>:
  match r:
    case Fail{e}:
      Fail{Cr.CrBadKeyLength{n}}
    case Done{x}:
      Done{x}

# a raw key: the cipher's key followed by the 16-byte tweak key
# (CrBadKeyLength for a key of 16 bytes or fewer, or one the cipher refuses)
def CrLrw.key(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CrLrwKey<K>>:
  +n = B.Octets.len(o)
  do Result<&2, &2, Cr.CrError, CrLrwKey<K>>:
    Cr.CrError.check(Nat.is_lt(16n, n), Cr.CrBadKeyLength{n})
    k : K <- key(B.Octets.take(Nat.sub(n, 16n), o))
    t : G.Gf128 <- cr.lrw.gf(n, G.Gf128.of_octets(B.Octets.drop(Nat.sub(n, 16n), o)))
    return CrLrwKey{k, t}

def cr.lrw.index.of(+n: Nat, r: Result<&2, &2, G.Gf128Error, G.Gf128>) -> Result<&2, &2, Cr.CrError, G.Gf128>:
  match r:
    case Fail{e}:
      Fail{Cr.CrBadIvLength{n}}
    case Done{x}:
      Done{x}

def cr.lrw.index(+iv: B.Octets) -> Result<&2, &2, Cr.CrError, G.Gf128>:
  cr.lrw.index.of(B.Octets.len(iv), G.Gf128.of_octets(iv))

# LRW on bytes: a message of whole blocks; the IV is the first block's
# 16-byte big-endian index (CrBadIvLength, CrNotBlockMultiple otherwise)
def CrLrw.encrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrLrwKey<K>, +iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match kk:
    case CrLrwKey{+k, +k2}:
      do Result<&2, &2, Cr.CrError, B.Octets>:
        i : G.Gf128 <- cr.lrw.index(iv)
        bs : List<&2, Blk> <- Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, m)
        return Md.CrModes.octets_of(~Blk, ~blk_to, CrLrw.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, i, bs))

def CrLrw.decrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrLrwKey<K>, +iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match kk:
    case CrLrwKey{+k, +k2}:
      do Result<&2, &2, Cr.CrError, B.Octets>:
        i : G.Gf128 <- cr.lrw.index(iv)
        bs : List<&2, Blk> <- Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, c)
        return Md.CrModes.octets_of(~Blk, ~blk_to, CrLrw.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, i, bs))
