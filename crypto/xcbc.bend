# XCBC-MAC over any block cipher (the block-cipher interface, block.bend), as
# RFC 3566 (The AES-XCBC-MAC-96 Algorithm and Its Use With IPsec, 2003)
# defines it for AES-128, after J. Black and P. Rogaway's three-key
# construction:
#   K1 = E(K, 0x01..01), K2 = E(K, 0x02..02), K3 = E(K, 0x03..03)
#   E[0] = 0; E[i] = E(K1, M[i] xor E[i-1]) for every block but the last;
#   the last block whole:  E[n] = E(K1, M[n] xor E[n-1] xor K2)
#   the last block short (or an empty message): padded with one 1 bit and
#   zeros to a block, E[n] = E(K1, pad(M[n]) xor E[n-1] xor K3)
# and the tag is E[n] (RFC 3566 truncates it to 96 bits for IPsec:
# CrXcbc.mac96). Over another cipher the constants are blocks of 0x01, 0x02,
# 0x03 bytes of its block size, and K1 must be a key the cipher takes (its
# key size equal to its block size, as for AES-128).
#
# As a MAC (mac.bend): ~CrXcbcKey<K>, ~CrXcbc.key(..), ~CrXcbc.mac(..),
# ~CrXcbc.verify(..), verify the interface's named default, so the MAC laws
# hold for XCBC over every cipher (LAWS.bend: xcbc_accepts).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./mac.bend as Mc
import ./octets.bend as O

# one block of bytes encrypted (a string the format refuses stays as it is)
def cr.xcbc.encb(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, x: Maybe<&2, Blk>, +o: B.Octets) -> B.Octets:
  match x:
    case None{}:
      o
    case Some{b}:
      blk_to(enc(k, b))

def cr.xcbc.e(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +o: B.Octets) -> B.Octets:
  cr.xcbc.encb(~K, ~Blk, ~enc, ~blk_to, k, blk_of(o), o)

# An XCBC key: the cipher's key schedule of K1, and K2 and K3 as bytes
type CrXcbcKey<-K: Data> is Data:
  CrXcbcKey{k1: K, k2: B.Octets, k3: B.Octets}

def cr.xcbc.key.of(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K) -> Result<&2, &2, Cr.CrError, CrXcbcKey<K>>:
  +k2 = cr.xcbc.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.rep(bsize, 2))
  +k3 = cr.xcbc.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.rep(bsize, 3))
  Result.map(&2, &2, Cr.CrError, K, CrXcbcKey<K>, k1 => CrXcbcKey{k1, k2, k3}, key(cr.xcbc.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.rep(bsize, 1))))

# The key from a raw key K (refused when the cipher refuses K or K1)
def CrXcbc.key(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, o: B.Octets) -> Result<&2, &2, Cr.CrError, CrXcbcKey<K>>:
  Result.bind(&2, &2, Cr.CrError, K, CrXcbcKey<K>, key(o), k => cr.xcbc.key.of(~K, ~Blk, ~bsize, ~key, ~enc, ~blk_of, ~blk_to, k))

def cr.xcbc.full(full: Bool, +bsize: Nat, +k2: B.Octets, +k3: B.Octets, +p: B.Octets) -> B.Octets:
  match full:
    case True{}:
      O.CrOct.xor(p, k2)
    case False{}:
      O.CrOct.xor(B.Octets.append(p, B.Octets.cons(128, B.Octets.zeros(Nat.sub(bsize, Nat.add(B.Octets.len(p), 1n))))), k3)

# the CBC-MAC over the pieces from E = e; the last piece is whole or short
def cr.xcbc.go(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k1: K, +k2: B.Octets, +k3: B.Octets, ps: List<&2, List<&2, U32>>, +e: B.Octets) -> B.Octets:
  match ps:
    case Nil{}:
      cr.xcbc.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k1, O.CrOct.xor(cr.xcbc.full(False{}, bsize, k2, k3, B.Octets.empty()), e))
    case Con{p, t}:
      match t:
        case Nil{}:
          +po = B.Octets.of_list(p)
          cr.xcbc.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k1, O.CrOct.xor(cr.xcbc.full(Nat.is_eq(B.Octets.len(po), bsize), bsize, k2, k3, po), e))
        case Con{q, u}:
          cr.xcbc.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k1, k2, k3, Con{q, u}, cr.xcbc.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k1, O.CrOct.xor(B.Octets.of_list(p), e)))

# The tag of m (one block)
def CrXcbc.mac(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrXcbcKey<K>, m: B.Octets) -> B.Octets:
  match kk:
    case CrXcbcKey{+k1, +k2, +k3}:
      cr.xcbc.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k1, k2, k3, O.CrOct.pieces(bsize, B.Octets.to_list(m)), B.Octets.zeros(bsize))

# RFC 3566's AES-XCBC-MAC-96: the tag's first 12 bytes
def CrXcbc.mac96(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrXcbcKey<K>, m: B.Octets) -> B.Octets:
  B.Octets.take(12n, CrXcbc.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, m))

# whether t is m's tag (every byte compared; the MAC interface's default)
def CrXcbc.verify(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrXcbcKey<K>, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~CrXcbcKey<K>, ~CrXcbc.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to), kk, m, t)
