# CMAC (NIST SP 800-38B; RFC 4493 for AES-CMAC), a MAC over any 128-bit
# block cipher (only its encryption is used; see cipher-modes.bend for the
# template arguments).
#   L = E(0^128), K1 = dbl(L), K2 = dbl(K1)
#   dbl(X) = X << 1, xor 0x87 into the last byte when X's top bit was set
#   the message in 16-byte blocks M_1 .. M_n (n >= 1); the last is xored with
#   K1 if it is whole, else padded with 0x80 0x00 .. and xored with K2;
#   the MAC is the last block of their CBC encryption (IV 0).
# A message may arrive in pieces: start, update (any number of times) and
# finish give the MAC of the pieces joined.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M

# Subkeys

def Cmac.dbl(b: M.CmBlock) -> M.CmBlock:
  match b:
    case M.CmBlock{+w0, +w1, +w2, +w3}:
      M.CmBlock{U32.or(U32.shl(w0), U32.shrn(w1, 31n)), U32.or(U32.shl(w1), U32.shrn(w2, 31n)), U32.or(U32.shl(w2), U32.shrn(w3, 31n)), U32.xor(U32.shl(w3), U32.and(135, M.cm.mask(U32.shrn(w0, 31n))))}

def cmac.k1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K) -> M.CmBlock:
  Cmac.dbl(enc(k, M.CmBlock.zero()))

def cmac.k2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K) -> M.CmBlock:
  Cmac.dbl(cmac.k1(~K, ~enc, k))

# the subkeys K1 and K2
def Cmac.subkey1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K) -> M.CmBlock:
  cmac.k1(~K, ~enc, k)

def Cmac.subkey2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K) -> M.CmBlock:
  cmac.k2(~K, ~enc, k)

# The state: the chaining value x, and the bytes not yet processed (at most
# 16, newest first) and their count. A full buffer is kept until the next byte
# arrives, since the last block is treated differently.
type CmacState is Data:
  CmacState{x: M.CmBlock, buf: List<&2, U32>, n: Nat}

def Cmac.start() -> CmacState:
  CmacState{M.CmBlock.zero(), Nil{}, 0n}

def cmac.push(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, full: Bool, +k: K, x: M.CmBlock, buf: List<&2, U32>, +n: Nat, b: U32) -> CmacState:
  match full:
    case True{}:
      CmacState{enc(k, M.CmBlock.xor(x, M.cm.block_of(List.reverse(&2, U32, buf)))), Con{b, Nil{}}, 1n}
    case False{}:
      CmacState{x, Con{b, buf}, 1n+n}

def cmac.step(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, s: CmacState, b: U32) -> CmacState:
  match s:
    case CmacState{x, buf, +n}:
      cmac.push(~K, ~enc, Nat.is_eq(n, 16n), k, x, buf, n, b)

def cmac.feed(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, xs: List<&2, U32>, s: CmacState) -> CmacState:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      cmac.feed(~K, ~enc, k, t, cmac.step(~K, ~enc, k, s, h))

# the state after the bytes of m
def Cmac.update(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, s: CmacState, m: B.Octets) -> CmacState:
  cmac.feed(~K, ~enc, k, B.Octets.to_list(m), s)

# the last block: whole, xor K1; partial (or empty), padded, xor K2
def cmac.last(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, full: Bool, +k: K, x: M.CmBlock, last: List<&2, U32>) -> M.CmBlock:
  match full:
    case True{}:
      enc(k, M.CmBlock.xor(M.CmBlock.xor(x, M.cm.block_of(last)), cmac.k1(~K, ~enc, k)))
    case False{}:
      enc(k, M.CmBlock.xor(M.CmBlock.xor(x, M.cm.block_of(B.append(last, Con{128, Nil{}}))), cmac.k2(~K, ~enc, k)))

# the 16-byte MAC
def Cmac.finish(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, s: CmacState) -> B.Octets:
  match s:
    case CmacState{x, buf, +n}:
      M.CmBlock.to_octets(cmac.last(~K, ~enc, Nat.is_eq(n, 16n), k, x, List.reverse(&2, U32, buf)))

# The MAC of m in one call
def Cmac.mac(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, m: B.Octets) -> B.Octets:
  Cmac.finish(~K, ~enc, k, Cmac.update(~K, ~enc, k, Cmac.start(), m))

# whether tag is m's 16-byte MAC, compared with no early exit
def Cmac.verify(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, m: B.Octets, tag: B.Octets) -> Bool:
  M.cm.ct_eq(B.Octets.to_list(Cmac.mac(~K, ~enc, k, m)), B.Octets.to_list(tag))
