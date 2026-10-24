# Michael, the message integrity code of TKIP (IEEE Std 802.11i-2004; the
# algorithm as A. Wool, IEEE Trans. Wireless Commun. 3(5), 2004, Fig. 1,
# and Huang, Seberry, Susilo and Bunder, LNCS 3823, 2005, Algorithms 2.1
# and 2.2, describe it; README.md): a 64-bit tag under a 64-bit key, over
# 32-bit words, little-endian (the byte order those sources do not state;
# IEEE 802.11-2012 M.6.3's TKIP vector and IEEE 802.11-2024's Annex J.2.1
# vectors confirm it: README.md). With the key (K0, K1) as two
# little-endian words, (L, R) = (K0, K1); the message is padded with the
# byte 0x5a and four to seven zero bytes to a multiple of four bytes; each
# word M_i is taken in by L = L xor M_i, (L, R) = b(L, R), where b is
#   R ^= L <<< 17; L += R; R ^= XSWAP(L); L += R;
#   R ^= L <<< 3;  L += R; R ^= L >>> 2;   L += R
# (XSWAP swaps the two bytes of each 16-bit half); the tag is L and R,
# little-endian. Michael was designed for the old hardware TKIP runs on,
# for a security level of only about 20 bits: it is here for TKIP.
#
# It streams through the engine with four-byte blocks (~last = 3). As a MAC
# the crypto package adapts it (crypto/inst_michael.bend).
import Base
import ../bytes/bytes.bend as B
import ./hashes.bend as Hs

# the block function b
def hs.michael.b(lr: Hs.HsW2) -> Hs.HsW2:
  match lr:
    case Hs.HsW2{+l0, r0}:
      +r1 = U32.xor(r0, Hs.hs.rotl(l0, 17n))
      +l1 = U32.add(l0, r1)
      +r2 = U32.xor(r1, U32.or(U32.shrn(U32.and(4278255360, l1), 8n), U32.shln(U32.and(16711935, l1), 8n)))
      +l2 = U32.add(l1, r2)
      +r3 = U32.xor(r2, Hs.hs.rotl(l2, 3n))
      +l3 = U32.add(l2, r3)
      +r4 = U32.xor(r3, Hs.hs.rotl(l3, 30n))
      Hs.HsW2{U32.add(l3, r4), r4}

def hs.michael.word(lr: Hs.HsW2, w: U32) -> Hs.HsW2:
  match lr:
    case Hs.HsW2{l, r}:
      hs.michael.b(Hs.HsW2{U32.xor(l, w), r})

# One four-byte word (any other length leaves the value unchanged)
def HsMichael.compress(lr: Hs.HsW2, blk: List<&2, U32>) -> Hs.HsW2:
  match blk:
    case [b0, b1, b2, b3]:
      hs.michael.word(lr, Hs.hs.le(b0, b1, b2, b3))
    case _:
      lr

# The key: eight bytes, as (K0, K1) (HsBadKeyLength otherwise)
def hs.michael.key(xs: List<&2, U32>) -> Result<&2, &2, Hs.HsError, Hs.HsW2>:
  match xs:
    case [a0, a1, a2, a3, b0, b1, b2, b3]:
      Done{Hs.HsW2{Hs.hs.le(a0, a1, a2, a3), Hs.hs.le(b0, b1, b2, b3)}}
    case _:
      Fail{Hs.HsBadKeyLength{B.len(xs)}}

def HsMichael.key(o: B.Octets) -> Result<&2, &2, Hs.HsError, Hs.HsW2>:
  hs.michael.key(B.Octets.to_list(o))

# the state before any byte, under a key
def HsMichael.init(k: Hs.HsW2) -> Hs.HsMdState<Hs.HsW2>:
  Hs.HsMd.start(~Hs.HsW2, k)

def HsMichael.update(s: Hs.HsMdState<Hs.HsW2>, o: B.Octets) -> Hs.HsMdState<Hs.HsW2>:
  Hs.HsMd.update(~Hs.HsW2, ~HsMichael.compress, ~3, s, o)

# the padding after cnt bytes of an unfinished word: 0x5a, then four to
# seven zeros, to a whole number of words
def hs.michael.pad(cnt: U32) -> List<&2, U32>:
  Con{90, B.zeros(U32.to_nat(U32.add(4, U32.and(U32.sub(3, cnt), 3))))}

# the tag of the bytes so far
def HsMichael.final(+s: Hs.HsMdState<Hs.HsW2>) -> B.Octets:
  Hs.HsW2.le(Hs.HsMd.cv(~Hs.HsW2, Hs.HsMd.update_list(~Hs.HsW2, ~HsMichael.compress, ~3, s, hs.michael.pad(Hs.HsMd.count(~Hs.HsW2, s)))))

# The tag in one call
def HsMichael.mic(k: Hs.HsW2, o: B.Octets) -> B.Octets:
  HsMichael.final(HsMichael.update(HsMichael.init(k), o))
