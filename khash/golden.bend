# bend-osdev-khash, multiplicative hashing by the golden ratio (Knuth, The
# Art of Computer Programming, vol. 3, section 6.4): multiply by a constant
# near 2^w / phi^2 and keep the top bits of the product. The constants are
# the kernel's GOLDEN_RATIO_32 (0x61C88647) and GOLDEN_RATIO_64
# (0x61C8864680B583EB).
import Base
import ../word64/word64.bend as W

def KHash.golden32() -> U32:
  1640531527

def KHash.golden64() -> W.W64:
  W.W64.from_parts(1640531526, 2159379435)

# v times the constant, all 32 bits (the kernel's __hash_32)
def KHash.hash32_raw(v: U32) -> U32:
  U32.mul(v, KHash.golden32())

# the top bits bits (0 to 32) of v times the constant
def KHash.hash_32(v: U32, bits: Nat) -> U32:
  U32.shrn(KHash.hash32_raw(v), Nat.sub(32n, bits))

# the top bits bits (0 to 32) of the 64-bit product
def KHash.hash_64(v: W.W64, bits: Nat) -> U32:
  W.W64.lo(W.W64.shr(W.W64.mul(v, KHash.golden64()), Nat.sub(64n, bits)))

# an unsigned long is 64 bits here
def KHash.hash_long(v: W.W64, bits: Nat) -> U32:
  KHash.hash_64(v, bits)
