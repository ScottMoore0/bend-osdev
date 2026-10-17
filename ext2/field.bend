# bend-osdev-ext2: reading the little-endian fields of an on-disk record whose
# length is already known (a missing field reads as 0), and flag tests.
import Base
import ../bytes/bytes.bend as B

def Ext2Field.u8(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, i), 0)

def Ext2Field.u16(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le16_at(o, i), 0)

def Ext2Field.u32(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, i), 0)

def Ext2Field.nat(o: B.Octets, i: Nat) -> Nat:
  U32.to_nat(Ext2Field.u32(o, i))

# the 48-bit number (hi mod 2^16) * 2^32 + lo: ext4's block numbers and
# sizes are at most 48 bits, and so is a Nat today (Bend 2.0.37), so the
# high half's upper 16 bits are ignored rather than overflow
def Ext2Field.join(hi: U32, lo: U32) -> Nat:
  Nat.add(Nat.mul(Nat.mul(U32.to_nat(U32.and(hi, 65535)), 65536n), 65536n), U32.to_nat(lo))

# whether any of the bits of mask are set in flags
def Ext2Field.has(flags: U32, mask: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(flags, mask), 0))
