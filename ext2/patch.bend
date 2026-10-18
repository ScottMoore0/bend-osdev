# bend-osdev-ext2: writing the little-endian fields of an on-disk record in
# place (the writer's mirror of field.bend). A record is changed by replacing
# bytes at an offset; every byte the change does not cover is kept, so fields
# this package does not know survive a write.
import Base
import ../bytes/bytes.bend as B

# o with the bytes of data from offset off on (o's length is kept when the
# data fits; o is never cut short)
def Ext2Patch.bytes(+o: B.Octets, +off: Nat, +data: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.take(off, o), B.Octets.append(data, B.Octets.drop(Nat.add(off, B.Octets.len(data)), o)))

def Ext2Patch.u8(+o: B.Octets, +off: Nat, v: U32) -> B.Octets:
  Ext2Patch.bytes(o, off, B.Octets.of_list([v]))

def Ext2Patch.u16(+o: B.Octets, +off: Nat, v: U32) -> B.Octets:
  Ext2Patch.bytes(o, off, B.Octets.le16(v))

def Ext2Patch.u32(+o: B.Octets, +off: Nat, v: U32) -> B.Octets:
  Ext2Patch.bytes(o, off, B.Octets.le32(v))

# a Nat's low and high 32-bit halves (U32.from_nat wraps; 2^32 is never
# built as a Nat)
def Ext2Patch.lo32(+n: Nat) -> U32:
  U32.from_nat(n)

def Ext2Patch.hi32(+n: Nat) -> U32:
  U32.from_nat(Nat.div(Nat.div(n, 65536n), 65536n))

# a Nat split over a 32-bit low field at lo and a high field at hi of
# hi_bytes bytes (2 or 4; 0 for none: the high half is then dropped)
def Ext2Patch.split.hi(+o: B.Octets, hi_bytes: Nat, +hi: Nat, v: U32) -> B.Octets:
  match hi_bytes:
    case 2n:
      Ext2Patch.u16(o, hi, v)
    case 4n:
      Ext2Patch.u32(o, hi, v)
    case _:
      o

def Ext2Patch.split(+o: B.Octets, +lo: Nat, +hi: Nat, hi_bytes: Nat, +n: Nat) -> B.Octets:
  Ext2Patch.split.hi(Ext2Patch.u32(o, lo, Ext2Patch.lo32(n)), hi_bytes, hi, Ext2Patch.hi32(n))

def Ext2Patch.split16.go(wide: Bool, +o: B.Octets, +hi: Nat, v: U32) -> B.Octets:
  match wide:
    case True{}:
      Ext2Patch.u16(o, hi, v)
    case False{}:
      o

# a 16-bit low field and a 16-bit high field (group descriptor counts)
def Ext2Patch.split16(+o: B.Octets, +lo: Nat, +hi: Nat, wide: Bool, +v: U32) -> B.Octets:
  Ext2Patch.split16.go(wide, Ext2Patch.u16(o, lo, U32.and(65535, v)), hi, U32.shrn(v, 16n))
