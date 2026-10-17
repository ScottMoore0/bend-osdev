# bend-osdev-partition, mbr.bend: the classic Master Boot Record and the
# protective MBR of a GPT disk.
#
# Layout (UEFI Specification, section 5.2.1, "Legacy Master Boot Record",
# which describes the classic layout): 440 bytes of boot code, the 4-byte disk
# signature at 440, two reserved bytes at 444, four 16-byte partition records
# at 446, and the bytes 0x55 0xAA at 510. A partition record holds the boot
# indicator (0x80: bootable), the CHS address of its first sector, the OS
# type, the CHS address of its last sector, its first LBA and its size in
# sectors (both little-endian).
#
# A CHS address is three bytes: the head; the sector (bits 0 to 5) with bits
# 8 and 9 of the cylinder above it; and the low 8 bits of the cylinder.
#
# The protective MBR (section 5.2.3) has one record: boot indicator 0, first
# CHS 0x000200, OS type 0xEE, last CHS the CHS address of the disk's last
# block (0xFFFFFF if it cannot be represented), first LBA 1, and size the
# disk's size in blocks less one (0xFFFFFFFF if that does not fit).
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

type MbrChs is Data:
  MbrChs{head: U32, sector: U32, cylinder: U32}

type MbrEntry is Data:
  MbrEntry{status: U32, first: MbrChs, os_type: U32, last: MbrChs, lba: U32, sectors: U32}

type Mbr is Data:
  Mbr{disk_signature: U32, p0: MbrEntry, p1: MbrEntry, p2: MbrEntry, p3: MbrEntry}

# The drive geometry a CHS address is computed with: heads per cylinder and
# sectors per track
type MbrGeometry is Data:
  MbrGeometry{heads: U32, sectors: U32}

# why a sector was refused
type MbrError is Data:
  MbrTooShort{}
  MbrBadSignature{}

def MbrError.show(e: MbrError) -> String:
  match e:
    case MbrTooShort{}:
      "too short"
    case MbrBadSignature{}:
      "no 0x55AA signature"

# CHS addresses

# the geometry partitioning tools use for disks without a real one: 255
# heads, 63 sectors per track
def MbrGeometry.standard() -> MbrGeometry:
  MbrGeometry{255, 63}

# the three bytes of a CHS address (head, sector and cylinder masked to 8, 6
# and 10 bits)
def MbrChs.encode(c: MbrChs) -> List<&2, U32>:
  match c:
    case MbrChs{U32{h}, U32{s}, U32{+y}}:
      [B.of_bits8(W.W64.bits.lo(8n, 24n, h)), B.of_bits8(W.W64.bits.cat(6n, 2n, W.W64.bits.lo(6n, 26n, s), W.W64.bits.lo(2n, 22n, W.W64.bits.hi(8n, 24n, y)))), B.of_bits8(W.W64.bits.lo(8n, 24n, y))]

def MbrChs.decode(a: U32, b: U32, c: U32) -> MbrChs:
  +bb = B.bits8(b)
  MbrChs{B.byte(a), U32{W.W64.bits.cat(6n, 26n, W.W64.bits.lo(6n, 2n, bb), Word.zero(26n))}, U32{W.W64.bits.cat(8n, 24n, B.bits8(c), W.W64.bits.cat(2n, 22n, W.W64.bits.hi(6n, 2n, bb), Word.zero(22n)))}}

# the address as stored: head, sector and cylinder masked to 8, 6 and 10 bits
def MbrChs.norm(c: MbrChs) -> MbrChs:
  match c:
    case MbrChs{h, s, y}:
      MbrChs{U32.and(255, h), U32.and(63, s), U32.and(1023, y)}

def MbrChs.of_lba.pick(big: Bool, +c: U32, +g: MbrGeometry, +lba: U32) -> MbrChs:
  match big:
    case True{}:
      MbrChs{255, 63, 1023}
    case False{}:
      match g:
        case MbrGeometry{+heads, +sectors}:
          MbrChs{U32.mod(U32.div(lba, sectors), heads), U32.add(U32.mod(lba, sectors), 1), c}

# the CHS address of a block in a geometry; (255, 63, 1023), stored as
# 0xFFFFFF, past cylinder 1023
def MbrChs.of_lba(+g: MbrGeometry, +lba: U32) -> MbrChs:
  match g:
    case MbrGeometry{+heads, +sectors}:
      +c = U32.div(lba, U32.mul(heads, sectors))
      MbrChs.of_lba.pick(U32.is_gt(c, 1023), c, g, lba)

# Partition records

def MbrEntry.empty() -> MbrEntry:
  MbrEntry{0, MbrChs{0, 0, 0}, 0, MbrChs{0, 0, 0}, 0, 0}

def MbrEntry.is_used(e: MbrEntry) -> Bool:
  match e:
    case MbrEntry{status, first, os_type, last, lba, sectors}:
      Bool.not(U32.is_eq(os_type, 0))

def MbrEntry.is_bootable(e: MbrEntry) -> Bool:
  match e:
    case MbrEntry{status, first, os_type, last, lba, sectors}:
      U32.is_eq(status, 128)

# the record as stored: status and OS type masked to 8 bits, the CHS
# addresses as MbrChs.norm
def MbrEntry.norm(e: MbrEntry) -> MbrEntry:
  match e:
    case MbrEntry{status, first, os_type, last, lba, sectors}:
      MbrEntry{U32.and(255, status), MbrChs.norm(first), U32.and(255, os_type), MbrChs.norm(last), lba, sectors}

def MbrEntry.encode(e: MbrEntry) -> List<&2, U32>:
  match e:
    case MbrEntry{status, first, os_type, last, lba, sectors}:
      Con{B.byte(status), B.append(MbrChs.encode(first), Con{B.byte(os_type), B.append(MbrChs.encode(last), B.append(B.le32(lba), B.le32(sectors)))})}

def MbrEntry.decode.go(l: Maybe<&2, U32>, n: Maybe<&2, U32>, a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32) -> Maybe<&2, MbrEntry>:
  match l n:
    case Some{x} Some{y}:
      Some{MbrEntry{B.byte(a0), MbrChs.decode(a1, a2, a3), B.byte(a4), MbrChs.decode(a5, a6, a7), x, y}}
    case _ _:
      None{}

def MbrEntry.decode(xs: List<&2, U32>) -> Maybe<&2, MbrEntry>:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, t}}}}}}}}}}}}}}}}:
      MbrEntry.decode.go(B.le32.head([a8, a9, a10, a11]), B.le32.head([a12, a13, a14, a15]), a0, a1, a2, a3, a4, a5, a6, a7)
    case _:
      None{}

# The whole sector

def Mbr.norm(m: Mbr) -> Mbr:
  match m:
    case Mbr{sig, p0, p1, p2, p3}:
      Mbr{sig, MbrEntry.norm(p0), MbrEntry.norm(p1), MbrEntry.norm(p2), MbrEntry.norm(p3)}

# n bytes: xs masked, cut or padded with zeros
def Mbr.fit(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Con{0, Mbr.fit(p, Nil{})}
        case Con{h, t}:
          Con{B.byte(h), Mbr.fit(p, t)}

# bytes 440 to 511
def Mbr.encode.tail(m: Mbr) -> List<&2, U32>:
  match m:
    case Mbr{sig, p0, p1, p2, p3}:
      B.append(B.le32(sig), Con{0, Con{0, B.append(MbrEntry.encode(p0), B.append(MbrEntry.encode(p1), B.append(MbrEntry.encode(p2), B.append(MbrEntry.encode(p3), [85, 170]))))}})

# the 512-byte sector: the boot code (cut or padded with zeros to 440 bytes),
# then the table
def Mbr.build(boot: B.Octets, m: Mbr) -> B.Octets:
  B.Octets.of_list(B.append(Mbr.fit(440n, B.Octets.to_list(boot)), Mbr.encode.tail(m)))

def Mbr.parse.fin(e0: Maybe<&2, MbrEntry>, e1: Maybe<&2, MbrEntry>, e2: Maybe<&2, MbrEntry>, e3: Maybe<&2, MbrEntry>, s: Maybe<&2, U32>) -> Result<&2, &2, MbrError, Mbr>:
  match e0 e1 e2 e3 s:
    case Some{a} Some{b} Some{c} Some{d} Some{x}:
      Done{Mbr{x, a, b, c, d}}
    case _ _ _ _ _:
      Fail{MbrTooShort{}}

def Mbr.parse.sig(ok: Bool, +r: List<&2, U32>) -> Result<&2, &2, MbrError, Mbr>:
  match ok:
    case True{}:
      Mbr.parse.fin(MbrEntry.decode(B.drop(6n, r)), MbrEntry.decode(B.drop(22n, r)), MbrEntry.decode(B.drop(38n, r)), MbrEntry.decode(B.drop(54n, r)), B.le32_at(r, 0n))
    case False{}:
      Fail{MbrBadSignature{}}

def Mbr.byte_is(m: Maybe<&2, U32>, v: U32) -> Bool:
  match m:
    case Some{x}:
      U32.is_eq(x, v)
    case None{}:
      False{}

def Mbr.parse.len(short: Bool, +r: List<&2, U32>) -> Result<&2, &2, MbrError, Mbr>:
  match short:
    case True{}:
      Fail{MbrTooShort{}}
    case False{}:
      Mbr.parse.sig(Bool.and(Mbr.byte_is(B.at(r, 70n), 85), Mbr.byte_is(B.at(r, 71n), 170)), r)

# bytes 440 to 511
def Mbr.parse.tail(+r: List<&2, U32>) -> Result<&2, &2, MbrError, Mbr>:
  Mbr.parse.len(Maybe.is_none(&2, U32, B.at(r, 71n)), r)

# the table of a 512-byte sector (the boot code is not read)
def Mbr.parse(o: B.Octets) -> Result<&2, &2, MbrError, Mbr>:
  Mbr.parse.tail(B.drop(440n, B.Octets.to_list(o)))

# the 440 bytes of boot code
def Mbr.boot_code(o: B.Octets) -> B.Octets:
  B.Octets.take(440n, o)

# The protective MBR of a GPT disk whose last block is last_lba

def Mbr.protective.size(big: Bool, lo: U32) -> U32:
  match big:
    case True{}:
      4294967295
    case False{}:
      lo

def Mbr.protective_with(g: MbrGeometry, +last_lba: W.W64) -> Mbr:
  +n = Mbr.protective.size(Bool.not(U32.is_eq(W.W64.hi(last_lba), 0)), W.W64.lo(last_lba))
  Mbr{0, MbrEntry{0, MbrChs{0, 2, 0}, 238, MbrChs.of_lba(g, n), 1, n}, MbrEntry.empty(), MbrEntry.empty(), MbrEntry.empty()}

def Mbr.protective(last_lba: W.W64) -> Mbr:
  Mbr.protective_with(MbrGeometry.standard(), last_lba)

# whether the first record has OS type 0xEE (a GPT disk)
def Mbr.is_protective(m: Mbr) -> Bool:
  match m:
    case Mbr{sig, MbrEntry{status, first, os_type, last, lba, sectors}, p1, p2, p3}:
      U32.is_eq(os_type, 238)
