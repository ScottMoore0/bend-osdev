# bend-osdev-acpi, rsdp.bend: the Root System Description Pointer (ACPI
# 6.5, section 5.2.5.3), the structure that leads to every other
# table:
#
#   offset  size  field
#        0     8  Signature "RSD PTR "
#        8     1  Checksum (bytes 0 to 19 sum to 0 mod 256)
#        9     6  OEMID
#       15     1  Revision (0 for ACPI 1.0, 2 from ACPI 2.0)
#       16     4  RsdtAddress (32-bit physical address of the RSDT)
#   from revision 2:
#       20     4  Length (of the whole structure, 36)
#       24     8  XsdtAddress (64-bit physical address of the XSDT)
#       32     1  Extended Checksum (all Length bytes sum to 0 mod 256)
#       33     3  Reserved
#
# Section 5.2.5.1 says where firmware puts it on IA-PC systems (the first
# KB of the EBDA, or 0xE0000 to 0xFFFFF, on a 16-byte boundary);
# AcpiRsdp.find searches a region's bytes, and UEFI systems hand the
# address over in the EFI configuration table instead.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./checksum.bend as C
import ./fields.bend as F

# the revision 2 fields
type AcpiRsdpExt is Data:
  AcpiRsdpExt{length: U32, xsdt_address: W.W64}

type AcpiRsdp is Data:
  AcpiRsdp{oem_id: B.Octets, revision: U32, rsdt_address: U32, ext: Maybe<&2, AcpiRsdpExt>}

def AcpiRsdp.signature() -> B.Octets:
  B.Octets.of_string("RSD PTR ")

def AcpiRsdp.revision(r: AcpiRsdp) -> U32:
  match r:
    case AcpiRsdp{o, v, a, x}:
      v

def AcpiRsdp.rsdt_address(r: AcpiRsdp) -> U32:
  match r:
    case AcpiRsdp{o, v, a, x}:
      a

def AcpiRsdp.ext(r: AcpiRsdp) -> Maybe<&2, AcpiRsdpExt>:
  match r:
    case AcpiRsdp{o, v, a, x}:
      x

def rs.xsdt(m: Maybe<&2, AcpiRsdpExt>) -> W.W64:
  match m:
    case None{}:
      W.W64.zero()
    case Some{AcpiRsdpExt{l, a}}:
      a

# the XSDT's address (zero for a revision 0 RSDP)
def AcpiRsdp.xsdt_address(r: AcpiRsdp) -> W.W64:
  rs.xsdt(AcpiRsdp.ext(r))

def rs.checked(m: Maybe<&2, AcpiRsdpExt>) -> Nat:
  match m:
    case None{}:
      20n
    case Some{AcpiRsdpExt{l, a}}:
      U32.to_nat(l)

# how many bytes the checksums covered: 20 for revision 0, Length after
def AcpiRsdp.checked(r: AcpiRsdp) -> Nat:
  rs.checked(AcpiRsdp.ext(r))

# Reading, checked in order: at least 20 bytes, the signature, the first
# checksum; for revision 2 or later: at least 36 bytes, a Length from 36 to
# the bytes given, the extended checksum

def rs.p7(ok: Bool, +l: U32, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match ok:
    case False{}:
      Fail{E.AcpiRsdpBadExtChecksum{C.AcpiChecksum.sum(B.Octets.take(U32.to_nat(l), o))}}
    case True{}:
      Done{AcpiRsdp{F.AcpiF.bytes(o, 9n, 6n), F.AcpiF.u8(o, 15n), F.AcpiF.u32(o, 16n), Some{AcpiRsdpExt{l, F.AcpiF.u64(o, 24n)}}}}

def rs.p6(ok: Bool, +l: U32, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match ok:
    case False{}:
      Fail{E.AcpiBadLength{l}}
    case True{}:
      rs.p7(C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)), l, o)

def rs.p5(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{36n, B.Octets.len(o)}}
    case True{}:
      +l = F.AcpiF.u32(o, 20n)
      rs.p6(Bool.and(Nat.is_le(36n, U32.to_nat(l)), Nat.is_le(U32.to_nat(l), B.Octets.len(o))), l, o)

def rs.p4(v1: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match v1:
    case True{}:
      Done{AcpiRsdp{F.AcpiF.bytes(o, 9n, 6n), F.AcpiF.u8(o, 15n), F.AcpiF.u32(o, 16n), None{}}}
    case False{}:
      rs.p5(Nat.is_le(36n, B.Octets.len(o)), o)

def rs.p3(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match ok:
    case False{}:
      Fail{E.AcpiRsdpBadChecksum{C.AcpiChecksum.sum(B.Octets.take(20n, o))}}
    case True{}:
      rs.p4(U32.is_lt(F.AcpiF.u8(o, 15n), 2), o)

def rs.p2(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match ok:
    case False{}:
      Fail{E.AcpiBadSignature{B.Octets.take(8n, o)}}
    case True{}:
      rs.p3(C.AcpiChecksum.ok(B.Octets.take(20n, o)), o)

def rs.p1(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{20n, B.Octets.len(o)}}
    case True{}:
      rs.p2(B.Octets.is_eq(B.Octets.take(8n, o), AcpiRsdp.signature()), o)

# the RSDP at the front of o
def AcpiRsdp.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiRsdp>:
  rs.p1(Nat.is_le(20n, B.Octets.len(o)), o)

# Writing: 20 bytes for revision 0 or 1, 36 after (Length written as 36),
# with both checksums computed

def rs.v1(oem: B.Octets, +rev: U32, rsdt: U32) -> B.Octets:
  C.AcpiChecksum.fix(8n, B.Octets.concat([AcpiRsdp.signature(), B.Octets.of_list([0]), F.AcpiF.fit(6n, oem), B.Octets.of_list([rev]), B.Octets.le32(rsdt)]))

def rs.build(m: Maybe<&2, AcpiRsdpExt>, +first: B.Octets) -> B.Octets:
  match m:
    case None{}:
      first
    case Some{AcpiRsdpExt{l, x}}:
      C.AcpiChecksum.fix(32n, B.Octets.concat([first, B.Octets.le32(36), B.Octets.le64(x), B.Octets.zeros(4n)]))

def AcpiRsdp.build(r: AcpiRsdp) -> B.Octets:
  match r:
    case AcpiRsdp{oem, rev, rsdt, x}:
      rs.build(x, rs.v1(oem, rev, rsdt))

# Finding: the first 16-byte-aligned offset of o holding a signature and a
# good first checksum

def rs.here(+o: B.Octets, +i: Nat) -> Bool:
  Bool.and(B.Octets.is_eq(B.Octets.slice(i, 8n, o), AcpiRsdp.signature()), Bool.and(Nat.is_le(Nat.add(i, 20n), B.Octets.len(o)), C.AcpiChecksum.ok(B.Octets.slice(i, 20n, o))))

def rs.find.go(fuel: Nat, hit: Bool, +o: B.Octets, +i: Nat) -> Maybe<&2, Nat>:
  match fuel:
    case 0n:
      None{}
    case 1n+p:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          +j = Nat.add(i, 16n)
          rs.find.go(p, rs.here(o, j), o, j)

def AcpiRsdp.find(+o: B.Octets) -> Maybe<&2, Nat>:
  rs.find.go(Nat.add(Nat.div(B.Octets.len(o), 16n), 1n), rs.here(o, 0n), o, 0n)
