# bend-osdev-acpi, facs.bend: the Firmware ACPI Control Structure, "FACS"
# (ACPI 6.5, section 5.2.10). It has no standard header and no
# checksum; the FADT points to it. 64 bytes:
#
#   offset  size  field
#        0     4  Signature "FACS"
#        4     4  Length (64 or more)
#        8     4  Hardware Signature
#       12     4  Firmware Waking Vector (32-bit)
#       16     4  Global Lock
#       20     4  Flags (bit 0 S4BIOS_F, bit 1 64BIT_WAKE_SUPPORTED_F)
#       24     8  X Firmware Waking Vector (64-bit)
#       32     1  Version (2 from ACPI 4.0)
#       33     3  Reserved
#       36     4  OSPM Flags (bit 0 64BIT_WAKE_F)
#       40    24  Reserved
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./fields.bend as F

type AcpiFacs is Data:
  AcpiFacs{length: U32, hardware_signature: U32, waking_vector: U32, global_lock: U32, flags: U32, x_waking_vector: W.W64, version: U32, ospm_flags: U32}

def facs.p3(ok: Bool, +l: U32, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiFacs>:
  match ok:
    case False{}:
      Fail{E.AcpiBadLength{l}}
    case True{}:
      Done{AcpiFacs{l, F.AcpiF.u32(o, 8n), F.AcpiF.u32(o, 12n), F.AcpiF.u32(o, 16n), F.AcpiF.u32(o, 20n), F.AcpiF.u64(o, 24n), F.AcpiF.u8(o, 32n), F.AcpiF.u32(o, 36n)}}

def facs.p2(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiFacs>:
  match ok:
    case False{}:
      Fail{E.AcpiBadSignature{B.Octets.take(4n, o)}}
    case True{}:
      +l = F.AcpiF.u32(o, 4n)
      facs.p3(Nat.is_le(64n, U32.to_nat(l)), l, o)

def facs.p1(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiFacs>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{64n, B.Octets.len(o)}}
    case True{}:
      facs.p2(B.Octets.is_eq(B.Octets.take(4n, o), B.Octets.of_string("FACS")), o)

# the FACS at the front of o: at least 64 bytes, the signature, a length
# of at least 64
def AcpiFacs.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiFacs>:
  facs.p1(Nat.is_le(64n, B.Octets.len(o)), o)

def AcpiFacs.build(f: AcpiFacs) -> B.Octets:
  match f:
    case AcpiFacs{l, hs, wv, gl, fl, xw, v, of}:
      B.Octets.concat([B.Octets.of_string("FACS"), B.Octets.le32(64), B.Octets.le32(hs), B.Octets.le32(wv), B.Octets.le32(gl), B.Octets.le32(fl), B.Octets.le64(xw), B.Octets.of_list([v]), B.Octets.zeros(3n), B.Octets.le32(of), B.Octets.zeros(24n)])
