# bend-osdev-acpi, bgrt.bend: the Boot Graphics Resource Table, "BGRT"
# (ACPI 6.5, section 5.2, Boot Graphics Resource Table), 56 bytes:
#
#   offset  size  field
#       36     2  Version (1)
#       38     1  Status: bit 0 displayed, bits 1-2 orientation offset
#                 (0, 90, 180, 270 degrees clockwise)
#       39     1  Image Type (0: a bitmap, BMP)
#       40     8  Image Address (physical address of the image)
#       48     4  Image Offset X
#       52     4  Image Offset Y
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F

type AcpiBgrt is Data:
  AcpiBgrt{header: H.AcpiHeader, version: U32, status: U32, image_type: U32, image_address: W.W64, offset_x: U32, offset_y: U32}

def bgrt.read(ok: Bool, +h: H.AcpiHeader, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiBgrt>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{56n, B.Octets.len(o)}}
    case True{}:
      Done{AcpiBgrt{h, F.AcpiF.u16(o, 36n), F.AcpiF.u8(o, 38n), F.AcpiF.u8(o, 39n), F.AcpiF.u64(o, 40n), F.AcpiF.u32(o, 48n), F.AcpiF.u32(o, 52n)}}

def AcpiBgrt.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiBgrt>:
  match t:
    case H.AcpiSdt{+h, body}:
      +o = B.Octets.append(H.AcpiHeader.encode(h), body)
      bgrt.read(Nat.is_le(56n, B.Octets.len(o)), h, o)

def bgrt.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiBgrt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiBgrt.of_sdt(t)

def AcpiBgrt.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiBgrt>:
  bgrt.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("BGRT"), o))

def AcpiBgrt.build(t: AcpiBgrt) -> B.Octets:
  match t:
    case AcpiBgrt{H.AcpiHeader{s, l, r, c, o, tid, orv, ci, cr}, v, st, it, a, x, y}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("BGRT"), l, r, c, o, tid, orv, ci, cr}, B.Octets.concat([B.Octets.le16(v), B.Octets.of_list([st, it]), B.Octets.le64(a), B.Octets.le32(x), B.Octets.le32(y)]))
