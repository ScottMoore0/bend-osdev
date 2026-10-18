# bend-osdev-acpi, header.bend: the system description table header that
# every table but the RSDP and the FACS begins with (ACPI 6.5, section
# 5.2.6), and the checks every such table must pass.
#
#   offset  size  field
#        0     4  Signature
#        4     4  Length (of the whole table, header included)
#        8     1  Revision
#        9     1  Checksum (all Length bytes sum to 0 mod 256)
#       10     6  OEMID
#       16     8  OEM Table ID
#       24     4  OEM Revision
#       28     4  Creator ID
#       32     4  Creator Revision
#
# Fields are little-endian. The four text fields are kept as Octets, exactly
# as stored (ACPI pads them with spaces or NULs; nothing is trimmed).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./checksum.bend as C

type AcpiHeader is Data:
  AcpiHeader{signature: B.Octets, length: U32, revision: U32, checksum: U32, oem_id: B.Octets, oem_table_id: B.Octets, oem_revision: U32, creator_id: B.Octets, creator_revision: U32}

def AcpiHeader.size() -> Nat:
  36n

def AcpiHeader.signature(h: AcpiHeader) -> B.Octets:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      s

def AcpiHeader.length(h: AcpiHeader) -> U32:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      l

def AcpiHeader.revision(h: AcpiHeader) -> U32:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      r

def AcpiHeader.checksum(h: AcpiHeader) -> U32:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      c

def AcpiHeader.oem_id(h: AcpiHeader) -> B.Octets:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      o

def AcpiHeader.oem_table_id(h: AcpiHeader) -> B.Octets:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      t

def AcpiHeader.oem_revision(h: AcpiHeader) -> U32:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      orv

def AcpiHeader.creator_id(h: AcpiHeader) -> B.Octets:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      ci

def AcpiHeader.creator_revision(h: AcpiHeader) -> U32:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      cr

# Writing: the 36 bytes, fields as given (the text fields must have their
# sizes, 4, 6, 8 and 4 bytes, and revision and checksum must be bytes, for
# decode to give the header back; LAWS.bend: header_round_trip)

def hd.byte(v: U32) -> B.Octets:
  B.Octets.of_list([v])

def AcpiHeader.encode(h: AcpiHeader) -> B.Octets:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      B.Octets.append(s, B.Octets.append(B.Octets.le32(l), B.Octets.append(hd.byte(r), B.Octets.append(hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))))

# Reading: each field split off the front in turn

def hd.short(+o: B.Octets) -> E.AcpiError:
  E.AcpiTooShort{36n, B.Octets.len(o)}

def hd.u32(o: B.Octets) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, 0n), 0)

def hd.u8.list(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

def hd.u8(o: B.Octets) -> U32:
  hd.u8.list(B.Octets.to_list(o))

def hd.d9(ok: Bool, +all: B.Octets, s: B.Octets, l: U32, r: U32, c: U32, o: B.Octets, t: B.Octets, orv: U32, ci: B.Octets, f: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match ok:
    case False{}:
      Fail{hd.short(all)}
    case True{}:
      Done{AcpiHeader{s, l, r, c, o, t, orv, ci, hd.u32(f)}}

def hd.d8(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets, l: U32, r: U32, c: U32, o: B.Octets, t: B.Octets, orv: U32) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, +rest}}:
      hd.d9(Nat.is_le(4n, B.Octets.len(rest)), all, s, l, r, c, o, t, orv, f, rest)

def hd.d7(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets, l: U32, r: U32, c: U32, o: B.Octets, t: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d8(B.Octets.split_at(4n, rest), all, s, l, r, c, o, t, hd.u32(f))

def hd.d6(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets, l: U32, r: U32, c: U32, o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d7(B.Octets.split_at(4n, rest), all, s, l, r, c, o, f)

def hd.d5(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets, l: U32, r: U32, c: U32) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d6(B.Octets.split_at(8n, rest), all, s, l, r, c, f)

def hd.d4(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets, l: U32, r: U32) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d5(B.Octets.split_at(6n, rest), all, s, l, r, hd.u8(f))

def hd.d3(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets, l: U32) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d4(B.Octets.split_at(1n, rest), all, s, l, hd.u8(f))

def hd.d2(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets, s: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d3(B.Octets.split_at(1n, rest), all, s, hd.u32(f))

def hd.d1(m: Maybe<&2, B.OctetsSplit>, +all: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  match m:
    case None{}:
      Fail{hd.short(all)}
    case Some{B.OctetsSplit{f, rest}}:
      hd.d2(B.Octets.split_at(4n, rest), all, f)

# the header in the first 36 bytes, fields as stored (unchecked);
# AcpiTooShort if there are fewer
def AcpiHeader.decode(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiHeader>:
  hd.d1(B.Octets.split_at(4n, o), o)

# The checks every table passes: a length from 36 bytes to the bytes given,
# and a checksum of zero over that length

def sdt.c3(ok: Bool, +raw: B.Octets) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match ok:
    case True{}:
      Done{raw}
    case False{}:
      Fail{E.AcpiBadChecksum{C.AcpiChecksum.sum(raw)}}

def sdt.c2(ok: Bool, +l: U32, +o: B.Octets) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match ok:
    case True{}:
      +raw = B.Octets.take(U32.to_nat(l), o)
      sdt.c3(C.AcpiChecksum.ok(raw), raw)
    case False{}:
      Fail{E.AcpiBadLength{l}}

def sdt.c1(m: Maybe<&2, U32>, +o: B.Octets) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match m:
    case None{}:
      Fail{E.AcpiTooShort{36n, B.Octets.len(o)}}
    case Some{+l}:
      sdt.c2(Bool.and(Nat.is_le(36n, U32.to_nat(l)), Nat.is_le(U32.to_nat(l), B.Octets.len(o))), l, o)

# a table's bytes, as far as its length field says (all of o if o is
# shorter than 8 bytes); bytes after the length are not part of the table
def AcpiSdt.bytes(+o: B.Octets) -> B.Octets:
  B.Octets.take(U32.to_nat(Maybe.default(&2, U32, B.Octets.le32_at(o, 4n), 4294967295)), o)

# the table at the front of o, checked: its length field from 36 to the
# bytes given (AcpiTooShort, AcpiBadLength), and its bytes summing to zero
# (AcpiBadChecksum). Answers the table's bytes (AcpiSdt.bytes(o)).
def AcpiSdt.check(+o: B.Octets) -> Result<&2, &2, E.AcpiError, B.Octets>:
  sdt.c1(B.Octets.le32_at(o, 4n), o)

# A checked table, split into its header and its body

type AcpiSdt is Data:
  AcpiSdt{header: AcpiHeader, body: B.Octets}

def sdt.split(+raw: B.Octets, r: Result<&2, &2, E.AcpiError, AcpiHeader>) -> Result<&2, &2, E.AcpiError, AcpiSdt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{h}:
      Done{AcpiSdt{h, B.Octets.drop(36n, raw)}}

def sdt.parse.go(r: Result<&2, &2, E.AcpiError, B.Octets>) -> Result<&2, &2, E.AcpiError, AcpiSdt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+raw}:
      sdt.split(raw, AcpiHeader.decode(raw))

# the table at the front of o, checked, as its header and body
def AcpiSdt.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSdt>:
  sdt.parse.go(AcpiSdt.check(o))

def AcpiSdt.header(t: AcpiSdt) -> AcpiHeader:
  match t:
    case AcpiSdt{h, b}:
      h

def AcpiSdt.body(t: AcpiSdt) -> B.Octets:
  match t:
    case AcpiSdt{h, b}:
      b

def sdt.sig.pick(ok: Bool, +s: B.Octets, t: AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiSdt>:
  match ok:
    case True{}:
      Done{t}
    case False{}:
      Fail{E.AcpiBadSignature{s}}

def sdt.sig.go(+sig: B.Octets, r: Result<&2, &2, E.AcpiError, AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiSdt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+t}:
      +s = AcpiHeader.signature(AcpiSdt.header(t))
      sdt.sig.pick(B.Octets.is_eq(s, sig), s, t)

# the same, also requiring the signature sig (AcpiBadSignature)
def AcpiSdt.parse_sig(+sig: B.Octets, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSdt>:
  sdt.sig.go(sig, AcpiSdt.parse(o))

# Building: a header and a body as a table, with the length and checksum
# fields computed (the header's own length and checksum are ignored)
def AcpiSdt.build(h: AcpiHeader, +body: B.Octets) -> B.Octets:
  match h:
    case AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      +len = U32.from_nat(Nat.add(36n, B.Octets.len(body)))
      C.AcpiChecksum.fix(9n, B.Octets.append(AcpiHeader.encode(AcpiHeader{s, len, r, 0, o, t, orv, ci, cr}), body))

def hd.spaces(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{32, hd.spaces(p)}

def hd.fit(+n: Nat, +o: B.Octets) -> B.Octets:
  +h = B.Octets.take(n, o)
  B.Octets.append(h, B.Octets.of_list(hd.spaces(Nat.sub(n, B.Octets.len(h)))))

# a header for building: signature, revision, OEMID, OEM table ID, with OEM
# revision 1 and creator "BEND" revision 1 (text fields fitted to size)
def AcpiHeader.make(sig: B.Octets, r: U32, oem: B.Octets, tid: B.Octets) -> AcpiHeader:
  AcpiHeader{hd.fit(4n, sig), 0, r, 0, hd.fit(6n, oem), hd.fit(8n, tid), 1, B.Octets.of_string("BEND"), 1}
