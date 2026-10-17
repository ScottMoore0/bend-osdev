# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input: a 32-bit value's eight hex digits read back as
# the value; a header reads back as itself; and parsing an archive built from
# any list of entries, in either format, gives the entries back. The last
# holds for the entries an archive can hold (CpioEntry.valid: sizes that fit
# in 32 bits, a name other than "TRAILER!!!", canonical Octets).
#
# Vectors: digits in both cases, a non-digit and a short field refused, the
# crc format's checksum, the bytes of a one-file archive (computed from
# cpio(5) by hand-checked Python, ref/gen.py), and each way an archive can be
# malformed, with the error it gives.
import Base
import ../bytes/bytes.bend as B
import ./hexfield.bend as H
import ./cpio.bend as C

# Properties, for every input

law hexfield_round_trip:
  for v: U32
  {H.hexfield_decode(H.hexfield_encode(v)) == Some{v} : Maybe<&2, U32>}

law header_round_trip:
  for +h: C.CpioHeader
  {C.CpioHeader.decode(C.CpioHeader.encode(h)) == Done{C.CpioHeaderAt{h, B.Octets.empty()}} : Result<&2, &2, C.CpioError, C.CpioHeaderAt>}

law parse_build:
  for +fmt: C.CpioFormat
  for +es: List<&2, C.CpioEntry>
  for ok: C.CpioEntry.valid_all(es)
  {C.Cpio.parse(C.Cpio.build(fmt, es)) == Done{es} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# Vectors: hex fields (0x12345678 = 305419896, 0xDEADBEEF = 3735928559)

law hexfield_digits:
  {H.hexfield_encode(3735928559) == B.Octets.of_string("DEADBEEF") : B.Octets}

law hexfield_either_case:
  {H.hexfield_decode(B.Octets.of_string("deadBEEF")) == Some{3735928559} : Maybe<&2, U32>}

law hexfield_order:
  {H.hexfield_decode(B.Octets.of_string("12345678")) == Some{305419896} : Maybe<&2, U32>}

law hexfield_not_digit:
  {H.hexfield_decode(B.Octets.of_string("0000000g")) == None{} : Maybe<&2, U32>}

law hexfield_short:
  {H.hexfield_decode(B.Octets.of_string("1234567")) == None{} : Maybe<&2, U32>}

# Vectors: archives

# "hello": 104 + 101 + 108 + 108 + 111
law checksum_hello:
  {C.Cpio.checksum(B.Octets.of_string("hello")) == 532 : U32}

# the file "a" (mode 0100644 = 33188) holding "hi", then the trailer
law one_file_archive:
  {B.Octets.hex(C.Cpio.build(C.CpioNewc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))])) == "30373037303130303030303030303030303038314134303030303030303030303030303030303030303030303031303030303030303030303030303030323030303030303030303030303030303030303030303030303030303030303030303030303030303230303030303030306100686900003037303730313030303030303030303030303030303030303030303030303030303030303030303030303030303130303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030423030303030303030545241494c455221212100000000" : String}

law empty_archive_newc:
  {C.Cpio.parse(C.Cpio.build(C.CpioNewc{}, [])) == Done{[]} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

law empty_archive_crc:
  {C.Cpio.parse(C.Cpio.build(C.CpioCrc{}, [])) == Done{[]} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# bytes after the trailer (an initramfs padded to a block) are ignored
law trailing_bytes:
  {C.Cpio.parse(B.Octets.append(C.Cpio.build(C.CpioCrc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]), B.Octets.zeros(12n))) == Done{[C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# Vectors: malformed archives

law reject_empty:
  {C.Cpio.parse(B.Octets.empty()) == Fail{C.CpioNoTrailer{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# the one-file archive without its trailer (the entry is 116 bytes)
law reject_no_trailer:
  {C.Cpio.parse(B.Octets.take(116n, C.Cpio.build(C.CpioNewc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]))) == Fail{C.CpioNoTrailer{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

law reject_truncated_header:
  {C.Cpio.parse(B.Octets.take(100n, C.Cpio.build(C.CpioNewc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]))) == Fail{C.CpioTruncated{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

law reject_truncated_data:
  {C.Cpio.parse(B.Octets.take(113n, C.Cpio.build(C.CpioNewc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]))) == Fail{C.CpioTruncated{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# 070707 (the old portable "odc" format) is not a newc or crc magic
law reject_magic:
  {C.Cpio.parse(B.Octets.append(B.Octets.of_string("070707"), B.Octets.drop(6n, C.Cpio.build(C.CpioNewc{}, [])))) == Fail{C.CpioBadMagic{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

law reject_hex:
  {C.Cpio.parse(B.Octets.append(B.Octets.of_string("0707010000000G"), B.Octets.drop(14n, C.Cpio.build(C.CpioNewc{}, [])))) == Fail{C.CpioBadHex{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# the crc archive with its data's first byte changed ("hi" to "Xi")
law reject_checksum:
  {C.Cpio.parse(B.Octets.append(B.Octets.take(112n, C.Cpio.build(C.CpioCrc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))])), B.Octets.append(B.Octets.of_string("X"), B.Octets.drop(113n, C.Cpio.build(C.CpioCrc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]))))) == Fail{C.CpioBadChecksum{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# the same archive in the newc format, whose check field is ignored, reads
law newc_ignores_check:
  {C.Cpio.parse(B.Octets.append(B.Octets.take(112n, C.Cpio.build(C.CpioNewc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))])), B.Octets.append(B.Octets.of_string("X"), B.Octets.drop(113n, C.Cpio.build(C.CpioNewc{}, [C.CpioEntry.file("a", 33188, B.Octets.of_string("hi"))]))))) == Done{[C.CpioEntry.file("a", 33188, B.Octets.of_string("Xi"))]} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

law reject_name_size:
  {C.Cpio.parse(C.CpioHeader.encode(C.CpioHeader{C.CpioNewc{}, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0})) == Fail{C.CpioBadNameSize{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# namesize 2, but the name "ab" has no NUL
law reject_no_nul:
  {C.Cpio.parse(B.Octets.append(C.CpioHeader.encode(C.CpioHeader{C.CpioNewc{}, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0}), B.Octets.of_string("ab"))) == Fail{C.CpioNoNul{}} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}

# The round trip's hypothesis is satisfiable, so parse_build is not vacuous:
# an ordinary one-file archive meets it
law valid_example:
  C.CpioEntry.valid_all([C.CpioEntry.file("hello.txt", 33188, B.Octets.of_string("hi"))])
