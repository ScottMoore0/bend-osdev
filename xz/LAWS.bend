# Properties, for every input:
#   * xz_decode never answers more output than the caller's maximum;
#   * an input whose first byte is not 0xFD is refused as bad magic, whatever
#     follows, and the empty input is truncated, whatever the parameters;
#   * an LZMA2 stream whose first chunk does not reset the dictionary is
#     corrupt, and so is one opened by a reserved control byte (0x03 to
#     0x7F), whatever follows and whatever the dictionary size and maximum;
#     the end marker alone is the empty stream;
#   * .lzma files: a valid header written and read back is itself; a bad
#     properties byte is refused (lc + lp above 4, or 225 and up); a header
#     cut short, or a stream of fewer than 5 bytes after a valid header, is
#     truncated; and whatever the input, a decoded file whose header declares
#     its size has that size.
#
# Vectors: small .xz files (made by Python's lzma module) decode to their
# data; a changed CRC32 is caught; LZMA2's dictionary sizes; small .lzma
# files (Python's lzma module, FORMAT_ALONE) of known and unknown size, and
# what goes wrong with them; the valid properties bytes; a header both ways.
#
# The decoding of LZMA data itself is not stated as a law: it is tested
# against Python's lzma module and the xz tool (ref/), on intact and
# corrupted files.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./lzma2.bend as L2
import ./xz.bend as X
import ./alone.bend as A
import ../word64/word64.bend as W

# A decoder's answer respects the maximum max: it is a failure, or output of
# at most max bytes
def xz_within(+max: U32, r: Result<&2, &2, E.XzError, B.Octets>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{o}:
      Nat.is_le(B.Octets.len(o), U32.to_nat(max))

law output_bounded:
  for +p: X.XzParams
  for i: B.Octets
  {xz_within(X.XzParams.max_out(p), X.xz_decode(p, i)) == True{} : Bool}

# A .lzma decoder's answer has the size the header declares, if it declares
# one (vacuous if the header is not read, or the decoder fails)
def alone_size_holds(hr: Result<&2, &2, E.XzError, A.XzAloneHeader>, r: Result<&2, &2, E.XzError, B.Octets>) -> Bool:
  match hr:
    case Fail{e}:
      True{}
    case Done{h}:
      match r:
        case Fail{e}:
          True{}
        case Done{o}:
          A.XzAlone.has_size(o, A.XzAloneHeader.size(h))

def alone_valid_pick(ok: Bool, +b: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      Con{b, rest}
    case False{}:
      rest

# the valid .lzma properties bytes below n, largest first
def alone_valid_below(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+(+k):
      alone_valid_pick(A.XzAlone.props_valid(U32.from_nat(k)), U32.from_nat(k), alone_valid_below(k))

law bad_magic:
  for +p: X.XzParams
  for +b: U32
  for +xs: List<&2, U32>
  for e: {U32.is_eq(B.byte(b), 253) == False{} : Bool}
  {X.xz_decode(p, B.Octets.of_list(Con{b, xs})) == Fail{E.XzBadMagic{}} : Result<&2, &2, E.XzError, B.Octets>}

law empty_input:
  for +p: X.XzParams
  {X.xz_decode(p, B.Octets.empty()) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}

law lzma2_needs_reset:
  for +d: U32
  for +m: U32
  for +xs: List<&2, U32>
  {L2.XzLzma2.decode(d, m, B.Octets.of_list(Con{2, xs})) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}

law lzma2_reserved_control:
  for +d: U32
  for +m: U32
  for +c: U32
  for +xs: List<&2, U32>
  for e1: {U32.is_lt(B.byte(c), 3) == False{} : Bool}
  for e2: {U32.is_lt(B.byte(c), 128) == True{} : Bool}
  {L2.XzLzma2.decode(d, m, B.Octets.of_list(Con{c, xs})) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}

law lzma2_end_only:
  for +d: U32
  for +m: U32
  {L2.XzLzma2.decode(d, m, B.Octets.of_list([0])) == Done{B.Octets.empty()} : Result<&2, &2, E.XzError, B.Octets>}

# Vectors

# lzma.compress(b"", check=lzma.CHECK_NONE)
law empty_file:
  {X.xz_decode(X.XzParams{64}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 0, 255, 18, 217, 65, 0, 0, 0, 0, 28, 223, 68, 33, 6, 114, 158, 122, 1, 0, 0, 0, 0, 0, 89, 90])) == Done{B.Octets.empty()} : Result<&2, &2, E.XzError, B.Octets>}

# lzma.compress(b"x", check=lzma.CHECK_CRC32): one uncompressed chunk
law one_byte:
  {X.xz_decode(X.XzParams{16}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 1, 105, 34, 222, 54, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 0, 120, 0, 0, 0, 0, 131, 22, 220, 140, 0, 1, 21, 1, 169, 99, 52, 96, 144, 66, 153, 13, 1, 0, 0, 0, 0, 1, 89, 90])) == Done{B.Octets.of_string("x")} : Result<&2, &2, E.XzError, B.Octets>}

# the same file with its block's CRC32 changed
law one_byte_bad_check:
  {X.xz_decode(X.XzParams{16}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 1, 105, 34, 222, 54, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 0, 120, 0, 0, 0, 0, 131, 22, 220, 141, 0, 1, 21, 1, 169, 99, 52, 96, 144, 66, 153, 13, 1, 0, 0, 0, 0, 1, 89, 90])) == Fail{E.XzBadCheck{}} : Result<&2, &2, E.XzError, B.Octets>}

# the empty file with its stream header's CRC32 changed
law bad_header_crc:
  {X.xz_decode(X.XzParams{64}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 0, 255, 18, 217, 64, 0, 0, 0, 0, 28, 223, 68, 33, 6, 114, 158, 122, 1, 0, 0, 0, 0, 0, 89, 90])) == Fail{E.XzBadHeaderCrc{}} : Result<&2, &2, E.XzError, B.Octets>}

# two uncompressed chunks, the first resetting the dictionary
law lzma2_uncompressed:
  {L2.XzLzma2.decode(4096, 16, B.Octets.of_list([1, 0, 1, 65, 66, 2, 0, 0, 67, 0])) == Done{B.Octets.of_string("ABC")} : Result<&2, &2, E.XzError, B.Octets>}

# the same, with a maximum of two bytes
law lzma2_too_large:
  {L2.XzLzma2.decode(4096, 2, B.Octets.of_list([1, 0, 1, 65, 66, 2, 0, 0, 67, 0])) == Fail{E.XzOutputTooLarge{}} : Result<&2, &2, E.XzError, B.Octets>}

# the dictionary sizes of LZMA2 properties bytes 0, 1, 19 and 40, and 41
# refused
law lzma2_dict_sizes:
  {[L2.XzLzma2.dict_size(0), L2.XzLzma2.dict_size(1), L2.XzLzma2.dict_size(19), L2.XzLzma2.dict_size(40), L2.XzLzma2.dict_size(41)] == [Some{4096}, Some{6144}, Some{3145728}, Some{4294967295}, None{}] : List<&2, Maybe<&2, U32>>}

# Properties, for every input: .lzma files

law alone_header_round_trip:
  for +h: A.XzAloneHeader
  for +rest: B.Octets
  for e: {A.XzAloneHeader.valid(h) == True{} : Bool}
  {A.XzAlone.header(B.Octets.append(A.XzAlone.header_bytes(h), rest)) == Done{h} : Result<&2, &2, E.XzError, A.XzAloneHeader>}

law alone_bad_props:
  for +p: A.XzAloneParams
  for +b: U32
  for +xs: List<&2, U32>
  for e: {A.XzAlone.props_valid(B.byte(b)) == False{} : Bool}
  {A.XzAlone.decode(p, B.Octets.of_list(Con{b, xs})) == Fail{E.XzBadFilterProps{}} : Result<&2, &2, E.XzError, B.Octets>}

law alone_empty:
  for +p: A.XzAloneParams
  {A.XzAlone.decode(p, B.Octets.empty()) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}

law alone_short_header:
  for +p: A.XzAloneParams
  for +b: U32
  for +xs: List<&2, U32>
  for e1: {A.XzAlone.props_valid(B.byte(b)) == True{} : Bool}
  for e2: {Nat.is_lt(List.length(&2, U32, xs), 12n) == True{} : Bool}
  {A.XzAlone.decode(p, B.Octets.of_list(Con{b, xs})) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}

law alone_short_stream:
  for +p: A.XzAloneParams
  for +h: A.XzAloneHeader
  for +xs: List<&2, U32>
  for e1: {A.XzAloneHeader.valid(h) == True{} : Bool}
  for e2: {Nat.is_lt(List.length(&2, U32, xs), 5n) == True{} : Bool}
  {A.XzAlone.decode(p, B.Octets.append(A.XzAlone.header_bytes(h), B.Octets.of_list(xs))) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}

law alone_declared_size:
  for +p: A.XzAloneParams
  for +i: B.Octets
  {alone_size_holds(A.XzAlone.header(i), A.XzAlone.decode(p, i)) == True{} : Bool}

# Vectors: .lzma files

# the valid properties bytes: lc + lp at most 4, pb at most 4 (75 of them)
law alone_props_table:
  {List.reverse(&2, U32, alone_valid_below(256n)) == [0, 1, 2, 3, 4, 9, 10, 11, 12, 18, 19, 20, 27, 28, 36, 45, 46, 47, 48, 49, 54, 55, 56, 57, 63, 64, 65, 72, 73, 81, 90, 91, 92, 93, 94, 99, 100, 101, 102, 108, 109, 110, 117, 118, 126, 135, 136, 137, 138, 139, 144, 145, 146, 147, 153, 154, 155, 162, 163, 171, 180, 181, 182, 183, 184, 189, 190, 191, 192, 198, 199, 200, 207, 208, 216] : List<&2, U32>}

# the header Python's lzma writes for an unknown size (lc 3, lp 0, pb 2, a
# 4 KiB dictionary), read, and the 13 bytes xz's defaults write (an 8 MiB
# dictionary)
law alone_header_python:
  {A.XzAlone.header(B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25])) == Done{A.XzAloneHeader{3n, 0n, 2n, 4096, None{}}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}

law alone_header_bytes:
  {A.XzAlone.header_bytes(A.XzAloneHeader{3n, 0n, 2n, 8388608, Some{W.W64.from_u32(5)}}) == B.Octets.of_list([93, 0, 0, 128, 0, 5, 0, 0, 0, 0, 0, 0, 0]) : B.Octets}

# lzma.compress(b"hello", format=lzma.FORMAT_ALONE, filters=[{"id":
# lzma.FILTER_LZMA1, "preset": 6, "dict_size": 4096}]): the size unknown,
# the end marker
law alone_unknown_size:
  {A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0])) == Done{B.Octets.of_string("hello")} : Result<&2, &2, E.XzError, B.Octets>}

# the same with its size, 5, in the header (and the end marker after it)
law alone_known_size:
  {A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0])) == Done{B.Octets.of_string("hello")} : Result<&2, &2, E.XzError, B.Octets>}

# size 0 and no end marker: the range decoder's 5 bytes alone
law alone_known_empty:
  {A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == Done{B.Octets.empty()} : Result<&2, &2, E.XzError, B.Octets>}

# a declared size of 6 for the 5 bytes: the end marker comes too soon
law alone_wrong_size:
  {A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0])) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}

# a byte after the stream
law alone_trailing:
  {A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0, 7])) == Fail{E.XzTrailingData{}} : Result<&2, &2, E.XzError, B.Octets>}

# a maximum of 4 bytes: the unknown size runs past it, the known size is
# past it
law alone_too_large:
  {[A.XzAlone.decode(A.XzAloneParams{4}, B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0])), A.XzAlone.decode(A.XzAloneParams{4}, B.Octets.of_list([93, 0, 16, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0]))] == [Fail{E.XzOutputTooLarge{}}, Fail{E.XzOutputTooLarge{}}] : List<&2, Result<&2, &2, E.XzError, B.Octets>>}
