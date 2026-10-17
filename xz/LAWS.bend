# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
#   * xz_decode never answers more output than the caller's maximum;
#   * an input whose first byte is not 0xFD is refused as bad magic, whatever
#     follows, and the empty input is truncated, whatever the parameters;
#   * an LZMA2 stream whose first chunk does not reset the dictionary is
#     corrupt, and so is one opened by a reserved control byte (0x03 to
#     0x7F), whatever follows and whatever the dictionary size and maximum;
#     the end marker alone is the empty stream.
#
# Vectors: small .xz files (made by Python's lzma module) decode to their
# data; a changed CRC32 is caught; LZMA2's dictionary sizes.
#
# The decoding of LZMA data itself is not stated as a law: it is tested
# against Python's lzma module and the xz tool (ref/), on intact and
# corrupted files.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./lzma2.bend as L2
import ./xz.bend as X

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
