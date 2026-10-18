# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
#   * RLE1: decoding the encoding of any byte string gives it back;
#   * move-to-front and RLE2: decoding the symbols of any byte string gives
#     it back, from any alphabet of at most 256 bytes that holds its bytes,
#     with any maximum not below its length;
#   * the Burrows-Wheeler transform, by the reference implementations: the
#     inverse of the forward transform is the block, for every block of n
#     copies of one byte (every byte, every n, n = 0 and 1 included) and for
#     every two-byte block. The general case (every block) is not proved: it
#     is held by vectors and by the differential test (ref/), for the fast
#     implementations as well;
#   * decompression never answers more output than the maximum;
#   * an input whose first, second or third byte is not "B", "Z", "h" is
#     refused as bad magic, whatever follows; the empty input is cut short.
#
# Vectors: empty streams made by the bzip2 tool (Python's bz2 module), one
# and two of them, with trailing bytes ignored or refused; compressing the
# empty input gives the tool's 14 bytes; CRC-32/BZIP2's check value; the
# transforms of "banana", both ways, fast and reference; the MTF and RLE1
# stages on small inputs. Blocks through the whole codec are checked by
# check.bend and ref/ (see the vectors' note below).
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L
import ./error.bend as E
import ./rle.bend as R
import ./mtf.bend as M
import ./bwt.bend as W
import ./stream.bend as S
import ./bzip2.bend as Z

# RLE1

# seven a's: four, then the count 3
law rle1_encode_run:
  {R.rle1_encode(B.Octets.of_string("aaaaaaab")) == B.Octets.of_list([97, 97, 97, 97, 3, 98]) : B.Octets}

law rle1_round_trip:
  for +o: B.Octets
  {R.rle1_decode(R.rle1_encode(o)) == o : B.Octets}

# Move-to-front and RLE2

law mtf_round_trip:
  for +alpha: B.Octets
  for +o: B.Octets
  for +k: Nat
  for c: {M.mtf_covers(alpha, o) == True{} : Bool}
  for s: {Nat.is_le(B.Octets.len(alpha), 256n) == True{} : Bool}
  {M.mtf_decode(alpha, M.mtf_encode(alpha, o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# the hypotheses can hold: bzip2's alphabet for "banana" covers it
law mtf_covers_banana:
  {M.mtf_covers(M.symbol_map(B.Octets.of_string("banana")), B.Octets.of_string("banana")) == True{} : Bool}

law symbol_map_banana:
  {M.symbol_map(B.Octets.of_string("banana")) == B.Octets.of_string("abn") : B.Octets}

law mtf_encode_banana:
  {M.mtf_encode(B.Octets.of_string("abn"), B.Octets.of_string("banana")) == [2, 2, 3, 2, 2, 2] : List<&2, U32>}

# a run of four zeros is the digits 2, 1: RUNB, RUNA
law mtf_encode_run:
  {M.mtf_encode(B.Octets.of_string("ab"), B.Octets.of_string("aaaab")) == [1, 0, 2] : List<&2, U32>}

law mtf_decode_too_large:
  {M.mtf_decode(B.Octets.of_string("abn"), [2, 2, 3, 2, 2, 2], 5n) == Fail{E.Bzip2OutputTooLarge{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law mtf_decode_bad_symbol:
  {M.mtf_decode(B.Octets.of_string("ab"), [3], 9n) == Fail{E.Bzip2BadSymbol{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# The Burrows-Wheeler transform

def bwt_undo_ref(b: W.Bzip2Bwt) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match b:
    case W.Bzip2Bwt{last, +ptr}:
      W.bwt_inverse_ref(last, ptr)

law bwt_ref_round_trip_constant:
  for +b: U32
  for +n: Nat
  {bwt_undo_ref(W.bwt_forward_ref(B.Octets.of_list(L.bz.rep(n, b)))) == Done{B.Octets.of_list(L.bz.rep(n, b))} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law bwt_ref_round_trip_two:
  for +a: U32
  for +b: U32
  {bwt_undo_ref(W.bwt_forward_ref(B.Octets.of_list([a, b]))) == Done{B.Octets.of_list([a, b])} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law bwt_banana:
  {W.bwt_forward(B.Octets.of_string("banana")) == W.Bzip2Bwt{B.Octets.of_string("nnbaaa"), 3} : W.Bzip2Bwt}

law bwt_ref_banana:
  {W.bwt_forward_ref(B.Octets.of_string("banana")) == W.Bzip2Bwt{B.Octets.of_string("nnbaaa"), 3} : W.Bzip2Bwt}

law bwt_inverse_banana:
  {W.bwt_inverse(B.Octets.of_string("nnbaaa"), 3) == Done{B.Octets.of_string("banana")} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law bwt_inverse_ref_banana:
  {W.bwt_inverse_ref(B.Octets.of_string("nnbaaa"), 3) == Done{B.Octets.of_string("banana")} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law bwt_inverse_bad_ptr:
  {W.bwt_inverse(B.Octets.of_string("nnbaaa"), 6) == Fail{E.Bzip2BadOrigPtr{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# Decompression: the output limit, and bad magic

# an answer within the maximum max: a failure, or at most max bytes
def bzip2_within(+max: U32, r: Result<&2, &2, E.Bzip2Error, B.Octets>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{o}:
      Nat.is_le(B.Octets.len(o), U32.to_nat(max))

law output_bounded:
  for +opts: S.Bzip2Options
  for src: B.Octets
  {bzip2_within(S.Bzip2Options.max(opts), Z.decompress_with(opts, src)) == True{} : Bool}

law bad_magic_1:
  for +opts: S.Bzip2Options
  for +b: U32
  for +xs: List<&2, U32>
  for e: {U32.is_eq(B.byte(b), 66) == False{} : Bool}
  {Z.decompress_with(opts, B.Octets.of_list(Con{b, xs})) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law bad_magic_2:
  for +opts: S.Bzip2Options
  for +b: U32
  for +xs: List<&2, U32>
  for e: {U32.is_eq(B.byte(b), 90) == False{} : Bool}
  {Z.decompress_with(opts, B.Octets.of_list(Con{66, Con{b, xs}})) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

law bad_magic_3:
  for +opts: S.Bzip2Options
  for +b: U32
  for +xs: List<&2, U32>
  for e: {U32.is_eq(B.byte(b), 104) == False{} : Bool}
  {Z.decompress_with(opts, B.Octets.of_list(Con{66, Con{90, Con{b, xs}}})) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# the hypotheses can hold
law not_magic_byte:
  {[U32.is_eq(B.byte(0), 66), U32.is_eq(B.byte(0), 90), U32.is_eq(B.byte(0), 104)] == [False{}, False{}, False{}] : List<&2, Bool>}

law empty_input:
  for +opts: S.Bzip2Options
  {Z.decompress_with(opts, B.Octets.empty()) == Fail{E.Bzip2Truncated{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# Vectors: streams from Python's bz2 module (libbzip2 1.0.8). Streams that
# hold a block are checked by check.bend instead: the kernel behind --verdict
# runs a block's 900,000-byte limit as a unary Nat and does not finish.

# bz2.compress(b"")
law decode_empty_stream:
  {Z.decompress_with(S.Bzip2Options{64, True{}}, B.Octets.of_list([66, 90, 104, 57, 23, 114, 69, 56, 80, 144, 0, 0, 0, 0])) == Done{B.Octets.empty()} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# two streams (levels 9 and 1), then trailing bytes, ignored
law decode_two_streams:
  {Z.decompress_with(S.Bzip2Options{64, True{}}, B.Octets.of_list([66, 90, 104, 57, 23, 114, 69, 56, 80, 144, 0, 0, 0, 0, 66, 90, 104, 49, 23, 114, 69, 56, 80, 144, 0, 0, 0, 0, 0, 0])) == Done{B.Octets.empty()} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# the same trailing bytes, refused when asked

law decode_trailing_refused:
  {Z.decompress_with(S.Bzip2Options{64, False{}}, B.Octets.of_list([66, 90, 104, 57, 23, 114, 69, 56, 80, 144, 0, 0, 0, 0, 0, 0])) == Fail{E.Bzip2TrailingData{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}

# Compression: the empty input is the bzip2 tool's 14 bytes
law compress_empty:
  {Z.compress(B.Octets.empty()) == B.Octets.of_list([66, 90, 104, 57, 23, 114, 69, 56, 80, 144, 0, 0, 0, 0]) : B.Octets}

# CRC-32/BZIP2's check value, 0xFC891918
law crc_check:
  {S.bzip2_crc(B.Octets.of_string("123456789")) == 4236843288 : U32}
