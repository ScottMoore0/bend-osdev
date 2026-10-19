# Properties, for every input: what the deflater writes, at any level and
# with any options, inflates back to its input (raw, zlib and gzip), and so
# does the stored stream; the inflater never answers more than its maximum;
# a block type of 11 is refused whatever follows it, and so is a first
# match, whatever its distance; the code huff_code gives a symbol is the one
# its tree decodes, whatever bits follow, so the codes built from any code
# lengths are prefix-free; Adler-32 can be computed in pieces.
#
# Vectors: RFC 1951's own codes (3.2.2's example, 3.2.6's fixed codes), the
# fixed trees, the classes of code lengths, Adler-32 and CRC-32 check values,
# streams zlib writes, and one stream for each way the inflater, the zlib
# reader and the gzip reader refuse their input.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./huffman.bend as H
import ./fixed.bend as X
import ./adler32.bend as A
import ./inflate.bend as I
import ./deflate.bend as D
import ./zlib.bend as Z
import ./gzip.bend as G

# whether a decoder's answer is within the maximum (a failure always is)
def deflate_within(+max: U32, r: Result<&2, &2, E.DeflateError, B.Octets>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{o}:
      Nat.is_le(B.Octets.len(o), U32.to_nat(max))

# Properties, for every input

law stored_round_trip:
  for +o: B.Octets
  for +m: U32
  for +ignore: Bool
  for h: {Nat.is_le(B.Octets.len(o), U32.to_nat(m)) == True{} : Bool}
  {I.inflate_with(I.InflateOptions{m, B.Octets.empty(), ignore}, D.stored_stream(o)) == Done{o} : Result<&2, &2, E.DeflateError, B.Octets>}

law deflate_round_trip:
  for +p: D.DeflateOptions
  for +o: B.Octets
  for +m: U32
  for +ignore: Bool
  for h: {Nat.is_le(B.Octets.len(o), U32.to_nat(m)) == True{} : Bool}
  {I.inflate_with(I.InflateOptions{m, B.Octets.empty(), ignore}, D.deflate_with(p, o)) == Done{o} : Result<&2, &2, E.DeflateError, B.Octets>}

law deflate_level_round_trip:
  for +l: U32
  for +o: B.Octets
  for +m: U32
  for +ignore: Bool
  for h: {Nat.is_le(B.Octets.len(o), U32.to_nat(m)) == True{} : Bool}
  {I.inflate_with(I.InflateOptions{m, B.Octets.empty(), ignore}, D.deflate_level(l, o)) == Done{o} : Result<&2, &2, E.DeflateError, B.Octets>}

law deflate_default_round_trip:
  for +o: B.Octets
  for +m: U32
  for +ignore: Bool
  for h: {Nat.is_le(B.Octets.len(o), U32.to_nat(m)) == True{} : Bool}
  {I.inflate_with(I.InflateOptions{m, B.Octets.empty(), ignore}, D.deflate(o)) == Done{o} : Result<&2, &2, E.DeflateError, B.Octets>}

law zlib_round_trip:
  for +zo: Z.ZlibOptions
  for +o: B.Octets
  for +m: U32
  for +d: B.Octets
  for +ignore: Bool
  for h: {Nat.is_le(B.Octets.len(o), U32.to_nat(m)) == True{} : Bool}
  {Z.zlib_decompress_with(I.InflateOptions{m, d, ignore}, Z.zlib_compress_with(zo, o)) == Done{o} : Result<&2, &2, E.DeflateError, B.Octets>}

law gzip_round_trip:
  for +p: D.DeflateOptions
  for +o: B.Octets
  for +m: U32
  for +d: B.Octets
  for +ignore: Bool
  for h: {Nat.is_le(B.Octets.len(o), U32.to_nat(m)) == True{} : Bool}
  {G.gzip_decompress_with(I.InflateOptions{m, d, ignore}, G.gzip_compress_with(G.GzipOptions{p, G.GzipHeader.default()}, o)) == Done{o} : Result<&2, &2, E.DeflateError, B.Octets>}

law output_bounded:
  for +opts: I.InflateOptions
  for src: B.Octets
  {deflate_within(I.InflateOptions.max(opts), I.inflate_with(opts, src)) == True{} : Bool}

law zlib_output_bounded:
  for +opts: I.InflateOptions
  for src: B.Octets
  {deflate_within(I.InflateOptions.max(opts), Z.zlib_decompress_with(opts, src)) == True{} : Bool}

law gzip_output_bounded:
  for +opts: I.InflateOptions
  for src: B.Octets
  {deflate_within(I.InflateOptions.max(opts), G.gzip_decompress_with(opts, src)) == True{} : Bool}

# BTYPE 11 (3.2.3: "reserved (error)"), in a final block or not, whatever
# the rest of the byte and the input after it hold
law bad_block_type:
  for +opts: I.InflateOptions
  for +x: U32
  for rest: B.Octets
  {I.inflate_with(opts, B.Octets.cons(U32.or(6, U32.shln(x, 3n)), rest)) == Fail{E.DeflateBadBlockType{}} : Result<&2, &2, E.DeflateError, B.Octets>}

law bad_block_type_final:
  for +opts: I.InflateOptions
  for +x: U32
  for rest: B.Octets
  {I.inflate_with(opts, B.Octets.cons(U32.or(7, U32.shln(x, 3n)), rest)) == Fail{E.DeflateBadBlockType{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a final fixed block that starts with a match (length code 257, then any of
# the 32 five-bit distance codes, then anything), with no dictionary: there
# is nothing before it
# to copy (3.2.3: "a distance cannot refer past the beginning of the output
# stream"), or the distance code is 30 or 31 (3.2.6: they "will never
# actually occur"), so the stream is refused
law first_match_refused:
  for +m: U32
  for +ignore: Bool
  for a: Bool
  for b: Bool
  for c: Bool
  for d: Bool
  for e: Bool
  for x: Bool
  for rest: B.Octets
  {Result.is_fail(&2, &2, E.DeflateError, B.Octets, I.inflate_with(I.InflateOptions{m, B.Octets.empty(), ignore}, B.Octets.cons(3, B.Octets.cons(U32{WCon{False{}, WCon{True{}, WCon{a, WCon{b, WCon{c, WCon{d, WCon{e, WCon{x, Word.zero(24n)}}}}}}}}}, rest)))) == True{} : Bool}

# a symbol's code is what the tree decodes, whatever follows it
law huff_code_decodes:
  for +ls: List<&2, U32>
  for +s: U32
  for +p: List<&2, Bool>
  for +rest: List<&2, Bool>
  for h: {H.huff_code(ls, s) == Some{p} : Maybe<&2, List<&2, Bool>>}
  {H.huff_decode(H.huff_tree(ls), List.append(&2, Bool, p, rest)) == Some{H.DflDecoded{s, rest}} : Maybe<&2, H.DflDecoded>}

# so no code is a prefix of another symbol's code
law huff_prefix_free:
  for +ls: List<&2, U32>
  for +s: U32
  for +t: U32
  for +p: List<&2, Bool>
  for +q: List<&2, Bool>
  for +more: List<&2, Bool>
  for hs: {H.huff_code(ls, s) == Some{p} : Maybe<&2, List<&2, Bool>>}
  for ht: {H.huff_code(ls, t) == Some{q} : Maybe<&2, List<&2, Bool>>}
  for hpq: {p == List.append(&2, Bool, q, more) : List<&2, Bool>}
  {s == t : U32}

law adler32_streaming:
  for +a: A.Adler32
  for +x: B.Octets
  for +y: B.Octets
  {A.Adler32.update(A.Adler32.update(a, x), y) == A.Adler32.update(a, B.Octets.append(x, y)) : A.Adler32}

# Vectors

# the fixed codes' trees (3.2.6), as fixed.bend holds them, are the canonical
# codes of the fixed lengths
law fixed_lit_tree:
  {H.huff_tree(H.huff_fixed_lit()) == X.fixed.lit() : H.DflTree}

law fixed_dist_tree:
  {H.huff_tree(H.huff_fixed_dist()) == X.fixed.dist() : H.DflTree}

# 3.2.2's example: "the alphabet ABCDEFGH, with bit lengths (3, 3, 3, 3, 3,
# 2, 4, 4)" has the codes 010, 011, 100, 101, 110, 00, 1110, 1111
law rfc_example_codes:
  {[H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 0), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 1), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 2), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 3), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 4), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 5), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 6), H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 7)] == [Some{[False{}, True{}, False{}]}, Some{[False{}, True{}, True{}]}, Some{[True{}, False{}, False{}]}, Some{[True{}, False{}, True{}]}, Some{[True{}, True{}, False{}]}, Some{[False{}, False{}]}, Some{[True{}, True{}, True{}, False{}]}, Some{[True{}, True{}, True{}, True{}]}] : List<&2, Maybe<&2, List<&2, Bool>>>}

# 3.2.6's table: literal/length 0 is 00110000, 143 is 10111111, 144 is
# 110010000, 255 is 111111111, 256 is 0000000, 279 is 0010111, 280 is
# 11000000, 287 is 11000111
law rfc_fixed_codes:
  {[H.huff_path(X.fixed.lit(), 0), H.huff_path(X.fixed.lit(), 143), H.huff_path(X.fixed.lit(), 144), H.huff_path(X.fixed.lit(), 255), H.huff_path(X.fixed.lit(), 256), H.huff_path(X.fixed.lit(), 279), H.huff_path(X.fixed.lit(), 280), H.huff_path(X.fixed.lit(), 287)] == [Some{[False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}]}, Some{[True{}, False{}, True{}, True{}, True{}, True{}, True{}, True{}]}, Some{[True{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]}, Some{[True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}]}, Some{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]}, Some{[False{}, False{}, True{}, False{}, True{}, True{}, True{}]}, Some{[True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]}, Some{[True{}, True{}, False{}, False{}, False{}, True{}, True{}, True{}]}] : List<&2, Maybe<&2, List<&2, Bool>>>}

# the classes of code lengths: complete, one one-bit code, incomplete,
# over-subscribed, none; the fixed codes are complete
law kraft_classes:
  {[H.huff_kraft([1, 1]), H.huff_kraft([0, 1, 0]), H.huff_kraft([2, 0]), H.huff_kraft([1, 2]), H.huff_kraft([1, 1, 1]), H.huff_kraft([0, 0, 0]), H.huff_kraft(H.huff_fixed_lit()), H.huff_kraft(H.huff_fixed_dist())] == [H.DflKraftComplete{}, H.DflKraftSingle{}, H.DflKraftIncomplete{}, H.DflKraftIncomplete{}, H.DflKraftOver{}, H.DflKraftEmpty{}, H.DflKraftComplete{}, H.DflKraftComplete{}] : List<&2, H.DflKraft>}

# Adler-32 (RFC 1950, 2.2: s1 starts at 1, s2 at 0, so no data gives 1);
# "Wikipedia" and "123456789" as Python's zlib.adler32 gives them
law adler32_vectors:
  {[A.adler32(B.Octets.empty()), A.adler32(B.Octets.of_string("a")), A.adler32(B.Octets.of_string("Wikipedia")), A.adler32(B.Octets.of_string("123456789"))] == [1, 6422626, 300286872, 152961502] : List<&2, U32>}

# CRC-32 as gzip stores it: the CRC catalogue's check value for
# "123456789", 0xCBF43926 (reveng.sourceforge.io, CRC-32/ISO-HDLC)
law crc32_vectors:
  {[G.gzip_crc32(B.Octets.empty()), G.gzip_crc32(B.Octets.of_string("123456789"))] == [0, 3421780262] : List<&2, U32>}

# BEGIN generated by gen/vectors.py

# a stored block (3.2.4): BFINAL 1, BTYPE 00, LEN 3, NLEN, the bytes
law inflate_stored:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99])) == Done{B.Octets.of_list([97, 98, 99])} : Result<&2, &2, E.DeflateError, B.Octets>}

# an empty final stored block
law inflate_stored_empty:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([1, 0, 0, 255, 255])) == Done{B.Octets.empty()} : Result<&2, &2, E.DeflateError, B.Octets>}

# zlib's raw stream for no data: one empty fixed block
law inflate_fixed_empty:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([3, 0])) == Done{B.Octets.empty()} : Result<&2, &2, E.DeflateError, B.Octets>}

# zlib's raw stream for "a"
law inflate_fixed_a:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([75, 4, 0])) == Done{B.Octets.of_list([97])} : Result<&2, &2, E.DeflateError, B.Octets>}

# zlib's raw stream for "hello hello hello" (a match reaching back 6 and overlapping itself)
law inflate_fixed_match:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([203, 72, 205, 201, 201, 87, 200, 64, 144, 0])) == Done{B.Octets.of_list([104, 101, 108, 108, 111, 32, 104, 101, 108, 108, 111, 32, 104, 101, 108, 108, 111])} : Result<&2, &2, E.DeflateError, B.Octets>}

# a dynamic block (3.2.7) holding "A", its literal/length code two one-bit codes
law inflate_dynamic:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 4, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44])) == Done{B.Octets.of_list([65])} : Result<&2, &2, E.DeflateError, B.Octets>}

# a dynamic block with a match at distance 1 ("AAAA")
law inflate_dynamic_four:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([21, 224, 1, 4, 0, 0, 0, 128, 32, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 248, 35, 2])) == Done{B.Octets.of_list([65, 65, 65, 65])} : Result<&2, &2, E.DeflateError, B.Octets>}

# one distance code of one bit (3.2.7), used
law inflate_dist_single:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([21, 224, 1, 4, 0, 0, 0, 128, 32, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 248, 35, 2])) == Done{B.Octets.of_list([65, 65, 65, 65])} : Result<&2, &2, E.DeflateError, B.Octets>}

# a literal/length code of one one-bit code, 256
law inflate_end_only:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 4, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12])) == Done{B.Octets.empty()} : Result<&2, &2, E.DeflateError, B.Octets>}

# BTYPE 11 (3.2.3: "reserved (error)")
law refuse_btype:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([7, 0, 0])) == Fail{E.DeflateBadBlockType{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# NLEN not the one's complement of LEN (3.2.4)
law refuse_nlen:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([1, 3, 0, 252, 254, 97, 98, 99])) == Fail{E.DeflateBadStoredLength{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a stored block cut short
law refuse_cut:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([1, 3, 0, 252, 255, 97, 98])) == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a stream with no final block
law refuse_nonfinal:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([0, 3, 0, 252, 255, 97, 98, 99])) == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# no input at all
law refuse_empty:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.empty()) == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# literal/length symbol 286 in a fixed block (3.2.6)
law refuse_lit286:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([115, 28, 3, 0])) == Fail{E.DeflateBadLitLenSymbol{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# distance symbol 30 in a fixed block (3.2.6)
law refuse_dist30:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([115, 4, 62, 0])) == Fail{E.DeflateBadDistSymbol{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a distance past the start of the output (3.2.3)
law refuse_far:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([115, 4, 66, 0])) == Fail{E.DeflateDistanceTooFar{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a distance past the start, by its extra bits
law refuse_far_extra:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([115, 116, 2, 146, 0])) == Fail{E.DeflateDistanceTooFar{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# HLIT 29 + 1: 287 literal/length codes
law refuse_hlit:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([253, 253, 1, 64, 18, 32, 0, 0, 0, 84, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 253, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 171, 170, 170, 170, 170, 170, 86, 85, 1, 0, 0, 0, 0, 0, 0, 128, 35, 0])) == Fail{E.DeflateTooManyCodes{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# HDIST 30: 31 distance codes
law refuse_hdist:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 254, 1, 4, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8])) == Fail{E.DeflateTooManyCodes{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an incomplete code length code
law refuse_clen_incomplete:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 8, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 168])) == Fail{E.DeflateBadCodeLengthCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an over-subscribed code length code
law refuse_clen_over:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 4, 0, 0, 0, 64, 16, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44])) == Fail{E.DeflateBadCodeLengthCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# code 16 with no length before it
law refuse_rep_first:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 5, 4, 0, 0, 0, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 2])) == Fail{E.DeflateBadRepeat{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a repeat past the HLIT + HDIST lengths
law refuse_rep_past:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 5, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 133])) == Fail{E.DeflateBadRepeat{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an incomplete literal/length code
law refuse_lit_incomplete:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 253, 1, 32, 0, 16, 0, 0, 0, 252, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 7, 0, 0, 0, 4, 1, 0])) == Fail{E.DeflateBadLitLenCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an over-subscribed literal/length code
law refuse_lit_over:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([13, 225, 1, 64, 16, 0, 0, 0, 16, 84, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 61, 130, 0, 0])) == Fail{E.DeflateBadLitLenCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a literal/length code with no code for 256
law refuse_no_end:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 4, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8])) == Fail{E.DeflateNoEndCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an incomplete distance code
law refuse_dist_incomplete:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 226, 1, 4, 0, 0, 0, 128, 32, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 11])) == Fail{E.DeflateBadDistCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an over-subscribed distance code
law refuse_dist_over:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 227, 1, 4, 0, 0, 0, 128, 32, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 168, 95])) == Fail{E.DeflateBadDistCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a single distance code of two bits
law refuse_dist_single2:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 4, 0, 0, 0, 128, 32, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 1])) == Fail{E.DeflateBadDistCode{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# the unused code of a one-code literal/length code
law refuse_lit_unused:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([5, 224, 1, 4, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0])) == Fail{E.DeflateBadLitLenSymbol{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# the unused code of a one-code distance code
law refuse_dist_unused:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([21, 224, 1, 4, 0, 0, 0, 128, 32, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 248, 163, 2])) == Fail{E.DeflateBadDistSymbol{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a match in a block with no distance codes
law refuse_dist_none:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([21, 224, 1, 4, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 17])) == Fail{E.DeflateBadDistSymbol{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# more output than the maximum (3 bytes, maximum 2)
law refuse_too_large:
  {I.inflate_with(I.InflateOptions{2, B.Octets.empty(), True{}}, B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99])) == Fail{E.DeflateOutputTooLarge{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# bytes after the stream, when refused
law refuse_trailing:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), False{}}, B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99, 88, 89, 90])) == Fail{E.DeflateTrailingData{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# bytes after the stream, ignored (as zlib ignores them)
law ignore_trailing:
  {I.inflate_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99, 88, 89, 90])) == Done{B.Octets.of_list([97, 98, 99])} : Result<&2, &2, E.DeflateError, B.Octets>}

# zlib's stream for no data (RFC 1950, 2.2: CMF 0x78, FLG 0x9C, then ADLER32 1)
law zlib_empty:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([120, 156, 3, 0, 0, 0, 0, 1])) == Done{B.Octets.empty()} : Result<&2, &2, E.DeflateError, B.Octets>}

# zlib's stream for "a"
law zlib_a:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([120, 156, 75, 4, 0, 0, 98, 0, 98])) == Done{B.Octets.of_list([97])} : Result<&2, &2, E.DeflateError, B.Octets>}

# CMF * 256 + FLG not a multiple of 31
law zlib_refuse_fcheck:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([120, 157, 3, 0, 0, 0, 0, 1])) == Fail{E.DeflateZlibBadHeader{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# CM 7
law zlib_refuse_cm:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([119, 133, 3, 0, 0, 0, 0, 1])) == Fail{E.DeflateZlibBadMethod{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# CINFO 8 ("Values of CINFO above 7 are not allowed")
law zlib_refuse_cinfo:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([136, 152, 3, 0, 0, 0, 0, 1])) == Fail{E.DeflateZlibBadWindow{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# FDICT set, and no dictionary
law zlib_refuse_fdict:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([120, 187, 0, 0, 0, 1, 3, 0, 0, 0, 0, 1])) == Fail{E.DeflateZlibNeedDict{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an ADLER32 that is not the data's
law zlib_refuse_adler:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([120, 156, 3, 0, 0, 0, 0, 0])) == Fail{E.DeflateZlibBadChecksum{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# ADLER32 cut short
law zlib_refuse_short:
  {Z.zlib_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([120, 156, 3, 0, 0, 0, 0])) == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# Python's gzip member for no data (RFC 1952, 2.3.1)
law gzip_empty:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == Done{B.Octets.empty()} : Result<&2, &2, E.DeflateError, B.Octets>}

# Python's gzip member for "a"
law gzip_a:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0])) == Done{B.Octets.of_list([97])} : Result<&2, &2, E.DeflateError, B.Octets>}

# two members, one after the other (2.2)
law gzip_two:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0, 31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0])) == Done{B.Octets.of_list([97, 97])} : Result<&2, &2, E.DeflateError, B.Octets>}

# a member, then zero bytes (ignored, as the gzip tool ignores them)
law gzip_zeros:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0, 0, 0, 0, 0])) == Done{B.Octets.of_list([97])} : Result<&2, &2, E.DeflateError, B.Octets>}

# not ID1 ID2
law gzip_refuse_magic:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 140, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0])) == Fail{E.DeflateGzipBadMagic{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# CM 7
law gzip_refuse_cm:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 7, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0])) == Fail{E.DeflateGzipBadMethod{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a reserved FLG bit ("Reserved FLG bits must be zero")
law gzip_refuse_flags:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 32, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0])) == Fail{E.DeflateGzipReservedFlags{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# a CRC32 that is not the data's
law gzip_refuse_crc:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 66, 190, 183, 232, 1, 0, 0, 0])) == Fail{E.DeflateGzipBadCrc{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an ISIZE that is not the data's size
law gzip_refuse_size:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 0, 0, 0, 0, 0, 2, 3, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 1])) == Fail{E.DeflateGzipBadSize{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# an FHCRC that is not the header's
law gzip_refuse_hcrc:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.of_list([31, 139, 8, 2, 0, 0, 0, 0, 2, 3, 0, 0, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0])) == Fail{E.DeflateGzipBadHeaderCrc{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# no input at all
law gzip_refuse_empty:
  {G.gzip_decompress_with(I.InflateOptions{1000, B.Octets.empty(), True{}}, B.Octets.empty()) == Fail{E.DeflateTruncated{}} : Result<&2, &2, E.DeflateError, B.Octets>}

# END generated by gen/vectors.py
