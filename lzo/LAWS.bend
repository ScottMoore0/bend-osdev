# Properties, for every input: whatever LZO1X decompression is given, it
# never answers more bytes than the maximum output size; a stream of
# literals (lzo1x_literals) decodes back to its bytes whenever the maximum
# holds them; what lzo1x_compress_with writes decodes back to its input,
# with any options; every proper prefix of a valid stream is refused as
# truncated, and a valid stream with anything after it as trailing; and a
# stream that opens with a match (whose distance is not the end marker's) is
# refused, since there is nothing before it to copy; the streaming reader,
# fed any pieces, answers what the one-shot decoder answers for the pieces
# joined; and Adler-32 in pieces is Adler-32 of the whole. Each law with a
# hypothesis has a witness that the hypothesis can hold.
#
# Vectors: hand-built streams, each derived from the kernel documentation's
# description of one encoding (the first-byte literal runs, the long literal
# run and its length bytes, M1 after a few literals and after many, M2, M3
# with trailing literals, overlapping and long matches, the end marker), and
# each kind of malformed stream; compression; Adler-32; lzop files built by
# hand from the format notes, and each kind of malformed file.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./decode.bend as D
import ./encode.bend as C
import ./lzo.bend as L
import ./adler32.bend as A
import ./lzop.bend as P

# Properties, for every input

law output_within_max:
  for +src: B.Octets
  for +max: Nat
  {Nat.is_le(B.Octets.len(Result.default(&2, &2, E.LzoError, B.Octets, D.lzo1x_decompress(src, max), B.Octets.empty())), max) == True{} : Bool}

law literals_round_trip:
  for +o: B.Octets
  for +k: Nat
  {D.lzo1x_decompress(C.lzo1x_literals(o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}

law compress_round_trip:
  for +opts: C.LzoCompressOptions
  for +o: B.Octets
  {D.lzo1x_decompress(C.lzo1x_compress_with(opts, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}

# every proper prefix a of a valid stream (one with at least a byte h after
# a) is refused as cut short
law truncation_rejected:
  for +a: B.Octets
  for +h: U32
  for +t: B.Octets
  for +max: Nat
  for +o: B.Octets
  for e: {D.lzo1x_decompress(B.Octets.append(a, B.Octets.cons(h, t)), max) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  {D.lzo1x_decompress(a, max) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

# "a", then the end marker: its prefix [18, 97, 17, 0] is cut short
law truncation_rejected_witness:
  exs o: B.Octets
  {D.lzo1x_decompress(B.Octets.append(B.Octets.of_list([18, 97, 17, 0]), B.Octets.cons(0, B.Octets.empty())), 100n) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}

# a valid stream with any bytes after it is refused
law trailing_rejected:
  for +a: B.Octets
  for +h: U32
  for +t: B.Octets
  for +max: Nat
  for +o: B.Octets
  for e: {D.lzo1x_decompress(a, max) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}
  {D.lzo1x_decompress(B.Octets.append(a, B.Octets.cons(h, t)), max) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}

law trailing_rejected_witness:
  exs o: B.Octets
  {D.lzo1x_decompress(B.Octets.of_list([17, 0, 0]), 0n) == Done{o} : Result<&2, &2, E.LzoError, B.Octets>}

# a first byte of 17 is M4 (H = 0, length 3): its distance, 16384 + D, is
# the end marker's when D = 0, and otherwise reaches before the start. Its
# first distance byte is 4 or more here (so D is not 0), whatever follows.
law first_match_rejected:
  for +lo: U32
  for +hi: U32
  for +rest: B.Octets
  for +max: Nat
  for e: {U32.is_lt(B.byte(lo), 4) == False{} : Bool}
  {D.lzo1x_decompress(B.Octets.cons(17, B.Octets.cons(lo, B.Octets.cons(hi, rest))), max) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}

law first_match_rejected_witness:
  exs lo: U32
  {U32.is_lt(B.byte(lo), 4) == False{} : Bool}

# Streaming: a stream fed to the reader in pieces gives what the one-shot
# decoder gives for the pieces joined, whatever the pieces

def LzoLaws.join(ps: List<&2, B.Octets>) -> B.Octets:
  match ps:
    case Nil{}:
      B.Octets.empty()
    case Con{p, t}:
      B.Octets.append(p, LzoLaws.join(t))

law reader_pieces:
  for +max: Nat
  for +ps: List<&2, B.Octets>
  {D.reader_decompress(max, ps) == D.lzo1x_decompress(LzoLaws.join(ps), max) : Result<&2, &2, E.LzoError, B.Octets>}

# Adler-32 in pieces is Adler-32 of the whole

law adler32_pieces:
  for +s: A.Adler32
  for +a: B.Octets
  for +b: B.Octets
  {A.Adler32.update(s, B.Octets.append(a, b)) == A.Adler32.update(A.Adler32.update(s, a), b) : A.Adler32}

# Vectors: decoding, one per encoding the documentation describes (each
# stream built by hand from its description)

# the end marker alone: M4 (0001 0001: H = 0, length 3) with distance 16384
law end_marker_only:
  {D.lzo1x_decompress(B.Octets.of_list([17, 0, 0]), 0n) == Done{B.Octets.empty()} : Result<&2, &2, E.LzoError, B.Octets>}

# first byte 18: 18 - 17 = 1 literal
law first_byte_one_literal:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 17, 0, 0]), 1n) == Done{B.Octets.of_string("a")} : Result<&2, &2, E.LzoError, B.Octets>}

# first byte 21: 4 literals
law first_byte_four_literals:
  {D.lzo1x_decompress(B.Octets.of_list([21, 97, 98, 99, 100, 17, 0, 0]), 4n) == Done{B.Octets.of_string("abcd")} : Result<&2, &2, E.LzoError, B.Octets>}

# first byte 255: 238 literals, the most a first byte holds
law first_byte_238_literals:
  {D.lzo1x_decompress(B.Octets.concat([B.Octets.of_list([255]), B.Octets.zeros(238n), C.lzo1x_end()]), 238n) == Done{B.Octets.zeros(238n)} : Result<&2, &2, E.LzoError, B.Octets>}

# 0000LLLL after no literals: 3 + L literals
law long_literal_run:
  {D.lzo1x_decompress(B.Octets.of_list([1, 97, 98, 99, 100, 17, 0, 0]), 4n) == Done{B.Octets.of_string("abcd")} : Result<&2, &2, E.LzoError, B.Octets>}

# 0000 0000, then length bytes 0 (255) and 1: 18 + 255 + 1 = 274 literals
law literal_length_bytes:
  {D.lzo1x_decompress(B.Octets.concat([B.Octets.of_list([0, 0, 1]), B.Octets.zeros(274n), C.lzo1x_end()]), 274n) == Done{B.Octets.zeros(274n)} : Result<&2, &2, E.LzoError, B.Octets>}

# "ab" (2 literals), then 0000DDSS after 1 to 3 literals: M1, 2 bytes, D = 1,
# H = 0: distance (0 << 2) + 1 + 1 = 2
law m1_after_few_literals:
  {D.lzo1x_decompress(B.Octets.of_list([19, 97, 98, 4, 0, 17, 0, 0]), 4n) == Done{B.Octets.of_string("abab")} : Result<&2, &2, E.LzoError, B.Octets>}

# M1 at distance 1: the copy overlaps itself
law m1_overlap:
  {D.lzo1x_decompress(B.Octets.of_list([19, 97, 98, 0, 0, 17, 0, 0]), 4n) == Done{B.Octets.of_string("abbb")} : Result<&2, &2, E.LzoError, B.Octets>}

# 0000DDSS after 4 literals or more is M1 at distance 2049 or more: with 4
# bytes of output, it reaches before the start
law m1_after_many_literals:
  {D.lzo1x_decompress(B.Octets.of_list([21, 97, 98, 99, 100, 0, 0, 17, 0, 0]), 100n) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}

# "abc", then 01LDDDSS: M2, 3 + 0 bytes, D = 2, H = 0: distance 3
law m2_three_bytes:
  {D.lzo1x_decompress(B.Octets.of_list([20, 97, 98, 99, 72, 0, 17, 0, 0]), 6n) == Done{B.Octets.of_string("abcabc")} : Result<&2, &2, E.LzoError, B.Octets>}

# "abc", then 1LLDDDSS: M2, 5 + 1 bytes, D = 2, H = 0: distance 3
law m2_six_bytes:
  {D.lzo1x_decompress(B.Octets.of_list([20, 97, 98, 99, 168, 0, 17, 0, 0]), 9n) == Done{B.Octets.of_string("abcabcabc")} : Result<&2, &2, E.LzoError, B.Octets>}

# "abcd", then 001LLLLL: M3, 2 + 8 bytes, LE16 14 = D 3 (distance 4), S 2:
# then 2 literals
law m3_with_trailing_literals:
  {D.lzo1x_decompress(B.Octets.of_list([21, 97, 98, 99, 100, 40, 14, 0, 120, 121, 17, 0, 0]), 16n) == Done{B.Octets.of_string("abcdabcdabcdabxy")} : Result<&2, &2, E.LzoError, B.Octets>}

# after a match with S = 0, 0000LLLL is a literal run again
law literal_run_after_match:
  {D.lzo1x_decompress(B.Octets.of_list([21, 97, 98, 99, 100, 40, 12, 0, 1, 119, 120, 121, 122, 17, 0, 0]), 18n) == Done{B.Octets.of_string("abcdabcdabcdabwxyz")} : Result<&2, &2, E.LzoError, B.Octets>}

# "a", then M3 of 10 bytes at distance 1
law m3_overlap:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 40, 0, 0, 17, 0, 0]), 11n) == Done{B.Octets.of_string("aaaaaaaaaaa")} : Result<&2, &2, E.LzoError, B.Octets>}

# "a", then M3 with L = 0 and a length byte of 1: 2 + 31 + 1 = 34 bytes
law m3_length_bytes:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 32, 1, 0, 0, 17, 0, 0]), 35n) == Done{B.Octets.of_string("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")} : Result<&2, &2, E.LzoError, B.Octets>}

# the end marker with length bytes and S bits: they are read and ignored
law end_marker_with_length:
  {D.lzo1x_decompress(B.Octets.of_list([16, 1, 3, 0]), 0n) == Done{B.Octets.empty()} : Result<&2, &2, E.LzoError, B.Octets>}

# Vectors: malformed streams

law empty_input:
  {D.lzo1x_decompress(B.Octets.empty(), 100n) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

law missing_end_marker:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97]), 100n) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

law cut_in_literals:
  {D.lzo1x_decompress(B.Octets.of_list([21, 97, 98]), 100n) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

law cut_in_distance:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 40, 0]), 100n) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

law cut_in_length_bytes:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 32, 0]), 1000n) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

# M3 at distance 2 with one byte of output
law distance_past_start:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 40, 4, 0, 17, 0, 0]), 100n) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}

# a first M4 at distance 16385
law first_m4:
  {D.lzo1x_decompress(B.Octets.of_list([16, 1, 4, 0, 17, 0, 0]), 100n) == Fail{E.LzoBadDistance{}} : Result<&2, &2, E.LzoError, B.Octets>}

# 11 bytes into a maximum of 5
law output_limit_match:
  {D.lzo1x_decompress(B.Octets.of_list([18, 97, 40, 0, 0, 17, 0, 0]), 5n) == Fail{E.LzoOutputTooLarge{}} : Result<&2, &2, E.LzoError, B.Octets>}

law output_limit_literals:
  {D.lzo1x_decompress(B.Octets.of_list([21, 97, 98, 99, 100, 17, 0, 0]), 3n) == Fail{E.LzoOutputTooLarge{}} : Result<&2, &2, E.LzoError, B.Octets>}

law trailing_byte:
  {D.lzo1x_decompress(B.Octets.of_list([17, 0, 0, 0]), 100n) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}

# Vectors: streaming and the entry file

law reader_three_pieces:
  {D.reader_decompress(100n, [B.Octets.of_list([20, 97]), B.Octets.of_list([98, 99, 168]), B.Octets.of_list([0, 17, 0, 0])]) == Done{B.Octets.of_string("abcabcabc")} : Result<&2, &2, E.LzoError, B.Octets>}

law reader_cut_short:
  {D.reader_decompress(100n, [B.Octets.of_list([20, 97]), B.Octets.of_list([98, 99, 168])]) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

law entry_round_trip:
  {L.decompress(L.compress(B.Octets.of_string("an LZO1X stream, compressed and back"))) == Done{B.Octets.of_string("an LZO1X stream, compressed and back")} : Result<&2, &2, E.LzoError, B.Octets>}

law entry_limit:
  {L.decompress_with(L.LzoOptions{5}, B.Octets.of_list([18, 97, 40, 0, 0, 17, 0, 0])) == Fail{E.LzoOutputTooLarge{}} : Result<&2, &2, E.LzoError, B.Octets>}

# Vectors: compression

law literals_short:
  {C.lzo1x_literals(B.Octets.of_string("abc")) == B.Octets.of_list([20, 97, 98, 99, 17, 0, 0]) : B.Octets}

# 300 literals: 0000 0000, then length bytes 0 (255) and 27: 18 + 255 + 27
law literals_length_bytes:
  {B.Octets.take(3n, C.lzo1x_literals(B.Octets.zeros(300n))) == B.Octets.of_list([0, 0, 27]) : B.Octets}

law compress_empty:
  {C.lzo1x_compress(B.Octets.empty()) == B.Octets.of_list([17, 0, 0]) : B.Octets}

# 300 zero bytes: one literal, then M3 with L = 0, length bytes 0 and 11
# (2 + 31 + 255 + 11 = 299), distance 1, then the end marker
law compress_run:
  {C.lzo1x_compress(B.Octets.zeros(300n)) == B.Octets.of_list([18, 0, 32, 0, 11, 0, 0, 17, 0, 0]) : B.Octets}

# "hello " (first byte 23), then M3 of 23 bytes at distance 6
law compress_text:
  {C.lzo1x_compress(B.Octets.of_string("hello hello hello hello hello")) == B.Octets.of_list([23, 104, 101, 108, 108, 111, 32, 53, 20, 0, 17, 0, 0]) : B.Octets}

# Vectors: Adler-32 (RFC 1950)

law adler32_empty:
  {A.adler32(B.Octets.empty()) == 1 : U32}

law adler32_wikipedia:
  {A.adler32(B.Octets.of_string("Wikipedia")) == 300286872 : U32}

# Vectors: the lzop container, files built by hand from the format notes
# (checksums computed with zlib)

# version 0x1030, method 1, level 5, Adler-32 of the data (flag 1), mode
# 0o100644, mtime 1700000000, name "a.txt"; a stored block "Bend!" and a
# compressed block (the stream of compress_text)
law lzop_two_blocks:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 1, 0, 0, 129, 164, 101, 83, 241, 0, 0, 0, 0, 0, 5, 97, 46, 116, 120, 116, 76, 102, 5, 243, 0, 0, 0, 5, 0, 0, 0, 5, 5, 22, 1, 155, 66, 101, 110, 100, 33, 0, 0, 0, 29, 0, 0, 0, 13, 163, 16, 10, 229, 23, 104, 101, 108, 108, 111, 32, 53, 20, 0, 17, 0, 0, 0, 0, 0, 0])) == Done{B.Octets.of_string("Bend!hello hello hello hello hello")} : Result<&2, &2, E.LzoError, B.Octets>}

law lzop_header_fields:
  {P.lzop_header(B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 1, 0, 0, 129, 164, 101, 83, 241, 0, 0, 0, 0, 0, 5, 97, 46, 116, 120, 116, 76, 102, 5, 243, 0, 0, 0, 0])) == Done{P.LzopHeader{4144, 8320, 2368, 1, 5, 1, 33188, 1700000000, 0, B.Octets.of_string("a.txt")}} : Result<&2, &2, E.LzoError, P.LzopHeader>}

# every checksum flag (0x1, 0x2, 0x100, 0x200) and a CRC-32 header (0x1000)
law lzop_every_checksum:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 19, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 219, 254, 93, 0, 0, 0, 29, 0, 0, 0, 13, 163, 16, 10, 229, 56, 83, 210, 246, 24, 160, 2, 166, 162, 20, 181, 82, 23, 104, 101, 108, 108, 111, 32, 53, 20, 0, 17, 0, 0, 0, 0, 0, 0])) == Done{B.Octets.of_string("hello hello hello hello hello")} : Result<&2, &2, E.LzoError, B.Octets>}

law lzop_bad_header_checksum:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 1, 0, 0, 129, 164, 101, 83, 241, 0, 0, 0, 0, 0, 5, 97, 46, 116, 120, 116, 76, 102, 5, 242, 0, 0, 0, 0])) == Fail{E.LzoBadHeaderChecksum{}} : Result<&2, &2, E.LzoError, B.Octets>}

# the stored block "Bend!" with its first byte changed ("Cend!")
law lzop_bad_block_checksum:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 1, 0, 0, 129, 164, 101, 83, 241, 0, 0, 0, 0, 0, 5, 97, 46, 116, 120, 116, 76, 102, 5, 243, 0, 0, 0, 5, 0, 0, 0, 5, 5, 22, 1, 155, 67, 101, 110, 100, 33, 0, 0, 0, 0])) == Fail{E.LzoBadChecksum{}} : Result<&2, &2, E.LzoError, B.Octets>}

# the same, unverified
law lzop_unverified:
  {P.lzop_decompress(P.LzopOptions{100, False{}}, B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 1, 0, 0, 129, 164, 101, 83, 241, 0, 0, 0, 0, 0, 5, 97, 46, 116, 120, 116, 76, 102, 5, 243, 0, 0, 0, 5, 0, 0, 0, 5, 5, 22, 1, 155, 67, 101, 110, 100, 33, 0, 0, 0, 0])) == Done{B.Octets.of_string("Cend!")} : Result<&2, &2, E.LzoError, B.Octets>}

law lzop_bad_magic:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_string("not an lzop file")) == Fail{E.LzoBadMagic{}} : Result<&2, &2, E.LzoError, B.Octets>}

# the filter flag (0x800)
law lzop_filter_unsupported:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 185, 1, 57, 0, 0, 0, 0])) == Fail{E.LzoUnsupported{}} : Result<&2, &2, E.LzoError, B.Octets>}

law lzop_bad_method:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 4, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 122, 1, 52, 0, 0, 0, 0])) == Fail{E.LzoBadMethod{}} : Result<&2, &2, E.LzoError, B.Octets>}

# version 0x0900: before the fields this package reads
law lzop_old_version:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 9, 0, 32, 128, 9, 64, 1, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 18, 0, 250, 0, 0, 0, 0])) == Fail{E.LzoBadVersion{}} : Result<&2, &2, E.LzoError, B.Octets>}

# a block stored in 4 bytes that holds 3
law lzop_block_larger:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 51, 1, 48, 0, 0, 0, 3, 0, 0, 0, 4, 97, 98, 99, 100, 0, 0, 0, 0])) == Fail{E.LzoBadBlockSize{}} : Result<&2, &2, E.LzoError, B.Octets>}

law lzop_trailing:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 51, 1, 48, 0, 0, 0, 0, 7])) == Fail{E.LzoTrailing{}} : Result<&2, &2, E.LzoError, B.Octets>}

law lzop_cut_short:
  {P.lzop_decompress(P.LzopOptions.default(), B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 51, 1, 48, 0, 0])) == Fail{E.LzoTruncated{}} : Result<&2, &2, E.LzoError, B.Octets>}

# the writer: an empty file is the header and the end
law lzop_write_empty:
  {P.lzop_compress(P.LzopWriteOptions{262144, False{}, False{}, False{}, False{}, False{}, 1, 5, B.Octets.empty(), 0, 0, C.LzoCompressOptions.default()}, B.Octets.empty()) == B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 51, 1, 48, 0, 0, 0, 0]) : B.Octets}

# the writer with every checksum and a CRC-32 header: the very file built
# by hand above
law lzop_write_every_checksum:
  {P.lzop_compress(P.LzopWriteOptions{262144, True{}, True{}, True{}, True{}, True{}, 1, 5, B.Octets.empty(), 0, 0, C.LzoCompressOptions.default()}, B.Octets.of_string("hello hello hello hello hello")) == B.Octets.of_list([137, 76, 90, 79, 0, 13, 10, 26, 10, 16, 48, 32, 128, 9, 64, 1, 5, 0, 0, 19, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 219, 254, 93, 0, 0, 0, 29, 0, 0, 0, 13, 163, 16, 10, 229, 56, 83, 210, 246, 24, 160, 2, 166, 162, 20, 181, 82, 23, 104, 101, 108, 108, 111, 32, 53, 20, 0, 17, 0, 0, 0, 0, 0, 0]) : B.Octets}

# the writer asked for checksums of the compressed bytes only writes the
# same checksums of the uncompressed bytes too (flags 0x303), as the lzop
# tool needs (LzopWriteOptions.normal)
# DRAFT: not yet reviewed by the maintainer
law lzop_write_compressed_checksums:
  {P.lzop_header(P.lzop_compress(P.LzopWriteOptions{262144, False{}, False{}, True{}, True{}, False{}, 1, 5, B.Octets.empty(), 0, 0, C.LzoCompressOptions.default()}, B.Octets.of_string("hello hello hello hello hello"))) == Done{P.LzopHeader{4144, 8320, 2368, 1, 5, 771, 0, 0, 0, B.Octets.empty()}} : Result<&2, &2, E.LzoError, P.LzopHeader>}

# streamed in pieces, with 8-byte blocks, then read back
law lzop_stream_round_trip:
  {P.lzop_decompress(P.LzopOptions.default(), P.lzop_stream(P.LzopWriteOptions{8, True{}, False{}, True{}, False{}, False{}, 1, 5, B.Octets.of_string("s"), 0, 0, C.LzoCompressOptions.default()}, [B.Octets.of_string("stream"), B.Octets.of_string("ed in three "), B.Octets.of_string("pieces, pieces, pieces")])) == Done{B.Octets.of_string("streamed in three pieces, pieces, pieces")} : Result<&2, &2, E.LzoError, B.Octets>}
