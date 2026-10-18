# Properties, for every input: whatever block decompression is given, it never
# answers more bytes than the maximum output size; a block of literals
# (block_literals) decodes back to its bytes whenever the maximum holds them,
# with or without a dictionary; what block_compress writes decodes back to its
# input, with or without a dictionary; a match with offset 0 after any
# literals is refused; and a first match is refused at every offset, since
# there is nothing before it to copy.
#
# Vectors: the block format's own examples of length bytes; hand-built blocks
# (overlapping matches, long match lengths) and every kind of malformed block;
# frames and streams, among them the frame the lz4 tool writes for empty
# input, and each kind of malformed frame; compressed frames that are the
# lz4 tool's bytes exactly, and frames that round trip.
#
# LZ4HC (the hash-chain matcher, chosen through Lz4Matcher): its blocks
# decode back to their input for every parameter choice, with or without a
# dictionary; the fast matcher chosen through the option is block_compress
# itself; the documented levels; an HC frame round trips, and an HC block is
# smaller than the greedy one where a longer, older match exists.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./frame.bend as F
import ./lz4.bend as L
import ./compress.bend as C
import ./hc.bend as H

# Properties, for every input

law output_within_max:
  for +src: B.Octets
  for +max: Nat
  {Nat.is_le(B.Octets.len(Result.default(&2, &2, K.Lz4Error, B.Octets, K.block_decompress(src, max), B.Octets.empty())), max) == True{} : Bool}

law literals_round_trip:
  for +xs: List<&2, U32>
  for +k: Nat
  {K.block_decompress(K.block_literals(B.Octets.of_list(xs)), Nat.add(B.Octets.len(B.Octets.of_list(xs)), k)) == Done{B.Octets.of_list(xs)} : Result<&2, &2, K.Lz4Error, B.Octets>}

law literals_round_trip_dict:
  for +dict: B.Octets
  for +o: B.Octets
  for +k: Nat
  {K.block_decompress_dict(dict, K.block_literals(o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}

law block_compress_round_trip:
  for +o: B.Octets
  {K.block_decompress(C.block_compress(o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}

law block_compress_dict_round_trip:
  for +dict: B.Octets
  for +o: B.Octets
  {K.block_decompress_dict(dict, C.block_compress_dict(dict, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}

law lz4hc_round_trip:
  for +p: H.Lz4HcParams
  for +o: B.Octets
  {K.block_decompress(C.block_compress_with(C.Lz4MatchHC{p}, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}

law lz4hc_dict_round_trip:
  for +p: H.Lz4HcParams
  for +dict: B.Octets
  for +o: B.Octets
  {K.block_decompress_dict(dict, C.block_compress_dict_with(C.Lz4MatchHC{p}, dict, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, K.Lz4Error, B.Octets>}

law block_compress_with_fast:
  for +o: B.Octets
  {C.block_compress_with(C.Lz4MatchFast{}, o) == C.block_compress(o) : B.Octets}

law offset_zero_rejected:
  for +xs: List<&2, U32>
  for +k: Nat
  for +rest: B.Octets
  {K.block_decompress(B.Octets.append(K.block_literals(B.Octets.of_list(xs)), B.Octets.append(B.Octets.of_list([0, 0]), rest)), Nat.add(B.Octets.len(B.Octets.of_list(xs)), k)) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

law offset_before_start_rejected:
  for +lo: U32
  for +hi: U32
  for +rest: B.Octets
  for +max: Nat
  {K.block_decompress(B.Octets.append(B.Octets.of_list([0, lo, hi]), rest), max) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# Vectors: the block format's examples of length bytes (a literal length of
# 48 is 15 then 33; of 280, 15 then 255 then 10; of 15, 15 then 0)

law spec_length_48:
  {B.Octets.take(2n, K.block_literals(B.Octets.zeros(48n))) == B.Octets.of_list([240, 33]) : B.Octets}

law spec_length_280:
  {B.Octets.take(3n, K.block_literals(B.Octets.zeros(280n))) == B.Octets.of_list([240, 255, 10]) : B.Octets}

law spec_length_15:
  {B.Octets.take(2n, K.block_literals(B.Octets.zeros(15n))) == B.Octets.of_list([240, 0]) : B.Octets}

# Vectors: blocks

# the empty input, as the block format writes it: one zero token
law empty_block:
  {K.block_decompress(B.Octets.of_list([0]), 0n) == Done{B.Octets.empty()} : Result<&2, &2, K.Lz4Error, B.Octets>}

# no token at all
law no_token:
  {K.block_decompress(B.Octets.of_list([]), 0n) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# "ab", a match at offset 2 of length 10 (it overlaps itself), "cdefg"
law overlapping_match:
  {K.block_decompress(B.Octets.of_list([38, 97, 98, 2, 0, 80, 99, 100, 101, 102, 103]), 17n) == Done{B.Octets.of_string("ababababababcdefg")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# "x", a match at offset 1 of length 4 + 15 + 255 + 20, "xxxxx"
law long_match:
  {K.block_decompress(B.Octets.of_list([31, 120, 1, 0, 255, 20, 80, 120, 120, 120, 120, 120]), 300n) == Done{B.Octets.of_string("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the same 17 bytes into a maximum of 16
law output_limit:
  {K.block_decompress(B.Octets.of_list([38, 97, 98, 2, 0, 80, 99, 100, 101, 102, 103]), 16n) == Fail{K.Lz4OutputTooLarge{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# offset 0
law offset_zero:
  {K.block_decompress(B.Octets.of_list([16, 97, 0, 0, 80, 97, 98, 99, 100, 101]), 100n) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# offset 2 with one byte of output
law offset_past_start:
  {K.block_decompress(B.Octets.of_list([16, 97, 2, 0, 80, 97, 98, 99, 100, 101]), 100n) == Fail{K.Lz4BadOffset{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# five literals promised, two there
law cut_in_literals:
  {K.block_decompress(B.Octets.of_list([80, 97, 98]), 100n) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# half an offset
law cut_in_offset:
  {K.block_decompress(B.Octets.of_list([16, 97, 1]), 100n) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a length byte of 255 with nothing after it
law cut_in_length:
  {K.block_decompress(B.Octets.of_list([240, 255]), 100n) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# 115 literals promised, three there
law length_past_input:
  {K.block_decompress(B.Octets.of_list([240, 100, 1, 2, 3]), 1000n) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the last sequence after a match has four literals, not five
law last_literals_short:
  {K.block_decompress(B.Octets.of_list([16, 97, 1, 0, 64, 97, 98, 99, 100]), 100n) == Fail{K.Lz4BadBlockEnd{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the last token has a match length
law last_token_has_match:
  {K.block_decompress(B.Octets.of_list([1]), 100n) == Fail{K.Lz4BadBlockEnd{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the last match starts 9 bytes before the end, not 12
law last_match_too_close:
  {K.block_decompress(B.Octets.of_list([16, 97, 1, 0, 80, 97, 98, 99, 100, 101]), 100n) == Fail{K.Lz4BadBlockEnd{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a block after the dictionary "abcd": a match of 8 at offset 4, reaching
# back into it and on over its own bytes, then 5 literals
law dict_match:
  {K.block_decompress_dict(B.Octets.of_string("abcd"), B.Octets.of_list([4, 4, 0, 80, 101, 102, 103, 104, 105]), 100n) == Done{B.Octets.of_string("abcdabcdefghi")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# Vectors: frames and streams

# what the lz4 tool writes for empty input: FLG 0x64, BD 0x40, header
# checksum 0xA7, the end mark, the content checksum 0x02CC5D05
law empty_frame:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 0, 0, 0, 0, 5, 93, 204, 2])) == Done{B.Octets.empty()} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a compressed block, with block checksums, content size and content checksum
law frame_with_checksums:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 92, 64, 24, 0, 0, 0, 0, 0, 0, 0, 146, 12, 0, 0, 0, 60, 97, 98, 99, 3, 0, 80, 98, 99, 97, 98, 99, 8, 58, 99, 182, 0, 0, 0, 0, 254, 224, 41, 171])) == Done{B.Octets.of_string("abcabcabcabcabcabcabcabc")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# an uncompressed block (BD 0x70: blocks up to 4 MB)
law frame_uncompressed:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0])) == Done{B.Octets.of_string("Bend!")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a skippable frame (magic 0x184D2A53, 2 bytes), then a frame
law skippable_then_frame:
  {L.decompress(B.Octets.of_list([83, 42, 77, 24, 2, 0, 0, 0, 122, 122, 4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0])) == Done{B.Octets.of_string("Bend!")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# two frames: their contents, in order
law two_frames:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0, 4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0])) == Done{B.Octets.of_string("Bend!Bend!")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# no frame at all
law empty_stream:
  {L.decompress(B.Octets.of_list([])) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# not a frame
law bad_magic:
  {L.decompress(B.Octets.of_list([1, 2, 3, 4, 5, 6, 7])) == Fail{K.Lz4BadMagic{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# FLG version 00
law bad_version:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 36, 64, 167, 0, 0, 0, 0])) == Fail{K.Lz4BadVersion{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a reserved block maximum size (BD 0x30)
law reserved_bd:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 100, 48, 167, 0, 0, 0, 0])) == Fail{K.Lz4BadDescriptor{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the empty frame with its header checksum changed
law bad_header_checksum:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 100, 64, 168, 0, 0, 0, 0, 5, 93, 204, 2])) == Fail{K.Lz4BadHeaderChecksum{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the empty frame with its content checksum changed
law bad_content_checksum:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 0, 0, 0, 0, 5, 93, 204, 3])) == Fail{K.Lz4BadContentChecksum{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the frame with checksums, with its block checksum changed
law bad_block_checksum:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 92, 64, 24, 0, 0, 0, 0, 0, 0, 0, 146, 12, 0, 0, 0, 60, 97, 98, 99, 3, 0, 80, 98, 99, 97, 98, 99, 9, 58, 99, 182, 0, 0, 0, 0, 254, 224, 41, 171])) == Fail{K.Lz4BadBlockChecksum{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a content size of 25 for 24 bytes of content (FLG 0x48: content size only)
law bad_content_size:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 72, 64, 25, 0, 0, 0, 0, 0, 0, 0, 230, 12, 0, 0, 0, 60, 97, 98, 99, 3, 0, 80, 98, 99, 97, 98, 99, 0, 0, 0, 0])) == Fail{K.Lz4BadContentSize{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a block size past the block maximum size (64 KB)
law block_too_large:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 1, 0, 1, 0])) == Fail{K.Lz4BlockTooLarge{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the empty frame without its last byte
law frame_cut_short:
  {L.decompress(B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 0, 0, 0, 0, 5, 93, 204])) == Fail{K.Lz4Truncated{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# a frame's descriptor: FLG 0x5C (linked blocks, block checksums, content
# size, content checksum), BD 0x40 (64 KB blocks)
law header_info:
  {F.frame_header(B.Octets.of_list([4, 34, 77, 24, 92, 64, 24, 0, 0, 0, 0, 0, 0, 0, 146, 12, 0, 0, 0, 60, 97, 98, 99, 3, 0, 80, 98, 99, 97, 98, 99, 8, 58, 99, 182, 0, 0, 0, 0, 254, 224, 41, 171])) == Done{F.Lz4FrameInfo{False{}, True{}, True{}, Some{W.W64.from_parts(0, 24)}, None{}, 65536}} : Result<&2, &2, K.Lz4Error, F.Lz4FrameInfo>}

# one frame, and the input after it
law frame_then_rest:
  {F.frame_decompress(F.Lz4Options.default(), B.Octets.of_list([4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0, 7, 8])) == Done{F.Lz4Frame{B.Octets.of_string("Bend!"), B.Octets.of_list([7, 8])}} : Result<&2, &2, K.Lz4Error, F.Lz4Frame>}

# checksums not verified: the bad block checksum goes through
law unverified:
  {L.decompress_with(F.Lz4Options{100, False{}, B.Octets.empty()}, B.Octets.of_list([4, 34, 77, 24, 92, 64, 24, 0, 0, 0, 0, 0, 0, 0, 146, 12, 0, 0, 0, 60, 97, 98, 99, 3, 0, 80, 98, 99, 97, 98, 99, 9, 58, 99, 182, 0, 0, 0, 0, 254, 224, 41, 171])) == Done{B.Octets.of_string("abcabcabcabcabcabcabcabc")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# the output limit counts across blocks and frames
law stream_limit:
  {L.decompress_with(F.Lz4Options{9, True{}, B.Octets.empty()}, B.Octets.of_list([4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0, 4, 34, 77, 24, 96, 112, 115, 5, 0, 0, 128, 66, 101, 110, 100, 33, 0, 0, 0, 0])) == Fail{K.Lz4OutputTooLarge{}} : Result<&2, &2, K.Lz4Error, B.Octets>}

# Vectors: compression

# the empty input: the very frame the lz4 tool writes
law compress_empty:
  {C.compress(B.Octets.empty()) == B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 0, 0, 0, 0, 5, 93, 204, 2]) : B.Octets}

# "hello hello hello hello hello": the very frame the lz4 tool writes (lz4
# 1.9.4, default options)
law compress_like_the_tool:
  {C.compress(B.Octets.of_string("hello hello hello hello hello")) == B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 15, 0, 0, 0, 110, 104, 101, 108, 108, 111, 32, 6, 0, 80, 104, 101, 108, 108, 111, 0, 0, 0, 0, 121, 177, 255, 249]) : B.Octets}

# a run of 300 zero bytes: one literal, a match at offset 1 of length
# 4 + 15 + 255 + 20 (it overlaps itself), and the last 5 literals
law compress_run:
  {C.block_compress(B.Octets.zeros(300n)) == B.Octets.of_list([31, 0, 1, 0, 255, 20, 80, 0, 0, 0, 0, 0]) : B.Octets}

# frames round trip: linked 16-byte blocks with every checksum and the
# content size, and a stream fed in three pieces
law frame_round_trip_linked:
  {L.decompress(C.frame_compress(C.Lz4FrameOptions{C.Lz4Max64KB{}, 16, False{}, True{}, True{}, True{}, C.Lz4MatchFast{}}, B.Octets.of_string("abcabcabcabcabcabcabcabcabcabcabcabc-the end-abcabcabcabcabc"))) == Done{B.Octets.of_string("abcabcabcabcabcabcabcabcabcabcabcabc-the end-abcabcabcabcabc")} : Result<&2, &2, K.Lz4Error, B.Octets>}

law frame_round_trip_stream:
  {L.decompress(C.frame_stream(C.Lz4FrameOptions{C.Lz4Max256KB{}, 20, True{}, True{}, True{}, False{}, C.Lz4MatchFast{}}, [B.Octets.of_string("streamed "), B.Octets.of_string("in three pieces, "), B.Octets.of_string("in three pieces!")])) == Done{B.Octets.of_string("streamed in three pieces, in three pieces!")} : Result<&2, &2, K.Lz4Error, B.Octets>}

law frame_round_trip_text:
  {L.decompress(C.compress(B.Octets.of_string("a frame: a magic, a descriptor, blocks, a frame end"))) == Done{B.Octets.of_string("a frame: a magic, a descriptor, blocks, a frame end")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# Vectors: LZ4HC

# the documented levels (3 to 12, 9 by default), and what each level sets:
# out-of-range levels are clamped
law lz4hc_levels:
  {[H.Lz4HcParams.level(H.lz4hc_level_min()), H.Lz4HcParams.level(H.lz4hc_level_default()), H.Lz4HcParams.level(H.lz4hc_level_max()), H.Lz4HcParams.level(0), H.Lz4HcParams.level(4), H.Lz4HcParams.level(10), H.Lz4HcParams.level(11), H.Lz4HcParams.level(99)] == [H.Lz4HcParams{4, 64, False{}}, H.Lz4HcParams{256, 4096, False{}}, H.Lz4HcParams{4096, 65535, True{}}, H.Lz4HcParams{4, 64, False{}}, H.Lz4HcParams{8, 128, False{}}, H.Lz4HcParams{512, 65535, True{}}, H.Lz4HcParams{1024, 65535, True{}}, H.Lz4HcParams{4096, 65535, True{}}] : List<&2, H.Lz4HcParams>}

law lz4hc_default_level:
  {[H.lz4hc_level_min(), H.lz4hc_level_default(), H.lz4hc_level_max()] == [3, 9, 12] : List<&2, U32>}

# an LZ4HC frame (level 12) decodes back
law lz4hc_frame_round_trip:
  {L.decompress(C.compress_hc(12, B.Octets.of_string("a frame: a magic, a descriptor, blocks, a frame end"))) == Done{B.Octets.of_string("a frame: a magic, a descriptor, blocks, a frame end")} : Result<&2, &2, K.Lz4Error, B.Octets>}

# " abcd" at the third "abcdefghij" is the greedy matcher's match (5
# bytes); LZ4HC's lazy matching (level 12) takes the 10-byte one after it
law lz4hc_smaller:
  {Nat.is_lt(B.Octets.len(C.block_compress_with(C.Lz4Matcher.hc(12), B.Octets.of_string("abcdefghij abcd1234 abcdefghij, the end"))), B.Octets.len(C.block_compress(B.Octets.of_string("abcdefghij abcd1234 abcdefghij, the end")))) == True{} : Bool}
