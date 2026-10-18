# Properties, for every input: decompression never answers more bytes than
# its limit; the one-shot decoder is the streaming decoder fed everything,
# and feeding in pieces is feeding the whole; four bytes that are no magic
# number are refused, whatever follows; a frame of raw blocks decodes back
# to its content, and so does whatever compress writes; a bit field reads
# back what was written; an FSE table and a Huffman code decode back what
# their encoders write, for every table and code.
#
# Vectors: RFC 8878's own examples (the Huffman code of its weights
# example, the FSE description field sizes of its example, the predefined
# distributions) and frames written byte by byte from its descriptions,
# among them each kind of malformed frame.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as Bi
import ./fse.bend as F
import ./huffman.bend as H
import ./xxh64.bend as X
import ./frame.bend as Fr
import ./zstd.bend as Z
import ./compress.bend as C

# Properties, for every input

# whatever the input and options, the output is at most the limit
law output_within_max:
  for +max: U32
  for +verify: Bool
  for +dict: B.Octets
  for +mw: U32
  for +src: B.Octets
  {Nat.is_le(B.Octets.len(Result.default(&2, &2, E.ZstdError, B.Octets, Z.decompress_with(Z.ZstdOptions{Fr.ZstdLimit{max}, verify, dict, mw}, src), B.Octets.empty())), U32.to_nat(max)) == True{} : Bool}

# feeding the input in two pieces is feeding it whole
law stream_pieces:
  for +opts: Z.ZstdOptions
  for +a: B.Octets
  for +b: B.Octets
  {Z.Zstd.finish(Z.Zstd.feed(Z.Zstd.feed(Z.Zstd.start(opts), a), b)) == Z.Zstd.finish(Z.Zstd.feed(Z.Zstd.start(opts), B.Octets.append(a, b))) : Result<&2, &2, E.ZstdError, B.Octets>}

# without a limit, the one-shot decoder is the streaming decoder, fed the
# input in any two pieces
law one_shot_is_streaming:
  for +verify: Bool
  for +dict: B.Octets
  for +mw: U32
  for +a: B.Octets
  for +b: B.Octets
  {Z.decompress_with(Z.ZstdOptions{Fr.ZstdNoLimit{}, verify, dict, mw}, B.Octets.append(a, b)) == Z.Zstd.finish(Z.Zstd.feed(Z.Zstd.feed(Z.Zstd.start(Z.ZstdOptions{Fr.ZstdNoLimit{}, verify, dict, mw}), a), b)) : Result<&2, &2, E.ZstdError, B.Octets>}

# a field of n bits holding v (below 2^n) reads back as v, whatever follows
law bits_round_trip:
  for +n: Nat
  for +v: Nat
  for +rest: List<&2, Bool>
  for h: {Nat.is_lt(v, Bi.ZstdBits.pow2(n)) == True{} : Bool}
  {Bi.ZstdBits.read(n, List.append(&2, Bool, Bi.ZstdBits.of_nat(n, v), rest)) == Some{Bi.ZstdBits{v, rest}} : Maybe<&2, Bi.ZstdBits>}

# for every FSE table and symbols: the bits ZstdFse.encode writes (whenever it
# writes any) decode back to the symbols, whatever follows them
law fse_round_trip:
  for +t: F.ZstdFseTable
  for +syms: List<&2, Nat>
  for +bits: List<&2, Bool>
  for +rest: List<&2, Bool>
  for h: {F.ZstdFse.encode(t, syms) == Some{bits} : Maybe<&2, List<&2, Bool>>}
  {F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, syms)) == Some{F.ZstdFseSyms{syms, rest}} : Maybe<&2, F.ZstdFseSyms>}

# for every Huffman code and symbols: the bits ZstdHuf.encode writes (whenever it
# writes any) decode back to the symbols, whatever follows them
law huf_round_trip:
  for +t: H.ZstdHufTable
  for +syms: List<&2, Nat>
  for +bits: List<&2, Bool>
  for +rest: List<&2, Bool>
  for h: {H.ZstdHuf.encode(t, syms) == Some{bits} : Maybe<&2, List<&2, Bool>>}
  {H.ZstdHuf.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, syms)) == Some{H.ZstdHufSyms{syms, rest}} : Maybe<&2, H.ZstdHufSyms>}

# a frame of raw blocks (Zstd.raw_frame: each byte in a block of its own)
# decodes back to its content, for every content
law raw_frame_round_trip:
  for +o: B.Octets
  {Z.decompress_with(Z.ZstdOptions.unlimited(), C.Zstd.raw_frame(o)) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}

# whatever compress writes decodes back to its input, for every input and
# every option
law compress_round_trip:
  for +opts: C.ZstdCompressOptions
  for +o: B.Octets
  {Z.decompress_with(Z.ZstdOptions.unlimited(), C.compress_with(opts, o)) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}

# four bytes that are neither the Zstandard magic number nor a skippable
# frame's (ZstdFrame.is_zstd, ZstdFrame.is_skippable) are refused, whatever follows
# them, whatever the limit and options (without a dictionary)
law bad_magic_refused:
  for +limit: Fr.ZstdLimit
  for +verify: Bool
  for +mw: U32
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +rest: B.Octets
  for +h: {Bool.or(Fr.ZstdFrame.is_zstd(B.mask([a, b, c, d])), Fr.ZstdFrame.is_skippable(B.mask([a, b, c, d]))) == False{} : Bool}
  {Z.decompress_with(Z.ZstdOptions{limit, verify, B.Octets.empty(), mw}, B.Octets.append(B.Octets.of_list([a, b, c, d]), rest)) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}

# Satisfiability witnesses: each hypothesis above holds for some input

law witness_bits:
  {Nat.is_lt(5n, Bi.ZstdBits.pow2(3n)) == True{} : Bool}

law witness_fse:
  {F.ZstdFse.encode(F.ZstdFse.table_ll(), [0n, 1n, 2n, 3n, 35n]) == Some{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}]} : Maybe<&2, List<&2, Bool>>}

# the code of the RFC 8878 Huffman example (below) writes symbols 0, 1, 2,
# 4, 5, 0 as 1 01 001 0000 0001 1
law witness_huf:
  {H.ZstdHuf.encode(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), [0n, 1n, 2n, 4n, 5n, 0n]) == Some{[True{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}]} : Maybe<&2, List<&2, Bool>>}

law witness_bad_magic:
  {Bool.or(Fr.ZstdFrame.is_zstd(B.mask([1, 2, 3, 4])), Fr.ZstdFrame.is_skippable(B.mask([1, 2, 3, 4]))) == False{} : Bool}

# Vectors: the examples of RFC 8878

# the Huffman example (section 4.2.1.1): weights 4, 3, 2, 0, 1 for symbols
# 0 to 4 imply weight 1 for symbol 5, and the codes 1, 01, 001, none, 0000,
# 0001
law rfc_huffman_weights:
  {H.ZstdHuf.of_weights([4n, 3n, 2n, 0n, 1n]) == Some{H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n)} : Maybe<&2, H.ZstdHufTable>}

law rfc_huffman_code_0:
  {H.ZstdHuf.code(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), 0n) == Some{[True{}]} : Maybe<&2, List<&2, Bool>>}

law rfc_huffman_code_1:
  {H.ZstdHuf.code(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), 1n) == Some{[False{}, True{}]} : Maybe<&2, List<&2, Bool>>}

law rfc_huffman_code_2:
  {H.ZstdHuf.code(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), 2n) == Some{[False{}, False{}, True{}]} : Maybe<&2, List<&2, Bool>>}

law rfc_huffman_code_3:
  {H.ZstdHuf.code(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), 3n) == None{} : Maybe<&2, List<&2, Bool>>}

law rfc_huffman_code_4:
  {H.ZstdHuf.code(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), 4n) == Some{[False{}, False{}, False{}, False{}]} : Maybe<&2, List<&2, Bool>>}

law rfc_huffman_code_5:
  {H.ZstdHuf.code(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), 5n) == Some{[False{}, False{}, False{}, True{}]} : Maybe<&2, List<&2, Bool>>}

# the predefined distributions' decoding tables (section 3.1.1.3.2.2): their
# first states (symbol, number of bits, baseline)
law rfc_predefined_ll:
  {List.take(&2, F.ZstdFseEntry, F.ZstdFse.entries(F.ZstdFse.table_ll()), 4n) == [F.ZstdFseEntry{0n, 4n, 0n}, F.ZstdFseEntry{0n, 4n, 16n}, F.ZstdFseEntry{1n, 5n, 32n}, F.ZstdFseEntry{3n, 5n, 0n}] : List<&2, F.ZstdFseEntry>}

law rfc_predefined_ml:
  {List.take(&2, F.ZstdFseEntry, F.ZstdFse.entries(F.ZstdFse.table_ml()), 4n) == [F.ZstdFseEntry{0n, 6n, 0n}, F.ZstdFseEntry{1n, 4n, 0n}, F.ZstdFseEntry{2n, 5n, 32n}, F.ZstdFseEntry{3n, 5n, 0n}] : List<&2, F.ZstdFseEntry>}

law rfc_predefined_of:
  {List.take(&2, F.ZstdFseEntry, F.ZstdFse.entries(F.ZstdFse.table_of()), 4n) == [F.ZstdFseEntry{0n, 5n, 0n}, F.ZstdFseEntry{6n, 4n, 0n}, F.ZstdFseEntry{9n, 5n, 0n}, F.ZstdFseEntry{15n, 5n, 0n}] : List<&2, F.ZstdFseEntry>}

# XXH64 (xxhash_spec.md), seed 0: the empty input and "abc"
law xxh64_empty:
  {X.ZstdXxh64.hash(W.W64.zero(), B.Octets.empty()) == W.W64.from_parts(4014398263, 1373170073) : W.W64}

law xxh64_abc:
  {X.ZstdXxh64.hash(W.W64.zero(), B.Octets.of_string("abc")) == W.W64.from_parts(1153182965, 2910259609) : W.W64}

# Vectors: frames written byte by byte from the descriptions of RFC 8878

law frame_empty_input:
  {Z.decompress(B.Octets.empty()) == Done{B.Octets.empty()} : Result<&2, &2, E.ZstdError, B.Octets>}

# single-segment, content size 3, one raw block
law frame_raw:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 3, 25, 0, 0, 97, 98, 99])) == Done{B.Octets.of_string("abc")} : Result<&2, &2, E.ZstdError, B.Octets>}

# an RLE block of 5, and the content checksum
law frame_rle_checksum:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 36, 5, 43, 0, 0, 122, 44, 253, 149, 55])) == Done{B.Octets.of_string("zzzzz")} : Result<&2, &2, E.ZstdError, B.Octets>}

# a skippable frame (2 bytes), then a frame
law frame_skippable:
  {Z.decompress(B.Octets.of_list([80, 42, 77, 24, 2, 0, 0, 0, 0, 7, 40, 181, 47, 253, 32, 3, 25, 0, 0, 97, 98, 99])) == Done{B.Octets.of_string("abc")} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_two:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 3, 25, 0, 0, 97, 98, 99, 40, 181, 47, 253, 32, 2, 17, 0, 0, 100, 101])) == Done{B.Octets.of_string("abcde")} : Result<&2, &2, E.ZstdError, B.Octets>}

# a compressed block: raw literals "bend-!", one sequence (5 literals, a
# match at offset 5 of length 14), the predefined tables
law frame_compressed:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 20, 101, 0, 0, 48, 98, 101, 110, 100, 45, 33, 1, 0, 144, 139, 22])) == Done{B.Octets.of_string("bend-bend-bend-bend!")} : Result<&2, &2, E.ZstdError, B.Octets>}

# Huffman-coded literals (one stream, direct weights), RLE sequence tables,
# and the checksum
law frame_huffman:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 36, 24, 149, 0, 0, 130, 64, 2, 6, 17, 112, 89, 31, 16, 52, 89, 108, 1, 84, 8, 1, 13, 3, 132, 164, 188, 111])) == Done{B.Octets.of_list([0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 3])} : Result<&2, &2, E.ZstdError, B.Octets>}

# a raw-content dictionary: a match of 8 reaching 16 back, into it
law frame_dictionary:
  {Z.decompress_with(Z.ZstdOptions{Fr.ZstdLimit{100}, True{}, B.Octets.of_string("0123456789abcdef"), 134217728}, B.Octets.of_list([40, 181, 47, 253, 32, 8, 53, 0, 0, 0, 1, 0, 67, 76, 32])) == Done{B.Octets.of_string("01234567")} : Result<&2, &2, E.ZstdError, B.Octets>}

# Vectors: each kind of malformed frame

law frame_bad_magic:
  {Z.decompress(B.Octets.of_list([1, 2, 3, 4, 97, 98, 99])) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_bad_checksum:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 36, 5, 43, 0, 0, 122, 0, 0, 0, 0])) == Fail{E.ZstdBadChecksum{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_reserved_bit:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 40, 3, 25, 0, 0, 97, 98, 99])) == Fail{E.ZstdReservedBit{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_block_type_3:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 3, 31, 0, 0, 97, 98, 99])) == Fail{E.ZstdBadBlockType{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_content_size:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 4, 25, 0, 0, 97, 98, 99])) == Fail{E.ZstdBadContentSize{}} : Result<&2, &2, E.ZstdError, B.Octets>}

# a 1 KB window (descriptor 0) past a max_window of 1000 bytes
law frame_window_too_large:
  {Z.decompress_with(Z.ZstdOptions{Fr.ZstdLimit{100}, True{}, B.Octets.empty(), 1000}, B.Octets.of_list([40, 181, 47, 253, 0, 0, 25, 0, 0, 97, 98, 99])) == Fail{E.ZstdWindowTooLarge{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_dictionary_mismatch:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 33, 77, 3, 25, 0, 0, 97, 98, 99])) == Fail{E.ZstdDictionaryMismatch{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_truncated:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 3, 25, 0, 0, 97, 98])) == Fail{E.ZstdTruncated{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_output_limit:
  {Z.decompress_with(Z.ZstdOptions{Fr.ZstdLimit{2}, True{}, B.Octets.empty(), 134217728}, B.Octets.of_list([40, 181, 47, 253, 32, 3, 25, 0, 0, 97, 98, 99])) == Fail{E.ZstdOutputTooLarge{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_block_too_large:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 10, 161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == Fail{E.ZstdBlockTooLarge{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_literals_exhausted:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 32, 69, 0, 0, 16, 113, 113, 1, 0, 4, 78, 11])) == Fail{E.ZstdLiteralsExhausted{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_bad_offset:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 32, 61, 0, 0, 8, 113, 1, 0, 13, 138, 16])) == Fail{E.ZstdBadOffset{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_no_huffman_tree:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 32, 53, 0, 0, 51, 128, 0, 1, 1, 0])) == Fail{E.ZstdNoHuffmanTree{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_no_fse_table:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 32, 37, 0, 0, 0, 1, 192, 1])) == Fail{E.ZstdNoFseTable{}} : Result<&2, &2, E.ZstdError, B.Octets>}

law frame_sequences_reserved:
  {Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 32, 37, 0, 0, 0, 1, 1, 1])) == Fail{E.ZstdBadSequencesHeader{}} : Result<&2, &2, E.ZstdError, B.Octets>}

# Vectors: compression

# the empty input: a single-segment frame, an empty raw block, the checksum
law compress_empty:
  {C.compress(B.Octets.empty()) == B.Octets.of_list([40, 181, 47, 253, 36, 0, 1, 0, 0, 153, 233, 216, 81]) : B.Octets}

# 40 equal bytes: one RLE block
law compress_rle:
  {C.compress(B.Octets.zeros(40n)) == B.Octets.of_list([40, 181, 47, 253, 36, 40, 67, 1, 0, 0, 114, 209, 241, 45]) : B.Octets}

# the block of frame_compressed, and the checksum
law compress_matches:
  {C.compress(B.Octets.of_string("bend-bend-bend-bend!")) == B.Octets.of_list([40, 181, 47, 253, 36, 20, 101, 0, 0, 48, 98, 101, 110, 100, 45, 33, 1, 0, 144, 139, 22, 4, 179, 94, 143]) : B.Octets}

law raw_frame_bytes:
  {C.Zstd.raw_frame(B.Octets.of_string("ab")) == B.Octets.of_list([40, 181, 47, 253, 0, 0, 8, 0, 0, 97, 8, 0, 0, 98, 1, 0, 0]) : B.Octets}
