# bend-osdev-deflate

DEFLATE compression and decompression, and the zlib and gzip formats around
it: the counterpart of Linux's `lib/zlib_inflate` and `lib/zlib_deflate`,
written in Bend from the RFCs. The inflater reads every stream zlib and the
gzip tool write (stored, fixed and dynamic blocks, a 32 KB window, preset
dictionaries), refuses malformed streams as zlib refuses them, never answers
more than the caller's maximum, and can be fed a stream in pieces of any
size. The deflater has levels 0 to 9, a matcher whose strategy and level are
parameters, and chooses each block's type (stored, fixed or dynamic) by its
exact size; what it writes inflates back to its input, which is proved for
every input and every option.

Each part stands alone: the bit reader and writer, the Huffman codes, the
window, the inflater, the matcher, the dynamic Huffman encoder, the block
writer, Adler-32, and the zlib and gzip wrappers. Byte strings are `Octets`
(bend-osdev-bytes).

## Specifications

* P. Deutsch, "DEFLATE Compressed Data Format Specification version 1.3",
  RFC 1951, May 1996: the bit packing (3.1.1), the canonical Huffman codes
  (3.2.2), the block header (3.2.3, "11 - reserved (error)"), stored blocks
  (3.2.4, "NLEN is the one's complement of LEN"), the length and distance
  codes (3.2.5), the fixed codes (3.2.6, "Literal/length values 286-287 will
  never actually occur in the compressed data", "distance codes 30-31 will
  never actually occur"), the dynamic header (3.2.7, the code length code
  order, codes 16, 17 and 18, "If only one distance code is used, it is
  encoded using one bit, not zero bits", "One distance code of zero bits
  means that there are no distance codes used at all"), distances across
  blocks (3.2.3, "a distance cannot refer past the beginning of the output
  stream"), and section 4's compressor (hash chains on 3-byte sequences,
  chains "arbitrarily truncated at a certain length, determined by a
  run-time parameter", lazy matching, inserting strings "only when no match
  was found, or when the match is not "too long"").
* P. Deutsch and J-L. Gailly, "ZLIB Compressed Data Format Specification
  version 3.3", RFC 1950, May 1996: CMF, FLG, FCHECK, FDICT and DICTID,
  FLEVEL, ADLER32 (2.2), the decompressor's duties (2.3: "A compliant
  decompressor must check CMF, FLG, and ADLER32"), Adler-32 (2.2: "s1 is the
  sum of all bytes, s2 is the sum of all s1 values. Both sums are done
  modulo 65521. s1 is initialized to 1, s2 to zero.").
* P. Deutsch, "GZIP file format specification version 4.3", RFC 1952, May
  1996: members one after another (2.2), the member header and its optional
  fields, FHCRC, CRC32 and ISIZE (2.3.1), the decompressor's duties
  (2.3.1.2).
* L. L. Larmore and D. S. Hirschberg, "A Fast Algorithm for Optimal
  Length-Limited Huffman Codes", Journal of the ACM 37(3), 1990: the
  package-merge algorithm, for the dynamic codes' lengths.
* CRC-32 is bend-osdev-crc's (the ISO-HDLC parameters; check value
  0xCBF43926 from the CRC catalogue, reveng.sourceforge.io).

No source code of zlib or of any other DEFLATE implementation was read
(bend-kit-zlib, which ships foreign C and JavaScript code, is not used). What
the RFCs leave open was taken from zlib 1.3 (through Python's `zlib`
module) and the gzip tool (1.12) as black boxes, by experiment; `ref/gen.py`
holds each experiment as a test case:

* **Incomplete and over-subscribed codes.** RFC 1951 says nothing about
  them. Over-subscribed codes are refused, as zlib does. Incomplete
  literal/length and distance codes are refused unless they are a single
  code of one bit (which 3.2.7 allows for distances, and zlib for both);
  no distance codes at all is allowed. An incomplete code length code is
  refused. A literal/length code without a code for 256 is refused.
* **HLIT above 29 or HDIST above 29** (287 or 288 literal/length codes, 31
  or 32 distance codes) are refused, as zlib refuses them; the RFC allows
  the fields but says those symbols never occur.
* **A first distance that reaches before the start** is refused as soon as
  its symbol is read (its least distance is already too far); zlib refuses
  the same streams.
* **Bytes after the final block** are not part of the stream: raw and zlib
  decoding ignore them, as zlib does (`InflateOptions`' `ignore` False
  refuses them). The zlib window size (CINFO below 7) is not enforced; CINFO
  above 7 is refused.
* **gzip.** The header's CRC16 is checked (the gzip tool checks it; Python's
  `gzip` does not); a reserved flag bit is refused (RFC 1952; the gzip
  tool). After a member: nothing, or only zero bytes, ends the file; one
  byte alone is a truncated member; ID1 ID2 start another member; anything
  else is trailing garbage, ignored as the tool ignores it ("decompression
  OK, trailing garbage ignored"), or refused with `ignore` False. An empty
  file is truncated.

The levels, the matcher's parameters at each level, the block size and the
segment size are this package's own choices; RFC 1951 gives no numbers.

## Files

| File | Holds |
|---|---|
| `deflate.bend` | the entry file: `deflate`, `deflate_with`, `deflate_level`, `deflate_unchecked_with`, the streaming deflater, `stored_stream`, `DeflateOptions` (and `inflate` by name) |
| `inflate.bend` | the inflater: stored, fixed and dynamic blocks, one-shot and streaming, `InflateOptions` |
| `huffman.bend` | Huffman codes from code lengths (3.2.2), shared by both directions: the decoding tree, the code of a symbol, the encoder's table, the Kraft classes, the fixed lengths |
| `fixed.bend` | the fixed codes' trees as constants (generated by `gen/fixed.py`) |
| `bits.bend` | the bit reader (a byte's bits, a field gathered low bit first) and the bit writer |
| `window.bend` | the inflater's 32 KB window |
| `codes.bend` | the length and distance codes of 3.2.5, both ways |
| `match.bend` | the deflater's matcher: hash chains, run-length, Huffman only; its parameters, named defaults and levels |
| `dynamic.bend` | the dynamic Huffman encoder: length-limited code lengths (package-merge), the run-length coded code lengths, the dynamic header |
| `block.bend` | blocks: the choice of stored, fixed or dynamic, and the writing of each |
| `zlib.bend` | the zlib format, one-shot and streaming, both ways |
| `gzip.bend` | the gzip format, one-shot and streaming, both ways |
| `adler32.bend` | Adler-32, one-shot and streaming |
| `error.bend` | `DeflateError` |
| `eq.bend`, `table.bend` | internal: bitwise equality (for the proofs), a U32-keyed trie |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/fixed.py`, `gen/proofs.py`, `gen/vectors.py` | generators: the fixed trees; the stored-block header lemmas in `PROOF.bend`; the stream vectors in `LAWS.bend` and their proofs |
| `check.bend` | examples, with their output |
| `ref/gen.py`, `ref/run.sh`, `ref/runner.bend` | the differential test |

Bend imports do not re-export: import the files whose defs you use (for
instance `deflate.bend` and `inflate.bend`, and `error.bend` to match on the
error).

## API

Everything that reads input answers `Result<&2, &2, DeflateError, A>`.

### Raw DEFLATE (`inflate.bend`, `deflate.bend`)

| Def or type | Meaning |
|---|---|
| `inflate(src)`, `inflate_with(opts, src)` | the output of the raw stream `src` (with `InflateOptions.default()`, or these options) |
| `inflate_split(opts, src)` | the output and the bytes after the stream: `DflInflated{out, rest}` |
| `InflateOptions{max, dict, ignore}`, `InflateOptions.default()` | the most output allowed (`U32`), a preset dictionary (raw: the stream starts after it; zlib: used when FDICT asks for it), whether bytes after the stream are ignored. Default: 64 MiB, none, ignored |
| `inflate_start(opts)`, `inflate_feed(i, o)`, `inflate_finish(i)`, `inflate_done(i)`, `inflate_rest(i)`, `inflate_room(i)` | streaming: `feed` answers `DflFed{inflater, out}`, the output the bytes complete; `finish` the rest (`DflInflated`) or the failure; `done` whether the final block has ended; `rest` the bytes after it so far; `room` the output still allowed |
| `deflate(o)`, `deflate_level(l, o)`, `deflate_with(opts, o)` | `o` compressed (level 6, level `l`, these options), checked by inflating it |
| `deflate_unchecked_with(opts, o)` | the same without the check: exactly the streaming deflater's bytes |
| `DeflateOptions{matcher, blocks, block_tokens, segment}`, `.default()` (level 6), `.level(l)`, `.fast()`, `.with_matcher`, `.with_blocks` | the matcher (`DflStrategy`), the block types (`DflBlockStrategy`), the most tokens a block holds (`Nat`, 16384), the input bytes the matcher works on at a time (`Nat`, 65536) |
| `deflate_start(opts)`, `deflate_feed(d, o)`, `deflate_finish(d)` | streaming: `feed` answers `DflDeflated{deflater, bytes}`, the whole bytes its input completes; fed in any pieces, the bytes are `deflate_unchecked_with`'s |
| `stored_stream(o)` | `o` as stored blocks of at most 255 bytes: the self-check's fallback |

Level 0 writes stored blocks only (65535 bytes each); levels 1 to 9 the
hash-chain matcher with the level's parameters and blocks of the smallest
type.

### Huffman codes (`huffman.bend`)

| Def or type | Meaning |
|---|---|
| `DflTree`: `DflHNil`, `DflHLeaf{sym}`, `DflHNode{zero, one}` | a decoding tree (open) |
| `huff_tree(lengths)` | the canonical code of these lengths (3.2.2), as a tree |
| `huff_code(lengths, sym)`, `huff_path(tree, sym)` | a symbol's code (`Maybe` a bit list, first bit sent first) |
| `huff_decode(tree, bits)` | the symbol whose code starts `bits`, and the bits after it (`DflDecoded{sym, rest}`) |
| `huff_kraft(lengths)` | `DflKraftEmpty`, `DflKraftSingle` (one one-bit code), `DflKraftComplete`, `DflKraftIncomplete`, `DflKraftOver` |
| `huff_table(lengths)`, `huff_bits(tab, sym)`, `huff_len(tab, sym)` | the encoder's table: each symbol's code (bits as sent) and length |
| `huff_fixed_lit()`, `huff_fixed_dist()`, `X.fixed.lit()`, `X.fixed.dist()` (`fixed.bend`) | the fixed lengths (3.2.6) and their trees |

### The deflater's parts

| Def or type | File | Meaning |
|---|---|---|
| `match_tokens(s, hist, xs)`, `match_tokens_rev` | `match.bend` | the tokens (`DflLit{b}`, `DflMatch{len, dist}`) for `xs` after the history `hist` (at most its last 32 KB reached) |
| `DflStrategy`: `DflStratChains{p}`, `DflStratRle{}`, `DflStratHuffman{}` | `match.bend` | hash chains with parameters `p`; distance 1 only; no matches |
| `DflMatchParams{chain, nice, lazy, insert}`, `.fast()`, `.lazy()`, `.level(l)` | `match.bend` | how many chain entries a search looks at; the length that ends a search; the length below which a match waits for a lazy look at the next byte (0: greedy); the longest match whose positions go into the table |
| `dyn_lengths(freqs, limit)` | `dynamic.bend` | optimal code lengths of at most `limit` bits, complete |
| `dyn_rle(lengths)`, `dyn_header(ll, dl)`, `dyn_header_bits(h)`, `dyn_write_header(w, final, h)` | `dynamic.bend` | the code lengths with 16, 17, 18; a dynamic header, its size, writing it |
| `DflBlockStrategy`: `DflBlockAuto`, `DflBlockFixed`, `DflBlockDynamic`, `DflBlockStored` | `block.bend` | the smallest type block by block, or one type |
| `block_write(w, final, s, toks, raw)`, `blocks_write(w, final, s, n, toks, raw)` | `block.bend` | one block; tokens cut into blocks of at most `n` |
| `code_lbase`, `code_lext`, `code_dbase`, `code_dext`, `code_of_len`, `code_of_dist` | `codes.bend` | 3.2.5's tables |
| `DflOut`, `out.new`, `out.put`, `out.bit`, `out.align`, `out.bytes`, `out.finish`, `out.take`; `bits.of`, `bits.field` | `bits.bend` | the bit writer and the reader's parts |

### zlib (`zlib.bend`) and gzip (`gzip.bend`)

| Def or type | Meaning |
|---|---|
| `zlib_compress(o)`, `zlib_compress_with(ZlibOptions{deflate, flevel}, o)`, `ZlibOptions.level(l)`, `.default()` | `o` as a zlib stream; FLEVEL (`DflFlevel`: fastest, fast, default, max) follows the level |
| `zlib_decompress(src)`, `zlib_decompress_with(opts, src)` | the data of a zlib stream |
| `zlib_start`, `zlib_feed`, `zlib_finish`; `zlib_inflate_start`, `zlib_inflate_feed`, `zlib_inflate_finish` | streaming, both ways (`DflZlibWritten`, `DflZlibFed`) |
| `gzip_compress(o)`, `gzip_compress_with(GzipOptions{deflate, header}, o)`, `GzipOptions.level(l)`, `.default()` | `o` as one gzip member |
| `GzipHeader{text, mtime, xfl, os, extra, name, comment, hcrc}`, `GzipHeader.default()`, `gzip_header_bytes(h)` | the header's fields (default: no time, XFL 0, OS 255, no optional fields) |
| `gzip_decompress(src)`, `gzip_decompress_with(opts, src)` | the data of every member, joined |
| `gzip_start`, `gzip_feed`, `gzip_finish`; `gzip_inflate_start`, `gzip_inflate_feed`, `gzip_inflate_finish` | streaming, both ways (`DflGzipWritten`, `DflGzipFed`); the reader hands out data as it comes, member after member |
| `gzip_crc32(o)` | the CRC-32 gzip stores |
| `adler32(o)`, `Adler32.start()`, `Adler32.update(a, o)`, `Adler32.finish(a)` (`adler32.bend`) | Adler-32 |

The option records, `DflTok`, `DflTree`, `DflDecoded`, `DflKraft`,
`DflInflated`, the streaming result records and `DeflateError` are open
(their constructors are part of the interface). `Inflater`, `Deflater`,
`ZlibWriter`, `ZlibInflater`, `GzipWriter`, `GzipInflater`, `DflOut`,
`DflWin` and `Adler32` are opaque.

### Failures

| `DeflateError` | When |
|---|---|
| `DeflateTruncated` | the input ends inside a stream, member or header (or is empty) |
| `DeflateBadBlockType` | BTYPE 11 |
| `DeflateBadStoredLength` | NLEN is not the complement of LEN |
| `DeflateTooManyCodes` | HLIT or HDIST above 29 |
| `DeflateBadCodeLengthCode` | the code length code is over-subscribed or incomplete |
| `DeflateBadRepeat` | code 16 first, or a repeat past the lengths |
| `DeflateBadLitLenCode`, `DeflateBadDistCode` | an over-subscribed code, or an incomplete one other than a single one-bit code |
| `DeflateNoEndCode` | no code for 256 |
| `DeflateBadCodeLengthSymbol`, `DeflateBadLitLenSymbol`, `DeflateBadDistSymbol` | bits that match no code; symbols 286, 287; distance symbols 30, 31 |
| `DeflateDistanceTooFar` | a distance before the start of the output (and dictionary) |
| `DeflateOutputTooLarge` | the output would pass the maximum |
| `DeflateTrailingData` | bytes after the stream, when refused |
| `DeflateZlibBadHeader`, `DeflateZlibBadMethod`, `DeflateZlibBadWindow`, `DeflateZlibNeedDict`, `DeflateZlibBadDictId`, `DeflateZlibBadChecksum` | FCHECK, CM, CINFO, FDICT without a dictionary, the wrong dictionary, ADLER32 |
| `DeflateGzipBadMagic`, `DeflateGzipBadMethod`, `DeflateGzipReservedFlags`, `DeflateGzipBadHeaderCrc`, `DeflateGzipBadCrc`, `DeflateGzipBadSize` | ID1 ID2, CM, a reserved flag, FHCRC, CRC32, ISIZE |

## Extension points

* **Options, all with named defaults:** `InflateOptions` (maximum,
  dictionary, trailing bytes), `DeflateOptions` (matcher, block types,
  block size, segment size), `DflMatchParams` (search depth, nice length,
  laziness, insertion limit; `.fast()` greedy and `.lazy()`, and the
  levels), `ZlibOptions` (FLEVEL), `GzipOptions` and `GzipHeader` (every
  header field).
* **Another matcher** (an optimal parser, say) goes in its own file beside
  `match.bend`, answering tokens for `(hist, xs)`, with a constructor in
  `DflStrategy` and a case in `match_tokens_rev`. Its round trip comes free:
  `deflate_with` inflates whatever the matcher's tokens became, so the law
  holds for any matcher; its quality needs the differential test.
* **Block choice:** `block.bend` sizes each type exactly; a block splitter
  that cuts where the statistics change (section 4: "when it determines
  that starting a new block with fresh trees would be useful") replaces
  `blocks_write`'s fixed cut.
* **Code lengths:** `dyn_lengths` is package-merge (optimal); a faster
  heuristic can replace it behind the same signature.
* **The window** is a 15-level trie (`window.bend`); any structure that
  answers the byte at a distance can replace it (the laws follow the
  inflater's states and output, not the window's representation).
* **Speed:** the inflater walks each Huffman code one bit at a time down its
  tree; a table-driven decoder would read several bits at once.
  `deflate_unchecked_with` skips the self-check (which inflates every
  stream it writes).
* **Dictionaries:** the inflater takes one; the deflater's matcher takes a
  history (`match_tokens`'s `hist`), so a deflater with a preset dictionary
  (and zlib's FDICT on writing) is a parameter away.

## Dependencies

`bytes` (Octets) and `crc` (CRC-32 for gzip, table-driven), from
bend-osdev. Adler-32 is written here (RFC 1950 defines it in a paragraph);
bend-kit-hash is not needed.

## Laws

`LAWS.bend` has 77 laws: 15 for every input and 62 vectors.

**For every input** (proved by induction):

* `deflate_round_trip`: `inflate_with(InflateOptions{m, empty, ignore},
  deflate_with(p, o)) == Done{o}` for every byte string `o`, every
  `DeflateOptions` `p` (so every level, matcher, laziness and block type),
  every maximum `m` at least `len(o)`, trailing bytes ignored or not; and
  the same for `deflate_level(l, o)` at every `l`
  (`deflate_level_round_trip`) and `deflate(o)`
  (`deflate_default_round_trip`). `inflate` is `inflate_with` with the
  default options, so `inflate(deflate(o)) == Done{o}` for every `o` up to
  64 MiB.
* `stored_round_trip`: the same for `stored_stream(o)`.
* `zlib_round_trip`: `zlib_decompress_with(opts, zlib_compress_with(zo, o))
  == Done{o}` for every `o`, every `ZlibOptions`, every dictionary option;
  `gzip_round_trip`: the same for gzip, for every `DeflateOptions`, with the
  default header.
* `output_bounded`, `zlib_output_bounded`, `gzip_output_bounded`: whatever
  the input and options, no decoder answers more than the maximum.
* `bad_block_type`, `bad_block_type_final`: a first byte whose BTYPE is 11
  is `DeflateBadBlockType`, whatever its other five bits and whatever
  follows, with any options.
* `first_match_refused`: a final fixed block that starts with length code
  257 and any of the 32 distance codes is refused, whatever follows.
* `huff_code_decodes`: for every code lengths, every symbol with a code,
  and every bit list after it, the tree decodes the code to the symbol and
  hands on the bits after it; `huff_prefix_free`: so no symbol's code is a
  prefix of another's (if `p == q ++ more` for codes `p` of `s` and `q` of
  `t`, then `s == t`).
* `adler32_streaming`: Adler-32 over two pieces is Adler-32 over the joined
  string.

How the round trip is proved: `deflate_with` inflates the stream it wrote
(with room for exactly `len(o)` bytes) and keeps it only if the inflater
reaches the end of the stream with nothing after it and its output equals
`o`; otherwise it answers `stored_stream(o)`. The proof covers both: the
fallback's round trip by induction over the input (stored blocks of at most
255 bytes, so each block's LEN is one byte; 255 generated lemmas read their
headers), and the kept stream's by a lemma that more room changes nothing
but the room left (the inflater's state machine never sees the maximum: a
driver around it counts the room). With any bytes after the stream, the
inflater hands them on unchanged, which the zlib and gzip proofs use for
their trailers.

**Not proved for every input**, and held instead by the vectors and the
differential test:

* that the matcher, the dynamic encoder and the block writer are right on
  their own (that the stream they write is the one the check keeps): the
  check makes the round trip hold whatever they write, and the differential
  test checks the fallback never happens (no stream it compressed is the
  fallback's);
* that `huff_tree` builds 3.2.2's canonical codes for every set of lengths
  (the prefix-free law holds for whatever tree it builds; the vectors pin
  3.2.2's example and 3.2.6's fixed codes, and the fixed trees equal the
  generated constants);
* that the inflater decodes every valid stream as RFC 1951 says (the
  differential test, against zlib on thousands of streams);
* that the streaming forms (inflater, deflater, zlib and gzip readers and
  writers) equal the one-shot forms for every split (the differential test
  feeds pieces and single bytes).

**Vectors** (proved by computation): the fixed trees; 3.2.2's example
codes; 3.2.6's fixed codes; the Kraft classes; Adler-32 of "", "a",
"Wikipedia", "123456789" (Python's `zlib.adler32`); CRC-32 of "" and
"123456789" (the catalogue's check value); raw streams (stored, fixed,
dynamic, a one-bit distance code, an end-only code, a match overlapping
itself) and one malformed stream for each refusal; zlib and gzip streams
from Python, two members, trailing zeros, and each header, checksum and size
refusal. `gen/vectors.py` writes them from `ref/gen.py`'s streams, with
zlib's answers checked.

The proofs reach `Octets` only through bytes' interface laws
(`octets_to_of`, `octets_of_to`, `octets_len_list`, `octets_append_list`,
`octets_cons_list`, `octets_split_at_append`, `octets_be32_round_trip`,
`octets_le32_round_trip`, `octets_of_list_idempotent`, `rev_rev`), and
compute through the list layer's `mask`, `byte`, `le32` and `be32`.

## Tests

`check.bend`: 3.2.2's and 3.2.6's codes; stored, fixed and empty streams;
refusals; compressing (default, level 0, empty, stored, dynamic only,
run-length); zlib and gzip, two members; Adler-32 and CRC-32; and 185 KB of
text compressed at levels 1, 6 and 9, inflated back, the streaming deflater
giving the same bytes, and the streaming inflater in three pieces.

`ref/run.sh` (needs `python3` with `zlib` and `gzip`; uses the `gzip` tool
when installed) generates (`ref/gen.py`) and checks (seed 2026; seeds 1 to 3
also pass):

* **decoding, 1,498 cases** (and the streaming decoders on 415
  of them, fed in thirds or single bytes): streams from Python's `zlib` in
  all three formats at every level 0 to 9 and every strategy (default,
  filtered, Huffman only, RLE, fixed), windows of 2^9 to 2^15, memory levels
  1 and 9; the gzip tool's files at levels 1, 6 and 9; several members and
  every kind of trailing bytes; each gzip and zlib header case; 45 streams
  built by hand (each malformation, each code-completeness case); and 630
  damaged copies (a bit flipped, a byte changed or zeroed, bytes deleted or
  inserted, the end cut). Each answer (the output's length and CRC-32, or a
  refusal) must be zlib's for raw and zlib streams, and the gzip tool's for
  gzip files: every stream zlib refuses is refused, and every stream it
  accepts decodes to the same bytes;
* **compression, 351 streams**: twelve inputs (empty, one byte, text,
  prose, runs, 70 KB of zeros, random bytes, all 256 values, two symbols,
  mixed, matches more than 32 KB apart) and 150 KB of prose, at every level
  0 to 9, with each matcher and block type, in all three formats, and
  through each streaming writer. Each must decode back with Python's `zlib`
  or `gzip` and with `gzip -d`, none may be the fallback, and each streaming
  writer's bytes must equal the one-shot bytes.

The test's references (zlib through Python, and the gzip tool) are outside
this repository. The streams built by hand come from `ref/gen.py`'s own bit
writer, written from RFC 1951, and are judged by zlib.

**Compression ratio against zlib** (raw DEFLATE, bytes; zlib 1.3 through
Python at the same level):

| Input | Size | Level 1 (zlib) | Level 6 (zlib) | Level 9 (zlib) |
|---|---|---|---|---|
| prose (repository docs) | 20,000 | 8,742 (9,067) | 8,071 (8,072) | 8,073 (8,071) |
| word text | 5,283 | 902 (919) | 738 (741) | 738 (742) |
| READMEs | 150,000 | 60,598 (63,471) | 54,610 (54,534) | 54,544 (54,440) |
| 1 MB of sources and READMEs | 1,048,576 | 200,229 (212,543) | 164,933 (165,533) | 163,622 (163,637) |
| 1 MB of random bytes | 1,048,576 | 1,048,896 (1,048,896) | 1,048,896 (1,048,896) | 1,048,896 (1,048,896) |

So on text the package is 3 to 6% smaller than zlib at level 1, and within
0.2% of it at levels 6 and 9; random bytes are stored, as zlib stores them.

## Speed and sizes

Every loop over the data is a tail call (the inflater's driver, the
matcher, the token and block writers, the stored-block writer, the bit
writer), except `stored_stream`'s structural recursion, which only the
self-check's fallback runs. Measured on native builds (Bend 2.0.37, WSL2),
reading the file and writing the output:

| 1 MB | time | peak memory |
|---|---|---|
| deflate, text, level 1 / 6 / 9 (each checked by inflating it) | 2.3 / 2.7 / 3.4 s | 170 MB |
| deflate, random bytes, level 1 / 6 / 9 | 3.1 / 3.0 / 2.9 s | 250 MB |
| inflate zlib -6's stream, text / random | 1.3 / 0.9 s | 100 MB |
| the streaming inflater, the same, in three pieces | 1.3 / 1.0 s | 100 / 165 MB |

The matcher's tables (Arrays) grow with the input, up to 2^15 slots each;
the window is a trie of 32768 bytes. Memory is mostly the `Octets` and
lists of the input and output (about 80 bytes per byte held).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK
(77 laws), `check.bend` passes, `ref/run.sh` 1,498 decoding cases match
zlib and the gzip tool and 351 compressed streams decode back (seeds 2026
and 1 to 3), `scripts/deps.sh` passes.
