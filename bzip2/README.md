# bend-osdev-bzip2

bzip2 decompression and compression. The decoder reads every `.bz2` file the
bzip2 tool writes (levels 1 to 9, several blocks, several streams back to
back), checks every block CRC and the stream CRCs, stops at the first
failure with a `Bzip2Error` naming it, and never answers more output than the
caller's maximum. The compressor writes streams that `bzip2 -d` decodes back
to the input.

Each stage stands alone: RLE1, move-to-front with RLE2, the Burrows-Wheeler
transform and its inverse, the Huffman codes, the bit reader and writer.
Byte strings are `Octets` (bend-osdev-bytes).

## Specification

* Joe Tsai, "BZip2 Format Specification" (2016, the `doc/bzip2-format.pdf` of
  github.com/dsnet/compress): the stream and block layout, the bit order, the
  symbol map, the selectors and their move-to-front coding, the delta-coded
  code lengths, the canonical Huffman codes, RUNA and RUNB, the inverse BWT's
  walk from origPtr, RLE1, the block and stream CRCs.
* The bzip2 manual, version 1.0.8 (`/usr/share/doc/bzip2/manual.html`, BSD
  licensed): the block sizes (100 to 900 KB), concatenated streams, the
  magic bytes, the CRCs.
* M. Burrows and D. J. Wheeler, "A Block-sorting Lossless Data Compression
  Algorithm", SRC Research Report 124 (1994): the transform and its inverse.
* U. Manber and G. Myers, "Suffix arrays: a new method for on-line string
  searches" (1993): the prefix-doubling sort the forward transform uses.
* The CRC catalogue (reveng.sourceforge.io): CRC-32/BZIP2, polynomial
  0x04C11DB7, most significant bit first, initial value and final XOR
  0xFFFFFFFF, check value 0xFC891918.

No source code of bzip2, libbzip2 or any other implementation of the format
was read. The behaviour on points the documents leave open was taken from
the bzip2 tool (1.0.8) as a black box, by experiment, and is held to it by
the differential test:

* **Randomised blocks** (the block header's randomised bit) are refused,
  `Bzip2Randomised`. The format notes used do not give the randomisation
  table, and neither the bzip2 tool (1.0.8) nor Python's `bz2` writes such
  blocks: none of the test's streams, at any level, has the bit set.
* **Over-full Huffman tables** (lengths that ask for more codes of some length
  than fit) get the codes that fit, in canonical order; the other symbols can
  never be read. A code no symbol has is `Bzip2BadHuffmanCode` when it is
  read.
* **After the last stream:** bytes that do not start a stream (the header
  fails as bad magic or a bad block size digit) are ignored, as `bzip2 -d`
  does ("trailing garbage after EOF ignored") and Python's `bz2` does;
  `Bzip2Options.ignore_trailing = False` refuses them (`Bzip2TrailingData`).
  An input that ends inside a stream header ("BZ", "BZh9") is
  `Bzip2Truncated` wherever it is, as with the tool (experiments:
  `printf hello | bzip2` followed by `garbage`, by two zero bytes, by `BZ`
  and by `BZh9`).
* **The empty input** is not a stream: `Bzip2Truncated`, as the tool says
  ("file ends unexpectedly"); Python's `bz2` answers no bytes.
* The padding bits after a stream's end are not checked; the tool does not
  check them either (experiment: `printf hello | bzip2`, its last byte's
  lowest bit flipped, decodes; the differential test has this case).
* A block's BWT may hold at most the stream's block size (level × 100,000
  bytes), else `Bzip2BlockTooLarge`; its origPtr must be below its length.
  Selectors past those the symbols use are read and ignored.

The compressor fills a block to 19 bytes below the block size (any length
up to it is valid; the margin keeps clear of the limit) and cuts a run of
equal bytes at a block's end, so each block's RLE1 decodes on its own.

## Files

| File | Holds |
|---|---|
| `bzip2.bend` | the entry file: `decompress`, `decompress_with`, `compress`, `compress_with` |
| `stream.bend` | streams: the header, the CRCs, several streams, trailing bytes, the decoding options, the output bound |
| `block.bend` | one block: its header, the symbol map, the selectors, the tables, the coded symbols, then the stages back to its bytes |
| `huffman.bend` | Huffman codes: the decoding tree from code lengths, decoding a symbol, code lengths from frequencies, the canonical codes |
| `mtf.bend` | move-to-front and RLE2 (RUNA/RUNB), both ways, alone; the symbol map |
| `bwt.bend` | the Burrows-Wheeler transform and its inverse: fast (arrays) and reference (lists) |
| `rle.bend` | RLE1, both ways |
| `bits.bend` | the bit reader and writer (most significant bit first) |
| `compress.bend` | the compressor, one-shot and streaming |
| `error.bend` | `Bzip2Error` |
| `list.bend` | list helpers (internal) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their output |
| `ref/gen.py`, `ref/run.sh`, `ref/runner.bend` | the differential test |

Bend imports do not re-export: import the files whose defs you use (for
instance `bzip2.bend`, and `error.bend` to match on the error).

## Public interface

Everything that reads input answers `Result<&2, &2, Bzip2Error, A>`.

### Decompression (`bzip2.bend`, `stream.bend`, `block.bend`)

| Def or type | Meaning |
|---|---|
| `decompress(src)` | the content of the `.bz2` file `src`, with `Bzip2Options.default()` |
| `decompress_with(opts, src)`, `stream_decode(opts, src)` | the same, with these options |
| `Bzip2Options{max, ignore_trailing}`, `Bzip2Options.default()`, `Bzip2Options.max` | the most output allowed (`U32`) and whether bytes after the last stream that do not start a stream are ignored. Default: 64 MiB, ignored |
| `stream_header(xs)` | "BZh" and the level digit at the front of a byte list: `Bzip2Head{bmax, rest}` (the block size in bytes, what follows) |
| `bzip2_crc(o)`, `bzip2_crc.spec()`, `bzip2_combine(c, b)` | CRC-32/BZIP2 of a block's bytes, its parameters in the crc package's model, and the stream CRC after one more block |
| `block_read(r, bmax, room)` | one block (or the stream's end) from a bit reader: `Bzip2BlkData{r, crc, bytes}`, `Bzip2BlkEnd{r, crc}` or `Bzip2BlkBad{e}`; the building block of a decoder that works a block at a time |

### Compression (`bzip2.bend`, `compress.bend`)

| Def or type | Meaning |
|---|---|
| `compress(o)`, `compress_with(opts, o)` | `o` as a bzip2 stream |
| `Bzip2CompressOptions{level, max_code}`, `Bzip2CompressOptions.default()` | the block size digit (1 to 9; others are taken as 9) and the longest Huffman code (9 to 20, clamped). Default: 9 and 17, as the tool |
| `Bzip2Writer.start(opts)`, `Bzip2Writer.feed(w, o)`, `Bzip2Writer.finish(w)` | streaming: `feed` answers `Bzip2Written{writer, bytes}`, the whole bytes of every block the input so far completes; `finish` answers the rest. Fed in any pieces, the output is the one-shot output |

### The stages alone

| Def or type | File | Meaning |
|---|---|---|
| `rle1_encode(o)`, `rle1_decode(o)` | `rle.bend` | RLE1: runs of 4 to 255 equal bytes as 4 and a count; every byte string decodes |
| `rle1_decode_list(ys, room)` | `rle.bend` | the same on a list, at most `room` bytes (reversed), `None` past it |
| `mtf_encode(alpha, o)`, `mtf_decode(alpha, syms, max)` | `mtf.bend` | move-to-front from the alphabet `alpha`, then RLE2: symbols 0 (RUNA), 1 (RUNB) and position + 1, as `List<&2, U32>`; decoding fails on a position past the alphabet (`Bzip2BadSymbol`) or more than `max` bytes |
| `mtf_covers(alpha, o)` | `mtf.bend` | whether `alpha` holds every byte of `o` (bytes it lacks are dropped by `mtf_encode`) |
| `symbol_map(o)` | `mtf.bend` | the bytes `o` uses, in increasing order: bzip2's alphabet |
| `mtf_decode_list(syms, alpha, room)` | `mtf.bend` | the decoder on lists |
| `bwt_forward(o)`, `bwt_inverse(last, ptr)` | `bwt.bend` | the transform (`Bzip2Bwt{last, ptr}`) and its inverse (`Bzip2BadOrigPtr` for a pointer past the end), fast |
| `bwt_forward_ref(o)`, `bwt_inverse_ref(last, ptr)` | `bwt.bend` | the same by the reference implementations (slow; for small blocks and for proofs) |
| `bwt_forward_list(xs)`, `bwt_inverse_list(xs, ptr)` | `bwt.bend` | the fast ones on lists (`Bzip2BwtList{last, ptr}`) |
| `huff_tree(lengths)`, `huff_decode(t, r)` | `huffman.bend` | the decoding tree of a table, and the next symbol from a bit reader (4294967295 when the bits match no code) |
| `huff_lengths(freqs, limit)`, `huff_codes(lengths)` | `huffman.bend` | code lengths from frequencies, at most `limit` bits; the canonical codes (an array: code in the low 24 bits, length above) |
| `Bzip2Bits`, `bits.start`, `bits.read`, `bits.flag`, `bits.align`, `bits.over`; `Bzip2Out`, `out.new`, `out.bits`, `out.finish` | `bits.bend` | the bit reader (0 past the end, which `bits.over` records) and writer |

The records (`Bzip2Options`, `Bzip2CompressOptions`, `Bzip2Bwt`,
`Bzip2BwtList`, `Bzip2Head`, `Bzip2Blk`, `Bzip2Written`, `Bzip2Error`) are
open: their constructors are part of the interface. `Bzip2Writer`,
`Bzip2Bits`, `Bzip2Out` and `Bzip2Huff` are opaque.

### Failures

| `Bzip2Error` | When |
|---|---|
| `Bzip2Truncated` | the input ends inside a stream, or is empty |
| `Bzip2BadMagic` | a stream does not start with "BZh" |
| `Bzip2BadBlockSize` | the digit after "BZh" is not 1 to 9 |
| `Bzip2BadBlockMagic` | neither a block nor a stream's end where one should start |
| `Bzip2Randomised` | a block's randomised bit is set |
| `Bzip2BadOrigPtr` | origPtr is not below the block's length |
| `Bzip2BadSymbolMap` | no byte is marked used |
| `Bzip2BadTableCount` | the number of tables is not 2 to 6 |
| `Bzip2BadSelectorCount` | no selectors |
| `Bzip2BadSelector` | a selector names a table past the last |
| `Bzip2BadCodeLength` | a code length outside 1 to 20 |
| `Bzip2BadHuffmanCode` | bits that match no code, or symbols past the selectors |
| `Bzip2BadSymbol` | a move-to-front position past the alphabet |
| `Bzip2BlockTooLarge` | a block holds more than its stream's block size |
| `Bzip2BadBlockCrc`, `Bzip2BadStreamCrc` | a CRC does not match |
| `Bzip2OutputTooLarge` | the output would pass the maximum |
| `Bzip2TrailingData` | bytes after the last stream, when refused |

## Extension points

* **Options:** `Bzip2Options` (the output bound, trailing bytes) and
  `Bzip2CompressOptions` (the block size, the code length limit), with named
  defaults.
* **A better compressor:** it writes one Huffman table (twice, since the
  format asks for two) and every selector names it. Fitting up to six tables
  to groups of symbols (the tool's iterative refinement) belongs in
  `compress.bend`'s `wr.block.syms` and `wr.sels`; nothing else changes. Its
  streams are within 3 to 5% of the tool's on text and smaller than the
  tool's on random data (see Speed).
* **The sort:** `bwt.bend`'s forward transform is prefix doubling with a
  counting sort per round; a suffix-array construction (SA-IS) can replace it
  behind `bwt_forward_list`, held to `bwt_forward_ref` by the vectors and the
  differential test.
* **Randomised blocks:** a decoder for them goes in `block.bend` (the bit is
  read in `blk.rand`) with the randomisation table as a parameter.
* **Streaming decoding:** not yet. A block is bit-aligned and carries no
  length, so a decoder fed in pieces cannot tell that a block is complete
  without decoding it: it would decode the pending block again on every feed,
  or hold its state mid-block. `block_read`, on a bit reader over the input
  so far, is the unit such a decoder is built from; `stream_decode` takes a
  whole file. The compressor streams.
* **CRC-32/BZIP2** is the crc package's parameter model
  (`bzip2_crc.spec()`, with its table-driven path); the crc package has no
  named spec for it yet.

## Dependencies

`bytes` (Octets) and `crc` (the CRC model and its table-driven path), from
bend-osdev.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer) has 27 laws.

**For every input** (proved by induction):

* `rle1_round_trip`: `rle1_decode(rle1_encode(o)) == o` for every byte
  string. The proof follows the encoder's pending run and the decoder's
  count, and a generated lemma for the 252 count values (a count byte reads
  back as the run it encodes).
* `mtf_round_trip`: `mtf_decode(alpha, mtf_encode(alpha, o), len(o) + k) ==
  Done{o}` for every `o`, every `k`, and every alphabet of at most 256 bytes
  that covers `o` (`mtf_covers`); with a vector showing the hypotheses hold
  (`mtf_covers_banana`). The proof covers move-to-front (the position the
  encoder finds is the byte the decoder takes, and moving it keeps the same
  members), the bijective base-2 digits of a run (RUNA, RUNB, one more zero
  adding the lowest weight), and the output bound.
* `bwt_ref_round_trip_constant` and `bwt_ref_round_trip_two`: the inverse of
  the forward transform is the block, by the reference implementations, for
  every block of `n` copies of one byte (every byte, every `n`: lengths 0 and
  1 included) and for every two-byte block. **The general case, every
  block, is not proved.** It needs the theory of the transform (the sorted
  rotations, the stable LF mapping), which is beyond these proofs for now.
  It is held by vectors and by the differential test, which also hold the
  fast implementations to the references: every block the decoder and the
  compressor handle goes through the fast transform and back.
* `output_bounded`: `decompress_with` never answers more than the maximum
  (through the final guard; the decoder also stops at the maximum while
  decoding).
* `bad_magic_1`, `bad_magic_2`, `bad_magic_3`: an input whose first, second
  or third byte is not "B", "Z", "h" is `Bzip2BadMagic` whatever follows,
  whatever the options; `not_magic_byte` shows the hypotheses hold;
  `empty_input`: the empty input is `Bzip2Truncated`.

The proofs reach `Octets` only through bytes' interface laws
(`octets_to_of`, `octets_of_to`, `octets_len_list`,
`octets_of_list_idempotent`), and compute through the list layer's `mask`
and `byte`. Each stage's tail-recursive form (what runs) is proved equal to
its structural form (what the round trips follow).

**Vectors** (proved by computation): RLE1 on a run; move-to-front on
"banana" and a run of four, a position past the alphabet, the bound; the
transform of "banana", both ways, fast and reference, and a pointer past
the end; empty streams from Python's `bz2` (one, two, with trailing bytes
ignored and refused); `compress` of the empty input is the tool's 14 bytes;
CRC-32/BZIP2's check value.

Vectors that decode a block, or run the whole codec, are in `check.bend`
instead of the laws: the Lean kernel behind `--verdict` runs a block's
900,000-byte limit as a unary `Nat` and does not finish (and on BWT blocks
of more than six bytes it fails with the message about a mismatch between
the implementation and the kernel, while `--check-only` proves them).

## Tests

`check.bend`: blocks from Python's `bz2` (one byte, "banana", two streams),
the output bound, a changed CRC, the randomised bit, a changed block magic, a
bad level digit, cut-off and empty inputs; `compress` of "banana" (and its
round trip), of the empty input and of a 1,000-byte run; RLE1 of the run;
both transforms of a text and the inverse; and a 359 KB input (text and
random bytes) compressed at level 1 (four blocks), decompressed, and
compressed again through the streaming writer in three pieces, which gives
the same stream (about 1.4 s and 70 MB in all).

`ref/run.sh` (needs `python3` with `bz2`; uses the `bzip2` tool when
installed, and needs no other tool) generates (`ref/gen.py`) and checks:

* **decoding, 113 cases:** streams from Python's `bz2` and the bzip2 tool at
  every level 1 to 9 (every level for some inputs, 1 and 9 for all): empty,
  one byte, text, runs of every length around RLE1's limits, zeros, random
  bytes, all 256 byte values, two symbols, mixed; several blocks (level 1
  and 2); three streams, with trailing garbage, zeros, "BZ" and "BZh9"; not
  bzip2; the empty input; a flipped padding bit; and 60 damaged copies (a byte changed, a bit
  flipped, bytes deleted, the end cut). Each answer (length and zlib CRC-32
  of the output, or an error) must be the bzip2 tool's; every damaged copy
  is refused by both;
* **compression, 42 streams:** the inputs above and a 250 KB one, at levels
  1, 2, 5 and 9, some through the streaming writer; each must decode back
  with Python's `bz2` and with `bzip2 -d`.

Seeds 1 to 5 and 2026 pass (about 6 s and 300 MB a run). Without the tool
(`BZIP2_TOOL=none`), the expected answers are Python's, and they pass too;
`run.sh` exits 77 only without `python3`'s `bz2`. The test's reference is
outside this repository (libbzip2, through the tool and Python), so it is
independent of the package.

## Speed and sizes

Every loop over the data is a tail call (the bit reader and writer, the
Huffman symbols, move-to-front, the transforms, RLE1, the block cutter, the
selectors), so nothing is limited by the stack. Measured on native builds
(Bend 2.0.37, WSL2), each run reading the file and writing the output, every
output checked with `cmp` and every stream with `bzip2 -d`:

| Input | decode `bzip2 -1` / `-9` | compress level 1 / 9 | size, level 9 (bzip2 -9) |
|---|---|---|---|
| 1 MB of text (this repository's sources) | 0.89 s / 0.84 s | 1.52 s / 1.68 s | 147,032 (141,150) |
| 4 MB of text | 3.71 s / 3.18 s | 6.04 s / 6.35 s | 555,757 (531,624) |
| 1 MB of random bytes | 1.93 s / 2.08 s | 5.33 s / 8.31 s | 1,051,923 (1,053,819) |
| 4 MB of random bytes | 7.92 s / 8.61 s | 24.6 s / 21.6 s | 4,207,302 (4,212,660) |

Peak memory: about 130 MB for 1 MB and 500 MB for 4 MB, most of it the input
and output `Octets` and the block's lists; the transforms' arrays take 4
bytes a slot. A run of 7
bytes repeated 150,000 times (1 MB, the prefix-doubling sort's worst case
after RLE1) compresses in 1.3 s. Random bytes compress slower than text:
move-to-front walks about half the alphabet per byte.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 155 cases match (113 decoded as the bzip2
tool decodes them, 42 compressed streams decode back with `bz2` and `bzip2
-d`; seeds 1 to 5 and 2026), `scripts/deps.sh` passes.
