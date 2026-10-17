# bend-osdev-lz4

LZ4 compression and decompression: the block format and the frame format.
The decoder is safe against malformed input. The compressor's blocks decode
back to its input, which is proved for every input.

Written from the LZ4 project's specifications (BSD-licensed documentation):

* the LZ4 Block Format Description (`lz4_Block_format.md`);
* the LZ4 Frame Format Description (`lz4_Frame_format.md`).

Checksums are XXH32 (seed 0), from `bend-kit-hash@0.2.0.0`. The reference
test (`ref/gen.py`) has its own XXH32, written from the xxHash specification
(`xxhash_spec.md`, from the xxHash project).

## Files

| File | Holds |
|---|---|
| `lz4.bend` | the entry file and main concern: decompressing an LZ4 stream (one frame or more, LZ4 and skippable), with options or the defaults |
| `frame.bend` | the frame format, decoding: one LZ4 frame, its header, its blocks and checksums; the decoding options |
| `block.bend` | the block format, decoding: the block decoder, the literal-only block encoder, and the error type every file answers |
| `compress.bend` | compression: the block compressor (greedy matcher, checked), the frame writer, one-shot and streaming |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

## API

Byte strings are `Octets` (bend-osdev-bytes). Everything that reads input
answers `Result<&2, &2, Lz4Error, A>`.

### Decompression

| Def | File | Meaning |
|---|---|---|
| `decompress(src)` | `lz4.bend` | the content of the stream `src`, with `Lz4Options.default()` |
| `decompress_with(opts, src)` | `lz4.bend` | the same, with these options |
| `Lz4Options{max, verify, dict}`, `Lz4Options.default()` | `frame.bend` | the most bytes to produce (`U32`); whether to verify block and content checksums; the dictionary every frame starts after. Default: 64 MiB, verified, no dictionary |
| `frame_decompress(opts, src)` | `frame.bend` | the LZ4 frame at the start of `src`: `Lz4Frame{content, rest}`, `rest` being the input after it |
| `frame_header(src)` | `frame.bend` | the frame's descriptor, `Lz4FrameInfo{indep, block_sum, content_sum, size, dict_id, block_max}` |
| `frame_checksum(o)` | `frame.bend` | XXH32 with seed 0 |
| `block_decompress(src, max)` | `block.bend` | the bytes of the block `src`, at most `max` (a `Nat`) of them |
| `block_decompress_dict(dict, src, max)` | `block.bend` | the same, for a block that may refer back into `dict` (a dictionary, or the earlier blocks of a frame); answers the block's own bytes |
| `block_literals(o)` | `block.bend` | the simplest valid block: `o` as one run of literals |
| `Lz4Error`, `Lz4Error.show` | `block.bend` | the failures, below, and their names |

### Compression (`compress.bend`)

| Def | Meaning |
|---|---|
| `compress(o)` | a frame holding `o`, with `Lz4FrameOptions.default()` |
| `frame_compress(opts, o)` | a frame holding `o`, with these options |
| `Lz4FrameOptions{block_max, block_size, indep, block_sum, content_sum, content_size}`, `Lz4FrameOptions.default()` | the block maximum size the header declares (`Lz4Max64KB`, `Lz4Max256KB`, `Lz4Max1MB`, `Lz4Max4MB`); where the content is cut into blocks (`U32`; 0, or more than the maximum, means the maximum); independent or linked blocks; block checksums; a content checksum; the content size in the header. Default: what the lz4 tool writes, 64 KB independent blocks with a content checksum |
| `frame_start(opts)`, `frame_feed(w, o)`, `frame_finish(w)` | streaming: each answers the frame's next bytes (`Lz4Written{writer, bytes}`, or the last bytes) |
| `frame_stream(opts, pieces)` | the frame the streaming writer gives for content fed in these pieces |
| `block_compress(o)` | a block for `o`: the matcher's, checked by decoding it (falling back to `block_literals(o)` should the check fail) |
| `block_compress_dict(dict, o)` | the same, for a block that may refer back into `dict` (at most its last 65535 bytes) |
| `block_compress_unchecked(o)` | the matcher's block, without the check |

The compressor is a greedy LZ77 matcher with a single-entry hash table (4096
slots, keyed by the next four bytes): it extends each match as far as the
end-of-block rules allow (a match starts 12 bytes or more before the end and
ends 5 bytes or more before it; matches may overlap themselves) and stores a
block uncompressed when compressing would not make it smaller. On the
differential test's inputs its frames are within about 15% of `lz4 -1`'s
size.

The types `Lz4Options`, `Lz4FrameInfo`, `Lz4Frame`, `Lz4Error`,
`Lz4FrameOptions`, `Lz4BlockMax` and `Lz4Written` are open records: their
constructors are part of the interface. `Lz4Writer` is opaque.

### Failures

| `Lz4Error` | When |
|---|---|
| `Lz4Truncated` | the input ends inside a block, a frame or a stream (or is empty) |
| `Lz4BadOffset` | a match offset of 0, or one before the start of the output (and dictionary) |
| `Lz4OutputTooLarge` | the output would pass the maximum, or a block would pass the block maximum size |
| `Lz4BadBlockEnd` | the end-of-block rules are broken: the last token has a match part, or after a match the last literals are fewer than 5, or the last match starts less than 12 bytes before the end |
| `Lz4BadMagic` | not an LZ4 or skippable frame where one should start (also the legacy format, which is not supported) |
| `Lz4BadVersion` | FLG's version is not 01 |
| `Lz4BadDescriptor` | a reserved bit of FLG or BD is set, or BD names a reserved block maximum size |
| `Lz4BadHeaderChecksum` | the header checksum does not match |
| `Lz4BlockTooLarge` | a block's size passes the block maximum size |
| `Lz4BadBlockChecksum`, `Lz4BadContentChecksum` | a checksum does not match (when verifying) |
| `Lz4BadContentSize` | the content size in the header is not the content's |

### Choices the specifications leave open

* The end-of-block rules are enforced: the specification allows a conformant
  decoder to reject a block that breaks them, and every block a compressor
  writes keeps them. The last token's match nibble must be 0.
* An empty block is the single token `0`; no input at all is `Lz4Truncated`.
* A stream holds one frame or more and nothing else: bytes after the last
  frame that do not start a frame are `Lz4BadMagic`.
* The header checksum is always checked; `verify` covers block and content
  checksums.
* A frame's dictionary ID is reported by `frame_header`, but the dictionary
  itself comes from the caller (`Lz4Options.dict`). The writer does not write
  dictionary IDs.

## Extension points

* **Options:** `Lz4Options` (decoding) and `Lz4FrameOptions` (writing) hold
  the real choices, with named defaults. The block functions take their limit
  directly, since a block does not record its size.
* **A better matcher** (hash chains, a high-compression parser) can replace
  the greedy one behind `block_compress`: the check keeps the round-trip law
  true whatever the matcher writes, so a new matcher needs no new proof, only
  the differential test.
* **Speed:** `block_compress` decodes every block it writes, to check it;
  `block_compress_unchecked` skips that, without the law. The decoder is the
  reference, written to be proved about: it keeps its output as a reversed
  list, so a match costs a walk back of its offset per byte. An array-based
  decoder can be added beside it, held to it by a law or by the differential
  test.
* **Streaming:** the writer streams (`frame_start`, `frame_feed`,
  `frame_finish`), but keeps the content for the content checksum, since
  XXH32 here is one-shot; a streaming XXH32 would let it forget each block
  once written. A streamed frame has no content size. A frame is decoded
  whole; `block_decompress_dict` is the building block for a streaming
  decoder.
* **Dictionaries:** `block_compress_dict` and `block_decompress_dict` take a
  dictionary; the frame writer could take one too (with its ID in the
  header).

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer) has 50 laws.

**For every input** (properties, proved by induction):

* `output_within_max`: whatever `src` and `max`, `block_decompress(src, max)`
  never answers more than `max` bytes;
* `literals_round_trip` and `literals_round_trip_dict`:
  `block_decompress(block_literals(o), len(o) + k) == Done{o}` for every byte
  string and every `k`, and the same after any dictionary;
* `block_compress_round_trip` and `block_compress_dict_round_trip`:
  `block_decompress(block_compress(o), len(o)) == Done{o}` for every `o`, and
  the same after any dictionary. Since the decoder refuses a block that breaks
  the end-of-block rules, this also says the compressor's blocks keep them;
* `offset_zero_rejected`: after any literals, a match with offset 0 is
  `Lz4BadOffset`, whatever follows;
* `offset_before_start_rejected`: a block that starts with a match is
  `Lz4BadOffset` at every offset, whatever follows.

The compressor's round trip holds for every input because `block_compress`
checks its block by decoding it and comparing, and falls back to the
literal-only block (whose round trip is proved) should they differ. The proof
covers the check and the fallback; it does not show that the greedy matcher
is right on its own, and a proof that it is (that every match it emits copies
the right bytes) is out of reach for now: it would need the matcher's array
table and its 32-bit offset arithmetic followed through the decoder bit by
bit. The differential test covers the matcher, and checks that the fallback
never happens on its inputs.

**Vectors** (proved by computation):

* decoding: the block format's examples of length bytes (48, 280 and 15
  literals); blocks with overlapping and long matches, and a dictionary; each
  malformed block (offset 0 and past the start, cut in literals, offset and
  length bytes, lengths past the input, the output limit, each end-of-block
  rule); frames and streams (the frame the lz4 tool writes for empty input,
  checksums, uncompressed blocks, skippable frames, two frames, the frame
  header, the input after a frame, unverified checksums, the limit across
  frames) and each malformed frame;
* compression: `compress` of the empty input and of
  `"hello hello hello hello hello"` are exactly the lz4 tool's frames (lz4
  1.9.4, default options); a run of 300 bytes; frame round trips with linked
  16-byte blocks and every checksum and the content size, with the streaming
  writer fed in three pieces, and with the defaults.

The frame format has vectors only: a property over frames would need XXH32
for every input, and bend-kit-hash's XXH32 is array code that bend-osdev does
not reason about. (A round trip vector on a 104-byte text proved by
`--check-only` but not by `--verdict`, which failed on it without a message;
the vector kept is shorter.)

The proofs follow the decoder byte by byte. Octets enter them only through
bytes' interface laws (`octets_append_list`, `octets_to_of`, `octets_of_to`,
`octets_len_list`), so they do not depend on how `Octets` stores its bytes.

## Tests

`ref/gen.py` holds an independent LZ4 implementation, written from the
specifications: a greedy LZ77 block encoder, a frame writer (every FLG
option, linked and independent blocks, uncompressed blocks, several blocks
per frame, skippable frames, several frames per stream, dictionaries), a
block and frame decoder, and XXH32. **It shares an author with this
package**, so it checks the package against a second reading of the
specifications. The reference `lz4` tool (1.9.4) is the independent check,
in both directions.

`ref/run.sh` (seed 2026) checks:

* **decoding, 427 cases:**
  * round trips: 60 blocks, 15 blocks after a dictionary, 40 frames and
    streams from `gen.py`'s writer, and the defaults;
  * 60 frames written by the lz4 tool over its options (`-1`, `-3`, `-9`,
    `-12`, `-B4` to `-B7`, `-B128` to `-B2048` for several blocks per frame,
    `-BD` linked blocks, `-BX` block checksums, `--content-size`,
    `--no-frame-crc`, and combinations), on random, text, repetitive and
    mixed inputs up to 12 KB;
  * the output limit: 10 blocks with a maximum one below their size;
  * corruptions: 140 blocks and 100 frames (the tool's among them) with bytes
    changed, deleted, inserted or cut off; the package must answer exactly
    what the Python decoder answers, the same bytes or the same failure;
* **compression, 68 cases**, on random, text, repetitive and mixed inputs up
  to 8 KB: 31 blocks, 8 blocks after a dictionary, 20 frames over the writer's
  options, the defaults, and 8 streamed frames. Each must decode back to its
  input with `gen.py`'s decoder and with `lz4 -d` (blocks wrapped in a frame;
  dictionary blocks through `lz4 -d -D`); `block_compress` must equal
  `block_compress_unchecked` (no fallback); repetitive inputs must shrink to
  under a quarter.

Seeds 1 to 5 also pass. Without the lz4 tool, `run.sh` runs the checks that
need no tool and exits 77 (a skip).

## Speed and limits

* The decoder works on lists, one byte at a time; a match costs a walk back
  of its offset per byte copied. The compressor's table is an array, but it
  decodes each block it writes (see Extension points).
* Bend 2.0.37's runtime overflows its stack on non-tail recursion deeper than
  about 20,000 to 30,000 calls. The decoder's own loops are tail calls, and
  decode 200 KB blocks, and bytes' `Octets` operations are tail-recursive and
  have no length limit. But some of this package's own code, and its use of
  bytes' structural list layer on whole inputs, is not tail-recursive: a
  100 KB compress-then-decompress round trip still overflows the stack, so
  keep inputs and outputs to about 20 KB until that code is converted. (List literals of a few thousand elements overflow it too, which is
  why `ref/gen.py` joins long inputs from pieces, and the tests stay under
  12 KB.)
* Block and frame sizes in the writer are `U32` counts, not `Nat`: the Lean
  kernel (`--verdict`) fails on Nat computations tens of thousands of
  successors long.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 427 decoding cases match and 68
compressed blocks and frames decode back (with `lz4` 1.9.4 installed).
