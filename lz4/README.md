# bend-osdev-lz4

LZ4 compression and decompression: the block format and the frame format.
The decoder is safe against malformed input. The compressor has two
matchers, chosen by a parameter: a fast greedy one, and LZ4HC's hash-chain
search at levels 3 to 12. Both write ordinary LZ4 blocks, and their blocks
decode back to their input, which is proved for every input.

Written from the LZ4 project's specifications (BSD-licensed documentation):

* the LZ4 Block Format Description, `doc/lz4_Block_format.md`
  (<https://github.com/lz4/lz4/blob/dev/doc/lz4_Block_format.md>): the
  sequences ("Compressed block format"), the end-of-block rules ("End of
  block conditions": the last 5 bytes are literals, the last match starts 12
  bytes or more before the end), and, under "Implementation notes",
  "Compression techniques": the format makes no assumption about how a
  compressor searches for and selects matches;
* the LZ4 Frame Format Description, `doc/lz4_Frame_format.md`, version
  1.6.4 (<https://github.com/lz4/lz4/blob/dev/doc/lz4_Frame_format.md>):
  the frame, its descriptor, data blocks, skippable frames;
* for LZ4HC, documentation only (no LZ4 source was read, for LZ4HC or
  anything else):
  * the lz4 README (<https://github.com/lz4/lz4/blob/dev/README.md>): LZ4_HC
    is a high-compression derivative, trading CPU time for compression
    ratio, with the same decompression speed;
  * the lz4(1) manual, lz4 1.10.0
    (<https://manpages.debian.org/unstable/lz4/lz4.1.en.html>), "Operation
    modifiers": `-#` takes levels 1 to 12, values above 12 are the same as
    12, 9 is the recommended level for high compression, and `--best` is
    12;
  * the LZ4 frame API manual, `doc/lz4frame_manual.html`
    (<https://github.com/lz4/lz4/blob/dev/doc/lz4frame_manual.html>,
    `LZ4F_preferences_t`): levels above the maximum count as the maximum,
    currently 12;
  * the `lz4` tool's own help, `lz4 -H` (1.9.4, observed as a black box):
    "-0 ... -2" are fast compression, all identical, and "-3 ... -12" high
    compression;
  * Yann Collet, "LZ4 explained" (RealTime Data Compression, 2011-05-26,
    <http://fastcompression.blogspot.com/2011/05/lz4-explained.html>): there
    is no restriction on how matches are found (full search with hash
    chains, MMC or BSTs, a fast scan), and LZ4-HC keeps full format
    compatibility.

  So the documents fix LZ4HC's output format (ordinary blocks), its levels
  (3 to 12 are high compression, 9 recommended, above 12 the same as 12)
  and that it searches harder for matches. They do not fix how: the
  hash-chain search here, its table sizes (a 2^15-slot head table, a
  65536-slot chain table) and every level's `depth`, `nice` and `lazy` (the
  table under LZ4HC below) are this package's own choices, as is mapping a
  level below 3 to 3 (the tool's levels 1 and 2 are its fast mode, which is
  `Lz4MatchFast` here).

Checksums are XXH32 (seed 0), from `bend-kit-hash@0.2.0.0`. The reference
test (`ref/gen.py`) has its own XXH32, written from the xxHash specification
(`xxhash_spec.md`, from the xxHash project).

## Files

| File | Holds |
|---|---|
| `lz4.bend` | the entry file and main concern: decompressing an LZ4 stream (one frame or more, LZ4 and skippable), with options or the defaults |
| `frame.bend` | the frame format, decoding: one LZ4 frame, its header, its blocks and checksums; the decoding options |
| `block.bend` | the block format, decoding: the block decoder, the literal-only block encoder, and the error type every file answers |
| `compress.bend` | compression: the greedy matcher, the choice of matcher (`Lz4Matcher`), the checked block compressor, the frame writer, one-shot and streaming |
| `hc.bend` | the LZ4HC matcher: hash chains, its parameters and levels |
| `seq.bend` | the sequence writer both matchers share (tokens, length bytes, offsets); internal |
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
| `block_compress_with(m, o)`, `block_compress_dict_with(m, dict, o)`, `block_compress_unchecked_with(m, o)` | the same three with the matcher `m` |
| `compress_hc(level, o)` | a frame holding `o`, with the default options but LZ4HC at this level |
| `Lz4Matcher`: `Lz4MatchFast{}`, `Lz4MatchHC{params}`; `Lz4Matcher.default()` (fast), `Lz4Matcher.hc(level)` | which matcher writes the blocks |
| `Lz4FrameOptions.with_matcher(opts, m)` | the same options with another matcher |

### LZ4HC (`hc.bend`)

| Def | Meaning |
|---|---|
| `Lz4HcParams{depth, nice, lazy}` | how many chain entries a search looks at (`U32`), at most; a match this long (`U32`) ends the search; whether to look one position ahead before taking a match (lazy matching) |
| `Lz4HcParams.level(l)`, `Lz4HcParams.default()` | the parameters of level `l` (below 3 is 3, above 12 is 12); the default is level 9 |
| `lz4hc_level_min()`, `lz4hc_level_default()`, `lz4hc_level_max()` | 3, 9 and 12 |

| Level | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|
| depth | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 4096 |
| nice | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 | 65535 | 65535 | 65535 |
| lazy | no | no | no | no | no | no | no | yes | yes | yes |

The LZ4HC matcher keeps two tables: a head table (2^15 slots, keyed by a
hash of the next four bytes) holding the latest position with each hash, and
a chain table of 65536 slots, the LZ4 window, holding for each position the
one before it with the same hash. At each position it walks the chain,
newest first, through at most `depth` candidates within 65535 bytes, and
takes the longest match; every position, inside matches too, goes into the
tables. With `lazy`, before taking a match it searches the next position,
and makes this byte a literal if a longer match starts there. It keeps the
same end-of-block rules as the greedy matcher, and takes a dictionary the
same way.

The fast matcher (the default) is a greedy LZ77 matcher with a single-entry
hash table (4096 slots, keyed by the next four bytes): it extends each match as far as the
end-of-block rules allow (a match starts 12 bytes or more before the end and
ends 5 bytes or more before it; matches may overlap themselves) and stores a
block uncompressed when compressing would not make it smaller. On the
differential test's inputs its frames are within about 15% of `lz4 -1`'s
size.

The types `Lz4Options`, `Lz4FrameInfo`, `Lz4Frame`, `Lz4Error`,
`Lz4FrameOptions`, `Lz4BlockMax`, `Lz4Written`, `Lz4Matcher` and
`Lz4HcParams` are open records: their constructors are part of the
interface. `Lz4Writer` is opaque. `Lz4FrameOptions` gained its last field,
`matcher`, with LZ4HC: code that builds the record by its constructor adds
`Lz4MatchFast{}` (or uses `Lz4FrameOptions.default()` and
`Lz4FrameOptions.with_matcher`).

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
* **The matcher** is a parameter (`Lz4Matcher`, and `Lz4FrameOptions`'s
  `matcher` for frames): the greedy one, or LZ4HC with any `Lz4HcParams`
  (the levels are named defaults; `depth`, `nice` and `lazy` can be set
  directly). Another matcher (an optimal parser, say) goes in its own file
  beside `hc.bend`, answering a byte list for `(dict, xs)` and writing its
  sequences with `seq.bend`, with a constructor in `Lz4Matcher` and a case in
  `cmp.block_with` (`compress.bend`). Its round-trip law comes free:
  `block_compress_with` checks every block by decoding it, whatever the
  matcher wrote, so the proof is the two lines `lz4hc_round_trip`'s is; its
  quality needs the differential test.
* **LZ4HC's tables:** the chain table's 65536 slots are the 64 KB window the
  format allows offsets to reach; the head table's 15 bits are this
  package's choice. Both are inside `hc.bend`, so a different hash or table
  size changes that file alone.
* **Speed:** `block_compress` decodes every block it writes, to check it;
  `block_compress_unchecked` skips that, without the law. The decoder is
  written to be proved about: it keeps its output as a reversed list, and a
  window over the last 64 KB (a binary trie keyed by position, depth 16) that
  matches read from, so a match costs a few steps per byte however far back
  it reads. The laws hold whatever the window answers (they follow lengths,
  literals and failures, not the bytes a match copies), so the window can be
  replaced by any structure that answers the byte at an offset; the vectors
  and the differential test check the bytes.
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

`LAWS.bend` has 57 laws. Seven are new with LZ4HC, and two (the frame round
trips with explicit options) gained the `matcher` field in their options.

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
  `Lz4BadOffset` at every offset, whatever follows;
* `lz4hc_round_trip` and `lz4hc_dict_round_trip`:
  `block_decompress(block_compress_with(Lz4MatchHC{p}, o), len(o)) == Done{o}`
  for every `o` and every `Lz4HcParams` `p` (so at every level, and for any
  depth, nice length and laziness), and the same after any dictionary;
* `block_compress_with_fast`: `block_compress_with(Lz4MatchFast{}, o)`
  is `block_compress(o)`, for every `o`, so the accepted laws about
  `block_compress` hold for the fast matcher chosen through the option.

The compressor's round trip holds for every input because `block_compress`
checks its block by decoding it and comparing, and falls back to the
literal-only block (whose round trip is proved) should they differ. The proof
covers the check and the fallback; it does not show that the greedy matcher
is right on its own, and a proof that it is (that every match it emits copies
the right bytes) is out of reach for now: it would need the matcher's array
table and its 32-bit offset arithmetic followed through the decoder bit by
bit. The differential test covers the matcher, and checks that the fallback
never happens on its inputs.

The round-trip law (`block_compress_round_trip`) is stated for
`block_compress`, whose matcher is fixed, not for any matcher, so LZ4HC has
its own: `lz4hc_round_trip`. It holds for the same reason: `block_compress_with`
checks whatever block the matcher wrote, so its proof is the same lemmas
(`check_ok`, `check_ok_dict`) applied to the HC matcher's block. As for the
greedy matcher, the proof does not show that the hash-chain search is right
on its own; the differential test does that, and checks that the fallback
never happens.

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
  writer fed in three pieces, and with the defaults;
* LZ4HC: `lz4hc_levels` and `lz4hc_default_level`, the documented
  levels (3, 9, 12) and the parameters each sets, out-of-range levels
  clamped; `lz4hc_frame_round_trip`, a level-12 frame decodes back;
  `lz4hc_smaller`, a text where the level-12 block is smaller than the greedy
  one (the greedy matcher takes a 5-byte match where lazy matching finds a
  10-byte one a byte later).

The frame format has vectors only. XXH32 is not what stands in the way: a
frame round trip can treat it as an opaque function (bend-osdev does not
reason about bend-kit-hash's array code), since it needs only that the
checksum the writer stores equals the one the reader computes over the same
bytes, which is `U32.is_eq` reflexivity. What a frame round trip still
needs, and this release does not prove:

* the block size field: the reader takes a block's size and its
  "uncompressed" flag from the bits of the word the writer builds with
  `U32.from_nat` of the block's length (with `U32.or` 2^31 for a stored
  block), so the top bit of that word must be shown to be 0 for every length
  up to the block maximum, and the masks followed bit by bit;
* the room: the reader decodes a compressed block of n bytes with room
  min(room, block maximum, 256 (n + 1)) (`U32.mul`), and the writer checked
  it with room exactly its length, so it needs the block decoder to answer
  the same with more room, and a block's output to be at most 256 (n + 1)
  bytes (a bound over the decoder's states);
* linked blocks: the writer checks a block after the last 65535 bytes of the
  frame, the reader decodes it after the whole frame so far, so it needs the
  decoder's window (a trie keyed by the position modulo 65536) to answer the
  same for the same last 64 KB (the chunking lemmas);
* the cutting of the content into blocks (counted in U32), the fuel of the
  writer's and the reader's loops, the header's FLG and BD bits for every
  option, the content size (`le64` of the length, `W64` equality) and the
  stream around the frame. (A round trip vector on a 104-byte text proved by
`--check-only` but not by `--verdict`, which failed on it without a message;
the vector kept is shorter. The same happened to an LZ4HC frame vector on
the 40-byte text of `lz4hc_smaller`, with either matcher; the frame vector
uses `frame_round_trip_text`'s text instead.)

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
* **compression, 113 cases**, on random, text, repetitive and mixed inputs up
  to 8 KB: 31 blocks, 8 blocks after a dictionary, 20 frames over the writer's
  options, the defaults, and 8 streamed frames, with the fast matcher; and
  with LZ4HC, 30 blocks (three at each level 3 to 12: one of any kind, one of
  word text and one of prose, slices of this repository's CONVENTIONS.md,
  AGENTS.md and REVIEW.md, 2 to 8 KB), 6 blocks after a dictionary, 8 frames
  over the writer's options at random levels, and `compress_hc(12, …)` of
  6 KB of prose. Each must decode back to its input with `gen.py`'s decoder
  and with `lz4 -d` (blocks wrapped in a frame; dictionary blocks through
  `lz4 -d -D`); `block_compress` must equal `block_compress_unchecked`, and
  `block_compress_with` `block_compress_unchecked_with` (no fallback);
  repetitive inputs must shrink to under a quarter; and at levels 9 to 12
  every text and prose block must be no larger than the fast matcher's block
  for the same input.

  The sizes measured (seed 2026; ratio = input / output; the lz4 tool's
  frames on the same inputs, which carry about 15 bytes of frame each, for
  comparison):

  | Inputs | Input bytes | LZ4HC | fast matcher | `lz4 -1` | `lz4 -9` | `lz4 -12` |
  |---|---|---|---|---|---|---|
  | levels 9 to 12, prose (4 blocks) | 18,171 | 12,770 (1.423) | 13,679 (1.328) | 1.351 | 1.425 | 1.426 |
  | levels 9 to 12, word text (4 blocks) | 18,961 | 6,554 (2.893) | 9,339 (2.030) | 2.040 | 2.862 | 2.907 |
  | levels 3 to 8, prose (6 blocks) | 39,845 | 25,670 (1.552) | 27,946 (1.426) | | | |
  | levels 3 to 8, word text (6 blocks) | 27,491 | 10,613 (2.590) | 13,584 (2.024) | | | |

  So at the high levels LZ4HC compresses text and prose about 7% (prose) to
  30% (word text) smaller than the fast matcher, and within about 0.5% of
  the lz4 tool's own `-9` and `-12`.

Seeds 1 to 5 also pass. Without the lz4 tool, `run.sh` runs the checks that
need no tool and exits 77 (a skip).

`check.bend` also compresses and decompresses a 70 KB block, past the
decoder's 64 KB window (see Speed and limits). The 1 MB round trips in Speed
and limits were run by hand against the lz4 tool, not in CI.

## Speed and limits

* Nothing recurses over the data's length except as a tail call: the
  decoder, both matchers, the frame reader and writer, the stream reader and
  the length bytes of a literal run (`lit.ext`, tail-recursive, proved equal
  to the structural `lit.ext.ref` the proofs follow) all run in constant
  stack, and use bytes' tail-recursive list forms (`len.fast`,
  `append.fast`, `take.fast`, `to_string.fast`, `rev_onto`). What still
  recurses is bounded: the window trie (depth 16), a frame header's fields.
* Measured on native builds (Bend 2.0.37, `bend file.bend -o prog`, WSL2;
  one process each, checked against `lz4` 1.9.4):

  | 1 MB (1,048,576 bytes) | time, native | peak memory, native | JavaScript lane, before |
  |---|---|---|---|
  | `compress`, text (lz4 -d gives it back) | 2.4 s | 127 MB | 11 s, 2.2 GB |
  | `decompress` of `lz4 -1`'s frame, text | 1.8 s | 128 MB | 14 s, 2.3 GB |
  | `decompress` of `lz4 -9 -BD -BX -B7 --content-size`'s frame (linked 4 MB blocks, block checksums) | 1.9 s | 128 MB | 17 s, 2.5 GB |
  | `frame_compress`, linked 4 MB blocks, every checksum and the size | 2.1 s | 152 MB | 12 s, 2.2 GB |
  | `frame_stream`, 256 KB blocks of 100,000 bytes, fed in two pieces | 2.4 s | 155 MB | 15 s, 2.8 GB |
  | `block_compress`, one 1 MB block (`block_decompress` gives it back) | 2.0 s | 179 MB | 17 s, 2.0 GB |
  | `block_decompress` of `lz4 -1 -B7`'s 1 MB block | 1.5 s | 126 MB | 11 s, 1.8 GB |
  | random bytes (stored blocks): `compress`, `decompress`, `block_compress` | 2.5, 0.76, 1.9 s | 132, 128, 250 MB | 11, 13, 20 s; 2.8, 2.6, 2.9 GB |
  | `compress_hc` at levels 3, 9 and 12, text (lz4 -d gives each back) | 2.7, 2.8, 3.8 s | 112 MB | |

  On that 1 MB of text (this release's sources), in 64 KB independent blocks
  (the writer's default), the frames are: fast matcher 309,845 bytes
  (`lz4 -1 -B4`: 298,775), LZ4HC level 3 256,042 (`lz4 -3 -B4`: 226,142),
  level 9 230,661 (`lz4 -9 -B4`: 221,169), level 12 223,946 (`lz4 -12 -B4`:
  219,314): LZ4HC is within 2 to 4% of the tool at levels 9 and 12, and
  further behind at low levels, where the tool's search differs more from
  this package's depths.

  These include reading the input from a file and writing the output (the
  text is this repository's sources). At 256 KB, `compress` takes 0.58 s
  and 35 MB, `decompress` 0.47 s and 34 MB; at 100 KB, 0.19 s and 17 MB, and
  0.15 s and 15 MB (on the JavaScript lane: 3.9 s and 660 MB, 3.4 s and
  720 MB; 1.5 s and 400 MB, 1.7 s and 380 MB). At 16 MB (base64 text, which
  lz4 stores rather than compresses), `compress` takes 43 s and
  `decompress` 12 s, each peaking at 2.0 GB. Before this release, 100 KB
  overflowed the JavaScript lane's stack.
* The limit now is memory, not the stack (a native build has a 2 GB stack):
  natively a call costs about 60 MB per MB of input and output together
  (1 MB in and 1 MB out peak at about 130 MB, 16 MB and 16 MB at 2.0 GB; an
  `Octets` holds about 80 bytes per byte; it was about 940 on the
  JavaScript lane when first measured, where 1 MB in and out took almost
  2 GB), so keep a single call to a few MB, or work a block at a time
  (`block_decompress_dict`, the streaming writer). Converting 1 MB to and
  from `Octets` takes well under a second natively (about 4 s on the
  JavaScript lane).
* List literals of a few thousand elements overflow the stack, which is why
  `ref/gen.py` joins long inputs from pieces, and its cases stay under 12 KB.
  `check.bend` holds one large case, a 70 KB block (past the decoder's 64 KB
  window, with matches reaching back up to 64 KB) compressed and decompressed
  (0.33 s and 19 MB natively with the rest of the file; about 2 s and
  400 MB on the JavaScript lane), and the same block with LZ4HC at level 9
  (with it, the whole file takes 0.97 s and 21 MB natively).
* Block and frame sizes in the writer are `U32` counts, not `Nat`: the Lean
  kernel (`--verdict`) fails on Nat computations tens of thousands of
  successors long.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(13 s, 0.50 GB peak; `--verdict` 51 s, 0.55 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 427 decoding cases match and 113
compressed blocks and frames (45 of them LZ4HC's) decode back (with `lz4`
1.9.4 installed; seeds 2026 and 1 to 5). 1 MB round trips, block and frame,
compressed and stored, and LZ4HC frames at levels 3, 9 and 12, pass against
`lz4` 1.9.4 (by hand); inputs are limited by `Octets` memory, not by the
stack.
