# bend-osdev-xz

Decompression of `.xz` files, safe against malformed input: every CRC32,
every block check, the index, the footer and every padding byte is checked,
and the decoder stops at the first failure with an `XzError` naming it. It
never answers more output than the caller's maximum. Corrupted data is
caught as far as the file's check (CRC32, CRC64 or SHA-256) allows; a file
with no check can only be caught by its structure.

Inputs and outputs are `Octets` (bend-osdev-bytes).

## Specifications

* "The .xz File Format", version 1.2.x, Lasse Collin and Igor Pavlov (public
  domain): the stream header and footer, blocks and block headers, filter
  flags, the index, variable-length integers, stream padding, the check IDs,
  the LZMA2 and delta filters' properties.
* The LZMA specification in the LZMA SDK ("lzma-specification", Igor Pavlov,
  public domain): the range decoder, literals with lc/lp/pb, matches and rep0
  to rep3, the state machine, length and distance coding. LZMA2's chunk
  format follows the description of the LZMA2 filter in the .xz format.

The code was written from these specifications; no source of xz-utils,
liblzma, the LZMA SDK or any GPL implementation was read.

## Files

| File | What it holds | Public |
|---|---|---|
| `xz.bend` | the entry: `.xz` files, one-shot and streaming | yes |
| `container.bend` | the container's fields: stream header and footer, block headers and filter flags, the index, variable-length integers | yes |
| `lzma2.bend` | the LZMA2 decoder (chunks, resets, the dictionary), one-shot and streaming, usable without the container | yes |
| `integrity.bend` | the block checks: none, CRC32, CRC64, SHA-256 | yes |
| `delta.bend` | the delta filter's decoder | yes |
| `error.bend` | `XzError`, one constructor per failure, and messages | yes |
| `lzma.bend` | the LZMA decoder, one chunk at a time | internal |
| `rangecoder.bend` | the range decoder and its probabilities | internal |

Bend imports do not re-export: a user imports the files whose defs they use
(for instance `xz.bend` and `error.bend`, to match on the error).

## Public interface

### `xz.bend`

| Def or type | Meaning |
|---|---|
| `XzParams{max_out: U32}`, `XzParams.default()` (16 MiB), `XzParams.max_out` | the parameters: the most output allowed (a `U32`, so at most 4 GiB - 1: positions in the dictionary are 32-bit) |
| `xz_decode(p, input) -> Result<&2, &2, XzError, Octets>` | a whole `.xz` file (one or more streams, with stream padding): its data, or the first failure |
| `XzDecoder.start(p) -> XzDecoder` | a streaming decoder |
| `XzDecoder.feed(d, input) -> Result<&2, &1, XzError, XzFed>` | more input; `XzFed{dec, out}` holds the output decoded so far |
| `XzDecoder.finish(d) -> Result<&2, &2, XzError, Octets>` | the end of the input: fails unless the file may end here (`XzTruncated`, or `XzBadPadding`); answers any output not yet answered (normally none) |

The streaming decoder releases output a chunk at a time, before the block's
check is verified (as `xz` itself does); `xz_decode` answers nothing unless
the whole file is valid. `feed` answers `Result<&2, &1, …>` rather than
`Result<&2, &2, …>` because the decoder holds arrays (the dictionary and the
probabilities), which are linear (`Type`), not `Data`.

### `lzma2.bend`

| Def or type | Meaning |
|---|---|
| `XzLzma2.decode(dict_size, max_out, input)` | a whole raw LZMA2 stream (and nothing after its end marker: `XzTrailingData`) |
| `XzLzma2.start(dict_size, max_out)`, `XzLzma2.feed(d, input)`, `XzLzma2.finish(d)` | the same in pieces; `XzLzma2Fed{dec, out, ended}`; `finish` answers `XzLzma2End{rest, consumed, room}`: the bytes after the end marker, the stream's size, and how much more output the maximum allows |
| `XzLzma2.dict_size(b) -> Maybe<&2, U32>` | the dictionary size of an LZMA2 properties byte |

### `container.bend`

| Def or type | Meaning |
|---|---|
| `XzStream.header(o)` | a stream header at the front of `o`: its check ID |
| `XzStream.footer(o)` | a stream footer: `XzFooter{backward, check}` (the index size, the check ID) |
| `XzStream.block_header(o)` | a block header: `XzBlockHeader{size, csize, usize, filters}`, filters as `XzFilter{id, props}` |
| `XzStream.index(o)` | an index: `XzIndex{records, size}`, records as `XzRecord{unpadded, uncompressed}` |
| `XzStream.vli(o)` | a variable-length integer |

These types are open: users may match on their constructors. Each parser
reads its structure at the front of `o` and checks its CRC32; `XzTruncated`
means `o` ended too soon, and nothing else.

### `integrity.bend`, `delta.bend`, `error.bend`

| Def or type | Meaning |
|---|---|
| `XzCheck` (open), `XzCheck.size(id)`, `XzCheck.start(id)`, `XzCheck.update(c, o)`, `XzCheck.finish(c)`, `XzCheck.compute(id, o)` | a block check, in pieces; `finish` gives the field as stored (CRCs little-endian, the SHA-256 digest) |
| `XzDelta`, `XzDelta.start(distance)`, `XzDelta.update(d, o)` (`XzDeltaOut{dec, out}`), `XzDelta.decode(distance, o)` | the delta filter, distance 1 to 256 |
| `XzError` (open), `XzError.show`, `XzError.check_name`, `XzError.filter_name` | the failures; the messages name an unsupported check or filter ("unsupported filter 4 (x86 BCJ)") |

`XzError`'s constructors: `XzTruncated`, `XzBadMagic`, `XzBadFooterMagic`,
`XzBadHeaderCrc`, `XzBadBlockHeaderCrc`, `XzBadIndexCrc`, `XzBadFooterCrc`,
`XzBadCheck`, `XzBadStreamFlags`, `XzFlagsMismatch`, `XzBadBlockHeader`,
`XzBadFilterProps`, `XzBadBlockSize`, `XzBadIndex`, `XzBadBackwardSize`,
`XzBadPadding`, `XzUnsupportedCheck{id}`, `XzUnsupportedFilter{id}`,
`XzCorruptLzma`, `XzOutputTooLarge`, `XzTrailingData`.

## What is supported

* Checks: none, CRC32, CRC64, SHA-256. The other check IDs are refused with
  `XzUnsupportedCheck{id}` (the format allows a decoder to skip them; this
  one does not decode data it cannot verify).
* Filters: LZMA2, and any number of delta filters before it. The BCJ filters
  (x86, PowerPC, IA-64, ARM, ARM-Thumb, SPARC, ARM64, RISC-V) are refused with
  `XzUnsupportedFilter{id}`, named in the message.
* Concatenated streams, stream padding, block headers with or without their
  sizes, any dictionary size.

## Extension points

* **The output limit** is the parameter `XzParams.max_out` (for LZMA2,
  `max_out`); memory follows it too, since the dictionary array never grows
  past the output allowed.
* **More filters**: a BCJ decoder goes in its own file beside `delta.bend`,
  with a case in `Xz.filter.err.mid` and `Xz.chain.build` (`xz.bend`).
* **More checks**: `integrity.bend` holds the table of check IDs; the
  SHA-256 provider (bend-collections) is used only there, so it can be
  replaced (for instance by a streaming SHA-256) without touching the rest.
* **The dictionary** is an `Array<U32>` inside `lzma2.bend` and `lzma.bend`,
  grown by doubling up to the dictionary size; another store can replace it
  there alone.
* **LZMA without LZMA2** (`.lzma` files, 7z): `lzma.bend` decodes a chunk of
  LZMA data given its registers and probabilities; a public LZMA1 decoder
  can be built on it. It is internal until then.

## Dependencies

`bytes`, `word64` and `crc` (CRC-32 and CRC-64/XZ) from bend-osdev, and
`bend-collections@1.0.0.0` (MIT, Giulio Rebuffo) for SHA-256: a pure,
verified implementation already on the hub, used only by `integrity.bend`.

## Laws

`LAWS.bend`:

* **for every input:**
  * `xz_decode` never answers more output than `max_out` (proved through the
    final guard in `xz_decode`; the LZMA2 decoders also refuse to pass the
    limit while decoding, which the differential test exercises);
  * an input whose first byte is not 0xFD is `XzBadMagic`, whatever follows;
    the empty input is `XzTruncated`, whatever the parameters;
  * an LZMA2 stream whose first chunk does not reset the dictionary is
    `XzCorruptLzma`, and so is one opened by a reserved control byte (0x03
    to 0x7F), whatever follows, for every dictionary size and maximum; the
    end marker alone is the empty stream.
* **vectors:** small `.xz` files made by Python's `lzma` decode to their
  data (no blocks; one block with an uncompressed chunk and a CRC32); a
  changed block check and a changed header CRC32 are caught; LZMA2
  uncompressed chunks, the output limit, and the dictionary sizes.

The decoding of LZMA data itself has no law: proving it would need a model
of LZMA to compare with. It is held to Python's `lzma` and the `xz` tool by
the differential test below, said plainly here.

## Tests

`check.bend`: one case per failure (each `XzError` the container can
answer, the unsupported check and filter, the output limit), a file fed one
byte at a time, raw LZMA2, the delta filter, the tables, and two large
inputs, beyond what a decoder recursing once per byte could reach: an
820-byte `.xz` file decoding to 100 KiB, and a 100 KiB raw LZMA2 stream of
two uncompressed chunks (64 KiB and 36 KiB), each checked by its length and
CRC32 (natively the whole of `check.bend` runs in 0.08 s and 16 MB; on
the JavaScript lane the two took about 0.7 s and 0.2 GB more than the rest
of the file).

`ref/run.sh` (needs `python3` with `lzma`, and `xz`) generates 229 cases
(`ref/gen.py`) and compares the decoder's output (length and SHA-256) with
the expected one:

* 110 `.xz` files: Python's `lzma` at presets 0 to 9 with each check type;
  empty input, one byte, text, random, repetitive and low-entropy data with
  each check type; delta filters (distances 1, 4, 256, and two in a row);
  unusual lc/lp/pb; an x86 BCJ file (expected: refused); the `xz` tool at
  presets 0, 1, 6, 9 and 6e, with small block sizes and with sizes in the
  block headers (`-T2`); concatenated streams, with and without padding,
  bad padding, trailing garbage, and the empty input;
* 80 of those files with a random byte changed or truncated at a random
  place, expected as the `xz` tool judges them (`xz -dc`): an error, or the
  same output;
* 20 raw LZMA2 streams, spliced from several encoder runs so that one stream
  has several chunks (dictionary resets, uncompressed chunks in the middle),
  invalid first chunks, and random corruptions (expected as Python's
  `lzma` judges them);
* 19 streaming cases: files and raw streams cut into random pieces and fed
  to `XzDecoder.feed` and `XzLzma2.feed`.

`SEED=n ref/run.sh` draws other random cases (seeds 1 to 5 and 2026 pass).

## Speed and limits

Every loop over the input or the output is a tail call: the buffered input
(appended and counted with bytes' `B.append.fast` and `B.len.fast`), the
LZMA2 chunks (taken with `B.take.fast`), the range decoder, the dictionary,
the output (gathered in a list, then made `Octets` once per feed; a single
piece is not copied again), the delta filter, the checks and the index (its
records compared by a tail call). So there is no length limit from the
JavaScript lane's stack (a native build has a 2 GB stack). Before this, a
38 KB `.xz` file (100 KB of output) and a raw LZMA2 stream of 100 KB
overflowed it; a small file with a large output (100 KB from 820 bytes) did
not.

Measured on native builds (Bend 2.0.37, `bend file.bend -o prog`, WSL2),
one run at a time, on files made by Python's `lzma` (random-word text,
which compresses about 3:1) and the `xz` tool; every output matched the
original byte for byte:

| Input | Output | Time, native | Peak memory, native | JavaScript lane, before |
|---|---|---|---|---|
| `xz_decode`, CRC64 | 100 KB | 0.05 s | 15 MB | 3.3 s, 0.47 GB |
| `xz_decode`, random data (uncompressed chunks), CRC32 | 100 KB | 0.06 s | 15 MB | 2.3 s, 0.58 GB |
| `xz_decode`, CRC32 | 1 MB | 0.55 s | 134 MB | 5.9 s, 1.9 GB |
| `xz_decode`, CRC64 | 1 MB | 0.55 s | 134 MB | 27 s, 2.0 GB |
| `xz_decode`, SHA-256 | 1 MB | 0.61 s | 208 MB | 7.0 s, 2.6 GB |
| `xz_decode`, 256 blocks of 4 KiB (`xz --block-size=4096`) | 1 MB | 0.83 s | 127 MB | 6.7 s, 2.1 GB |
| `xz_decode`, two streams with padding | 1 MB | 0.57 s | 130 MB | 6.5 s, 2.6 GB |
| `xz_decode`, delta (distance 4) then LZMA2 | 512 KB | 0.40 s | 68 MB | 6.9 s, 2.1 GB |
| `xz_decode`, delta (distance 4) then LZMA2 (630 KB compressed) | 1 MB | 0.77 s | 134 MB | more than 3 GB |
| `xz_decode`, delta (distance 4) then LZMA2 | 4 MB | 3.0 s | 531 MB | not tried |
| `xz_decode`, CRC64 | 8 MB | 4.3 s | 1.06 GB | |
| `XzDecoder.feed` in 64 KiB pieces, CRC64 | 1 MB | 0.59 s | 134 MB | 23 s, 1.9 GB |
| `XzDecoder.feed` in 4 KiB pieces, CRC32 | 1 MB | 0.61 s | 134 MB | 12 s, 1.8 GB |

(The times include reading the file and writing the output.) What limits
size now is memory, not the stack: an `Octets` holds about 80 bytes of
memory per byte natively (it was about 1 KB on the JavaScript lane when
first measured), and the decoder holds its input and its output, so
natively a 1 MB output needs about 130 MB and 8 MB about 1 GB. Nothing in
this package depends on how `Octets` stores its bytes. CRC64 is no longer
the slow check natively (on the JavaScript lane the CRC-64 of 1 MB took
about 19 s in `crc` on its own; natively it takes about 0.05 s).

The streaming decoder buffers at most one LZMA2 chunk (64 KiB compressed)
and re-checks whether it is complete on each `feed`, so tiny pieces cost
time quadratic in the chunk's size; the index is likewise re-parsed until it
is complete.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (with its 100 KiB cases), `ref/run.sh` 229 cases match;
1 MB outputs decode exactly, natively within about 130 MB of memory (see
Speed and limits).
