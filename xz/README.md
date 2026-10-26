# bend-osdev-xz

Decompression of `.xz` files, and of the legacy `.lzma` format (the one
Linux's initramfs decompressors also accept), safe against malformed input.
In `.xz` files every CRC32, every block check, the index, the footer and
every padding byte is checked, and the decoder stops at the first failure with an `XzError` naming it. It
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
* The `.lzma` ("LZMA alone") format, checked against these documents (all
  public domain):
  * XZ Utils' `doc/lzma-file-format.txt` ("The .lzma File Format", Lasse
    Collin, last modified 2024-04-08), read in an installed XZ Utils
    documentation directory,
    <https://dawn2.umd.edu/PBC/conda/share/doc/xz/lzma-file-format.txt>:
    * 1: a 13-byte header, then the LZMA data; data after the first stream
      is corruption to XZ Utils (other implementations ignore it). This
      package follows XZ Utils: `XzTrailingData`.
    * 1.1.1 Properties: one byte, `(pb * 5 + lp) * 9 + lc`, with lc 0 to 8,
      lp 0 to 4, pb 0 to 4, larger values invalid; XZ Utils additionally
      requires `lc + lp <= 4`, which this package requires too (its
      probability array, `rangecoder.bend`, holds the literal coder only up
      to that).
    * 1.1.2 Dictionary Size: 32 bits, little-endian; any value is allowed
      (2^n and 2^n + 2^(n-1) are recommended for portability). This package
      accepts any value.
    * 1.1.3 Uncompressed Size: 64 bits, little-endian; all ones means
      unknown, and then the stream must end with the end of payload marker;
      a known size may also be followed by the marker (allowed since the
      2022 revision; XZ Utils 5.2.5 and older refuse it). XZ Utils refuses
      known sizes of 256 GiB or more (to avoid false positives when
      detecting the format); this package refuses any known size above its
      `max_out` (a `U32`) with `XzOutputTooLarge`.
    * 1.2: the LZMA data's own format is left to the LZMA SDK.
  * xz(1), <https://tukaani.org/xz/man/xz.1.html>: OPTIONS, "Custom
    compressor filter chains" (`--lzma1`): lc and lp may not sum to more
    than 4; LZMA UTILS COMPATIBILITY, "Unsupported .lzma files": xz refuses
    `lc + lp > 4`, and dictionary sizes other than 2^n and 2^n + 2^(n-1);
    it decodes files with or without the end of payload marker, and calls
    a file with data after its stream corrupt.
  * liblzma's API documentation, `lzma_options_lzma`,
    <https://www.tukaani.org/xz/liblzma-api/structlzma__options__lzma.html>
    (`dict_size`: the minimum dictionary size is 4096 bytes; `lc`: `lc + lp
    <= 4`), and `lzma12.h`,
    <https://www.tukaani.org/xz/liblzma-api/lzma12_8h.html>
    (`LZMA_DICT_SIZE_MIN` 4096, `LZMA_LCLP_MAX` 4, `LZMA_PB_MAX` 4).

  This package treats a dictionary size below 4096 as 4096 when it checks
  match distances. That is liblzma's documented minimum, and the LZMA SDK's
  decoder is reported to do the same (`LZMA_DIC_MIN`), but the SDK's own
  specification is distributed only as an archive
  (`lzma-specification.7z`, <https://www.7-zip.org/sdk.html>), which was
  not downloaded, so that part of the SDK was not read. Observed of the
  `xz` tool 5.4.5 as a black box (not documentation): it decodes a file
  whose header names a dictionary of 3 bytes (3 = 2 + 1), refuses one of
  2^31 - 1 bytes as "File format not recognized", and accepts all ones.

The code was written from these specifications; no source of xz-utils,
liblzma, the LZMA SDK or any GPL implementation was read.

## Files

| File | What it holds | Public |
|---|---|---|
| `xz.bend` | the entry: `.xz` files, one-shot and streaming | yes |
| `alone.bend` | `.lzma` files: the header both ways, decoding one-shot and streaming | yes |
| `container.bend` | the container's fields: stream header and footer, block headers and filter flags, the index, variable-length integers | yes |
| `lzma2.bend` | the LZMA2 decoder (chunks, resets, the dictionary), one-shot and streaming, usable without the container | yes |
| `integrity.bend` | the block checks: none, CRC32, CRC64, SHA-256 | yes |
| `delta.bend` | the delta filter's decoder | yes |
| `error.bend` | `XzError`, one constructor per failure, and messages | yes |
| `lzma.bend` | the LZMA decoder core: a step at a time (with the end marker), a chunk at a time, and the growing dictionary array; used by `lzma2.bend` and `alone.bend` | internal |
| `rangecoder.bend` | the range decoder and its probabilities | internal |
| `gen/proofs.py` | writes `PROOF.bend`'s case-split lemmas for the `.lzma` header laws | (generator) |

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

### `alone.bend`

| Def or type | Meaning |
|---|---|
| `XzAloneHeader{lc, lp, pb, dict_size, size}` (open), `XzAloneHeader.size(h)`, `XzAloneHeader.valid(h)` | a `.lzma` header: lc, lp, pb (`Nat`), the dictionary size (`U32`), the uncompressed size (`Maybe<&2, W64>`, `None` if unknown); `valid`: `lc + lp <= 4`, `pb <= 4`, and a known size other than all ones |
| `XzAlone.header(o)` | the header at the front of `o`: `XzBadFilterProps` for a bad properties byte, `XzTruncated` if `o` is shorter than 13 bytes |
| `XzAlone.header_bytes(h)` | the header's 13 bytes |
| `XzAlone.props(lc, lp, pb)`, `XzAlone.props_valid(b)` | the properties byte; whether a byte is valid (below 225, `lc + lp <= 4`) |
| `XzAlone.has_size(o, s)` | whether `o`'s length is the size `s` (always, if `s` is unknown) |
| `XzAloneParams{max_out: U32}`, `XzAloneParams.default()` (16 MiB), `XzAloneParams.max_out` | the most output allowed |
| `XzAlone.decode(p, input)` | a whole `.lzma` file: its data, or the first failure |
| `XzAlone.start(p)`, `XzAlone.feed(d, input)` (`XzAloneFed{dec, out}`), `XzAlone.finish(d)` | the same in pieces: `feed` answers the output decoded so far, `finish` the rest |

A `.lzma` file's failures: `XzTruncated` (the header or the stream cut
short), `XzBadFilterProps` (a bad properties byte), `XzOutputTooLarge`
(a known size past the maximum, or an unknown one running past it),
`XzCorruptLzma` (corrupt data, the end marker before the declared size, or
data past it), `XzTrailingData` (bytes after the stream). With a known size,
the stream may end there or with the end marker; with an unknown size, it
must end with the end marker. The streaming decoder holds the header until
it and the range decoder's first 5 bytes are in; after that each `feed`
decodes as far as its unread input surely reaches (a symbol reads at most
48 bytes) and answers that output at once; there is nothing like a block
check to wait for in this format.

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
* `.lzma` files: any valid properties; any dictionary size (the `xz` tool
  refuses sizes other than 2^n, 2^n + 2^(n-1) and all ones, as a sign that
  a file is not `.lzma`; Python's `lzma` and this decoder do not); known and
  unknown sizes, with or without the end marker when the size is known.
  Nothing may follow the stream (as `xz` judges it; Python's `lzma` ignores
  what does not decode).

## Extension points

* **The output limit** is the parameter `XzParams.max_out` (for LZMA2,
  `max_out`); memory follows it too, since the dictionary array never grows
  past the output allowed.
* **More filters**: a BCJ decoder goes in its own file beside `delta.bend`,
  with a case in `Xz.filter.err.mid` and `Xz.chain.build` (`xz.bend`).
* **More checks**: `integrity.bend` holds the table of check IDs; the
  SHA-256 provider (bend-collections) is used only there, so it can be
  replaced (for instance by a streaming SHA-256) without touching the rest.
* **The dictionary** is an `Array<U32>`, grown by doubling up to the
  dictionary size (or the output allowed) by `lzma.bend`'s
  `XzLzma.dict_grow`, which LZMA2 and `.lzma` share; another store can
  replace it there alone.
* **The LZMA decoder core** (`lzma.bend`) is shared through its interface:
  `XzLzma.step` decodes one byte (or reads the end marker, which leaves
  `XzLzRegs.at_end`), `XzLzma.chunk` a known number of bytes. LZMA2 decodes
  chunks with it; `alone.bend` steps it, checking after each step whether
  the stream went wrong or ended. Another LZMA1 container (7z's coder, raw
  LZMA1) goes in its own file beside `alone.bend` in the same way; the
  limits on `lc` and `lp` are the probability array's (`rangecoder.bend`,
  2^14 slots).
* **`.lzma` parameters:** `XzAloneParams` holds the output limit; the
  header's own choices (lc, lp, pb, dictionary size, size) are the open
  record `XzAloneHeader`, written by `XzAlone.header_bytes`.

## Dependencies

`bytes`, `word64` (`.lzma`'s 64-bit size, too) and `crc` (CRC-32 and CRC-64/XZ) from bend-osdev, and
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
    end marker alone is the empty stream;
  * `.lzma` files:
    * `alone_header_round_trip`: every valid header (`XzAloneHeader.valid`),
      written by `header_bytes` and read by `header` with anything after
      it, is itself;
    * `alone_bad_props`: a first byte that `props_valid` refuses (`lc + lp`
      above 4, or 225 and up) is `XzBadFilterProps`, whatever follows and
      whatever the parameters; `alone_props_table` lists the 75 bytes it
      accepts;
    * `alone_empty`, `alone_short_header` and `alone_short_stream`: the
      empty input, a valid properties byte with fewer than 12 bytes after
      it, and a valid header with fewer than 5 bytes of stream after it,
      are each `XzTruncated`;
    * `alone_declared_size`: for every input and parameters, if the header
      declares a size and the decoder answers, the output has that size
      (proved through the decoder's last guard, `XzAl.guard`, which refuses
      any other length; the decoder also stops at the size, which the
      differential test exercises).
* **vectors:** small `.xz` files made by Python's `lzma` decode to their
  data (no blocks; one block with an uncompressed chunk and a CRC32); a
  changed block check and a changed header CRC32 are caught; LZMA2
  uncompressed chunks, the output limit, and the dictionary sizes; `.lzma`:
  Python's header read, a header's bytes, `"hello"` from Python's
  FORMAT_ALONE with the size unknown and with it written into the header,
  size 0 with no end marker, and a size one too large, a byte after the
  stream and the output limit refused.

The `.lzma` round trip is proved with the header's fields split into bits
(`al_fields`, `al_drop`) and its properties enumerated (`al_props`, the 75
valid choices, the rest refuted): `gen/proofs.py` writes those lemmas into
`PROOF.bend`. Octets and W64 enter the proofs only through bytes' and
word64's interface laws (`octets_append_list`, `octets_to_of`, `parts_of`).

The decoding of LZMA data itself has no law, in LZMA2 or in `.lzma`:
proving it would need a model of LZMA to compare with. It is held to
Python's `lzma` and the `xz` tool by the differential test below, said
plainly here.

## Tests

`check.bend`: one case per failure (each `XzError` the container can
answer, the unsupported check and filter, the output limit), a file fed one
byte at a time, raw LZMA2, the delta filter, the tables, and two large
inputs, beyond what a decoder recursing once per byte could reach: an
820-byte `.xz` file decoding to 100 KiB, and a 100 KiB raw LZMA2 stream of
two uncompressed chunks (64 KiB and 36 KiB), each checked by its length and
CRC32 (natively the whole of `check.bend` runs in 0.08 s and 16 MB; on
the JavaScript lane the two took about 0.7 s and 0.2 GB more than the rest
of the file). For `.lzma`: Python's file for `"hello"` with the size
unknown, known, and fed one byte at a time; its header read and a header
written; a bad properties byte, a header cut short, a byte after the
stream, the output limit; and a 125-byte file from `xz --format=lzma`
decoding to 100 KiB, checked by length and CRC32 (with these, 0.09 s and
16 MB natively).

`ref/run.sh` (needs `python3` with `lzma`, and `xz`) generates 389 cases
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
  to `XzDecoder.feed` and `XzLzma2.feed`;
* 146 `.lzma` files, decoded by `XzAlone.decode`:
  * 44 of unknown size, with the end marker: Python's `lzma` (FORMAT_ALONE)
    at presets 0 to 9, on empty, one-byte, random, repetitive and
    low-entropy data, with lc/lp/pb of (0,0,0), (4,0,4), (0,4,2), (1,3,0),
    (2,2,1) and dictionaries of 4 KiB, 64 KiB and 1 MiB; and `xz
    --format=lzma` at `-0`, `-1`, `-6`, `-9`, `-6e` and two `--lzma1`
    option sets, on empty, one-byte and text inputs;
  * 12 of those with the size written into the header (the end marker then
    follows the known size);
  * 7 of known size without an end marker, from `gen.py`'s literal-only
    LZMA encoder (written from the LZMA specification's range coder and
    literal coder; neither Python nor the tool writes this variant), up to
    3000 bytes, with lc 0, lp 4, pb 4 in one and a dictionary size of 1 in
    another; Python's `lzma` and the `xz` tool decode them all;
  * 7 refused: a size one too large, a size one too small, a byte after
    the stream, properties bytes 225 and `lc + lp = 5`, the header alone,
    the header cut short;
  * 50 with a byte changed (anywhere but the dictionary size field: the
    tool refuses, as "not recognized", a dictionary size other than 2^n,
    2^n + 2^(n-1) or all ones, a guess at whether a file is `.lzma` at all
    that the format does not require; this decoder accepts any size, as
    Python's `lzma` does), 20 cut short, and 6 with random bytes appended,
    expected as `xz -dc --format=lzma` judges them: an error, or the same
    output;
* 14 streaming `.lzma` cases: intact and damaged files cut into random
  pieces and fed to `XzAlone.feed`.

  (With seed 2026, 87 of the 160 `.lzma` cases are expected to fail and do;
  the rest decode to exactly the tool's output.)

Every intact `.lzma` file is checked, as it is generated, to decode to its
data with Python's `lzma` and with the `xz` tool, and every refused one to
be refused by the tool.

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
| `XzAlone.decode`, `xz --format=lzma -6` (134 KB), size unknown | 1 MB | 0.38 s | 141 MB | |
| `XzAlone.decode`, `xz --format=lzma -0` (165 KB) | 1 MB | 0.35 s | 127 MB | |
| `XzAlone.decode`, Python's FORMAT_ALONE, size written into the header | 1 MB | 0.36 s | 133 MB | |
| `XzAlone.decode`, random data (`xz --format=lzma`) | 1 MB | 0.73 s | 143 MB | |
| `XzAlone.feed` in 64 KiB pieces, `xz --format=lzma -6` | 1 MB | 0.68 s | 119 MB | |

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
is complete. The `.lzma` streaming decoder measures its unread input once
per round of steps (a round being as many steps as that input surely
covers, at 48 bytes a symbol), so it costs a few list steps per byte more
than the one-shot decoder; it holds only the input not yet decoded.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(14 s, 0.48 GB peak; `--verdict` 30 s, 0.55 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (with its 100 KiB cases), `ref/run.sh` 389 cases match
(160 of them `.lzma`; seeds 2026 and 1 to 5); 1 MB outputs decode exactly,
`.xz` and `.lzma`, natively within about 140 MB of memory (see Speed and
limits).
