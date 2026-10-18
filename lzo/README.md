# bend-osdev-lzo

LZO1X compression and decompression, and the lzop file container. The
decoder is safe against malformed input: it never reads past its input,
never writes past its maximum output size, and names every failure. What
the compressor writes decodes back to its input, which is proved for every
input.

**Clean-room.** LZO's reference implementation (liblzo) and the Linux
kernel's `lib/lzo` are GPL. This package was written from documentation
only (below); no LZO source code, from any implementation, was opened, read
or searched while writing it. That is the basis for its MIT licence.

## Specification

There is no published specification of the LZO1X format; the kernel's own
document says it is "not a specification". The package follows these
documents, and only these. There was no network while it was written, so it
was written from what its author knows of their content (they could not be
re-read while writing); the reference test (below) checks it against a
second implementation of the same reading, by the same author, and will
check it against the lzop tool once that is installed.

1. **The Linux kernel's `Documentation/staging/lzo.rst`**, "LZO stream format
   as understood by Linux's LZO decompressor" (a prose description of the
   bitstream; documentation, not code). From it come:
   * a stream is a run of instructions, each an opcode byte with operands,
     then more bytes (length bytes, a distance, literals);
   * the first byte is read differently: 18 to 255 open with byte − 17
     literals; 0 to 16 are ordinary instructions (16 is a copy from the
     still-empty output);
   * the "state": how many literals the last instruction copied (0, 1 to 3,
     or 4 or more), which only the 0000xxxx instructions depend on:
     * after 0 literals, `0000LLLL` is a run of 3 + L literals;
     * after 1 to 3, `0000DDSS` + H is M1, 2 bytes at distance
       (H << 2) + D + 1 (up to 1 KiB);
     * after 4 or more, `0000DDSS` + H is M1, 3 bytes at distance
       (H << 2) + D + 2049 (2 to 3 KiB);
   * `0001HLLL` + LE16 is M4: 2 + L bytes at distance 16384 + (H << 14) + D
     (16 to 48 KiB); `001LLLLL` + LE16 is M3: 2 + L bytes at distance D + 1
     (up to 16 KiB); the LE16 is `DDDDDDDD DDDDDDSS`;
   * `01LDDDSS` + H is M2 of 3 + L bytes and `1LLDDDSS` + H M2 of 5 + L bytes,
     at distance (H << 3) + D + 1 (up to 2 KiB);
   * a length field of 0 means length bytes follow: the field's maximum,
     plus 255 for each zero byte, plus the first non-zero byte, plus the
     instruction's constant;
   * after each match, S (its last two bits, or the distance field's) more
     literals follow, and S is the next instruction's state; a literal run
     leaves state 4;
   * the end of the stream is M4 with distance 16384 (three bytes,
     `0x11 0x00 0x00` as compressors write it);
   * a version 1 bitstream (LZO-RLE, first byte 17 followed by a version
     byte) exists for zram; it is not what lzop and liblzo write.
2. **The lzop file-format notes** (descriptions of the `.lzo` container). From
   them come: the magic `89 4C 5A 4F 00 0D 0A 1A 0A`; the big-endian header
   fields version, library version, version needed to extract (from version
   0x0940), method (1 LZO1X-1, 2 LZO1X-1(15), 3 LZO1X-999: all LZO1X
   streams), level (from 0x0940), flags, filter (with flag 0x800), mode,
   mtime low and high (high from 0x0940), the name (a length byte, then the
   bytes), and the header checksum over the fields from version to the end
   of the name (Adler-32, or CRC-32 with flag 0x1000); the flags 0x1 and
   0x100 (Adler-32 and CRC-32 of each block's uncompressed bytes), 0x2 and
   0x200 (of its compressed bytes, present only when the block is
   compressed), 0x40 (an extra header field), 0x400 (multipart), 0x800 (a
   filter); each block is its uncompressed size, its stored size (equal:
   stored as is; smaller: LZO1X; an uncompressed size of 0 ends the file),
   the checksums, the data; the default block size is 256 KiB.
3. **RFC 1950, section 8.2**, for Adler-32 (initial value 1). CRC-32 is the
   zlib CRC (CRC-32/ISO-HDLC), from bend-osdev-crc.

### Where the documents leave things open, and what the package does

* **The first byte's ranges.** The kernel document lists "18..21: copy 0..3
  literals, state = (byte − 17) = 0..3" and "22..255: length = (byte − 17) =
  4..238", whose ranges and formula disagree by one (18 − 17 is 1). The
  package follows the formula: a first byte b of 18 or more copies b − 17
  literals (1 to 238), and leaves state b − 17 below 4, else 4.
* **First byte 17.** Version 0 only: 17 is an ordinary M4 instruction, so
  `11 00 00` is the empty stream. LZO-RLE (version 1) is not supported; its
  run-of-zeros form (M4 with distance 0xBFFF and a fourth byte) is read as an
  ordinary M4.
* **The end marker's other fields.** The document says only that distance
  16384 ends the stream. The package reads the marker's length field (and
  any length bytes) and both distance bytes, and ignores its length and its
  S bits; the marker is M4 with H = 0 and D = 0.
* **Bytes after the end marker** are refused (`LzoTrailing`); input that ends
  before it is cut short (`LzoTruncated`).
* **Overlapping matches.** A match may be longer than its distance: it is
  copied a byte at a time, so it repeats the bytes it has just written (the
  usual LZ77 reading; the document does not say).
* **Distances.** A match reaching before the start of the output is refused
  (`LzoBadDistance`); there is no preset dictionary.
* **The document's note** that some length checks are missing from the
  kernel's code: here every byte read is checked.
* **lzop versions.** Files older than version 0x0940 (whose header lacks the
  fields above) and files needing a version above 0x1040 to extract are
  refused (`LzoBadVersion`); methods other than 1 to 3 are `LzoBadMethod`.
* **lzop features left out.** Filters (0x800), multipart files (0x400) and
  the extra header field (0x40) are refused (`LzoUnsupported`); the other
  flags (name, path, OS and character set bits) are informational and
  ignored.
* **lzop limits and order.** A block larger than 64 MiB is refused (a bound
  this package chooses); bytes after the end of the file are `LzoTrailing`;
  a file shorter than the magic is `LzoBadMagic`. The header checksum is
  always checked; block checksums when `verify` is set, the compressed
  bytes' before decompressing, the uncompressed bytes' after.
* **What the writer records.** Version 0x1030, library version 0x2080,
  version needed 0x0940, mtime high 0. These are choices, not yet checked
  against `lzop -d`.

**Not yet checked against the lzop tool.** The tool is not installed here,
and nothing about the container has been observed from it. The container
code rests on the format notes alone; `ref/run.sh` decodes the tool's files
and has the tool decode the package's as soon as `lzop` is installed.

## Files

| File | Holds |
|---|---|
| `lzo.bend` | the entry file and main concern: an LZO1X stream in, its bytes out (and back), with options or the defaults |
| `decode.bend` | LZO1X decompression: the one-shot decoder and the streaming reader |
| `encode.bend` | LZO1X compression: the literal-only stream and the checked LZO1X-1-style compressor |
| `window.bend` | the decoder's window over its last 64 KiB of output (internal; replaceable) |
| `error.bend` | `LzoError`, the failures every file answers |
| `lzop.bend` | the lzop container: reading, writing, streaming writing |
| `adler32.bend` | Adler-32 (one-shot and streaming) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

## API

Byte strings are `Octets` (bend-osdev-bytes). Everything that reads input
answers `Result<&2, &2, LzoError, A>`.

### LZO1X streams

| Def | File | Meaning |
|---|---|---|
| `decompress(src)` | `lzo.bend` | the bytes of the stream `src`, with `LzoOptions.default()` |
| `decompress_with(opts, src)` | `lzo.bend` | the same, with these options |
| `LzoOptions{max}`, `LzoOptions.default()` | `lzo.bend` | the most bytes to produce (`U32`); default 64 MiB |
| `compress(o)` | `lzo.bend` | a stream holding `o` (`lzo1x_compress`) |
| `lzo1x_decompress(src, max)` | `decode.bend` | the bytes of the stream `src`, at most `max` (a `Nat`) of them |
| `reader_start(max)`, `reader_feed(r, piece)`, `reader_finish(r)` | `decode.bend` | streaming: each piece answers `LzoRead{reader, bytes}`, the bytes it completes; `finish` answers `Done{room left}` if the stream ended at its end marker |
| `reader_decompress(max, pieces)` | `decode.bend` | a stream fed to a reader in these pieces, the bytes joined |
| `lzo1x_compress(o)`, `lzo1x_compress_with(opts, o)` | `encode.bend` | a stream for `o`: the matcher's, checked by decoding it (falling back to `lzo1x_literals(o)` should the check fail) |
| `lzo1x_compress_unchecked(opts, o)` | `encode.bend` | the matcher's stream, without the check |
| `LzoCompressOptions{hash_bits, max_dist}`, `LzoCompressOptions.default()` | `encode.bend` | the hash table's size (2^hash_bits slots) and the farthest a match may reach (at most 49151); default 14 bits, 49151 |
| `lzo1x_literals(o)` | `encode.bend` | the simplest stream: `o` as one literal run, then the end marker |
| `lzo1x_end()` | `encode.bend` | the end marker, `11 00 00` |
| `LzoError`, `LzoError.show` | `error.bend` | the failures, below, and their names |

### lzop files (`lzop.bend`)

| Def | Meaning |
|---|---|
| `lzop_decompress(opts, src)` | the content of the lzop file `src` |
| `LzopOptions{max, verify}`, `LzopOptions.default()` | the most bytes to produce (`U32`); whether to check the block checksums. Default: 64 MiB, checked |
| `lzop_header(src)` | the header: `LzopHeader{version, lib_version, need, method, level, flags, mode, mtime_low, mtime_high, name}` |
| `lzop_compress(opts, o)` | an lzop file holding `o` |
| `LzopWriteOptions{block_size, adler_d, crc_d, adler_c, crc_c, header_crc, method, level, name, mode, mtime, lzo}`, `LzopWriteOptions.default()` | where blocks are cut (1 to 64 MiB; else 256 KiB); which checksums to write (of the uncompressed and the compressed bytes; CRC-32 for the header); the method and level to record; the name, mode and mtime; the compressor's options. Default: 256 KiB blocks, Adler-32 of the uncompressed bytes, method 1, level 1, no name |
| `lzop_start(opts)`, `lzop_feed(w, o)`, `lzop_finish(w)` | streaming writing: each answers the file's next bytes (`LzopWritten{writer, bytes}`, or the last bytes) |
| `lzop_stream(opts, pieces)` | the file the streaming writer gives for content fed in these pieces |

### Adler-32 (`adler32.bend`)

`adler32(o)`; streaming: `Adler32.start()`, `Adler32.update(s, o)`,
`Adler32.finish(s)`.

The types `LzoOptions`, `LzoCompressOptions`, `LzoRead`, `LzoError`,
`LzopOptions`, `LzopHeader`, `LzopWriteOptions`, `LzopWritten` are open
records: their constructors are part of the interface. `LzoReader`,
`LzopWriter` and `Adler32` are opaque.

### Failures

| `LzoError` | When |
|---|---|
| `LzoTruncated` | the input ends before the end marker, or inside a header or block |
| `LzoBadDistance` | a match reaches before the start of the output |
| `LzoOutputTooLarge` | the output would pass the maximum |
| `LzoTrailing` | bytes after the end marker, or after an lzop file's end |
| `LzoBadMagic` | not an lzop file |
| `LzoBadVersion` | an lzop version before 0x0940, or one needing more than 0x1040 to extract |
| `LzoBadMethod` | an lzop method other than 1 to 3 |
| `LzoUnsupported` | an lzop filter, multipart file or extra header field |
| `LzoBadHeaderChecksum` | the lzop header checksum does not match |
| `LzoBadBlockSize` | an lzop block stored larger than it is, larger than 64 MiB, or not decoding to its size |
| `LzoBadChecksum` | an lzop block checksum does not match (when verifying) |

## The compressor

An LZO1X-1-style greedy LZ77 matcher with a single-entry hash table keyed
by the next four bytes. It writes M2 for matches of 3 to 8 bytes within
2 KiB, M3 within 16 KiB, M4 beyond, with length bytes for long matches;
up to 3 literals after a match ride in its S bits, and longer runs get
their own instruction. The first literal run uses the first-byte form. It
does not write M1 (which only pays for 2- and 3-byte matches). Matches are
4 bytes or more and may overlap themselves.

## Extension points

* **Options:** `LzoOptions`, `LzoCompressOptions`, `LzopOptions` and
  `LzopWriteOptions` hold the real choices, each with a named default. The
  stream functions take their limit directly, since a stream does not
  record its size.
* **A better matcher** (hash chains, lazy matching, M1 for short matches,
  an LZO1X-999-style parser) can replace the greedy one behind
  `lzo1x_compress_with`: the check keeps the round-trip law true whatever
  the matcher writes, so a new matcher needs no new proof, only the
  differential test.
* **The window:** `window.bend` is behind four defs (`win.empty`, `win.put`,
  `win.get`, `win.count`). The laws follow lengths, literals and failures,
  not the bytes a match copies, so any structure that answers the byte at a
  distance can replace the trie.
* **Speed:** `lzo1x_compress_with` decodes every stream it writes, to check
  it; `lzo1x_compress_unchecked` skips that, without the law.
* **Streaming:** the reader (`reader_*`) decodes a stream in pieces and keeps
  only its window; the lzop writer streams too, keeping only the bytes not
  yet in a block (lzop's checksums are per block). The lzop reader is
  one-shot for now; the streaming reader is the building block for one that
  reads a block at a time.
* **Checksums:** Adler-32 lives here because no other package has it; it
  could move to a shared checksum package without changing this interface.
* **Other LZO formats** (LZO1X-RLE, LZO1Y, LZO1Z, LZO2A) would be new files
  beside `decode.bend`; their documentation was not used here.

## Laws

`LAWS.bend` has 64 laws: 8 properties, 3 witnesses and 53 vectors.

**For every input** (properties, proved by induction):

* `output_within_max`: whatever `src` and `max`, `lzo1x_decompress(src, max)`
  never answers more than `max` bytes;
* `literals_round_trip`: `lzo1x_decompress(lzo1x_literals(o), len(o) + k) ==
  Done{o}` for every byte string and every `k`;
* `compress_round_trip`: `lzo1x_decompress(lzo1x_compress_with(opts, o),
  len(o)) == Done{o}` for every input and all options;
* `truncation_rejected`: every proper prefix of a valid stream is refused as
  `LzoTruncated` (if `a ++ [h] ++ t` decodes, `a` is cut short);
* `trailing_rejected`: a valid stream followed by any bytes is refused as
  `LzoTrailing`;
* `first_match_rejected`: a stream that opens with a match (first byte 17)
  whose first distance byte is 4 or more (so that it is not the end marker)
  is `LzoBadDistance`, whatever follows;
* `reader_pieces`: decoding a stream through the reader, in any pieces, is
  exactly the one-shot decoder on the pieces joined (bytes and failures);
* `adler32_pieces`: Adler-32 updated piece by piece is Adler-32 of the
  whole.

Laws with a hypothesis each have a witness that it can hold
(`truncation_rejected_witness`, `trailing_rejected_witness`,
`first_match_rejected_witness`).

The compressor's round trip holds for every input because
`lzo1x_compress_with` checks its stream by decoding it and comparing, and
falls back to the literal-only stream (whose round trip is proved) should
they differ. The proof covers the check and the fallback; it does not show
that the greedy matcher is right on its own. The differential test covers
the matcher, and checks that the fallback never happens on its inputs. The
round trip is stated with the maximum equal to the input's length (the
size the check decodes with); `literals_round_trip` holds for every larger
maximum too.

A for-all law that every match reaching before the start of the output is
refused, at every distance, is not stated: it would need the distance
fields' bit arithmetic followed for unknown bytes. `first_match_rejected`
covers the case with no output, and vectors and the differential test the
rest.

**Vectors** (proved by computation; 53): a stream for each encoding the
kernel document describes, built by hand from its description (the
first-byte runs of 1, 4 and 238 literals, the long literal run and its
length bytes, M1 after a few literals and after many, M2 of both lengths,
M3 with trailing literals, with length bytes and overlapping, a literal run
after a match, the end marker alone and with length bytes); each malformed
stream (empty, cut in literals, distances and length bytes, the end marker
missing, distances before the start, the output limit for literals and
matches, a trailing byte); streaming in three pieces; compression (the
literal-only stream's bytes, the empty input, a run, a text); Adler-32
(RFC 1950's construction, the Wikipedia example); lzop files built by hand
from the format notes, with checksums computed by zlib (two blocks, stored
and compressed; every checksum flag and a CRC-32 header; the header's
fields; a bad header checksum, a bad block checksum, unverified, bad magic,
a filter, a bad method, an old version, a block stored larger than it is,
trailing bytes, a file cut short); the writer's empty file, its file with
every checksum (the very bytes built by hand), and a streamed file read
back.

A successful M4 needs more than 16 KiB of output, so the vectors cover it
only as a failure (`first_m4`);
`check.bend` does (H = 0 and H = 1, up to distance 49151), with M1 after
many literals, and so does the differential test.

The proofs follow the decoder byte by byte. Octets enter them only through
bytes' interface laws (`octets_append_list`, `octets_to_of`,
`octets_of_to`, `octets_len_list`, `octets_cons_list`, `rev_rev`), so they
do not depend on how `Octets` stores its bytes.

## Tests

`ref/gen.py` holds an independent implementation, written from the same
documents: an instruction-at-a-time decoder (the package's is a
byte-at-a-time state machine) that names each failure at the same point of
the stream, an encoder that writes every encoding the kernel document
describes (both first-byte forms, the long literal run, M1 after few and
after many literals, M2, M3 and M4 with and without length bytes, S
literals), choosing among valid encodings at random, and an lzop reader and
writer whose checksums come from Python's zlib. **It shares an author with
this package**, so it checks the package against a second reading of the
documents, not against LZO's reference implementation. When the `lzop`
tool is installed, the test also decodes the tool's files (`-1`, `-3`,
`-7`, `-9`) and has `lzop -d` decode every file the package writes.

`ref/run.sh` (seed 2026) checks:

* **decoding, 224 cases:** 42 streams written by `gen.py` (up to 20 KB, two
  with M4 distances), the output limit one byte below the size (6),
  streaming in random pieces, some corrupted (10), 110 corrupted streams
  (bytes changed, deleted, inserted or cut off: the package must answer
  exactly what the Python decoder answers, the same bytes or the same
  failure), 16 lzop files across the flags, methods, names and block sizes,
  and 40 corrupted lzop files, verified or not;
* **compression, 38 cases:** 26 streams (random, text, repetitive and mixed
  inputs up to 20 KB, over several hash sizes and distance limits), 9 lzop
  files over the writer's options and 3 streamed ones. Each must decode back
  to its input with `gen.py`'s decoder (and `lzop -d`, when installed);
  `lzo1x_compress_with` must equal `lzo1x_compress_unchecked` (no
  fallback); repetitive inputs must shrink to under a quarter.

The run takes about 75 s (two native builds). Seeds 1 to 5 also pass
(each with lzop missing: the tool's checks have not run).

Without python3, `run.sh` exits 77 (a skip). Without the lzop tool it runs
everything else and says so; **CI needs the apt package `lzop`** for the
tool's checks.

## Speed and limits

Measured on native builds (`bend file.bend -o prog`), Bend 2.0.37, WSL2:

| About 1 MB of text (1,045,996 bytes; words from a 16-word list) | Time | Peak memory |
|---|---|---|
| building the input only (the baseline in every row) | 0.14 s | 84 MB |
| `lzo1x_compress_unchecked` (to 341,802 bytes, 32.7%) | 0.41 s | 106 MB |
| `lzo1x_compress` (the same, then decoded and compared) | 2.15 s | 181 MB |
| `lzo1x_compress_unchecked`, then `lzo1x_decompress` and a comparison | 2.01 s | 204 MB |
| `lzop_compress` then `lzop_decompress` (defaults: 256 KiB blocks, Adler-32, checked compression) | 4.13 s | 205 MB |

So decoding runs at about 0.7 MB/s (the window trie costs a few steps per
byte) and matching at about 4 MB/s; the compressor's self-check, a full
decode, is most of `lzo1x_compress`'s time. The figures were measured by
hand (one run each), not in CI.

* Nothing recurses over the data's length except as a tail call: the
  decoder, the matcher, the length bytes (`ext.go`, tail-recursive, proved
  equal to the structural `ext.ref` the proofs follow), the lzop block
  loops. What still recurses is bounded: the window trie (depth 16).
* The decoder keeps its output as a reversed list as well as in the window;
  memory, not the stack, is the limit, as for every `Octets` pipeline (see
  AGENTS.md, "Runtime and checker limits"). Keep a single call to a few MB,
  or use the streaming reader and the lzop writer, which work a piece at a
  time.
* List literals of a few thousand elements overflow the stack, so
  `ref/gen.py` joins long inputs from pieces.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 224 decoding cases match and 38
compressed streams and lzop files decode back (seeds 2026 and 1 to 5),
`scripts/deps.sh` passes. The lzop tool is not installed, so nothing has
been checked against it yet: the container rests on the format notes alone,
and its interoperation with lzop is unverified until CI installs `lzop`.
