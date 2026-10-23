# Audit of bend-kit-hash@0.2.0.0

Audited against bend-osdev's REVIEW.md, October 2026, for its use through
this adapter (and by lz4, which takes its XXH32).

**What was audited:** the package as published on BendHub,
bend-kit-hash@0.2.0.0: one file, `hash.bend` (15,389 bytes; the hub
mirror's content directory 0xb0776c613aafddb88fd284dd3c763501), which
imports bend-kit-bytes@0.3.2.0. It has FNV-1a 32 and 64, XXH32, XXH64,
SipHash-1-3, CRC-32 and Adler-32, each over a bend-kit `Bytes` buffer
(handed back beside the value) and over a byte string (`*.str`). Its
source repository (github.com/paymog/bend-kit, `hash/`, Apache-2.0) also
holds a `LAWS.bend`, `PROOF.bend` and `README.md` at the same VERSION;
none of them is in the published package, and they were not used here.

**How:** the code read against each algorithm's specification
(README.md, "Specifications"); laws stated here over its functions,
proved by computation and accepted by `--verdict`; a differential test on
random inputs against outside implementations (Python's zlib, the lz4,
zstd and openssl commands) and bend-osdev's own CRC-32, Adler-32, XXH64
and SipHash-1-3; and a probe of the buffer invariant its code relies on.

## Per algorithm

| Algorithm | Proved here (by computation, `--verdict`) | Tested | Divergence |
|---|---|---|---|
| CRC-32 (ISO-HDLC) | the catalogue's check value; equal to crypto's `CrCrc32` instance over crc on the empty input and the check string, and to crc's `crc32` on 37 bytes | 74 inputs vs `zlib.crc32` and crc's, 74 through the hash interface in two pieces; 10,000 bytes vs crc's (check.bend) | none |
| Adler-32 (RFC 1950) | equal to deflate's on the empty input, "Wikipedia", and 300 bytes of ff (s1 and s2 wrap modulo 65521) | 74 inputs vs `zlib.adler32` and deflate's; 10,000 bytes vs deflate's | none |
| FNV-1a 32, 64 | RFC 9923 section 8.3's values for "a", "foobar", "Hello!" 01 ff ed | 74 inputs vs `ref/model.py` (written from RFC 9923, checked on its values) | none |
| XXH32 | the lz4 command's values of the empty input, "abc", and 00 .. 13 (seed 0) | 74 inputs (seed 0) vs the lz4 command's frame checksum, and with random seeds vs `ref/model.py` | none |
| XXH64 | equal to zstd's on the empty input and "abc" (seed 0; zstd proves those values: `xxh64_empty`, `xxh64_abc`), 12 bytes with a seed, and 45 bytes | 74 inputs, seed 0 and random seeds, vs `ref/model.py` and zstd's (the model's low 32 bits match the zstd command's frame checksum on every input); 10,000 bytes vs zstd's | none |
| SipHash-1-3 | the openssl command's value of 00 .. 0e under the key 00 .. 0f; equal to bend-osdev-siphash's on 0, 1, 7, 8, 12 and 15 bytes | 74 inputs with random keys vs the openssl command and siphash's; 10,000 bytes vs siphash's | **on a buffer whose bytes past `len` are not zero** (below) |

**For every input, nothing about bend-kit-hash's values is proved**, here
or in the published package: its functions compute over `Array<U32>` words
under bend-kit-bytes' invariant (every byte at or past `len` is zero), and
neither Base's `Array` nor bend-kit-bytes publishes laws a proof could
use. This adapter's laws for every input (the hash interface's streaming,
split and length laws, the MAC interface's accepts and agrees) treat
bend-kit-hash's functions as given and hold whatever they compute.

The inputs tested include every length at which a reader fetches a word
past the buffer (bend-kit-bytes allocates 2^d words, and `Array.get`
wraps): lengths of 4 * 2^d bytes for d = 1 to 8, and 5 and 1 below and 1
and 3 above. bend-kit-hash reads that wrapped word only when no byte of it
is used, and every result there was correct.

## The finding: SipHash-1-3 hashes bytes past the buffer's length

`sip.last` builds SipHash's last block from the whole words at the
message's end: when 1 to 3 (or 5 to 7) bytes are left, it takes their
word (and the word before it) unmasked, relying on the bytes past `len`
being zero. Every other hash in the file masks its tail (`tail` folds
exactly the bytes left).

bend-kit-bytes documents that invariant and its own operations keep it, so
through its API (and through this adapter, which builds buffers with
`from_string`) the results are right. But `Bytes{len, buf}` is a public
constructor: a buffer built directly, or by any later operation that
shortens `len` without clearing, gets a different SipHash-1-3 for the same
bytes. A probe with the two words "ABCDEFGH" and `len` 1 to 8 (key 00 ..
0f) gave wrong values for lengths 1 to 3 and 5 to 7, and right ones for
0, 4 and 8; the clean buffers' values match the openssl command. The
other five hashes gave the same value for the clean and the dirty buffer.

A proposed fix (mask the last block to its `len % 8` bytes) and an issue
text are drafted in `bend-audit/pr/kithash/` (`ISSUE.md`,
`0001-siphash13-mask-last-block.diff`, `probe_dirty_buffer.bend`); with it,
the dirty buffers give the clean values and the clean values are
unchanged. Nothing has been posted.

## Against REVIEW.md

* **Public interface:** not listed in the published package (no README);
  the file's header names the hashes and the `.str` forms. `W64{hi, lo}`
  is open by necessity: there is no constructor def and no accessor of the
  high half (`W64.lo` only), so a caller with a seed or key must build the
  constructor or go through `mul32`, `W64.swap` and `W64.add`, as this
  adapter does.
* **Other packages' internals:** every hash matches bend-kit-bytes'
  `Bytes{len, buf}` constructor and builds it again, and SipHash depends
  on its invariant (above).
* **Streaming:** none; every hash is one call over a whole buffer, and the
  `.str` forms copy the string into a buffer first. This adapter's hash
  state therefore holds the whole message.
* **Errors and names:** no function can fail. Its type and helper names
  (`W64`, `V4`, `V64`, `S4`, `Crc`, `tail`, `bytewise`, ...) are not
  prefixed; Bend scopes them by package, so they clash with nothing here
  (lz4 imports bend-kit-hash beside word64's `W64`).
* **Laws:** none published with it (its repository's unpublished
  `LAWS.bend` has vectors only). Here: the vectors and agreement laws above
  (lz4's frame vectors also compute its XXH32).
* **Reference and fast implementations:** one implementation each; CRC-32
  is table-driven only, and builds its 256-entry table on every call
  (2,048 bit steps before the first byte), which dominates short inputs.
* **Dependencies and licensing:** bend-kit-bytes@0.3.2.0 (and through it
  bend-kit-int@0.2.0.0). The published package has no `LICENSE`; the
  repository is Apache-2.0.
* **Tests and status:** none published. Here: the 57 laws pass
  `--verdict`, `check.bend` passes, `ref/run.sh` 592 cases match.
* **Coverage of the brief:** bend-kit-hash has SipHash-1-3 only. SipHash-2-4
  (the paper's proposal, and Linux's `siphash`) and HalfSipHash (Linux's
  `hsiphash` on 32-bit machines) are in bend-osdev-siphash, written from
  the paper and the reference implementation.

## Verdict

Correct on every input tested, for all seven hashes, through the adapter.
One robustness defect (SipHash-1-3 on a buffer that breaks bend-kit-bytes'
invariant), not reachable through this adapter or bend-kit-bytes' own
operations; a fix is drafted. Usable here at exactly 0.2.0.0; a later
version should be audited again before the pin moves.
