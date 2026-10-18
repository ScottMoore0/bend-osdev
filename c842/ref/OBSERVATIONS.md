# Black-box observations of Linux's 842

The format conventions that the public documents leave open were settled
by running Linux's 842 as a black box. Every convention the package
follows, other than those taken from the paper or the patent (see
`../README.md`), cites an experiment below. No Linux source was read.

## Setup

* **Kernel:** Ubuntu's `linux-image-unsigned-6.8.0-147-generic`, with
  `linux-modules-6.8.0-147-generic` and the matching headers
  (`apt-get download`, 2026-10-18). Its `boot/config-6.8.0-147-generic`
  sets `CONFIG_CRYPTO_842=m`, `CONFIG_842_COMPRESS=m` and
  `CONFIG_842_DECOMPRESS=m`.
* **The oracle:** a test module (`kmod842.c`, GPL-2.0, test tooling only,
  outside this repository in `bend-audit/kmod842/`). It was written from the
  crypto API's documented call pattern, and calls the crypto API's `"842"`
  algorithm through the asynchronous compression interface. A debugfs file
  takes one request (compress or decompress, an output capacity, the
  bytes) and answers the return code and the output.
* **The VM:** QEMU (`qemu-system-x86`, TCG) boots the kernel with an
  initramfs built by `mkinitrd.py`. Its static `init` loads `842_compress`,
  `842_decompress`, `842` and `kmod842`, runs every request in a file, and
  prints one line per answer: `R <i> <ret> <len> <hex>`.
* **Running it:** `bend-audit/kmod842/run-vm.sh REQ OUT`. The scripts for
  each experiment and their raw outputs are in
  `bend-audit/kmod842/experiments/`.

Notation: bits are written most significant first; "t" is a 5-bit code.

## E0: the oracle answers

* compress `""` → `-22` (EINVAL; the crypto API refuses empty input);
* compress 8 zero bytes → `e780000000000000`;
* compress `01 02 … 08` → `0008101820283038479f43cda0400000`.

## E1: compression of chosen inputs (42 inputs)

The outputs were decoded under the hypotheses below. All 42 decode back to
their inputs, and all 42 CRCs and paddings match.

* **Bit order.** The first 5 bits of the first byte are the first code:
  `0x00 08 10 …` is `00000` followed by the bytes `01 02 …`, shifted by 5
  bits. Fields are written most significant bit first and packed from each
  byte's top bit down (every output in E1 to E7).
* **The literal chunk is t = 0, four 16-bit literals** (`01..08` →
  `00000` + `0102 0304 0506 0708`). That is 69 bits, the paper's
  maximum per chunk.
* **The end is t = 30 (`11110`), then 32 bits of CRC.** Examples:
  * `zeros8` → `11100 11110` + 32 zero bits;
  * `01..08` → t0 + 64 bits, `11110`, CRC `7d0f3681`.
* **Z8 is t = 28 (`11100`):** 8 zero bytes → `e7 80 …`, that is
  `11100 11110` + CRC 0.
* **RPT is t = 27 (`11011`) with a 6-bit field N − 1:** N copies of the
  previous 8 bytes.
  * zeros16 → Z8 RPT(field 0);
  * zeros24 → Z8 RPT(1);
  * zeros512 → Z8 RPT(62), that is 1 + 63 chunks;
  * zeros520 → Z8 RPT(63), 65 chunks;
  * zeros1024 → Z8 RPT(63) RPT(62);
  * `ABCDEFGH`×2 → t0 RPT(0); ×3 → RPT(1); ×65 → RPT(63); ×66 →
    RPT(63) RPT(0).
* **Input that isn't a multiple of 8.** The tail is t = 29 (`11101`), a 3-bit
  count 1 to 7, then that many bytes.
  * 1 byte → `11101 001 00000001 11110` + CRC;
  * 9 bytes → t0, then `11101 001 09`;
  * 1 to 7 bytes and 9 to 15 bytes all follow this pattern.
* **The CRC.** It is CRC-32 with polynomial 0x04C11DB7, most significant
  bit first, initial value 0 and no final XOR, over the uncompressed bytes.
  * The 1-byte input `01` gives `04c11db7`, the polynomial itself.
  * All-zero inputs give 0.
  * All 42 outputs match.
  * The check value of `123456789` is 0x89A1897F.
  * In bend-osdev-crc's parameter model this is
    `Crc32Spec{32, 0x04C11DB7, 0, not reflected, 0}`. The catalogue has no
    named CRC with these parameters: CRC-32/MPEG-2 has the same
    polynomial and bit order but starts at 0xFFFFFFFF.
* **Padding.** After the CRC, zero bits up to a whole number of 8-byte
  words:
  * 106 bits → 16 bytes, 130 bits → 24 bytes, 42 bits → 8 bytes;
  * with a capacity of 15 the 16-byte output is refused (`-28`), and 16
    is accepted.
* **Pointers seen in compressor output:**
  * `A + ABCDwxyz` → t20 (P4 LL LL) with P4 index 0;
  * `A + wxyzEFGH` → t4 (LL LL P4) with index 1;
  * `A + EFGHABCD` → t24 (P4 P4) with indices 1 and 0;
  * `A + ABwxyzGH` → t11 (P2 LL LL P2) with indices 0 and 3;
  * `A + xyGHxyCD` → t6 with P2 indices 3 and 1;
  * `A + ABCDEFwx` → t22 (P4 P2 LL) with indices 0 and 2;
  * `A + B + A` → t25 (P8) with index 0.

  So a P4 index counts 4-byte phrases (index 1 = bytes 4 to 7), and a P2
  index counts 2-byte phrases. This matches the paper: the low pointer bits
  choose the part of the 8-byte entry, and "high" is the first in memory.

## E2: decompression of crafted streams

* **All 26 templates.** Each stream is two literal chunks, then template t
  with chosen literals and pointers, then END with the right CRC. All 26
  decode exactly as US 2006/0106870 A1's Figure 3 lays them out (t0 to t25).
* **Codes 26 and 31** → `-22`.
* **Pointers to positions not yet written** → `-22`: P8 index 1, P4
  index 2 or P2 index 4, after one chunk.
* **RPT and Z8 chunks take history positions.** For `A, RPT(0), B`:
  * P8 index 1 → `A`, the repeated copy;
  * P8 index 2 → `B`;
  * after `A, Z8`, P8 index 1 → zeros.
* **RPT** as the first template → `-22`. `Z8 RPT(2)` → 32 zero bytes.
* **Wrong CRC** → `-22`.
* **What follows the CRC is ignored:**
  * 8 or 1 trailing bytes are accepted;
  * padding of one bits is accepted;
  * a stream ending at the CRC's last byte, without padding, is accepted;
  * cutting into the CRC → `-75` (EOVERFLOW);
  * no END at all → `-75`.
* **The empty stream** → `-22` (the crypto API, as in E0).
* **Short data:**
  * count 0 → `-22`;
  * short data with 7 bytes, then END → accepted;
  * short data in the middle of a stream (before a template, or twice) →
    accepted, and the output continues after it.
* **Output capacity:**
  * 16 bytes into 15 → `-28` (ENOSPC);
  * into 16 → accepted;
  * into 0 → `-22` (the crypto API).
* **Wrap-around streams.** `ring8_wrap` and `ring2_wrap` were refused,
  but their expected bytes had been worked out by hand wrongly: the
  chunk a pointer template writes itself takes the next history position.
  So the CRC did not match. E3 and E4 repeat them correctly.
* **`ring8_full`:** 256 chunks, then P8 index 255 → chunk 255.

## E3: the histories are rings, indexed by position

All of the following match the rule "an index i of a size-s phrase reads
the latest position p ≡ i·s (mod H) that is before the current chunk". H is
2048 for P8 and P4, and 512 for P2.

* **Decompression, chunk k = (k, 7k + 3) as two big-endian words:**
  * P8 at 257, 258, 300, 512 and 513 chunks, indices 0, 1, 2, 43, 44, 45
    and 255. For example, after 257 chunks index 0 → chunk 256 and index 1 →
    chunk 1; after 300 chunks index 43 → chunk 299 and 44 → chunk 44.
  * P4 indices 0 to 4 after 257 and 258 chunks.
  * P2 indices 0, 3, 4, 5, 7, 8 and 255 after 64, 65, 66 and 128 chunks.
* **Compression** of 300 distinct chunks followed by chunk k:
  * k = 44, 45, 50 → P8 index k;
  * k = 290 → P8 index 34 (290 mod 256);
  * k = 0, 10, 43 (already overwritten) → no P8;
  * k = 299 → RPT(0);
  * the second half of chunk 10 (the word 73) → P4 index 146, the first
    half of chunk 73, which holds the same word (2 × 73 = 146);
  * 2-byte phrases → P2 indices.

## E4: corrected wrap-around, short data mid-stream, large inputs

* **The E2 wrap-around streams,** now with the right expected bytes: both
  match.
* **After short data** (3 bytes, so the output is not a multiple of 8):
  * accepted, matching the rule as refined in E6:
    * P8 index 0;
    * P4 indices 0 and 1;
    * P2 indices 0 to 3;
    * RPT;
    * after a literal, short data and Z8, P8 index 1 → `abc` + five zeros;
  * refused (`-22`): P8 index 1, P4 index 2, P2 index 4.
* **Compression of large inputs:**
  * 64 KiB random → 70528 bytes;
  * 64 KiB text → 19656 bytes;
  * 256 KiB → `-22` (see E5);
  * 2049 to 2055 random bytes → the short data tail with counts 1 to 7.

## E5 and E6: pointers when the output isn't a multiple of 8

E5 tried three candidate rules. E6 then decoded, for each probe, a stream
for every 2-byte, 4-byte or 8-byte value present in the output. In each
probe only the right value's CRC is accepted, so the kernel's choice can
be read off. Results (n = output length when the pointer is read, which
includes the template's earlier sub-phrases):

| n | pointer | reads position |
|---|---|---|
| 521 | P2 index 0 / 1 / 255 | 512 / 514 (into its own chunk) / 510 |
| 519 | P2 index 0 / 1 / 3 | 0 / 2 / 6 |
| 520 | P2 index 0 / 1 / 3 | 512 / 514 / 518 (both in its own chunk) |
| 525 | P2 index 0 / 1 / 3 | 512 / 514 / 518 |
| 2051 | P8 index 0 | 0 |
| 2055 | P4 index 0 / 1 | 0 / 4 |
| 2057 | P2 index 0 / 1 | 2048 / 2050 |
| 17 | P2 index 3 / 4 | 6 / 8 |
| 1033 | P2 index 0 / 1 | 1024 / 1026 |

(A "rejected" answer in E6's own output means the value read was not among
the probe's candidates: it lay partly in the template's own output, which
the probe left out. E7 confirms these positions with the model.)

**The rule.** Let t8 be n rounded down to a multiple of 8. A pointer with
index i, for phrases of s bytes in a history of H bytes, reads s bytes at
the latest position p ≡ i·s (mod H) with p < t8. If there is none (p < 0),
the stream is refused. Concretely: p = ⌊t8 / H⌋·H + i·s, less H if that
is t8 or more.

On a stream whose short data comes last (the only kind Linux's compressor
writes, and the only kind this package's compressor writes), t8 is the
current chunk's start. So this is E3's rule.

* **Size limits of the crypto API path, not of the format:**
  * compression of more than 131072 input bytes → `-22`;
  * output past 131072 bytes → `-28` (98304 random bytes compress, 131064
    do not);
  * decompression to 131072 bytes is accepted, to 131080 → `-28`.

## E7: fuzzing the decoder against the model

`fuzz.py` writes random streams:
* literal chunks, then random templates (pointers mostly valid), RPT, Z8,
  short data (sometimes count 0), and codes 26 and 31;
* END with the right CRC 93% of the time;
* then sometimes the stream is cut, a bit flipped, or bytes appended, and
  sometimes the capacity is a little too small.

4000 streams were compared with `model.py`'s decoder, mapping its failures
to errno as follows:
* truncated → −75;
* output too large → −28;
* bad template, pointer, repeat, short data or CRC → −22.

All agree, except the empty stream (the API's `-22`; the model says
truncated). By outcome:
* 1085 accepted, with the same bytes;
* 182 bad CRC;
* 1452 bad pointer;
* 14 bad repeat;
* 472 bad short data;
* 403 bad template;
* 203 too large;
* 185 truncated.

So the order of the checks also agrees: each failure is reported where
the model reports it, and capacity is checked as each sub-phrase's bytes
are written.

**A Linux bug found here.** RPT after 1 to 7 bytes of output (possible
only after short data) makes Linux read before its output buffer.
* In the VM the first such stream oopsed the kernel ("unable to handle page
  fault", RIP `sw842_decompress+0x26d`): short data of 2 and 4 bytes, then
  RPT.
* E8 reproduces it with the 16-byte stream `eb616263d81e00000000000000000000`
  (short data `abc`, RPT with field 0, END). The fault address is 5 bytes
  before the buffer.
* Linux's own compressor never writes such a stream, but its decompressor
  accepts input from elsewhere.

This package refuses such a stream (`C842BadRepeat`), as Linux refuses
RPT with no output at all. The fuzzer leaves these streams out, so that
the VM survives.

## E8: the repeat bug

See E7. Stream `eb616263d81e00000000000000000000`, capacity 4096 → kernel
oops. It was not pursued further: the same bug was found independently and fixed upstream: Karl Mehltretter's
series "lib/842: reject malformed streams before invalid memory accesses"
(linux-crypto, 2026-08-29), applied to the crypto tree on 2026-09-11. Kernels without that series (Ubuntu's 6.8.0-147,
for one) still have it.

## The recorded vectors

`linux-vectors.txt` was written by `bend-audit/kmod842/record.py` from one
VM run. It holds:
* 155 inputs compressed by Linux, plus the empty input (`-22`);
* the package's streams decompressed by Linux: for each input, the default
  compressor, a 4-bit-table compressor and the literal-only stream;
* 1500 fuzzed streams with Linux's answers.

`model.py` agrees with all 2119 lines (`run.sh` checks the package the
same way).

## What the paper says, and where the observations add to it

* **Agreement:**
  * the 5-bit template;
  * LL as 2 raw bytes;
  * P8 as an 8-bit index into a 2 KB history of 8-byte entries;
  * P4 as a 9-bit index into the same 2 KB, with the low bit choosing the
    half (0 = the first 4 bytes, the "high" half on a big-endian machine);
  * P2 as an 8-bit index into a 512-byte history, with the low 2 bits
    choosing the quarter;
  * each chunk written to the next history position, overwriting the oldest;
  * Z8 as 8 zero bytes;
  * RPT repeating the previous 8 bytes;
  * at most 69 bits per chunk.
* **RPT's field.** The paper calls the 6-bit argument N, and says
  "Z8, RPT(63)" encodes 512 zero bytes. Linux writes those 512 bytes as Z8
  and a field of 62 (E1), and reads a field f as f + 1 repeats. This agrees
  with the paper's example only if RPT(N)'s field holds N − 1, which the
  paper does not say. If the field held N itself, Linux's reading would
  disagree with the paper by one.
* **The 29 templates.** The paper counts 29 templates in all. Linux decodes
  30 codes:
  * the 26 combinations;
  * RPT (27), Z8 (28), END (30);
  * short data (29), which the paper doesn't mention.

  Codes 26 and 31 are refused. Which of END and short data is the paper's
  29th cannot be told without the hardware.
* **The template numbering** is not in the paper. Linux's matches
  US 2006/0106870 A1's Figure 3 for codes 0 to 25. The patent's run state
  is 26, where Linux's RPT is 27.
