# bend-osdev-c842

IBM's 842 compression, as Linux's 842 and POWER's NX accelerator read and
write it: compression, decompression (one-shot and streaming), and the
format's parser and serialiser, with Linux's CRC trailer.
* The decoder is safe against malformed input: it never writes past its
  maximum output, refuses what it cannot read, and names every failure.
  Every pointer it resolves names the position the format intends, among
  bytes already written and at most 2055 back (inside its 4096-byte
  window), or the stream is refused; proved for every stream.
* What the compressor writes decodes back to its input, and is never longer
  than the format's documented worst case of 69 bits a chunk. Both are proved
  for every input.

**Clean-room.** Linux's 842 (`lib/842`, `crypto/842.c`, the NX driver) is
GPL. This package was written from IBM's published paper and patent, and
from black-box tests of Linux's 842: inputs fed to the kernel's crypto API in
a VM, and its outputs and answers read back. No Linux source, kernel header
or kernel test vector was read. That is the basis for its MIT licence.
* One web search's summary, not a page opened, quoted a few words of Linux's
  `lib/842` header: that code 0 to 0x19 index a table, and that a
  software-only short data template exists. Nothing was taken from it; both
  facts were settled by the experiments below.

## Specification

1. **The paper:** B. Blaner et al., "IBM POWER7+ processor on-chip
   accelerators for cryptography and active memory expansion", *IBM J. Res. &
   Dev.* 57(6), 2013, paper 3, pages 3:10 to 3:13 ("Memory
   compression/decompression accelerator for AME"). From it come:
   * input in 8-byte chunks, each split into one 8-byte, two 4-byte and four
     2-byte sub-phrases;
   * a 5-bit template for each chunk, which says how the pointers and
     literals that follow make it up;
   * LL, a literal, is 2 raw bytes;
   * P8 is an 8-bit pointer into a history of 256 8-byte entries (2 KB);
   * P4 is a 9-bit pointer to one of 512 4-byte phrases in that same 2 KB
     history, two to an entry. The low bit is 0 for the entry's high 4 bytes
     and 1 for its low 4;
   * P2 is an 8-bit pointer to one of 256 2-byte phrases in a 512-byte
     history (64 entries of 8 bytes). The low two bits are 00 for the high 2
     bytes and 11 for the low 2;
   * each chunk is written to the histories at the next sequential location.
     They are rings: the counter rolls over and overwrites older data;
   * Z8 encodes 8 zero bytes;
   * RPT(N), with a 6-bit argument, repeats the previous 8 bytes N times.
     "Z8, RPT(63)" is 512 zero bytes in 5 + 5 + 6 = 16 bits;
   * 29 templates in all, counting the special ones, and at most 69 bits a
     chunk.
2. **The patent:** US 2006/0106870 A1, "Data compression using a nested
   hierarchy of fixed phrase length dictionaries" (IBM; Franaszek,
   Lastras-Montano, Robinson; 2004). Its Figure 3 is a state table of 27
   states: the 26 ways to cover 8 bytes with LL, P2, P4 and P8, numbered 0 to
   25, and a run state 26. Linux numbers its templates 0 to 25 exactly so
   (observation E2).
3. **Black-box observations of Linux's 842:** Ubuntu's 6.8.0-147-generic
   kernel, through the crypto API, in QEMU. They are logged with every input
   and output in `ref/OBSERVATIONS.md`. From them come:
   * the 5-bit code of each template, as in the patent (E1, E2);
   * RPT is 27, with a 6-bit field holding N − 1 (E1);
   * Z8 is 28 (E1);
   * the end is 30 (E1);
   * 26 and 31 are invalid (E2);
   * short data is 29: a 3-bit count of 1 to 7, then that many bytes. It is
     used for a tail of fewer than 8 bytes, and Linux accepts it anywhere in a
     stream (E1, E2, E4);
   * bits are written most significant first, packed from each byte's top
     bit (E1);
   * the end template is followed by a CRC-32 of the uncompressed bytes:
     polynomial 0x04C11DB7, most significant bit first, initial value 0, no
     final XOR (E1). Its check value is 0x89A1897F, and it is computed through
     bend-osdev-crc's parameter model;
   * after the CRC, zero bits to a whole number of 8-byte words. Linux ignores
     anything after the CRC (E1, E2);
   * how a pointer's index names a position (E3 to E6). An index i of an
     s-byte phrase, in a history of H bytes, reads s bytes at the latest
     position p ≡ i·s (mod H) below the output's length rounded down to 8.
     There must be one;
   * the decoder's answers: EINVAL, EOVERFLOW (cut short) or ENOSPC (output
     full), and where each is found (E7, 4000 fuzzed streams).

### Where the sources meet, and what the package does

* **RPT's field.** The paper calls RPT's 6-bit argument N and writes 512 zero
  bytes as "Z8, RPT(63)". Linux writes those 512 bytes as Z8 and a field of
  62, and reads a field f as f + 1 repeats. The two agree if the paper's
  RPT(63) means 63 repeats with a field of 62; the paper does not say how N
  is coded. The package follows Linux: field f, f + 1 repeats.
* **29 templates or 30 codes.** Linux decodes 30 codes: the 26 templates, RPT,
  Z8, the end and short data. The paper counts 29. Short data is probably a
  software addition (the paper does not mention it), but this can't be told
  without the hardware.
* **The run state.** The patent's run state is 26; Linux's RPT is 27, and 26
  is invalid.
* **RPT with fewer than 8 bytes of output.** Linux refuses RPT on an empty
  output. After 1 to 7 bytes (possible only after short data), it reads before
  its output buffer: E7 and E8 crashed the VM's kernel this way, with the
  16-byte stream `eb616263d81e00000000000000000000`. The package refuses such
  a stream (`C842BadRepeat`). This was found here on 2026-10-18 in Ubuntu's
  6.8.0-147 kernel; the same bug was found independently and fixed upstream: Karl Mehltretter's
  series "lib/842: reject malformed streams before invalid memory accesses"
  (linux-crypto, 2026-08-29), applied to the crypto tree on 2026-09-11.
* **The size of a stream.** Linux's crypto API path refuses compressing more
  than 128 KiB, and decompressing into more (E5). That is the API's limit, not
  the format's; the package has none beyond its maximum output.

## Files

| File | Holds |
|---|---|
| `c842.bend` | the entry file and main concern: a stream in, its bytes out (and back), with options or the defaults |
| `format.bend` | the format: sub-phrase kinds, the 26 templates, the codes, tokens, the serialiser, packing, the bit-at-a-time parser, the whole-stream token reader, the worst case |
| `bits.bend` | bit-level access to bytes and words (generated by `gen/bits.py`) |
| `decode.bend` | the decoder: one-shot and streaming |
| `pointer.bend` | the pointer rule: the position an index names, after n bytes of output |
| `window.bend` | random access to the last 4096 bytes by position (internal; replaceable) |
| `match.bend` | the matcher: the hash tables that find earlier phrases, and its strategy parameter |
| `encode.bend` | the encoder: the literal stream, the chunk loop, the check |
| `crc.bend` | the CRC trailer, through bend-osdev-crc |
| `error.bend` | `C842Error` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `proof_pointer.bend` | the pointer rule's arithmetic as `Nat` facts, for the proofs (internal) |
| `check.bend` | examples, with their output |
| `gen/bits.py`, `gen/proof_lemmas.py`, `gen/vectors.py` | generators of `bits.bend`, of `PROOF.bend`'s deep patterns, and of the vector laws |
| `ref/model.py`, `ref/gen.py`, `ref/runner.bend`, `ref/run.sh` | the differential test (below) |
| `ref/linux-vectors.txt`, `ref/OBSERVATIONS.md` | the vectors recorded from Linux, and the log of the experiments |

## API

Byte strings are `Octets` (bend-osdev-bytes). Everything that reads input
answers `Result<&2, &2, C842Error, A>`.

### Streams (`c842.bend`)

| Def | Meaning |
|---|---|
| `decompress(src)` | the bytes of the stream `src`, at most 64 MiB |
| `decompress_with(opts, src)`, `C842Options{max}`, `C842Options.default()` | the same with a maximum (`U32`) |
| `compress(o)` | a stream holding `o` (default options) |
| `compress_with(opts, o)` | the same with `C842CompressOptions` |

### Decoding (`decode.bend`)

| Def | Meaning |
|---|---|
| `c842.decompress(src, max)` | the bytes of `src`, at most `max` (a `Nat`) |
| `c842.reader_start(max)`, `c842.reader_feed(r, piece)`, `c842.reader_finish(r)` | streaming: feed a stream in any pieces |
| `c842.reader_decompress(max, pieces)` | a stream fed in these pieces |
| `c842.u32_same(a, b)` | word equality, bit by bit (used for the CRC) |

### The pointer rule (`pointer.bend`)

| Def | Meaning |
|---|---|
| `c842.pointer(n, k, i)` | the position (`Some{p}`) that the pointer of kind `k` with index `i` reads after `n` bytes of output, or `None{}` if there is none; the decoder resolves every pointer with it |

### Encoding (`encode.bend`)

| Def | Meaning |
|---|---|
| `c842.compress(o)`, `c842.compress_with(opts, o)` | a stream for `o`, checked by decoding it (else the literal stream) |
| `c842.compress_bits(opts, o)` | the same stream's bits, before padding |
| `c842.compress_unchecked(opts, o)`, `c842.compress_bits_unchecked(opts, o)` | the encoder's stream, without the check |
| `c842.literals(o)`, `c842.literal_bits(o)` | the literal stream (the worst case) and its bits |
| `C842CompressOptions{strategy}`, `C842CompressOptions.default()` | the matcher's strategy; the default is `C842Strategy.default()` |

### The matcher (`match.bend`)

| Def | Meaning |
|---|---|
| `C842Strategy`: `C842NoMatch{}`, `C842Hash{bits8, bits4, bits2}` | no pointers (literals, Z8 and RPT only), or direct-mapped hash tables of 2^bits entries for 8-, 4- and 2-byte phrases |
| `C842Strategy.default()` | `C842Hash{10, 11, 10}`: the hardware's 1K and 2K tables for 8- and 4-byte phrases, and 1K for 2-byte phrases |
| `c842.match.new(s)`, `c842.match.find(m, kind, i, phrase, window)`, `c842.match.add(m, kind, j, phrase)` | the matcher's interface, for another encoder |

### The format (`format.bend`)

| Def | Meaning |
|---|---|
| `C842Kind` (`C842LL`, `C842P2`, `C842P4`, `C842P8`), `.width`, `.size`, `.history` | a sub-phrase: its bits, bytes, and the history its index counts in |
| `c842.templates()`, `c842.template(t)` | the 26 templates, by code |
| `c842.code.repeat()`, `.zero()`, `.short()`, `.end()` | 27, 28, 29, 30 |
| `C842Token` (`C842Chunk{t, fields}`, `C842Repeat{n}`, `C842Zero{}`, `C842Short{bytes}`, `C842End{crc}`), `C842Field` (`C842Lit{hi, lo}`, `C842Ptr{index}`) | a stream as values (RPT's `n` is the field: n + 1 repeats) |
| `c842.serialise(tokens)`, `c842.fmt.token(t)` | the tokens' bits; one token's |
| `c842.fmt.cat(a, b)`, `c842.fmt.zeros(n)` | bit lists: joined; n zero bits |
| `c842.tokens(src)` | a stream's tokens, up to its end (the format only: pointers, repeats and the CRC are the decoder's to check) |
| `c842.pack(bits)`, `c842.unpack(o)`, `c842.pack.fill(bits)` | bits to bytes (zero-filled to whole 8-byte words) and back; the zero bits added |
| `C842Parser.start()`, `C842Parser.step(p, bit)`, `C842Step`, `C842Event` | the bit-at-a-time parser: each bit answers the event it completes |
| `c842.worst_bits(n)`, `c842.worst_bytes(n)` | the worst case for n bytes: in bits before padding, and in bytes |

### The CRC (`crc.bend`)

`C842Crc.spec()` (a `Crc32Spec` of bend-osdev-crc) and `c842.crc(o)`.

The types `C842Options`, `C842CompressOptions`, `C842Strategy`, `C842Kind`,
`C842Field`, `C842Token`, `C842Error`, `C842Step` and `C842Event` are open:
their constructors are part of the interface. `C842Dec`, `C842Parser`,
`C842Matcher` and `C842Win` are opaque.

### Failures

| `C842Error` | When | Linux |
|---|---|---|
| `C842Truncated` | the input ends before the end template's CRC | EOVERFLOW |
| `C842OutputTooLarge` | a byte would pass the maximum | ENOSPC |
| `C842BadTemplate` | code 26 or 31 | EINVAL |
| `C842BadPointer` | no position yet for a pointer's index | EINVAL |
| `C842BadRepeat` | RPT with fewer than 8 bytes of output | EINVAL with none; Linux misbehaves with 1 to 7 |
| `C842BadShort` | short data with count 0 | EINVAL |
| `C842BadCrc` | the CRC is not the output's | EINVAL |

## The compressor

Chunk by chunk, greedy:
* a chunk equal to the previous one is part of a run, written as RPT (at most
  64 chunks per RPT, as the 6-bit field allows);
* else eight zero bytes are Z8;
* else the matcher looks up the chunk's seven phrases. The chunk is written
  with the template of fewest bits whose pointers were all found, the lowest
  code on a tie.

As in the paper, each phrase size has a direct-mapped hash table. A hit is
only a hint: the phrase's bytes are compared with the history before a
pointer is written, and the position must be one the decoder will read (no
more than the history back from the chunk). The hash is FNV-1a (the
hardware's XOR trees are its own). The tail is short data. All the tables
are updated for every chunk.

The stream is then checked: `compress_with` decodes it, and writes the
literal stream instead should it not decode back or be longer than the worst
case. The differential test confirms the check never falls back on its
inputs.

Linux's own compressor makes different choices in places, so the two
compressors' streams differ for some inputs. Each decodes the other's
(`ref/run.sh`).

## Extension points

* **The strategy:** `C842Strategy` is the matcher's parameter, with
  `C842Strategy.default()`; `C842NoMatch` turns matching off. A new strategy
  (hash chains, a different hash, lazy choice between overlapping phrases) is
  a new constructor in `match.bend`.
* **A different encoder:** the matcher's three defs and the format's tokens
  and serialiser are public. The check in `compress_with` keeps the round-trip
  law true whatever an encoder writes, so a new encoder needs no new proof,
  only the differential test.
* **The format's tables:** `c842.templates()` is a value, and the parser looks
  templates up in it. A variant format (another numbering, say the patent's
  run state at 26) changes that table and the codes in one place.
* **The pointer rule:** `pointer.bend` is one def, `c842.pointer`, which
  the decoder calls with its output's length. A variant format (other
  history sizes) changes it there; `pointer_found`, `pointer_rule` and
  `pointer_in_window` state what a replacement must keep.
* **The window:** `window.bend` is behind three defs (`c842.win.empty`,
  `.put`, `.get`). The laws do not depend on what it answers, so any
  structure that gives the byte at a position can replace the trie.
* **The CRC:** `C842Crc.spec()` is a bend-osdev-crc parameter set. Another
  check would change only `crc.bend`.
* **Streaming:** the decoder reads a stream in pieces (`c842.reader_*`). The
  encoder is one-shot for now. Its state is a few tables, the window and the
  pending run, so a streaming encoder could feed chunks as they come and
  finish the CRC with bend-osdev-crc's `start`/`update`/`finish`.
* **Speed:** `compress_unchecked` skips the check (and the round-trip law).

## Laws

`LAWS.bend` has 75 laws: 20 properties, 1 witness and 54 vectors.

**For every input** (properties, proved by induction):

* `pack_round_trip`: a stream's bytes unpack to its bits, then the zero bits
  `pack.fill` counts;
* `literals_round_trip`: the literal stream decodes back to its bytes for
  every maximum that holds them;
* `compress_round_trip`: what `compress_with` writes decodes back to its
  input, for every input and all options;
* `literal_bits_worst`: the literal stream is exactly `worst_bits(len)` bits
  before padding. That is 69 for each chunk, 8 + 8k for a tail of k bytes,
  and 37 for the end and its CRC;
* `compress_within_worst`: the compressor's stream is never longer than that;
* `compress_packs`: its bytes are those bits, packed;
* `output_within_max`: whatever the input and maximum, the decoder never
  answers more bytes than the maximum;
* `trailing_ignored`: a valid stream followed by anything decodes as the
  stream alone (with a witness that the hypothesis can hold);
* `reader_pieces`: decoding through the reader, in any pieces, answers what
  the one-shot decoder answers for the pieces joined;
* `code26_rejected`, `code31_rejected`, `repeat_first_rejected`,
  `short_zero_rejected`: a stream that opens with code 26 or 31, with RPT, or
  with short data of count 0 is refused, whatever follows.

**The pointer rule** (`pointer.bend`), for every output length `n`, every
kind `k` and every index `i` of the kind's width. With `s` the kind's size,
`H` its history and `t8` the length rounded down to 8 (`n / 8 * 8`), an
index reads `s` bytes at the latest position `p ≡ i·s (mod H)` below `t8`,
and there must be one:
* `pointer_found`: a position exists exactly when `i·s < t8` (`i·s` itself
  is the least position congruent to it); otherwise `c842.pointer` answers
  `None{}` and the decoder refuses the stream (`C842BadPointer`);
* `pointer_rule`: the position `p` it answers has `p mod H = i·s`,
  `p + s <= t8` (so `p` and the `s` bytes from it are below `t8`) and
  `t8 <= p + H` (so the next position congruent to `i·s` is not: `p` is the
  latest);
* `pointer_in_window`: so `p + s <= n` and `n <= p + H + 7`: every byte a
  pointer reads is already written, at most 2055 bytes back, inside the
  decoder's window of the last 4096;
* `parser_indices_fit`: every index the parser reads, along any bits from
  the start, has its kind's width (8 bits for P2 and P8, 9 for P4), which
  is the hypothesis `i·s < H` of the laws above. The decoder resolves each
  pointer the parser announces with `c842.pointer` at its output's length
  (`decode.bend`), so these laws cover every pointer of every stream, in
  every state of the decoder;
* `first_p8_rejected`, `first_p4_rejected`, `first_p2_rejected`: a stream
  that opens with a pointer (templates 25, 20 and 10, whose first
  sub-phrases are P8, P4 and P2) is refused as `C842BadPointer`, whatever
  its index and whatever follows: nothing is written yet, so `t8 = 0`.

How the round trip is proved:
* the literal stream's proof follows the decoder bit by bit over symbolic
  bytes: each byte's bits are read back by deep patterns (`bits.bend`), and
  the CRC's 32 bits likewise;
* the compressor's round trip holds because `compress_with` checks its
  stream and falls back to the literal stream. The proof covers the check and
  the fallback; the matcher itself is covered by the differential test and
  the Linux vectors, not by a proof.

How the pointer rule is proved (`proof_pointer.bend`): `c842.pointer`
computes, from the output's length `n`, `t8 = n & ~7`, `base = t8 & -H`
and `p0 = base + s·i`. With `n`'s word split at 3 bits and `t8`'s at H's
bits, their values are `t8 = 8·D`, `t8 = rr + H·B` (`rr < H`), `base = H·B`
and `p0 = H·B + i·s`, which does not wrap: it is at most the word of `t8`'s
high bits and H's bits all ones. These come from the laws of bend-osdev-u32
on U32 values (`u32_add_value`, `u32_sub_value`, `u32_shln_value`,
`u32_lt_value`, `word_value_lt`; u32 is a dependency of the proofs only)
and private lemmas on `Word.and` and on `Word.mul` by a power of two. Then `p0 < t8` exactly when `i·s < rr`; if
not, `p0 < H` exactly when `B = 0`; the three cases give the rule. The
index's width is the parser's invariant: in a field state, the bits read
and the bits left add up to the width, with at least one left.

What isn't proved:
* that the bytes a pointer copies are the output's bytes at its position:
  the laws state the position, not what the window (`window.bend`, a trie
  keyed by a position's low 12 bits) answers there. Vectors cover each
  template, and the differential test covers positions across the
  histories' wrap-around.

**Vectors** (proved by computation; 54):
* the paper's examples:
  * Z8 then RPT(63) is 512 zero bytes, and its two codes are 16 bits;
  * P8 is 13 bits;
  * P4_P2_LL is the template [P4, P2, LL];
  * 69 bits is the most a chunk takes;
  * there are 26 templates;
* Linux's streams, which the package writes byte for byte: one byte, eight
  and nine bytes, Z8, Z8 with RPT, RPT, and the P4 LL LL, P4 P4, P2 and P8
  templates;
* every template of the patent's Figure 3, decoded as Linux decoded it;
* Linux's answers to a bad CRC, a stream cut short, a full output, trailing
  bytes, an unwritten pointer, and short data mid-stream;
* the RPT that made Linux read before its buffer;
* the CRC's check value;
* the worst case for 8 and 64 bytes;
* the token reader;
* the pointer rule's answers of both kinds (`pointer_vectors`, which is also
  the witness that the hypothesis of `pointer_rule` can hold).

The proofs check with `--verdict` too.

## Tests

`ref/run.sh` runs `ref/runner.bend` natively over `ref/cases.bin`, written by
`ref/gen.py` (seed 2026), and compares every answer. The cases come from two
places.

**The Linux vectors** (`ref/linux-vectors.txt`, 2118 cases). These are data
from one run of Linux's 842 as a black box: Ubuntu 6.8.0-147-generic, the
crypto API's `"842"`, in QEMU. The tooling is outside this repository, in
`bend-audit/kmod842/`:
* `kmod842.c`, a GPL-2.0 test module written from the crypto API's documented
  call pattern;
* `run-vm.sh`, which builds it against the Ubuntu headers, builds the
  initramfs (`mkinitrd.py`, `init.c`) and boots QEMU;
* `record.py`, which writes the requests and the vectors file.

The run.sh checks, in both directions:
* the 155 streams Linux compressed (from 1 byte to 4 KB: ramps, zeros,
  repeats, text, random data, repeated phrases) decode in the package to
  their inputs;
* for each input, the package's compressor (default and 4-bit tables) and
  its literal stream write exactly the streams Linux decoded back to the
  input;
* each of 1497 fuzzed streams gets from the package the answer Linux gave.
  That is the same bytes, or a failure with Linux's errno: 234 accepted, 1161
  refused with EINVAL, 60 with EOVERFLOW, 42 with ENOSPC.

To record the vectors again (optional), see the comment at the top of
`ref/run.sh`; the VM run takes a few seconds.

**The model** (`ref/model.py`, about 2070 cases a seed). It is an independent
implementation written from the same sources: the paper, the patent and
`ref/OBSERVATIONS.md`. **It shares an author with this package**, so it
checks the package against a second reading of those sources, not against
IBM's or Linux's implementation. Linux's answers above are the independent
check. Against the model:
* compression, checked and unchecked, under six strategies, of random, text,
  run, zero, repeated-chunk and far-repeat inputs from 0 to 12000 bytes;
* the literal stream;
* decoding of the package's streams, with a maximum one byte short, and in
  pieces;
* 1500 fuzzed streams, valid and malformed, with random maximums;
* the token reader on malformed streams.

Seeds 2026 and 1 to 5 pass. The model also agrees with all 4000 streams of
experiment E7 and every line of `linux-vectors.txt`.

Without python3, `run.sh` exits 77 (a skip). It needs no other tool: the
Linux answers are data.

## Speed and limits

Measured on native builds (`bend file.bend -o prog`), Bend 2.0.37, WSL2, on
937,064 bytes of text (words from a 16-word list), one run each, by hand:

| Run | Time | Peak memory |
|---|---|---|
| building the input only (the baseline in every row) | 0.11 s | 75 MB |
| `compress_unchecked` (to 374,328 bytes, 39.9%) | 3.3 s | 184 MB |
| `compress` (the same, then decoded and compared) | 6.8 s | 336 MB |
| `compress_unchecked`, then `decompress` | 5.1 s | 184 MB |
| `literals` (1,010,280 bytes: the worst case) | 0.6 s | 318 MB |

So decoding runs at about 0.5 MB/s and matching at about 0.3 MB/s. The
template choice (26 templates tried per chunk) is most of the encoder's
time.
* The decoder reads the stream bit by bit as a list (a tail-recursive loop)
  and keeps its output as a list as well as in the window; memory, not the
  stack, is the limit. Keep a single call to a few MB, or feed the reader in
  pieces.
* Packing, unpacking and the serialiser recurse over the bits (structurally,
  as the proofs follow them). Native builds have a 2 GB stack, which holds
  inputs of many MB; on the JavaScript lane, keep inputs to a few KB.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (75 laws), `--verdict` ALL PROOFS
CHECK, `check.bend` passes, `ref/run.sh` 4186 cases match (2118 from the Linux
vectors, 2068 against the model; seeds 2026 and 1 to 5), `scripts/deps.sh`
passes. Linux compatibility: verified against Linux 6.8's 842 as recorded in
`ref/linux-vectors.txt`. Not verified against POWER's NX hardware.
