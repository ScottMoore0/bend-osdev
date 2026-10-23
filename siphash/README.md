# bend-osdev-siphash

SipHash-c-d and HalfSipHash-c-d, keyed hashes (pseudorandom functions) for
short inputs, for every number of compression rounds c and finalization
rounds d, with the 64- and 128-bit outputs of SipHash and the 32- and
64-bit outputs of HalfSipHash; streaming and one-shot. Linux's
`lib/siphash.c` uses SipHash-2-4 (`siphash`) and SipHash-1-3 or
HalfSipHash-1-3 (`hsiphash`, on 64- and 32-bit machines); all three are
named parameter sets here.

The directory is `siphash` and the entry file `siphash/siphash.bend`; the
hub name is `bend-osdev-siphash`. bend-kit-hash has SipHash-1-3 only;
bend-osdev-kithash makes this package's SipHash and HalfSipHash, and
bend-kit-hash's SipHash-1-3, instances of crypto's MAC interface, and
proves the two SipHash-1-3s agree on its vectors.

## Specifications

* **SipHash:** J.-P. Aumasson and D. J. Bernstein, *SipHash: a fast
  short-input PRF* (permanent ID b9a943a805fbfc6fde808af9fc0ecdfa, date
  2012.09.18), section 2 (initialization, compression, finalization,
  SipRound) and Appendix A (the test values of SipHash-2-4).
* **The 128-bit output and HalfSipHash:** the reference implementation,
  `siphash.c` and `halfsiphash.c` of github.com/veorq/SipHash (CC0; the
  paper defines neither). HalfSipHash works on 32-bit words with a 64-bit
  key: v0 = k0, v1 = k1, v2 = k0 ^ 6c796765, v3 = k1 ^ 74656462, the
  rotations 5, 16, 8, 7, 13, 16, the length in the top byte of the last
  32-bit word, and the output v1 ^ v3. A double-width output xors ee into
  v1 at the start and into v2 (in place of ff) before finalization, and
  follows the first word with v1 ^= dd, d more rounds and a second word.
* **Vectors:** the reference implementation's `vectors.h` (the four tables
  of 64 entries: SipHash-2-4 with 64- and 128-bit outputs, HalfSipHash-2-4
  with 32- and 64-bit outputs, for the key 00 01 .. 0f and the messages
  00 01 .. (i - 1), as its `test.c` builds them), read as data into
  `ref/vectors.py`.

## Files

| File | Holds |
|---|---|
| `siphash.bend` | the error type, the parameters (`SipParams`), SipHash's keys, state, streaming and one-shot forms |
| `halfsiphash.bend` | HalfSipHash: its keys, state, streaming and one-shot forms, and its named parameter sets |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | all 256 published vectors, the openssl command's SipHash-1-3 and -4-8 values, pieces, bytes and refusals (written by `gen/check.py`) |
| `gen/check.py` | writes `check.bend` from `ref/vectors.py` (`--check` checks it is up to date) |
| `ref/model.py` | SipHash-c-d and HalfSipHash-c-d in Python, written from the paper and the reference implementation |
| `ref/vectors.py` | `vectors.h`'s four tables, as data |
| `ref/gen.py`, `ref/run.sh` | the differential test (below) |

## Public interface

**`siphash.bend`**

| Def or type | Meaning |
|---|---|
| `SipError` (`SipBadKeyLength{got}`) | a key of the wrong length (16 bytes for SipHash, 8 for HalfSipHash) |
| `SipParams{c, d, wide}` (open) | c compression rounds, d finalization rounds, the double-width output |
| `SipParams.sip24()`, `.sip13()`, `.sip48()`, `.sip24_wide()` | SipHash-2-4 (the paper's proposal), -1-3, -4-8 (the paper's conservative proposal), -2-4 with the 128-bit output |
| `SipParams.c`, `.d`, `.wide`, `.out_len` | the fields; the output length (8 or 16 bytes) |
| `SipKey` (opaque), `SipKey.of_words(k0, k1)`, `SipKey.of_octets(o)`, `SipKey.k0`, `SipKey.k1` | a key: two 64-bit words, or 16 bytes read little-endian (`SipBadKeyLength` otherwise) |
| `SipState` (opaque), `SipHash.start(prm, key)`, `SipHash.update(s, o)`, `SipHash.update_byte(s, b)`, `SipHash.finish(s)`, `SipHash.params(s)` | streaming: the output is 8 (or 16) bytes, each 64-bit word little-endian, as the reference implementation writes it |
| `SipHash.hash(prm, key, o)`, `siphash24(key, o)`, `siphash13(key, o)` | one call |
| `SipHash.mac(prm, key_bytes, o)` | one call from a raw key: `Result<&2, &2, SipError, B.Octets>` |

**`halfsiphash.bend`**: `HalfSipParams.hsip24()`, `.hsip13()`,
`.hsip24_wide()` (64-bit output), `HalfSipParams.out_len` (4 or 8 bytes);
`HsipKey` (opaque), `HsipKey.of_words(k0, k1)`, `HsipKey.of_octets(o)`
(8 bytes), `HsipKey.k0`, `HsipKey.k1`; `HsipState` (opaque),
`HalfSipHash.start`, `.update`, `.update_byte`, `.finish`, `.params`,
`.hash`, `.mac`; `halfsiphash24(key, o)`, `halfsiphash13(key, o)`.

Everything else (`sip.*`, `hsip.*`, `SipV`, `HsipV`) is internal.

## Extension points

* **The rounds and the output width** are the parameter record: any
  SipHash-c-d or HalfSipHash-c-d (the paper's cryptanalysis targets
  SipHash-1-0, -2-1, ... included) by building `SipParams{c, d, wide}`;
  the named sets are defaults.
* **Keys** come as words (`of_words`, as Linux's `siphash_key_t` holds
  them) or as bytes (`of_octets`).
* **Streaming:** `start`, `update` (any split), `update_byte`, `finish`;
  the state holds the at most 7 (or 3) bytes of the word being filled, so
  data can arrive a byte at a time.
* **As a MAC** through crypto's interface: bend-osdev-kithash's
  `inst_mac.bend`.

## Laws

`LAWS.bend` has 19 laws, all proved and accepted by `--verdict`.

* **For every parameter set, key, state and message:**
  `siphash_streaming` and `halfsiphash_streaming` (the state after
  a ++ b is the state after a, then b), `siphash_update_empty`,
  `halfsiphash_update_empty`, `siphash_split` and `halfsiphash_split` (the
  one-shot output is the streaming output for every split),
  `siphash_length` and `halfsiphash_length` (the output has 8 or 16, and 4
  or 8, bytes, from every state). The streaming proofs go through bytes'
  `octets_append_list`; the lengths through the bytes of a word.
* **Vectors, by computation:** the paper's Appendix A (its little-endian
  reading of the key, and SipHash-2-4 of 00 .. 0e = a129ca6149be45e5);
  `vectors.h`'s `vectors_sip64[0]` and `[8]`, `vectors_sip128[15]`,
  `vectors_hsip32[0]` and `[7]`, `vectors_hsip64[15]`; SipHash-1-3 of
  00 .. 0e, the openssl command's value; the refusal of a 15-byte SipHash
  key and a 16-byte HalfSipHash key.

**Not proved, and tested:** that the byte-at-a-time state computes the
paper's word-at-a-time definition for every input (the code takes bytes
one at a time and compresses a word when its eighth byte arrives, which is
the definition rearranged; a proof would relate the pending word built
from shifted bytes to the little-endian word of eight bytes). It is tested
on all 256 published vectors and 672 cases against the openssl command
(below).

## Tests

* `check.bend`: all 256 entries of `vectors.h` (each message hashed in one
  piece); SipHash-1-3 of 15 and 63 bytes and SipHash-4-8 of 15 bytes (the
  openssl command's values); SipHash-2-4 of 10,000 pseudo-random bytes
  (openssl's value); HalfSipHash-1-3 of 15 and 63 bytes (`ref/model.py`'s
  values: no outside implementation is installed); SipHash-2-4 of 63 bytes
  in three pieces, of 9 bytes a byte at a time, HalfSipHash-2-4 in two
  pieces; keys of the wrong length refused and of the right one accepted.
* `ref/run.sh` (672 cases with the default seed): 48 random keys and
  messages (0 to 300 bytes, and lengths around word boundaries), each in
  one piece and in two at a random split: SipHash-2-4, -1-3, -4-8 and -2-4
  with the 128-bit output against the openssl command (`openssl mac ...
  SIPHASH` with its c-rounds and d-rounds, OpenSSL 3.0.13), an independent
  implementation; HalfSipHash-2-4, -1-3 and -2-4 with the 64-bit output
  against `ref/model.py`. **The model shares an author with this
  package**; it is checked first against all 256 published vectors, and
  for SipHash against openssl on every case.
* A bend-kit-hash comparison: bend-osdev-kithash's laws prove this
  package's SipHash-1-3 equals bend-kit-hash's on six messages, and its
  ref test compares them on 74 random inputs against openssl.

## Sizes

Every loop is tail-recursive over the bytes, so a message has no length
limit beyond memory. Native build (Bend 2.0.37, WSL2), 1 MB of
pseudo-random bytes: building the input alone 0.95 s and 131 MB;
SipHash-2-4 of it, with the building, 1.35 s and 155 MB (result checked
against openssl). `check.bend` takes about 4 s with its build.

## Notes on use

SipHash-2-4 is the paper's proposal for a MAC and hash-table key; the
reduced-round SipHash-1-3 and HalfSipHash are what Linux uses for hash
tables only (`hsiphash`), not as MACs. The output is 64 bits (or 128), so
a forgery succeeds with probability 2^-64 per try (the paper, section 3).
None of this is constant-time, and Bend's runtime promises nothing about
running time.

## Dependencies

`DEPS`: `bytes` (Octets, and its laws in the proofs), `word64` (W64, for
SipHash's state).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 3 s), `--verdict` ALL
PROOFS CHECK (about 5 s, 247 MB), `check.bend` passes, `ref/run.sh` 672
cases match, `scripts/deps.sh` passes.
