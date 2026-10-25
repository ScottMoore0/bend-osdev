# bend-osdev-md-engine

The Merkle–Damgård engine that bend-osdev's hash packages stream through,
and what they share:

* the engine: a state (`HsMdState<C>`) holding any chaining value type, the
  bytes of the unfinished block and the number of blocks compressed;
  `update` over any compression function and block size; the usual padding
  with a length field and the final step built on it;
* its streaming law, `md_streaming`, proved once for every chaining value
  type, compression function and block size (each hash package's
  streaming law is this law at its own defs);
* the chaining-value types `HsW2`, `HsW4`, `HsW5`, `HsW8` (open types),
  their digest bytes in either byte order, with laws on their lengths;
* the 64-byte block's sixteen words `HsW16` (open), word helpers (rotation,
  words of bytes, a block's words little- or big-endian) and the length
  fields;
* the error type `HsError` (`HsBadKeyLength{got}`).

It holds no hash. The hashes are packages of their own, each on this one:
[md4](../md4/), [md5](../md5/), [sha1](../sha1/),
[ripemd160](../ripemd160/), [sm3](../sm3/), [streebog](../streebog/)
(Streebog-256 and Streebog-512) and [michael](../michael/) (TKIP's MIC).

The directory is `md-engine` and the entry file `md-engine/md-engine.bend`;
the hub name is `bend-osdev-md-engine`. It and the hash packages were split
from bend-osdev-hashes@0.1.0.0, which they supersede (that version stays on
the hub as it was).

**Names.** The types and helpers keep the names they had in hashes
(`HsMdState`, `HsMd.*`, `HsW2` to `HsW16`, `HsError`, `hs.*`), so no hash's
code changes; types and constructors are global in Bend, and these names
collide with nothing. The `hs.*` helpers the hash packages build on (below)
are public now, as they must be for another package to use them.

## Specifications

* **The Merkle–Damgård construction and its padding:** the message in
  blocks through a compression function from an initial chaining value,
  padded with the byte 0x80, zeros, and the message's length in bits as an
  eight-byte field, little-endian (RFC 1320 and RFC 1321, section 3.1 and
  3.2) or big-endian (FIPS 180-4, section 5.1.1; SM3, as the sm3 package
  cites it), to a whole number of blocks.
* **Byte orders of the words:** little-endian words (RFC 1320, RFC 1321,
  RIPEMD-160, Michael) and big-endian ones (FIPS 180-4, GB/T 32905), as the
  hash packages' specifications state them.

Written from the public specifications only; no GPL source was read.

## Files

| File | Holds |
|---|---|
| `md-engine.bend` | the engine (`HsMdState`, `HsMd.*`), the chaining-value types and their digest bytes, `HsW16`, the word helpers, the length fields and `HsError` |
| `gen/laws.py` | writes `LAWS.bend` and `PROOF.bend` (`--check` checks they are current) |

## Public interface

**The engine** (the chaining value type `C` and the compression function
are template arguments; `~last` is the block size less one, a power of two
less one for `HsMd.md_pad`)

| Def / type | Meaning |
|---|---|
| `HsMdState<C>` | the state (opaque) |
| `HsMd.start(~C, cv)` | the state before any byte, from the initial chaining value |
| `HsMd.update(~C, ~compress, ~last, s, o)` | the state after more bytes (`Octets`), in any pieces |
| `HsMd.update_list(~C, ~compress, ~last, s, xs)` | the same, for bytes as a list |
| `HsMd.cv(~C, s)`, `HsMd.pending(~C, s)`, `HsMd.count(~C, s)`, `HsMd.blocks(~C, s)` | the state's parts: the chaining value, the bytes of the unfinished block (first first), how many there are, the number of blocks compressed (`W64`) |
| `HsMd.bits(~C, ~last, s)` | the length so far in bits, modulo 2^64 |
| `HsMd.md_pad(~last, cnt, field)` | the padding after `cnt` bytes of an unfinished block: 0x80, zeros, then the length field |
| `HsMd.final_md(~C, ~compress, ~last, ~field, ~out, s)` | the final step: the padding with the length in bits (`~field` writes it), through the engine, then the digest of the chaining value (`~out`) |

**Shared by the hashes**

| Def / type | Meaning |
|---|---|
| `HsW2{a, b}`, `HsW4{a, ..., d}`, `HsW5{a, ..., e}`, `HsW8{a, ..., h}` | chaining values of two, four, five and eight 32-bit words (open types) |
| `HsW2.le`, `HsW4.le`, `HsW5.le`, `HsW5.be`, `HsW8.be` | their digest bytes: each word little- or big-endian, in order |
| `HsW16{x0, ..., x15}` | the sixteen words of a 64-byte block (open type) |
| `hs.block.le(blk)`, `hs.block.be(blk)` | a 64-byte block's sixteen words, little- or big-endian (zeros for a list of another length: the engine passes only whole blocks) |
| `hs.rotl(x, n)` | rotation left by `n` (1 to 31) |
| `hs.le(a, b, c, d)`, `hs.be(a, b, c, d)` | the word of four bytes, little-endian (`a` least significant) or big-endian |
| `hs.len.le(v)`, `hs.len.be(v)` | the eight-byte length field, little- or big-endian (`~field` of `HsMd.final_md`) |
| `HsError` | `HsBadKeyLength{got}`: a key of a length the algorithm does not take (Michael's) |

Everything else (`hs.md.*`) is internal.

## Extension points

* **A new Merkle–Damgård hash** is a package on this one: a chaining value
  type (one of `HsW2` to `HsW8`, or its own, as Streebog's `HsStbCv`), a
  compression function on blocks of any power-of-two size (through
  `~last`) and a final step: `HsMd.final_md` with its length field and
  digest bytes for the usual padding (as md4, md5, sha1, ripemd160 and sm3
  do), or its own (as streebog and michael do). Its streaming law is
  `md_streaming` at its defs, with nothing more to prove; its digest-length
  law is one of the length laws below at its final chaining value (the hash
  packages' `gen/laws.py` write both).
* **Compression functions are template arguments**, so a hash's
  compression function can be replaced (a different unrolling, a faster
  table) and every law here still holds.
* **Open types:** `HsW2` to `HsW16` and `HsError` are open, so a hash
  builds and matches them directly; the state `HsMdState` is opaque (its
  parts through `HsMd.cv`, `pending`, `count` and `blocks`).

## Laws

`LAWS.bend` (written by `gen/laws.py`) has 6 laws, all for every input.

* `md_streaming`: the engine's update over `a ++ b` is update over `a`,
  then `b`, from every state, for every chaining value type, compression
  function and block size (from hashes). The update is a fold of a step
  over the bytes, so this holds by induction on `a`, whatever the step
  does.
* `w2_le_length`, `w4_le_length`, `w5_le_length`, `w5_be_length`,
  `w8_be_length` (new with the split: a package's proofs can use another
  package's laws, not its private lemmas): the digest bytes of every
  chaining value have 8, 16, 20, 20 and 32 bytes, whatever its words are.
  The hash packages' `<h>_length` laws rest on them (michael on
  `w2_le_length`, md4 and md5 on `w4_le_length`, ripemd160 on
  `w5_le_length`, sha1 on `w5_be_length`, sm3 on `w8_be_length`).

How they are proved: `md_streaming` by induction on the bytes with bytes'
`octets_append_list`; the lengths on the words' symbolic bits (a deep
pattern, then `{==}`) with bytes' `octets_len_of_list`.

## Tests

* `check.bend`: the word helpers and a 64-byte block's words both ways,
  each chaining value type's digest bytes, the padding's length around a
  block boundary (and for four-byte blocks), and the engine over a toy
  compression function: a 200-byte message in one piece and in three, with
  the same state (chaining value, pending bytes, count, blocks, bits) and
  digest. The expected lines were computed by hand from the definitions
  (in Python).
* No differential test: the engine has no independent implementation of its
  own. Each hash package tests it under its compression function, against
  Python's hashlib or a specification-checked model, whole and in pieces.

## Dependencies

`DEPS`: `bytes` (Octets, and its laws in the proofs) and `word64` (the
block count and the length fields). No hub package.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s), `--verdict` ALL PROOFS
CHECK (4 s, 0.37 GB peak), `check.bend` passes, `gen/laws.py --check` up
to date, `scripts/deps.sh` passes.
