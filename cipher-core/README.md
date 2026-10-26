# bend-osdev-cipher-core

What the block and stream ciphers of bend-osdev's cipher packages share, and
the modes for 64-bit block ciphers:

* the error type `LcError` every cipher package answers;
* the 64-bit block `LcBlock64` (an open type), its XOR, hex text and byte
  forms;
* word helpers (rotations, bytes, words of bytes), native and on bits (the
  bit forms are for steps a proof must undo);
* tables (`LcTab`, an open type) a cipher builds once per key;
* Feistel rounds over any round function and round-key type;
* `modes64.bend`: ECB and CBC for any 64-bit block cipher.

It holds no cipher. The ciphers are packages of their own, each on this one:
[des](../des/) (DES and Triple DES), [sm4](../sm4/), [camellia](../camellia/),
[serpent](../serpent/), [twofish](../twofish/), [aria](../aria/),
[cast6](../cast6/) (CAST-256), [blowfish](../blowfish/),
[cast5](../cast5/) (CAST-128), [tea](../tea/), [xtea](../xtea/),
[fcrypt](../fcrypt/) and [rc4](../rc4/).

The directory is `cipher-core` and the entry file `cipher-core/cipher-core.bend`;
the hub name is `bend-osdev-cipher-core`. It and the cipher packages were
split from bend-osdev-legacy-ciphers@0.1.0.0, which they supersede (that
version stays on the hub as it was).

**Why the 64-bit modes are here, not a package of their own.** `modes64.bend`
reads and writes blocks through the block's byte form (`lc.block8`,
`lc.block_bytes`), and its byte-layer law (`blocks64_octets_round_trip`)
rests on the same bit-level lemmas as the block's own
(`block64_octets_round_trip`). A separate package would have to make those
internals public and add laws only to cross the boundary, for 177 lines of
code. It is in its own file, so a program that needs only the block or the
helpers does not import it (Bend imports do not re-export).

**Names.** The types and helpers keep the names they had in legacy-ciphers
(`LcError`, `LcBlock64`, `LcTab`, `lc.*`, `Lc64.*`, `m64.*`), so no cipher's
code changes; types and constructors are global in Bend, and these names
collide with nothing.

## Specifications

* **ECB and CBC** (64-bit blocks): NIST SP 800-38A, *Recommendation for Block
  Cipher Modes of Operation*, sections 6.1 and 6.2.
* **The block's byte form:** two big-endian 32-bit words, as DES (FIPS 46-3),
  Blowfish, CAST-128 (RFC 2144) and FCrypt specify their blocks (TEA and XTEA
  choose their words' order themselves).
* **Feistel rounds:** the round (L, R) -> (R, L xor f(k, R)) of FIPS 46-3,
  undone by (L', R') -> (R' xor f(k, L'), L'), over any f; CAST-128 and
  FCrypt are built on it.

## Files

| File | Holds |
|---|---|
| `cipher-core.bend` | `LcError`, `LcBlock64`, the word helpers, tables, Feistel rounds |
| `modes64.bend` | ECB and CBC for any 64-bit block cipher (`Lc64.*`) |
| `gen/proof.py` | the generator of `PROOF.bend`'s region "bits" (the rotations by 1 and 31 and the byte swap undone, and a block's bytes, on a word's 32 bits); `python3 gen/proof.py` rewrites it, `--check` checks it is up to date |

## Public interface

Every fallible function answers `Result<&2, &2, LcError, A>`.

**`cipher-core.bend`**

| Def / type | Meaning |
|---|---|
| `LcError` | `LcBadKeyLength{got}`, `LcBadIvLength{got}`, `LcNotBlockMultiple{len}` |
| `LcBlock64{hi, lo}` | a 64-bit block, two big-endian words (open type) |
| `LcBlock64.zero()`, `LcBlock64.xor(a, b)`, `LcBlock64.hex(b)` | the zero block, XOR, hex text |
| `LcBlock64.to_octets(b)`, `LcBlock64.of_octets(o) -> Maybe` | 8 bytes and back (`None` for another length) |
| `lc.rotl(x, n)`, `lc.byte(x, n)`, `lc.be(a, b, c, d)`, `lc.le(a, b, c, d)`, `lc.bit(x, i)`, `lc.at(xs, n)` | native word helpers: rotation left by 1 to 31, byte n from the least significant, the word of four bytes (big- or little-endian), bit i, element n of a list (0 past the end) |
| `lc.wrotl(m, n, w)`, `lc.rotl1.bits` .. `lc.rotl31.bits` (1, 3, 5, 7, 10, 13, 19, 22, 25, 27, 29, 31) | rotations on bits |
| `lc.bits8(b)`, `lc.of8(s)`, `lc.be.bits(a, b, c, d)`, `lc.b0.bits(w)` .. `lc.b3.bits(w)`, `lc.bswap.bits(w)` | bytes on bits: a byte's bits and back, a word of bytes, a word's bytes (b0 the most significant), the byte swap |
| `lc.msb(x, acc)`, `lc.rev_bits(bs, acc)`, `lc.drop_bits(n, bs)`, `lc.word_lsb(n, bs)`, `lc.nth(bs, i)` | words as lists of bits and back (DES's permutations) |
| `LcTab` (`LcLeaf{v}`, `LcNode{l, r}`; open), `lc.tab(d, xs)`, `lc.tab.get(d, t, i)`, `lc.tab.set(d, t, i, v)` | a table of 2^d words, read and written by the bits of an index |
| `lc.fe.step(~RK, ~f, k, b)`, `lc.fe.unstep`, `lc.fe.run(~RK, ~f, ks, b)`, `lc.fe.unrun` | a Feistel round over the round function f and round key k, undone; a list of rounds, undone last to first |
| `lc.swap(b)` | the two halves exchanged |

**`modes64.bend`** (the cipher as template arguments `~K`, `~enc`, `~dec`,
as in the 128-bit modes)

| Def | Meaning |
|---|---|
| `Lc64.ecb_encrypt_blocks(~K, ~enc, +k, bs)`, `Lc64.ecb_decrypt_blocks(~K, ~dec, +k, bs)` | ECB on a list of blocks |
| `Lc64.cbc_encrypt_blocks(~K, ~enc, +k, iv, bs)`, `Lc64.cbc_decrypt_blocks(~K, ~dec, +k, iv, bs)` | CBC on a list of blocks |
| `Lc64.blocks_of(o)`, `Lc64.octets_of(bs)` | bytes to whole blocks (`LcNotBlockMultiple`) and back |
| `Lc64.ecb_encrypt(~K, ~enc, +k, m)`, `Lc64.ecb_decrypt(~K, ~dec, +k, c)` | ECB on bytes (whole blocks) |
| `Lc64.cbc_encrypt(~K, ~enc, +k, iv, m)`, `Lc64.cbc_decrypt(~K, ~dec, +k, iv, c)` | CBC on bytes, an 8-byte IV (`LcBadIvLength`) |
| `m64.ecb(~K, ~f, +k, bs)`, `m64.cbc.enc(~K, ~enc, +k, bs, iv)`, `m64.cbc.dec(~K, ~dec, +k, bs, iv)` | the modes' structural (reference) forms, which the mode laws are stated over: a cipher's package proves its mode round trips by induction over them |

Everything else (`lc.block_bytes`, `lc.block8`, `lc.block_of`, the
`lc.tab.*` helpers not listed, and `m64.*` not listed) is internal.

## Extension points

* **Any 64-bit cipher in the modes:** `modes64.bend` takes the cipher as
  template arguments (`~K`, `~enc`, `~dec`) and never looks inside the key;
  other 64-bit modes (CFB, OFB, CTR, CBC-MAC) can be added beside ECB and CBC
  the same way. For padding, pkcs7's `Pkcs7.pad(8n, m)` and
  `Pkcs7.unpad(8n, m)` take an 8-byte block size.
* **Any round function:** the Feistel rounds take the round function and the
  round-key type as templates, with laws (`feistel_unrun_run`,
  `feistel_run_unrun`) that hold whatever they are.
* **Open types:** `LcBlock64`, `LcTab` and `LcError` are open, so a cipher
  builds and matches them directly.
* **Streaming:** a message arrives in pieces through the block layer: the last
  ciphertext block of one call is the next call's IV.

## Laws

`LAWS.bend` (16 laws).

**About the block and the modes** (from legacy-ciphers):

* `block64_octets_round_trip`, `blocks64_octets_round_trip`: a block, and a
  list of blocks, read back from its bytes; `block64_octets_dual`: 8 bytes
  read as a block are written back as those bytes (the format both ways, for
  crypto's CBC-CS3 proof);
* `modes64_not_whole_blocks` (a vector): the 64-bit modes refuse a message
  that is not whole blocks.

**Shared by the ciphers' proofs** (new with the split: a package's proofs can
use another package's laws, not its private lemmas). Each is stated simple
side first, the form a rewrite (`%e : P`) takes:

* `word_xor_cancel`, `u32_xor_cancel`, `block64_xor_cancel`: XOR undone, for
  every word of any width, every 32-bit word and every 64-bit block;
* `rotl1_rotl31`, `rotl31_rotl1`, `bswap_bswap`: the rotations by 1 and 31
  bits and the byte swap, on bits, undone for every word;
* `feistel_unrun_run`, `feistel_run_unrun`: Feistel rounds undone, and
  undoing, for every round function, list of round keys and block;
* `modes64_ecb_blocks`, `modes64_cbc_blocks`: ECB and CBC decryption after
  encryption on blocks is the structural forms' (`m64.*`), for every cipher,
  key, IV and list of blocks;
* `modes64_ecb_octets`, `modes64_cbc_octets`: on the bytes of a list of
  blocks under the bytes of an IV, it is the block layer's.

With these a cipher's package proves its mode round trips (des does, for DES
and 3DES) by an induction over the structural forms that uses its own round
trip at each block.

How they are proved: XOR by induction on a word's bits; the rotations, the
byte swap and a block's bytes on a word's 32 symbolic bits (`gen/proof.py`,
each a deep pattern then `{==}`); the Feistel rounds by induction on the
round keys, each round undone by XOR whatever f is; the modes' loops (tail
calls) proved equal to their structural forms; the byte layers with
`block64_octets_round_trip` and `blocks64_octets_round_trip`, which rest on
bytes' laws (`octets_to_of`, `octets_of_to`).

## Tests

* `check.bend` runs the block's hex and byte forms both ways (and a 7-byte
  string refused), XOR, the bit forms of the byte swap and rotations against
  their native forms, a table read and written, eight Feistel rounds over a
  toy round function and back, the byte layer's blocks, and ECB and CBC over a
  toy cipher (XOR with the key block: not a cipher, but enough to show the
  modes chain and undo themselves), with both refusals (a 7-byte IV, a message
  that is not whole blocks).
* No `ref/`: this package holds no cipher. Its modes are compared with an
  independent implementation through the cipher packages' differential
  tests: des's `ref/` runs DES and 3DES in CBC through `modes64.bend` against
  Python's `cryptography`, and every other 64-bit cipher's runs CBC through it
  against `cryptography` (Blowfish, CAST-128) or the package's model.

## Dependencies

`DEPS`: `bytes` (`Octets`, and its laws in the proofs) and `word64` (the bit
slicing that the bit-level helpers are built from).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(2 s, 0.34 GB peak; `--verdict` 6 s, 0.39 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (4 s), `--verdict` ALL PROOFS CHECK (4 s, 0.36 GB peak), `check.bend` passes, `gen/proof.py --check` up to date, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.
