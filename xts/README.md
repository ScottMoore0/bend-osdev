# bend-osdev-xts

XTS, the tweakable mode for storage, over any 128-bit block cipher: the
block layer, the byte layer with ciphertext stealing, and sector numbers,
with decryption proved to undo encryption for every cipher and data key that
satisfy the round-trip hypothesis, every tweak key, sequence number and data
unit of at least 16 bytes.

The directory is `xts` and the entry file `xts/xts.bend`; the hub name is
`bend-osdev-xts`. It is one of the packages split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was): mode-core, one package per mode (cbc, xts, ccm, cmac,
pkcs7), aes and aes-modes.

## Specifications

Written from the public specifications only:

* **XTS:** IEEE Std 1619-2007, *Cryptographic Protection of Data on
  Block-Oriented Storage Devices* (XTS-AES), sections 5.1 to 5.4 (its
  Annex B vectors run over AES in aes-modes); NIST SP 800-38E.

## Files

| File | Holds |
|---|---|
| `xts.bend` | multiplication by alpha, the block layer, the byte layer with ciphertext stealing, sector numbers |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | XTS over a toy permutation, with expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test, over AES, against Python's `cryptography` |

## Public interface

The cipher is the template arguments `~K`, `~enc`, `~dec` (mode-core's
README); `k1` is the data key and `k2` the tweak key.

| Def | Meaning |
|---|---|
| `Xts.mul_alpha(t)` | multiplication by alpha in GF(2^128) (IEEE 1619, 5.2) |
| `Xts.tweak(~K, ~enc, +k2, i)` | T_0 = E(k2, i) |
| `Xts.encrypt_blocks(~K, ~enc, +k1, t, bs)`, `Xts.decrypt_blocks(~K, ~dec, +k1, t, bs)` | the block layer, from tweak t |
| `Xts.encrypt(~K, ~enc, +k1, +k2, i, p)`, `Xts.decrypt(~K, ~enc, ~dec, +k1, +k2, i, c)` | a data unit of at least 16 bytes (`CmTooShort`), any length (ciphertext stealing), 16-byte sequence number `i` (`CmBadTweakLength`); answer `Result<&2, &2, CmError, Octets>` |
| `Xts.encrypt.ref`, `Xts.decrypt.ref` | the structural forms the laws' proofs reason about, equal to the defs above for every input |
| `Xts.sector(n: W64) -> Octets` | the sequence number of sector `n` (little-endian, zero-filled) |

Everything else (`xts.*`) is internal. With AES: aes-modes'
`CmAes.xts_encrypt` and `CmAes.xts_decrypt` take a 32- or 64-byte key (Key1
then Key2).

## Extension points

* **Any 128-bit block cipher** as the template arguments.
* **The sequence number** is a parameter: `Xts.sector` for disk sectors, or
  any 16 bytes.
* **Data units are independent**, one call each; there is no streaming
  within a unit.

## Laws

`LAWS.bend` (3 laws). The round trips take the hypothesis `inv` at the data
key `k1`, as cbc's laws do (cbc's README): for every list of blocks xs,
`CmBlock.dec_enc(~K, ~enc, ~dec, k1, xs) == xs`, used once in each proof
(on the blocks XOR their tweaks, and ciphertext stealing's two).

* `xts_blocks_round_trip`: XTS on blocks, for every data key and starting
  tweak (T_0 = `Xts.tweak(k2, i)`, so every k2 and i are covered);
* `xts_round_trip`: XTS on bytes, ciphertext stealing included, for every
  pair of keys, every 16-byte sequence number and every data unit of at
  least 16 bytes;
* `xts_sector` (a vector): the sequence number of sector 0x9a785432.

bend-osdev-cm-instances states the two round trips with no hypothesis for
AES and each 128-bit cipher package. The vector with AES (a data unit
shorter than a block refused) is aes-modes' law `xts_short`.

The laws are proved of the code that runs (the tail-call loops equal to
`xts.enc`, `xts.dec`, `Xts.encrypt.ref`, ...); the byte layer's lemmas are
mode-core's laws, used under their old names; bytes' interface laws hold
the byte layer, and nothing looks inside `Octets`.

## Tests

* `check.bend`: XTS over a toy permutation (not a cipher): multiplication
  by alpha, the tweak, the block layer, whole blocks and ciphertext stealing
  both ways, the sector number, the refusals (a short data unit, a short
  sequence number), and 32 KB and 5 bytes both ways. Its outputs are
  recorded as a regression test; XTS itself is tested against the
  specification over AES (below).
* `ref/run.sh`: XTS over AES-128 and AES-256, both ways, every tail length
  0 to 15 after one block and after several, and 512-byte sectors, against
  Python's `cryptography` (72 cases with the default seed; through
  aes-modes' named defaults, imported from `ref/` only).
* aes-modes' `check.bend`: IEEE 1619 vectors 1, 2 and 15 to 18, with
  decryption.

## Notes on use

* SP 800-38E requires XTS's two keys to differ; this package does not check
  it (IEEE 1619's vector 1 uses equal keys).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s, 0.42 GB peak), `--verdict` ALL PROOFS CHECK (7 s, 0.41 GB peak, with mode-core's proofs), `check.bend` passes, `ref/run.sh` 72 cases match, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`), `word64` (`W64` sector numbers) and
`mode-core` (the block, the error type, the byte layer, and its laws in the
proofs).
