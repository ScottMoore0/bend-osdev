# bend-osdev-cbc

CBC, cipher block chaining, over any 128-bit block cipher: on blocks, on
bytes (a whole number of blocks), and on bytes of any length with PKCS #7
padding, with decryption proved to undo encryption for every cipher and key
that satisfy the round-trip hypothesis, every IV and every message.

The directory is `cbc` and the entry file `cbc/cbc.bend`; the hub name is
`bend-osdev-cbc`. It is one of the packages split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was): mode-core (the block, the error type and the byte layer
the modes share), one package per mode (cbc, xts, ccm, cmac, pkcs7), aes
and aes-modes.

## Specifications

Written from the public specifications only:

* **CBC:** NIST SP 800-38A, *Recommendation for Block Cipher Modes of
  Operation* (2001), section 6.2 (its Appendix F.2 vectors run over AES in
  aes-modes).
* **PKCS #7 padding:** RFC 5652, section 6.3 (bend-osdev-pkcs7).

## Files

| File | Holds |
|---|---|
| `cbc.bend` | CBC on blocks and on bytes, with and without padding |
| `LAWS.bend`, `PROOF.bend` | the round trips on blocks and on bytes, and their proofs |
| `LAWS_padded.bend`, `PROOF_padded.bend` | padded CBC's round trip, and its proof (from the pair above and pkcs7's laws) |
| `check.bend` | CBC over a toy permutation, with expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test, over AES, against Python's `cryptography` |

## Public interface

The cipher is the template arguments `~K`, `~enc`, `~dec` and the key `+k`
(mode-core's README). All fallible functions answer
`Result<&2, &2, CmError, Octets>`.

| Def | Meaning |
|---|---|
| `Cbc.encrypt_blocks(~K, ~enc, +k, iv, bs)`, `Cbc.decrypt_blocks(~K, ~dec, +k, iv, bs)` | the block layer: lists of `CmBlock` under a `CmBlock` IV |
| `Cbc.encrypt(~K, ~enc, +k, iv, m)`, `Cbc.decrypt(~K, ~dec, +k, iv, c)` | bytes: a 16-byte IV (`CmBadIvLength`), a whole number of blocks (`CmNotBlockMultiple`) |
| `Cbc.encrypt_padded(...)`, `Cbc.decrypt_padded(...)` | any length, PKCS #7 padded (`CmTooShort`, `CmBadPadding`, ...) |
| `Cbc.encrypt.ref`, `Cbc.decrypt.ref` | the structural forms the laws' proofs reason about, equal to the defs above for every input |

Everything else (`cbc.*`) is internal. With AES as the cipher:
`~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt` (bend-osdev-aes), or
aes-modes' `CmAes.cbc_encrypt` and the rest, which take the raw key.

## Extension points

* **Any 128-bit block cipher** as the template arguments; nothing here
  changes.
* **Streaming:** the block layer is the streaming interface: the last
  ciphertext block of one call is the IV of the next.
* **Padding:** pkcs7's `Pkcs7.pad` and `Pkcs7.unpad` with block size 16; a
  caller who pads otherwise uses `Cbc.encrypt` on whole blocks.

## Laws

Two pairs of law and proof files, each checked in a process of its own
(CONVENTIONS.md, Laws).

`LAWS.bend` (2 laws). They take the hypothesis `inv: @xs ->
{CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs}` at the key: for every list
of blocks, each block encrypted and decrypted back is itself, so they hold
for every cipher and key that satisfy it (bend-osdev-cm-instances proves
`inv` for AES and each 128-bit cipher package, and states these laws there
with no hypothesis). It is an ordinary hypothesis, used once, so
`--verdict` models it.

* `cbc_blocks_round_trip`: CBC on blocks, for every key, IV and list of
  blocks;
* `cbc_round_trip`: CBC on bytes, for every key, every 16-byte IV and every
  message of whole blocks: encryption succeeds and decryption gives the
  message back.

`LAWS_padded.bend` (1 law): `cbc_padded_round_trip`: for every cipher and
key with `inv`, every 16-byte IV and every message of any length,
`Cbc.encrypt_padded` succeeds and `Cbc.decrypt_padded` gives the message
back: from `cbc_round_trip` on the padded message (whole blocks, by pkcs7's
`pkcs7_pad_blocks`) and pkcs7's `pkcs7_round_trip`; decryption's first
check, that the ciphertext is not empty, holds because an empty one would
decrypt to the empty string, which unpadding refuses. It is here because
padded CBC is cbc's (`cbc.bend` uses pkcs7), and in a pair of its own so
that a proof using only the two laws above takes in none of pkcs7's proofs.

The laws are proved of the code that runs: the tail-call loops are proved
equal to their structural forms (`cbc.enc`, `cbc.dec`,
`Cbc.encrypt.ref`, ...) for every input. The byte layer's lemmas are
mode-core's laws (`join_split`, `split_fast`, ...); `PROOF_padded.bend`
has private copies of three small defs of pkcs7's proofs (False is not
True, and `unpad` with its checks as arguments), since a package's proofs
use another's laws only.

The vectors with AES (SP 800-38A F.2.1's first block, a 15-byte key, a
message that is not whole blocks, a short IV) are aes-modes' laws.

## Tests

* `check.bend`: CBC over a toy permutation (not a cipher: the words rotated,
  XOR the key): the block layer both ways, bytes both ways, padding (also
  of the empty message), and the refusals (not whole blocks, a short IV, an
  empty padded ciphertext, bad padding), and 32 KB both ways. Its
  encryptions were checked against a Python model of the toy permutation in
  CBC.
* `ref/run.sh`: CBC over AES, both ways, with and without padding, against
  Python's `cryptography` (64 cases with the default seed; through
  aes-modes' named defaults, which the test imports from `ref/` only).
* aes-modes' `check.bend`: SP 800-38A F.2.1, F.2.2, F.2.5 and F.2.6.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(2 s, 0.34 GB peak; `--verdict` 5 s, 0.62 GB peak) and `PROOF_padded.bend`
(2 s, 0.37 GB peak; `--verdict` 6 s, 0.64 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s, 0.34 GB peak), `--verdict` ALL PROOFS CHECK (4 s, 0.41 GB peak, with mode-core's proofs); `PROOF_padded.bend` ALL PROOFS CHECK (2 s, 0.37 GB) and under `--verdict` (5 s, 0.43 GB peak, with `PROOF.bend`'s and pkcs7's proofs), each in a process of its own; `check.bend` passes, `ref/run.sh` 64 cases match, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`), `mode-core` (the block, the error type, the
byte layer, and its laws in the proofs) and `pkcs7` (the padding, and its
laws in `PROOF_padded.bend`).
