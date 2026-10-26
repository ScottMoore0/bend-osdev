# bend-osdev-ccm

CCM, counter with CBC-MAC: authenticated encryption over any 128-bit block
cipher (only its encryption is used), with decryption proved to accept what
encryption produced and give the message back, for every cipher, key, tag
length, nonce, associated data and message.

The directory is `ccm` and the entry file `ccm/ccm.bend`; the hub name is
`bend-osdev-ccm`. It is one of the packages split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was): mode-core, one package per mode (cbc, xts, ccm, cmac,
pkcs7), aes and aes-modes.

## Specifications

Written from the public specifications only:

* **CCM:** NIST SP 800-38C (2004) and RFC 3610, *Counter with CBC-MAC
  (CCM)* (2003) (its packet vectors, section 8, run over AES in aes-modes).

## Files

| File | Holds |
|---|---|
| `ccm.bend` | CCM encryption and decryption |
| `LAWS.bend`, `PROOF.bend` | the law, and its proof |
| `check.bend` | CCM over a toy permutation, with expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test, over AES, against Python's `cryptography` |

## Public interface

The cipher is the template arguments `~K`, `~enc` (mode-core's README).

| Def | Meaning |
|---|---|
| `Ccm.encrypt(~K, ~enc, +k, m, nonce, aad, p)` | the ciphertext followed by the `m`-byte tag |
| `Ccm.decrypt(~K, ~enc, +k, m, nonce, aad, c)` | the plaintext, or `CmTagMismatch` (the tag is compared with no early exit, and no plaintext is released from a message that fails) |
| `Ccm.encrypt.ref`, `Ccm.decrypt.ref` | the structural forms the law's proof reasons about, equal to the defs above for every input |

Both answer `Result<&2, &2, CmError, Octets>`. `m` is 4, 6, ..., 16
(`CmBadTagLength`); the nonce is 7 to 13 bytes, L = 15 - N
(`CmBadNonceLength`); the message must be shorter than 2^(8L) bytes
(`CmTooLong`). Everything else (`ccm.*`) is internal. With AES:
aes-modes' `CmAes.ccm_encrypt` and `CmAes.ccm_decrypt`.

## Extension points

* **Any 128-bit block cipher** as the template arguments (encryption only).
* **Parameters, not fixed choices:** the tag length and the nonce length.
* **No streaming:** B_0 holds the message length, so a message cannot start
  before its length is known (RFC 3610 is not an online mode).

## Laws

`LAWS.bend` (1 law): `ccm_round_trip`: for every cipher (no hypothesis:
CCM only encrypts), key, tag length, nonce, associated data and message,
decrypting what encryption produced gives the message back, and when the
parameters are refused both refuse alike. crypto's CCM AEAD (its
`LAWS_cm.bend`, `ccm_aead_round_trip`) rests on it.

It is proved of the code that runs (the tail-call loops equal to
`ccm.ctrb`, `Ccm.encrypt.ref`, ...); the byte layer's lemmas are
mode-core's laws, used under their old names. The vectors with AES (a tag
of odd length and a 6-byte nonce refused) are aes-modes' laws.

## Tests

* `check.bend`: CCM over a toy permutation (not a cipher): encryption,
  decryption, a tampered tag refused, an empty message, the refused tag and
  nonce lengths, and 32 KB both ways; the outputs are recorded as a
  regression test.
* `ref/run.sh`: CCM over AES-128 and AES-256, encryption, decryption and a
  tampered tag refused, over every tag length and every nonce length,
  against Python's `cryptography` (60 cases with the default seed; through
  aes-modes' named defaults, imported from `ref/` only).
* aes-modes' `check.bend`: RFC 3610 packets 1 to 3, with decryption and a
  tampered tag.

## Notes on use

* A CCM nonce must never repeat under one key.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(2 s, 0.39 GB peak; `--verdict` 5 s, 0.60 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s, 0.36 GB peak), `--verdict` ALL PROOFS CHECK (4 s, 0.43 GB peak, with mode-core's proofs), `check.bend` passes, `ref/run.sh` 60 cases match, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`), `mode-core` (the block, the error type, the
byte layer, and its laws in the proofs); `word64` and `u32` in the proofs
only (the bits of a word, and u32's laws of `Nat` arithmetic).
