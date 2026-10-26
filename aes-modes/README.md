# bend-osdev-aes-modes

The modes with AES as the cipher: the named defaults. CBC (with and without
PKCS #7 padding), XTS, CCM and CMAC, each taking the raw key as Octets and
picking AES-128 or AES-256 by its length; and the specifications' vectors.

The directory is `aes-modes` and the entry file `aes-modes/aes-modes.bend`
(published as `aes_modes.bend`); the hub name is `bend-osdev-aes-modes`. It
is one of the packages split from bend-osdev-cipher-modes@0.1.0.0, which
they supersede (that version stays on the hub as it was): mode-core, one
package per mode (cbc, xts, ccm, cmac, pkcs7), aes and aes-modes.

**Why a package of its own.** It is the only code that needs both AES and
the modes. In aes, every user of AES as a cipher (crypto, cm-instances,
aead) would depend on the five mode packages; in a mode package, every mode
would depend on AES and so on bend-collections, which the modes avoid so
that a program bringing its own cipher does not pull it in. Here each
dependency is used.

## Specifications

The specifications' vectors, run over AES:

* **CBC:** NIST SP 800-38A (2001), Appendix F.2.
* **XTS:** IEEE Std 1619-2007, Annex B.
* **CCM:** RFC 3610, section 8.
* **CMAC:** RFC 4493, section 4.

The modes and AES are cited by their own packages.

## Files

| File | Holds |
|---|---|
| `aes-modes.bend` | the named defaults: every mode with AES, taking the raw key |
| `LAWS.bend`, `PROOF.bend` | the vectors that fit as laws, and their proofs |
| `check.bend` | the specifications' other vectors, and 32 KB through CBC, XTS and CCM, with expected output |

## Public interface

**`aes-modes.bend`**: `CmAes.cbc_encrypt`, `CmAes.cbc_decrypt`,
`CmAes.cbc_encrypt_padded`, `CmAes.cbc_decrypt_padded`, `CmAes.xts_encrypt`,
`CmAes.xts_decrypt` (a 32- or 64-byte key: Key1 then Key2),
`CmAes.ccm_encrypt`, `CmAes.ccm_decrypt`, `CmAes.cmac`. Each takes the raw
key as Octets, picks AES-128 or AES-256 by its length (`CmBadKeyLength`
otherwise) and answers `Result<&2, &2, CmError, Octets>`.

To expand a key once and use it many times, call aes' `CmAes.key` and the
mode with `~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt`.

## Extension points

* **Another default cipher:** a program that wants another cipher calls the
  modes with its template arguments; this package is the only one that
  names AES as the modes' default, and can be replaced as a whole.

## Laws

`LAWS.bend` (8 laws), vectors proved by computation: `aes_bad_key_length`
(a 15-byte key refused), `cbc_sp800_38a_f21_block1` (SP 800-38A F.2.1's
first block), `cbc_not_whole_blocks` and `cbc_short_iv` (the byte layer's
refusals), `xts_short` (a data unit shorter than a block refused),
`ccm_bad_tag_length` and `ccm_bad_nonce_length`, and `cmac_rfc4493_k1`
(RFC 4493's subkey K1).

The laws for every input are the modes' (cbc, xts, ccm, cmac) and AES's
(aes); bend-osdev-cm-instances states the CBC and XTS round trips at AES
with no hypothesis. The checker evaluates AES slowly and keeps what it
evaluates, so more vectors run past its memory; the others run in
`check.bend`.

## Tests

`check.bend` runs every other vector of the four specifications (24 of
them): SP 800-38A F.2.1, F.2.2, F.2.5 and F.2.6, and F.2.1 padded; IEEE 1619
vectors 1, 2 and 15 to 18, with decryption; RFC 3610 packets 1 to 3, with
decryption and a tampered tag refused; RFC 4493 examples 1 to 4 and K2; and
CBC and CCM over 32 KB and XTS over 32 KB and 5 bytes, both ways, as a
regression test (the last 16 bytes of each ciphertext were checked against
Python's `cryptography`). FIPS 197's vectors are aes' `check.bend`.

The differential tests against Python's `cryptography` are the mode
packages' `ref/` (cbc, xts, ccm, cmac), which run through these defs (264
cases in all with aes' 28).

## Sizes

Every loop over a message's bytes or blocks is a tail call, so a message has
no length limit beyond memory, on both of Bend 2.0.37's lanes. Measured in
cipher-modes (the code is unchanged), on a native build (`bend file.bend -o
prog`, WSL2) with AES-128 (for XTS, a 256-bit key: two AES-128 keys), over
pseudo-random messages, each run including building the message, every
ciphertext checked against Python's `cryptography`:

| Run | Time, native | Peak RAM, native |
|---|---|---|
| CBC encryption, 1 MB | 3.4 s | 104 MB |
| CBC encryption and decryption back, 512 KB | 3.8 s | 102 MB |
| XTS encryption, 1 MB | 3.5 s | 106 MB |
| XTS encryption and decryption back, 512 KB | 3.8 s | 103 MB |
| CMAC, 1 MB | 2.6 s | 101 MB |
| CCM encryption, 1 MB (12-byte nonce) | 5.8 s | 121 MB |
| CCM encryption and decryption back, 512 KB | 5.9 s | 111 MB |

AES dominates the time (natively about 300 KB/s per pass of AES). Most of
the memory is the message as `Octets` (about 80 bytes per byte natively) and
the lists and blocks the modes work on.

## Notes on use

* CBC decryption with padding tells the caller whether the padding was good:
  exposed to an attacker, that is a padding oracle. Prefer CCM (or CBC with a
  MAC checked first) for data an attacker can change.
* SP 800-38E requires XTS's two keys to differ; this package does not check
  it (IEEE 1619's vector 1 uses equal keys).
* A CCM nonce must never repeat under one key; a CBC IV must be
  unpredictable.
* Tag comparisons look at every byte (no early exit). That is a property of
  the code as written, not a timing guarantee: Bend's runtime promises
  nothing about running time.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(6 s, 0.67 GB peak; `--verdict` 17 s, 0.73 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (5 s, 0.65 GB peak), `--verdict` ALL PROOFS CHECK (16 s, 0.75 GB peak; the vectors evaluate AES, and import no package's proofs), `check.bend` passes, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`), `mode-core` (the block and the error type),
`aes` (the cipher), and the modes `cbc`, `xts`, `ccm` and `cmac`.
