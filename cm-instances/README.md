# bend-osdev-cm-instances

The CBC and XTS modes (bend-osdev-cbc and bend-osdev-xts) over each 128-bit
block cipher of bend-osdev, with their round-trip laws written out and proved per cipher: CBC on
blocks and on bytes, and XTS on blocks and on bytes (ciphertext stealing
included), over SM4, Camellia, Serpent, Twofish, ARIA and CAST-256 (the
sm4, camellia, serpent, twofish, aria and cast6 packages) and AES
(the aes package, the modes' named default), each for every key and input with no hypothesis.

The directory is `cm-instances` and the entry file
`cm-instances/cm-instances.bend`; the hub name is `bend-osdev-cm-instances`.

## Specifications

None of its own: the modes' are cbc's and xts' (NIST SP 800-38A, IEEE Std
1619-2007) and the ciphers' are their packages' (their READMEs cite them).
No GPL source was read.

## Files

| File | Holds |
|---|---|
| `cm-instances.bend` | the entry file: the ciphers' template arguments for the modes, as a comment (the package adds no code to either package) |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs (written by `gen/instances.py`) |
| `check.bend` | every cipher through the four round trips at run time, with expected output (written by `gen/instances.py`) |
| `gen/instances.py` | the table of ciphers: writes `LAWS.bend`, `PROOF.bend` and `check.bend` (`--check` checks they are up to date) |

## Public interface

No defs or types: the package's content is its laws, which are about
the modes' public defs (cbc's `Cbc.encrypt_blocks`, `Cbc.decrypt_blocks`,
`Cbc.encrypt`, `Cbc.decrypt`; xts' `Xts.encrypt_blocks`, `Xts.decrypt_blocks`,
`Xts.encrypt`, `Xts.decrypt`; mode-core's `CmBlock.dec_enc`) at each cipher's public
defs (`LcSm4Key`, `LcSm4.encrypt`, `LcSm4.decrypt`, and the same for
`LcCamellia`, `LcSerpent`, `LcTwofish`, `LcAria`, `LcCast6`; and
aes' `CmAesKey`, `CmAes.encrypt`, `CmAes.decrypt`). A proof
elsewhere uses a law here by importing `LAWS.bend` and `PROOF.bend`.

## Laws

`LAWS.bend` has 35 laws, five per cipher c in sm4, camellia, serpent,
twofish, aria, cast6 and aes, all proved, all accepted by `--verdict`:

* `c_dec_enc`: for every key and list of blocks,
  `CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs`: the cipher meets
  the modes' round-trip hypothesis at every key. By induction on the
  list, with the cipher's own law (`c_round_trip` in the cipher's package, and
  `aes_round_trip` in aes: `dec(k, enc(k, b)) == b` for every key
  and block) at every block.
* `c_cbc_blocks_round_trip`, `c_cbc_round_trip`, `c_xts_blocks_round_trip`,
  `c_xts_round_trip`: cbc's and xts' four laws at the cipher's template
  arguments, with nothing assumed (CBC on bytes for every 16-byte IV and
  message of whole blocks, XTS on bytes for every 16-byte sequence number
  and data unit of at least 16 bytes, as cbc and xts state them). Each is
  that law with `c_dec_enc` as its hypothesis `inv`.

**Why per cipher.** cbc and xts state the four laws once, for every
cipher and key that satisfy the hypothesis. Its hypothesis is an ordinary
one, used once, because `--verdict` cannot model a template hypothesis
whose type is a proposition, and an ordinary hypothesis is affine (a
function is not `Data`), so it cannot be used at every step of an
induction; a cipher's own law can, as a global name. So the induction that
turns the cipher's law into the hypothesis is written out per cipher, as
crypto's `gen/instances.py` does for its interfaces.

**Why a package of its own.** The proofs take in the modes' proofs and
the ciphers' own. cbc and xts cannot hold them (the cipher packages depend
on them, for their tests, and on mode-core, for `CmBlock`); each cipher package could hold its own, but its
`--verdict` would grow from seconds and about 0.5 GB to minutes and well
over 1 GB (nearly all of it the modes' proofs), for every user of the
cipher alone, and AES's would have no cipher package to go in. Here they
are one component, the instances of one package's laws over the others'
ciphers, which a user takes or leaves.

**Not here.** The 64-bit ciphers: the 128-bit modes are 128-bit;
cipher-core's `modes64.bend` has their ECB and CBC, with laws in the cipher
packages (des: DES's and 3DES's mode round trips). CCM and CMAC need no
hypothesis (the modes' laws hold for every cipher already).

## Extension points

* **A new 128-bit cipher** whose package proves `dec(k, enc(k, b)) == b`
  for every key and block: a row in `gen/instances.py`'s `CIPHERS` (its
  import, key type, encryption, decryption, that law's name, and a key it
  accepts), then `python3 gen/instances.py`.
* **A new mode law** in cbc or xts with the same hypothesis: a statement
  and a one-line proof in `laws_of` and `proofs_of`.

## Tests

`check.bend` runs each cipher through the four round trips once, under a
16-byte key (and, for XTS, a second one): a list of four blocks (CBC and XTS
on blocks), 64 bytes (CBC and XTS on bytes) and 61 bytes (XTS with
ciphertext stealing), each decrypted back and compared. Its expected lines
are "ok". The ciphers' values are tested in their packages (the
specifications' vectors, and CBC against Python's `cryptography` and the
`openssl` command) and in aes (FIPS 197's vectors and `cryptography`), and
the modes' in cbc and xts (and over AES in aes-modes: the specifications'
vectors; and a differential test against `cryptography`); there is nothing
here beyond those for a differential test to compare, so there is no
`ref/`.

## Dependencies

`DEPS`: `bytes` (Octets), `mode-core` (`CmBlock`), `cbc` and `xts` (the
modes, and their laws and proofs), `aes` (AES, and its round-trip law and
proof), `cipher-core` (the ciphers' error type `LcError`, which
`check.bend` names), and `sm4`, `camellia`, `serpent`, `twofish`, `aria` and
`cast6` (the ciphers, their round-trip laws and proofs).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(3.9 minutes, 1.53 GB peak; `--verdict` 8.0 minutes, 1.51 GB peak) ALL
PROOFS CHECK, with and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (3.5 minutes, 1.43 GB peak),
`--verdict` ALL PROOFS CHECK (7.4 minutes, 1.41 GB peak, nearly all of it
aes' proofs, which include bend-osdev-gf's, with cbc's, xts' and
mode-core's; measured after the split of cipher-modes into mode-core, aes
and one package per mode), `check.bend` passes, `gen/instances.py --check`
up to date, `scripts/deps.sh` passes.
