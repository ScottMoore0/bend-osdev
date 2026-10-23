# bend-osdev-cm-instances

cipher-modes' modes over each 128-bit block cipher of bend-osdev, with
cipher-modes' round-trip laws written out and proved per cipher: CBC on
blocks and on bytes, and XTS on blocks and on bytes (ciphertext stealing
included), over SM4, Camellia, Serpent, Twofish, ARIA and CAST-256 (the
legacy-ciphers package) and AES (cipher-modes' own), each for every key and
input with no hypothesis.

The directory is `cm-instances` and the entry file
`cm-instances/cm-instances.bend`; the hub name is `bend-osdev-cm-instances`.

## Specifications

None of its own: the modes' are cipher-modes' (NIST SP 800-38A, IEEE Std
1619-2007) and the ciphers' are legacy-ciphers' and cipher-modes' (their
READMEs cite them).
No GPL source was read.

## Files

| File | Holds |
|---|---|
| `cm-instances.bend` | the entry file: the ciphers' template arguments for cipher-modes, as a comment (the package adds no code to either package) |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs (written by `gen/instances.py`) |
| `check.bend` | every cipher through the four round trips at run time, with expected output (written by `gen/instances.py`) |
| `gen/instances.py` | the table of ciphers: writes `LAWS.bend`, `PROOF.bend` and `check.bend` (`--check` checks they are up to date) |

## Public interface

No defs or types: the package's content is its laws, which are about
cipher-modes' public defs (`Cbc.encrypt_blocks`, `Cbc.decrypt_blocks`,
`Cbc.encrypt`, `Cbc.decrypt`, `Xts.encrypt_blocks`, `Xts.decrypt_blocks`,
`Xts.encrypt`, `Xts.decrypt`, `CmBlock.dec_enc`) at each cipher's public
defs (`LcSm4Key`, `LcSm4.encrypt`, `LcSm4.decrypt`, and the same for
`LcCamellia`, `LcSerpent`, `LcTwofish`, `LcAria`, `LcCast6`; and
cipher-modes' `CmAesKey`, `CmAes.encrypt`, `CmAes.decrypt`). A proof
elsewhere uses a law here by importing `LAWS.bend` and `PROOF.bend`.

## Laws

`LAWS.bend` has 35 laws, five per cipher c in sm4, camellia, serpent,
twofish, aria, cast6 and aes, all proved, all accepted by `--verdict`:

* `c_dec_enc`: for every key and list of blocks,
  `CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs`: the cipher meets
  cipher-modes' round-trip hypothesis at every key. By induction on the
  list, with the cipher's own law (`c_round_trip` in legacy-ciphers, and
  `aes_round_trip` in cipher-modes: `dec(k, enc(k, b)) == b` for every key
  and block) at every block.
* `c_cbc_blocks_round_trip`, `c_cbc_round_trip`, `c_xts_blocks_round_trip`,
  `c_xts_round_trip`: cipher-modes' four laws at the cipher's template
  arguments, with nothing assumed (CBC on bytes for every 16-byte IV and
  message of whole blocks, XTS on bytes for every 16-byte sequence number
  and data unit of at least 16 bytes, as cipher-modes states them). Each is
  cipher-modes' law with `c_dec_enc` as its hypothesis `inv`.

**Why per cipher.** cipher-modes states the four laws once, for every
cipher and key that satisfy the hypothesis. Its hypothesis is an ordinary
one, used once, because `--verdict` cannot model a template hypothesis
whose type is a proposition, and an ordinary hypothesis is affine (a
function is not `Data`), so it cannot be used at every step of an
induction; a cipher's own law can, as a global name. So the induction that
turns the cipher's law into the hypothesis is written out per cipher, as
crypto's `gen/instances.py` does for its interfaces.

**Why a package of its own.** The proofs take in cipher-modes' and
legacy-ciphers' proofs. cipher-modes cannot hold them (legacy-ciphers
depends on it, for `CmBlock`); legacy-ciphers could, but its `--verdict`
would grow from about 40 s and 0.7 GB to about 6 minutes and 1.9 GB, for
every user of its ciphers alone, and it would hold laws about cipher-modes'
AES. Here they are one component, the instances of one package's laws over
the others' ciphers, which a user takes or leaves.

**Not here.** The 64-bit ciphers: cipher-modes' modes are 128-bit; legacy-ciphers'
`modes64.bend` has their ECB and CBC, with laws there. CCM and CMAC need no
hypothesis (cipher-modes' laws hold for every cipher already).

## Extension points

* **A new 128-bit cipher** whose package proves `dec(k, enc(k, b)) == b`
  for every key and block: a row in `gen/instances.py`'s `CIPHERS` (its
  import, key type, encryption, decryption, that law's name, and a key it
  accepts), then `python3 gen/instances.py`.
* **A new mode law** in cipher-modes with the same hypothesis: a statement
  and a one-line proof in `laws_of` and `proofs_of`.

## Tests

`check.bend` runs each cipher through the four round trips once, under a
16-byte key (and, for XTS, a second one): a list of four blocks (CBC and XTS
on blocks), 64 bytes (CBC and XTS on bytes) and 61 bytes (XTS with
ciphertext stealing), each decrypted back and compared. Its expected lines
are "ok". The ciphers' values are tested in legacy-ciphers (the
specifications' vectors, and CBC against Python's `cryptography` and the
`openssl` command) and in cipher-modes (AES: FIPS 197's vectors and
`cryptography`), and the modes' in cipher-modes (the specifications'
vectors, and a differential test against `cryptography`); there is nothing
here beyond those for a differential test to compare, so there is no
`ref/`.

## Dependencies

`DEPS`: `bytes` (Octets), `cipher-modes` (the modes, `CmBlock`, AES, and its
laws and proofs), `legacy-ciphers` (the ciphers, their round-trip laws and
proofs).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK
(about 6 minutes, 1.9 GB peak, nearly all of it cipher-modes' proofs, which
include bend-osdev-gf's), `check.bend` passes, `gen/instances.py --check` up
to date, `scripts/deps.sh` passes.
