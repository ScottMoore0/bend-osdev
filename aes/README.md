# bend-osdev-aes

AES-128, AES-192 and AES-256 as a 128-bit block cipher for the modes
(cbc, xts, ccm, cmac and any other on mode-core's `CmBlock`), with its
decryption proved to undo its encryption for every key and block.
Encryption is bend-collections'; the inverse cipher is written here.

The directory is `aes` and the entry file `aes/aes.bend`; the hub name is
`bend-osdev-aes`. It is one of the packages split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was): mode-core, one package per mode (cbc, xts, ccm, cmac,
pkcs7), aes (a cipher, not a mode) and aes-modes (the modes with AES).

## Specifications

* **AES:** FIPS 197 (November 2001), with the example vectors of its
  Appendix C (C.1, C.2, C.3). Encryption is bend-collections'; the inverse
  cipher (section 5.3) is written here, over bend-collections' round keys.
  The proof of the round trip uses bend-osdev-gf's laws of section 4.2's
  field.

## Files

| File | Holds |
|---|---|
| `aes.bend` | AES as a block cipher: the key, encryption (bend-collections), decryption (here) |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `gen/aes_proof.py` | writes the AES round-trip proof (the "aes" region of `PROOF.bend`; `--check` checks it is current) |
| `check.bend` | FIPS 197 C.1 to C.3, with expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's `cryptography` |

A mode never imports `aes.bend`: a program that brings its own cipher does
not depend on bend-collections.

## Public interface

**`aes.bend`**: `CmAesKey` (opaque), `CmAes.key(o)` (16 or 32 bytes;
`CmBadKeyLength` otherwise), `CmAes.key128(o)`, `CmAes.key192(o)` (24
bytes), `CmAes.key256(o)`, `CmAes.encrypt(k, b)`, `CmAes.decrypt(k, b)`, and
`CmAes.prepare(k)`, which answers the key as it is: decryption uses the
key's schedule directly, so there is nothing left to compute ahead (it
computed decryption round keys in earlier versions of bend-osdev-cipher-modes, and is
kept so that their callers build). Use as
`~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt`. Everything else
(`aes.*`) is internal.

## AES and bend-collections

bend-collections@1.0.0.0 (`src/crypto/aes/aes.bend`, MIT) has AES
encryption only: `expand_key` and `encrypt_block`, over its `Schedule` (the
number of rounds and the round keys) and its state type (`types.bend`). It
has **no decryption**. CBC and XTS need it, so `aes.bend` here adds FIPS
197's inverse cipher: it undoes bend-collections' `cipher` round by round,
with the same schedule's round keys, the last first (AddRoundKey,
InvMixColumns, InvShiftRows, InvSubBytes). A key's schedule is
bend-collections' `expand_key` of its bytes, for AES-128, AES-192 and
AES-256 alike. The inverse S-box is computed rather than looked up (the
inverse affine map, then x^254 in GF(2^8) with masks instead of branches), so
no branch or table index depends on key or data bytes; InvMixColumns'
products by {09}, {0b}, {0d} and {0e} are sums of doublings, likewise
branch-free (the proof checks each against bend-osdev-gf's product in AES's
field, on all 256 bytes). Both directions use the round keys with each byte
masked to its low 8 bits (`aes.sched`), which changes nothing for a key made
by `CmAes.key` and makes the round trip hold for every value of `CmAesKey`.

## Extension points

* **Replaceable:** a table-driven or hardware AES can take this one's place
  as the modes' template arguments; aes-modes is the only package that
  names it as a default.
* **Faster paths** (bit-sliced AES) can go behind the same defs, tied to
  these by the differential test.

## Laws

`LAWS.bend` (2 laws).

**`aes_round_trip`**: `CmAes.decrypt(k, CmAes.encrypt(k, b)) == b` for
every key (every value of `CmAesKey`: any number of rounds and any round
keys, AES-128, AES-192 and AES-256 among them) and every block. So the
modes' laws hold for AES with no hypothesis: bend-osdev-cm-instances states
them (`aes_cbc_round_trip`, `aes_xts_round_trip`, ...), and crypto's AES
rows use it (`aes_block_round_trip`, ECB, CBC, PCBC and LRW over AES).

**`aes128_fips197_c1`** (a vector): FIPS 197 C.1, AES-128 encryption of one
block.

bend-collections-laws-crypto@1.0.0.0 (an allowed hub package, the proved
laws of bend-collections) proves bend-collections' AES encryption equal to
an executable FIPS 197 specification and the S-box circuit equal to the
specification's S-box, but it has no decryption and no inverse law, and its
AES proofs do not pass `--verdict` (the S-box proof runs out of the
kernel's fuel). So the proof (`gen/aes_proof.py`, the "aes" region of
`PROOF.bend`) reads bend-collections' encryption as written (its `cipher`,
`rounds`, `round`, `last_round`, `sub_bytes`, `shift_rows`, `mix_columns`,
`add_round_key`, and `sbox.bend`'s `sbox`, `xtime`, `mul3`), as the
definition of the cipher it inverts:

* each byte fact is checked on all 256 bytes: the inverse S-box undoes the
  S-box, and the S-box, xtime and mul3 give bytes;
* InvMixColumns undoes MixColumns on every column of bytes, through
  bend-osdev-gf's field laws: its products are the field's, each output
  byte splits into four rows of four products, regrouped by input byte, and
  each input byte's four products sum to it or to zero;
* ShiftRows is undone by computation, AddRoundKey by XOR twice (mode-core's
  `u32_xor_xor`);
* a round, the last round and the first AddRoundKey are undone on every
  state of bytes; the rounds and the cipher by induction on the round keys;
  the block's bytes into the state and back (mode-core's
  `bytes_onto_block16`).

The S-box circuit is never evaluated on unknown bits (that blows up in the
kernel): every byte fact is used on a byte in the form `U32.and(255, x)`,
rewritten first to its eight bits, which the 256 cases fix.

**Not proved:** AES encryption undoes decryption (the reverse direction; it
holds, since AES is a permutation, but would need MixColumns after
InvMixColumns and the S-box after its inverse, which nothing here uses).

## Tests

* `check.bend`: FIPS 197 C.1 decryption, and C.2 (AES-192) and C.3
  (AES-256) both ways (C.1's encryption is the law). The checker evaluates
  AES slowly (about 0.4 GB and a second per block) and keeps what it
  evaluates, so these run compiled rather than as laws.
* `ref/run.sh`: AES-128, AES-192 and AES-256 single blocks, both ways, against
  Python's `cryptography` (28 cases with the default seed).
* The modes over AES: their packages' `ref/` tests and aes-modes'
  `check.bend`.

Speed, on a native build: about 300 KB/s per pass of AES; decryption is as
fast as encryption (aes-modes' README, Sizes).

## Side channels

The inverse S-box is computed without branches or table lookups on secret
bytes. That is a property of the code as written, not a timing guarantee:
Bend's runtime promises nothing about running time, and no timing
measurement has been made.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(3.4 minutes, 1.21 GB peak; `--verdict` 7.6 minutes, 1.25 GB peak) ALL
PROOFS CHECK, with and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (3.4 minutes, 1.17 GB peak), `--verdict` ALL PROOFS CHECK (7.2 minutes, 1.24 GB peak; both include bend-osdev-gf's and mode-core's proofs), `gen/aes_proof.py --check` up to date, `check.bend` passes, `ref/run.sh` 28 cases match, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass. Packages that import `PROOF.bend` pass `--verdict` with it: bend-osdev-cm-instances, and crypto (`PROOF_cm.bend`).

## Dependencies

`DEPS`: `bytes` (`Octets`), `mode-core` (the block `CmBlock`, the error
type, and its laws in the proof), `gf` (GF(2^8) products for InvMixColumns,
and its field laws in the proof) and `bend-collections@1.0.0.0`, for AES
encryption.
