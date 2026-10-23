# bend-osdev-cipher-modes

Block-cipher modes of operation over any 128-bit block cipher: CBC (with and
without PKCS #7 padding), XTS (with ciphertext stealing), CCM (authenticated
encryption) and CMAC, with AES-128, AES-192 and AES-256 as the named default
cipher, its decryption proved to undo its encryption for every key and block.

The directory is `cipher-modes` and the entry file `cipher-modes/cipher-modes.bend`
(Bend accepts the hyphen in a module name); the hub name is
`bend-osdev-cipher-modes`.

## Specifications

Written from the public specifications only:

* **CBC:** NIST SP 800-38A, *Recommendation for Block Cipher Modes of
  Operation* (2001), section 6.2; test vectors from Appendix F.2.
* **PKCS #7 padding:** RFC 5652, *Cryptographic Message Syntax*, section 6.3.
* **XTS:** IEEE Std 1619-2007, *Cryptographic Protection of Data on
  Block-Oriented Storage Devices* (XTS-AES), sections 5.1 to 5.4 and the test
  vectors of Annex B; NIST SP 800-38E.
* **CCM:** NIST SP 800-38C (2004) and RFC 3610, *Counter with CBC-MAC (CCM)*
  (2003), with RFC 3610's packet vectors (section 8).
* **CMAC:** NIST SP 800-38B (2005) and RFC 4493, *The AES-CMAC Algorithm*
  (2006), with its test vectors (section 4).
* **AES:** FIPS 197 (November 2001), with the example vectors of its
  Appendix C (C.1, C.2, C.3). Encryption is bend-collections'; the inverse
  cipher (section 5.3) is written here, over bend-collections' round keys.
  The proof of the round trip uses bend-osdev-gf's laws of section 4.2's
  field.

## Files

| File | Holds |
|---|---|
| `cipher-modes.bend` | the 128-bit block `CmBlock`, the error type `CmError`, and the byte helpers every mode shares |
| `cbc.bend` | CBC, on blocks and on bytes, with and without padding |
| `pkcs7.bend` | PKCS #7 padding, for any block size from 1 to 255 |
| `xts.bend` | XTS: multiplication by alpha, the block layer, the byte layer with ciphertext stealing, sector numbers |
| `ccm.bend` | CCM encryption and decryption |
| `cmac.bend` | CMAC subkeys, the MAC, and its streaming interface |
| `aes.bend` | AES-128, AES-192 and AES-256 as a block cipher: the key, encryption (bend-collections), decryption (here) |
| `aes_modes.bend` | the named defaults: every mode with AES, taking the raw key |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | the specifications' vectors, with expected output |
| `gen/aes_proof.py` | writes the AES round-trip proof (the "aes" region of `PROOF.bend`; `--check` checks it is current) |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's `cryptography` |

Bend imports do not re-export, so import the files you use. A mode file never
imports `aes.bend`: a program that brings its own cipher does not depend on
bend-collections.

## The block cipher is a parameter

Every mode takes the cipher as template arguments, specialised at compile
time:

```
~K: Data                          the cipher's (expanded) key
~enc: K -> CmBlock -> CmBlock     encrypt one block
~dec: K -> CmBlock -> CmBlock     decrypt one block (CBC and XTS decryption only)
+k: K                             the key
```

The modes never look inside `K`. A `CmBlock` is `CmBlock{w0, w1, w2, w3}`,
four big-endian 32-bit words (byte 0 of the block is the top byte of `w0`);
the type is open, so a cipher adapter may build and match it directly, or
convert with `CmBlock.of_octets` / `CmBlock.to_octets`. Every value of the
type is a block, so "decryption inverts encryption" is a statement about
every value.

## Public interface

**`cipher-modes.bend`**

| Def / type | Meaning |
|---|---|
| `CmBlock{w0, w1, w2, w3}` | a 128-bit block (open type) |
| `CmBlock.zero()`, `CmBlock.xor(a, b)`, `CmBlock.hex(b)` | the zero block, XOR, hex text |
| `CmBlock.dec_enc(~K, ~enc, ~dec, +k, xs)` | each block of `xs` encrypted and decrypted back under `k`: `xs` itself wherever decryption undoes encryption (the round-trip laws' hypothesis) |
| `CmBlock.of_octets(o) -> Maybe<&2, CmBlock>`, `CmBlock.to_octets(b) -> Octets` | 16 bytes to a block and back (`None` for another length) |
| `CmError` | `CmBadKeyLength{got}`, `CmBadIvLength{got}`, `CmBadTweakLength{got}`, `CmBadNonceLength{got}`, `CmBadTagLength{got}`, `CmBadBlockSize{got}`, `CmNotBlockMultiple{len}`, `CmTooShort{len}`, `CmTooLong{len}`, `CmBadPadding{}`, `CmTagMismatch{}` |

**`cbc.bend`** (all fallible functions answer `Result<&2, &2, CmError, Octets>`)

| Def | Meaning |
|---|---|
| `Cbc.encrypt_blocks(~K, ~enc, +k, iv, bs)`, `Cbc.decrypt_blocks(~K, ~dec, +k, iv, bs)` | the block layer: lists of `CmBlock` under a `CmBlock` IV |
| `Cbc.encrypt(~K, ~enc, +k, iv, m)`, `Cbc.decrypt(~K, ~dec, +k, iv, c)` | bytes: a 16-byte IV, a whole number of blocks |
| `Cbc.encrypt_padded(...)`, `Cbc.decrypt_padded(...)` | any length, PKCS #7 padded |

**`pkcs7.bend`**: `Pkcs7.pad(bs, m)`, `Pkcs7.unpad(bs, m)` (`CmBadBlockSize`,
`CmTooShort`, `CmNotBlockMultiple`, `CmBadPadding`).

**`xts.bend`**

| Def | Meaning |
|---|---|
| `Xts.mul_alpha(t)` | multiplication by alpha in GF(2^128) (IEEE 1619, 5.2) |
| `Xts.tweak(~K, ~enc, +k2, i)` | T_0 = E(k2, i) |
| `Xts.encrypt_blocks(~K, ~enc, +k1, t, bs)`, `Xts.decrypt_blocks(~K, ~dec, +k1, t, bs)` | the block layer, from tweak t |
| `Xts.encrypt(~K, ~enc, +k1, +k2, i, p)`, `Xts.decrypt(~K, ~enc, ~dec, +k1, +k2, i, c)` | a data unit of at least 16 bytes, any length (ciphertext stealing), 16-byte sequence number `i` |
| `Xts.sector(n: W64) -> Octets` | the sequence number of sector `n` (little-endian, zero-filled) |

**`ccm.bend`**: `Ccm.encrypt(~K, ~enc, +k, m, nonce, aad, p)` answers the
ciphertext followed by the `m`-byte tag; `Ccm.decrypt(~K, ~enc, +k, m, nonce,
aad, c)` answers the plaintext, or `CmTagMismatch` (the tag is compared with
no early exit, and no plaintext is released from a message that fails).
`m` is 4, 6, ..., 16; the nonce is 7 to 13 bytes (L = 15 - N); the message
must be shorter than 2^(8L) bytes.

**`cmac.bend`**

| Def | Meaning |
|---|---|
| `Cmac.dbl(b)`, `Cmac.subkey1(~K, ~enc, +k)`, `Cmac.subkey2(...)` | the doubling and the subkeys K1, K2 |
| `CmacState`, `Cmac.start()`, `Cmac.update(~K, ~enc, +k, s, m)`, `Cmac.finish(~K, ~enc, +k, s)` | streaming; `CmacState` is opaque |
| `Cmac.mac(~K, ~enc, +k, m) -> Octets` | the 16-byte MAC in one call |
| `Cmac.verify(~K, ~enc, +k, m, tag) -> Bool` | a 16-byte tag, compared with no early exit |

**`aes.bend`**: `CmAesKey` (opaque), `CmAes.key(o)` (16 or 32 bytes),
`CmAes.key128(o)`, `CmAes.key192(o)` (24 bytes), `CmAes.key256(o)`,
`CmAes.encrypt(k, b)`, `CmAes.decrypt(k, b)`, and `CmAes.prepare(k)`, which
answers the key as it is: decryption uses the key's schedule directly, so
there is nothing left to compute ahead (it computed decryption round keys
in earlier versions, and is kept so that their callers build). Use as
`~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt`.

**`aes_modes.bend`**: `CmAes.cbc_encrypt`, `CmAes.cbc_decrypt`,
`CmAes.cbc_encrypt_padded`, `CmAes.cbc_decrypt_padded`, `CmAes.xts_encrypt`,
`CmAes.xts_decrypt` (a 32- or 64-byte key: Key1 then Key2),
`CmAes.ccm_encrypt`, `CmAes.ccm_decrypt`, `CmAes.cmac`. Each takes the raw key
as Octets and picks AES-128 or AES-256 by its length.

Everything else (`cm.*`, `cbc.*`, `xts.*`, `ccm.*`, `cmac.*`, `aes.*`,
`CmSplit`) is internal.

## AES and bend-collections

bend-collections@1.0.0.0 (`src/crypto/aes/aes.bend`, MIT) has AES
encryption only: `expand_key` and `encrypt_block`, over its `Schedule` (the
number of rounds and the round keys) and its state type (`types.bend`). It
has **no decryption**. CBC and XTS need it, so `aes.bend` here adds FIPS
197's inverse cipher: it undoes bend-collections' `cipher` round by round,
with the same schedule's round keys, the last first (AddRoundKey,
InvMixColumns, InvShiftRows, InvSubBytes). Encryption still goes through
bend-collections, as the task's named default, and a key's schedule is
bend-collections' `expand_key` of its bytes, for AES-128, AES-192 and
AES-256 alike. The inverse S-box is computed rather than looked up (the
inverse affine map, then x^254 in GF(2^8) with masks instead of branches), so
no branch or table index depends on key or data bytes; InvMixColumns'
products by {09}, {0b}, {0d} and {0e} are sums of doublings, likewise
branch-free (the proof checks each against bend-osdev-gf's product in AES's
field, on all 256 bytes). Both directions
use the round keys with each byte masked to its low 8 bits (`aes.sched`),
which changes nothing for a key made by `CmAes.key` and makes the round trip
hold for every value of `CmAesKey`.

**The round trip is proved** (`aes_round_trip`, below), for every key and
block. bend-collections-laws-crypto@1.0.0.0 (an allowed hub package, the
proved laws of bend-collections) was read first: it proves bend-collections'
AES encryption equal to an executable FIPS 197 specification
(`Cipher.value`, `Block.value`) and the S-box circuit equal to the
specification's S-box, but it has no decryption and no inverse law; and its
AES proofs do not pass `--verdict` (the S-box proof, `sbox_bits`, runs out
of the kernel's fuel, at 4.6 GB), so a proof here that imported them would
fail `--verdict` too. So the proof (`gen/aes_proof.py`, the "aes" region of
`PROOF.bend`) reads bend-collections' encryption as written (its `cipher`,
`rounds`, `round`, `last_round`, `sub_bytes`, `shift_rows`, `mix_columns`,
`add_round_key`, and `sbox.bend`'s `sbox`, `xtime`, `mul3`), as the
definition of the cipher it inverts:

* each byte fact is checked on all 256 bytes: the inverse S-box undoes the
  S-box, and the S-box, xtime and mul3 give bytes;
* InvMixColumns undoes MixColumns on every column of bytes, through
  bend-osdev-gf's field laws (multiplication distributes over addition,
  addition is associative and commutative): its products are the field's
  (checked on all 256 bytes), each output byte splits into four rows of
  four products, regrouped by input byte, and each input byte's four
  products sum to it or to zero (checked on all 256 bytes);
* ShiftRows is undone by computation, AddRoundKey by XOR twice;
* a round, the last round and the first AddRoundKey are undone on every
  state of bytes, and each gives a state of bytes again; the rounds and the
  cipher by induction on the round keys; the block's bytes into the state
  and back.

The S-box circuit is never evaluated on unknown bits (that blows up in the
kernel): every byte fact is used on a byte in the form `U32.and(255, x)`,
rewritten first to its eight bits, which the 256 cases fix.

Speed, on a native build on this machine: decryption is as fast as
encryption (CBC over 512 KB encrypted and decrypted back in about 3.8 s,
1 MB encrypted in about 3.4 s; Sizes below). In the proof checker AES is
costly (about 0.4 GB and a second per block for
encryption), which limits the vectors `LAWS.bend` can hold (below).

## Errors

Every fallible function answers `Result<&2, &2, CmError, A>`; each failure
has its own constructor (above). Low-level conversions (`CmBlock.of_octets`)
answer `Maybe`.

## Streaming

* **CMAC** has `start`/`update`/`finish`, and a law that pieces give the MAC
  of the whole.
* **CBC**: the block layer is the streaming interface: the last ciphertext
  block of one call is the IV of the next.
* **XTS** works on one data unit (a sector) at a time; units are independent.
* **CCM** has none: B_0 holds the message length, so a message cannot start
  before its length is known (RFC 3610 is not an online mode).

## Extension points

* **Any 128-bit block cipher:** pass its key type and its block functions as
  the template arguments; nothing in the modes changes. A cipher that also
  proves `dec(k, enc(k, b)) == b` gets the round-trip laws below: an
  induction on the list turns that law into their hypothesis, and
  bend-osdev-cm-instances writes it, and the four laws, out for each of
  legacy-ciphers' 128-bit ciphers (its `gen/instances.py` takes a new row).
* **The default cipher:** `aes.bend` can be replaced (for instance by a
  table-driven or hardware AES) without touching the modes; `aes_modes.bend`
  is the only file that names it.
* **Parameters, not fixed choices:** the cipher, the PKCS #7 block size, the
  CCM tag and nonce lengths, the XTS sequence number (`Xts.sector` for disk
  sectors), and the tag check (`Cmac.verify`, or `Cmac.mac` and a truncation
  of the caller's choice).
* **Faster paths** (bit-sliced AES, packed GF arithmetic) can go behind the
  same defs, tied to these by the differential test.

## Laws

`LAWS.bend`. Laws that need decryption to undo encryption take the
hypothesis `inv: @xs -> {CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs}` at
the law's key (`k`, or XTS's data key `k1`): for every list of blocks, each
block encrypted and decrypted back is itself. So they hold for every cipher
and key that satisfy it. The hypothesis says no more than `dec(k, enc(k,
b)) == b` for every block `b` at that key (a list of one block gives that,
and an induction gives every list from it), and less than the earlier form
of these laws asked, which was a template hypothesis for every key; so each
law says at least as much as before. It is an ordinary hypothesis, used once
in each proof (on the list of blocks the mode gives the cipher: the CBC
inputs, the blocks XOR their tweaks, ciphertext stealing's two), so
`--verdict` models it, where it has no model of a template hypothesis whose
type is a proposition. The proofs then take the list's equation apart a
block at a time (an equation is `Data`, so copyable).

For a cipher whose package proves `dec(k, enc(k, b)) == b` for every key and
block as a law, `bend-osdev-cm-instances` proves the hypothesis for every key
and list (by induction, using that law at every block) and states the four
laws at that cipher with no hypothesis: SM4, Camellia, Serpent, Twofish, ARIA
and CAST-256 (legacy-ciphers).

**For every input:**

* `cbc_blocks_round_trip`: CBC on blocks, for every key, IV and list of
  blocks (with `inv`);
* `cbc_round_trip`: CBC on bytes, for every key, every 16-byte IV and every
  message of whole blocks: encryption succeeds and decryption gives the
  message back (with `inv`);
* `xts_blocks_round_trip`: XTS on blocks, for every data key and starting
  tweak (with `inv`);
* `xts_round_trip`: XTS on bytes, ciphertext stealing included, for every
  pair of keys, every 16-byte sequence number and every data unit of at
  least 16 bytes (with `inv`, at the data key);
* `ccm_round_trip`: for every cipher (no hypothesis: CCM only encrypts), key,
  tag length, nonce, associated data and message, decrypting what encryption
  produced gives the message back, and when the parameters are refused both
  refuse alike;
* `cmac_streaming`: the CMAC state after `a ++ b` is the state after `a`,
  then `b`, for every cipher, key and state;
* `block_octets_round_trip`: a block written as Octets reads back as itself.

The modes run tail-recursive loops (see Sizes); the proofs reason about the
structural forms kept beside them (`cm.split`, `cm.join_onto`, `cbc.enc`,
`xts.enc`, `ccm.ctrb`, ... and `Cbc.encrypt.ref`, `Xts.encrypt.ref`,
`Ccm.encrypt.ref`, ...), and `PROOF.bend` proves every public def equal to
its structural form for every input (the `tr.*` lemmas), so each law is
proved of the code that runs.

The byte-layer laws are proved through bytes' interface laws
(`octets_of_to`, `octets_to_of`, `octets_len_list`, `octets_append_list`,
`take_drop`) and its list layer; nothing looks inside `Octets`.

**Vectors** (proved by computation): FIPS 197 C.1 (AES-128 encryption), SP
800-38A F.2.1's first block, RFC 4493's subkey K1, PKCS #7 padding examples,
the XTS sector number, and the refusals (bad key, IV, tag and nonce lengths,
a data unit shorter than a block, a message that is not whole blocks).

Every other vector of the four specifications runs compiled in `check.bend`
(29 of them): FIPS 197 C.1, C.2 and C.3 both ways; SP 800-38A F.2.1, F.2.2, F.2.5
and F.2.6; IEEE 1619 vectors 1, 2 and 15 to 18 (stealing), with decryption;
RFC 3610 packets 1 to 3, with decryption and a tampered tag refused; RFC 4493
examples 1 to 4 and K2. They are not laws because the checker keeps what it
evaluates, and more than a few AES blocks in one proof file run past its
memory (about 3 GB here).

**AES** (`aes_round_trip`): `CmAes.decrypt(k, CmAes.encrypt(k, b)) == b`
for every key (every value of `CmAesKey`: any number of rounds and any
round keys, AES-128, AES-192 and AES-256 among them) and every block. So the
four mode laws hold for AES with no hypothesis: bend-osdev-cm-instances
states them (`aes_cbc_round_trip`, `aes_xts_round_trip`, ...), and crypto's
AES rows use it (`aes_block_round_trip`, ECB, CBC, PCBC and LRW over AES).

**Not proved:** AES encryption undoes decryption (the reverse direction; it
holds, since AES is a permutation, but would need MixColumns after
InvMixColumns and the S-box after its inverse, which nothing here uses);
the PKCS #7 round trip (`unpad(pad(m)) == m`, and so padded CBC), which needs
modular arithmetic on the message length that is not done yet; it is covered
by the vectors and the differential test.

## Tests

`ref/run.sh` compares every mode with Python's `cryptography` package (an
implementation outside this repository), on random keys, IVs, tweaks, nonces
and messages up to 1.5 KB (264 cases): AES-128, AES-192 and AES-256 blocks
both ways; CBC both ways,
with and without padding; XTS both ways, every tail length 0 to 15 after one
block and after several, and 512-byte sectors; CCM encryption, decryption,
and a tampered tag refused, over every tag and nonce length; CMAC in one call
and in two pieces. `check.bend` runs the specification vectors above.

## Sizes

Every loop over a message's bytes or blocks is a tail call, so a message has
no length limit beyond memory, on both of Bend 2.0.37's lanes (the
JavaScript lane overflows its stack at some tens of thousands of nested
calls; a native build has a 2 GB stack). Measured on Bend 2.0.37 (native
build, `bend file.bend -o prog`, WSL2) with AES-128 (for XTS, a 256-bit key:
two AES-128 keys), over pseudo-random messages, each run including building
the message, every ciphertext checked against Python's `cryptography`:

| Run | Time, native | Peak RAM, native | JavaScript lane, before |
|---|---|---|---|
| CBC encryption, 1 MB | 3.4 s | 104 MB | 12.8 s, 2.5 GB |
| CBC encryption and decryption back, 512 KB | 3.8 s | 102 MB | 18.2 s, 2.1 GB |
| XTS encryption, 1 MB | 3.5 s | 106 MB | 13.1 s, 2.5 GB |
| XTS encryption and decryption back, 512 KB | 3.8 s | 103 MB | 15.2 s, 2.1 GB |
| CMAC, 1 MB | 2.6 s | 101 MB | 8.7 s, 1.7 GB |
| CCM encryption, 1 MB (12-byte nonce) | 5.8 s | 121 MB | 17.3 s, 2.6 GB |
| CCM encryption and decryption back, 512 KB | 5.9 s | 111 MB | 11.4 s, 1.9 GB |

(Native times re-measured in October 2026, after decryption came to use
bend-collections' schedule; the JavaScript-lane column is from before.)

AES dominates the time (natively about 300 KB/s per pass of AES), so the
native build gains less here than in the packages that only move bytes.
Most of the memory is the message as `Octets` (about 80 bytes per byte
natively) and the lists and blocks the modes work on; on the JavaScript
lane a round trip of 1 MB needed more than 3 GB before `Octets` became
compact. Before this, CBC, XTS and CCM overflowed the JavaScript lane's
stack at 32 KB (CMAC was already a loop), and PKCS #7 padding walked the
message as a list (it now works on `Octets`).
`check.bend` runs CBC and CCM over 32 KB and XTS over 32 KB and 5 bytes,
both ways, as a regression test.

## Notes on use

* CBC decryption with padding tells the caller whether the padding was good:
  exposed to an attacker, that is a padding oracle. Prefer CCM (or CBC with a
  MAC checked first) for data an attacker can change.
* SP 800-38E requires XTS's two keys to differ; this package does not check
  it (IEEE 1619's vector 1 uses equal keys).
* A CCM nonce must never repeat under one key; a CBC IV must be
  unpredictable.

## Dependencies

`DEPS`: `bytes` (Octets), `word64` (`W64` sector numbers, and the bit slicing
the byte conversions are built from), `gf` (GF(2^8) products for
InvMixColumns in `aes.bend`, and its field laws in the proof) and
`bend-collections@1.0.0.0`, for AES encryption, as the task names it; only
`aes.bend` (and the proof) imports it.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 2 minutes, 1.6 GB),
`--verdict` ALL PROOFS CHECK (about 5 minutes, 1.9 GB peak; both include
bend-osdev-gf's proofs, and the kernel takes about 3 minutes of it),
`check.bend` passes, `ref/run.sh` 264 cases match, `gen/aes_proof.py
--check` up to date, `scripts/deps.sh` passes. (`--verdict` failed here
until the four round-trip laws took their hypothesis as the ordinary `inv`
above rather than a template `~inv`, which the BendTT kernel cannot model.)
Packages that import `PROOF.bend` pass `--verdict` with it:
bend-osdev-cm-instances, and crypto (whose `--verdict` peaks at 2.8 GB with
it).

## Side channels

Tag comparisons look at every byte (no early exit), and the inverse S-box is
computed without branches or table lookups on secret bytes. That is a property
of the code as written, not a timing guarantee: Bend's runtime (lazy, shared
evaluation, compiled through C) promises nothing about running time, and no
timing measurement has been made. Do not rely on this package for resistance
to timing attacks.
