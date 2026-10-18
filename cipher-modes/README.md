# bend-osdev-cipher-modes

Block-cipher modes of operation over any 128-bit block cipher: CBC (with and
without PKCS #7 padding), XTS (with ciphertext stealing), CCM (authenticated
encryption) and CMAC, with AES-128 and AES-256 as the named default cipher.

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
* **AES:** FIPS 197. Encryption is bend-collections'; the inverse cipher
  (section 5.3) and the key expansion it needs (section 5.2) are written here.

## Files

| File | Holds |
|---|---|
| `cipher-modes.bend` | the 128-bit block `CmBlock`, the error type `CmError`, and the byte helpers every mode shares |
| `cbc.bend` | CBC, on blocks and on bytes, with and without padding |
| `pkcs7.bend` | PKCS #7 padding, for any block size from 1 to 255 |
| `xts.bend` | XTS: multiplication by alpha, the block layer, the byte layer with ciphertext stealing, sector numbers |
| `ccm.bend` | CCM encryption and decryption |
| `cmac.bend` | CMAC subkeys, the MAC, and its streaming interface |
| `aes.bend` | AES-128 and AES-256 as a block cipher: the key, encryption (bend-collections), decryption (here) |
| `aes_modes.bend` | the named defaults: every mode with AES, taking the raw key |

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
`CmAes.key128(o)`, `CmAes.key256(o)`, `CmAes.encrypt(k, b)`, `CmAes.decrypt(k,
b)`, and `CmAes.prepare(k)`, which computes the decryption round keys once
(without it, `CmAes.decrypt` derives them for every block). Use as
`~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt`.

**`aes_modes.bend`**: `CmAes.cbc_encrypt`, `CmAes.cbc_decrypt`,
`CmAes.cbc_encrypt_padded`, `CmAes.cbc_decrypt_padded`, `CmAes.xts_encrypt`,
`CmAes.xts_decrypt` (a 32- or 64-byte key: Key1 then Key2),
`CmAes.ccm_encrypt`, `CmAes.ccm_decrypt`, `CmAes.cmac`. Each takes the raw key
as Octets and picks AES-128 or AES-256 by its length.

Everything else (`cm.*`, `cbc.*`, `xts.*`, `ccm.*`, `cmac.*`, `aes.*`,
`CmSplit`, `CmAesState`) is internal.

## AES and bend-collections

bend-collections@1.0.0.0 (`src/crypto/aes/aes.bend`, MIT) has AES
encryption only: `expand_key` and `encrypt_block` (and `aes.bend`'s other
functions are its internals). It has **no decryption**. CBC and XTS need it,
so `aes.bend` here adds FIPS 197's inverse cipher and the key expansion it
needs, written from the specification; encryption still goes through
bend-collections, as the task's named default. The inverse S-box is computed
rather than looked up (the inverse affine map, then x^254 in GF(2^8) with
masks instead of branches), so no branch or table index depends on key or
data bytes. Decryption is tested, not proved: against FIPS 197 C.1 and C.3,
SP 800-38A F.2.2 and F.2.6, IEEE 1619's vectors and Python's `cryptography`
(no law ties it to encryption; that would mean evaluating 10 to 14 AES rounds
on symbolic bits, which is out of reach). The mode laws take the inversion as
a hypothesis instead.

Speed, through `bend file.bend` on this machine: a 4 KiB CBC or XTS unit
encrypts or decrypts in about 0.15 s beyond start-up, decryption no slower
than encryption. In the proof checker AES is costly (about 0.4 GB and a
second per block for encryption, several GB for one block of decryption),
which limits the vectors `LAWS.bend` can hold (below).

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
  proves `dec(k, enc(k, b)) == b` gets the round-trip laws below for free.
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

`LAWS.bend` (a draft, not yet reviewed by the maintainer). Laws that need
decryption to undo encryption take the hypothesis `~inv: @k -> @b ->
{dec(k, enc(k, b)) == b}`, so they hold for every cipher that satisfies it.

**For every input:**

* `cbc_blocks_round_trip`: CBC on blocks, for every key, IV and list of
  blocks (with `~inv`);
* `cbc_round_trip`: CBC on bytes, for every key, every 16-byte IV and every
  message of whole blocks: encryption succeeds and decryption gives the
  message back (with `~inv`);
* `xts_blocks_round_trip`: XTS on blocks, for every data key and starting
  tweak (with `~inv`);
* `xts_round_trip`: XTS on bytes, ciphertext stealing included, for every
  pair of keys, every 16-byte sequence number and every data unit of at
  least 16 bytes (with `~inv`);
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
(27 of them): FIPS 197 C.1 and C.3 both ways; SP 800-38A F.2.1, F.2.2, F.2.5
and F.2.6; IEEE 1619 vectors 1, 2 and 15 to 18 (stealing), with decryption;
RFC 3610 packets 1 to 3, with decryption and a tampered tag refused; RFC 4493
examples 1 to 4 and K2. They are not laws because the checker keeps what it
evaluates, and more than a few AES blocks in one proof file run past its
memory (about 3 GB here).

**Not proved:** AES decryption inverts AES encryption (tested only, above);
the PKCS #7 round trip (`unpad(pad(m)) == m`, and so padded CBC), which needs
modular arithmetic on the message length that is not done yet; it is covered
by the vectors and the differential test.

## Tests

`ref/run.sh` compares every mode with Python's `cryptography` package (an
implementation outside this repository), on random keys, IVs, tweaks, nonces
and messages up to 1.5 KB (252 cases): AES blocks both ways; CBC both ways,
with and without padding; XTS both ways, every tail length 0 to 15 after one
block and after several, and 512-byte sectors; CCM encryption, decryption,
and a tampered tag refused, over every tag and nonce length; CMAC in one call
and in two pieces. `check.bend` runs the specification vectors above.

## Sizes

Every loop over a message's bytes or blocks is a tail call (Bend 2.0.37's
runtime overflows its stack at some tens of thousands of nested calls), so a
message has no length limit beyond memory. Measured on Bend 2.0.37 (native
build, WSL2) with AES-128 (AES-256 for XTS's two keys), over pseudo-random
messages, every ciphertext checked against Python's `cryptography`:

| Run | Time | Peak RAM |
|---|---|---|
| CBC encryption, 1 MB | 12.8 s | 2.5 GB |
| CBC encryption and decryption back, 512 KB | 18.2 s | 2.1 GB |
| XTS encryption, 1 MB | 13.1 s | 2.5 GB |
| XTS encryption and decryption back, 512 KB | 15.2 s | 2.1 GB |
| CMAC, 1 MB | 8.7 s | 1.7 GB |
| CCM encryption, 1 MB (12-byte nonce) | 17.3 s | 2.6 GB |
| CCM encryption and decryption back, 512 KB | 11.4 s | 1.9 GB |

Most of the memory is the message as `Octets` (about 940 bytes per byte
today) and as the lists and blocks the modes work on; a round trip of 1 MB
needs more than 3 GB until `Octets` is compact. Before this, CBC, XTS and
CCM overflowed the stack at 32 KB (CMAC was already a loop), and PKCS #7
padding walked the message as a list (it now works on `Octets`).
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
the byte conversions are built from) and `bend-collections@1.0.0.0`, for AES
encryption, as the task names it; only `aes.bend` imports it.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK; `--verdict` SOME PROOFS FAIL:
the four laws that take the cipher hypothesis `~inv` (and their four lemmas)
are outside the BendTT kernel's scope ("no model for ~inv": the translation
cannot model a template whose type is a proposition; bend-mathlib's laws with
`~assoc` and `~comm` hit the same; the run now reports it as "a mismatch
between the TypeScript implementation, and the formalized BendTT kernel"),
and every other law and lemma, the `tr.*` lemmas tying the tail-recursive
forms to the structural ones included, passes `--verdict` when they are left
out; `check.bend` passes; `ref/run.sh` 252 cases match.

## Side channels

Tag comparisons look at every byte (no early exit), and the inverse S-box is
computed without branches or table lookups on secret bytes. That is a property
of the code as written, not a timing guarantee: Bend's runtime (lazy, shared
evaluation, compiled through C) promises nothing about running time, and no
timing measurement has been made. Do not rely on this package for resistance
to timing attacks.
