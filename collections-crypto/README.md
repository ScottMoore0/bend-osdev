# bend-osdev-collections-crypto

bend-collections' cryptography as instances of bend-osdev-crypto's interfaces
(`crypto/aead.bend`, `stream.bend`, `mac.bend`, `hash.bend`, `kex.bend`,
`sign.bend`), through adapters, the way kitbytes adapts bend-kit's bytes:
AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305 and XChaCha20-Poly1305 as AEADs;
ChaCha20 (any round count) and XChaCha20 as stream ciphers; Poly1305 and GMAC
as MACs; BLAKE2b-512, BLAKE2b with any digest length, BLAKE2s-256, BLAKE3 and
Keccak-256 as hashes; X25519 as a key agreement; Ed25519 as a signature
scheme. Nothing is rewritten: every algorithm is bend-collections' code, and
the laws its companion package proves about that code are used here where
they can be.

`AUDIT.md` is an audit of the adapted code against REVIEW.md: what
bend-collections proves, what it only tests, how it differs from the
specifications and from Python's cryptography, and what is missing.

The directory is `collections-crypto` and the entry file
`collections-crypto/collections-crypto.bend`; the hub name is
`bend-osdev-collections-crypto`.

## Why a package of its own

* **No other package sees bend-collections' types.** Keys and states are this
  package's opaque types, bytes cross as `Octets`, and every refusal is
  crypto's `CrError`; a program that wants these algorithms uses crypto's
  interfaces and this package's named instances.
* **crypto's check stays where it is.** crypto's `PROOF.bend` took about
  2.3 GB of the 3 GB a check may use when this package was written (crypto's
  laws are now in several pairs of files, each checked on its own); these instances have their own table
  (`gen/instances.py`), as pubkey's do, and add no rows to crypto's.

## Where the code comes from

The code is bend-collections@1.0.0.0's `src/crypto`. It is imported from
bend-collections-laws-crypto@1.0.0.0, which ships the same files (compared
file by file: identical, except that it lacks four `hex.bend` files nothing
here uses) together with the proofs about them. Bend names a def by the
package it comes from, so those proofs are about the laws package's copy;
importing that copy is what lets `LAWS.bend` use them, as crypto's
`inst_sha2.bend` does. Of the hub packages approved for this work
(bend-collections@1.0.0.0, bend-collections-laws-crypto@1.0.0.0,
bend-kit-hash@0.2.0.0, bend-kit-bignum@0.1.0.0), only
bend-collections-laws-crypto@1.0.0.0 is needed.

## Specifications

Read for this package (the algorithms themselves are bend-collections'):

* **ChaCha20, Poly1305, ChaCha20-Poly1305:** RFC 8439, Y. Nir and A.
  Langley, *ChaCha20 and Poly1305 for IETF Protocols* (June 2018): sections
  2.3 and 2.4 (the 32-bit block counter, "2^32 blocks, or 256 GB"), 2.5
  (Poly1305, a one-time authenticator), 2.8 (the AEAD, P_MAX
  274,877,906,880 bytes); vectors from 2.3.2, 2.4.2, 2.5.2, 2.6.2 and
  2.8.2.
* **XChaCha20, XChaCha20-Poly1305:** draft-irtf-cfrg-xchacha-03, S.
  Arciszewski, *XChaCha: eXtended-nonce ChaCha and AEAD_XChaCha20_Poly1305*
  (January 10, 2020; expired, not an IETF document): section 2.2
  (HChaCha20) and its vector, 2.3 (the first 16 nonce bytes to HChaCha20,
  four zero bytes and the last 8 as the ChaCha20 nonce, block counter 0 by
  default and 1 in the AEAD); vectors from A.3.1 and A.3.2.1.
* **AES-GCM, GMAC:** NIST SP 800-38D, M. Dworkin, *Recommendation for Block
  Cipher Modes of Operation: Galois/Counter Mode (GCM) and GMAC* (November
  2007): section 5.2 (GMAC: GCM with no confidential data), 5.2.1.1 (input
  lengths, len(P) <= 2^39 - 256 bits, 96-bit IVs recommended), 5.2.1.2 (tag
  lengths); vectors from D. McGrew and J. Viega, *The Galois/Counter Mode of
  Operation (GCM)* (the submission to NIST, as `gcm-spec.pdf` at
  csrc.nist.gov's proposed modes; its title page carries no date), Appendix
  B, test cases 1 to 4 and 13 to 16.
* **BLAKE2:** RFC 7693, M-J. Saarinen (Ed.) and J-P. Aumasson, *The BLAKE2
  Cryptographic Hash and Message Authentication Code (MAC)* (November 2015):
  section 2.5 (the parameter block's digest length `nn` and key length
  `kk`), 3.3 (keyed hashing); vectors from appendices A and B.
* **BLAKE3:** J. O'Connor, J-P. Aumasson, S. Neves and Z. Wilcox-O'Hearn,
  *BLAKE3: one function, fast everywhere* (version 20211102173700); vectors
  from the BLAKE3 team's `test_vectors/test_vectors.json` (the input bytes
  0, 1, ..., 250 repeated; the hash mode's first 32 bytes), read from the
  BLAKE3 repository on GitHub.
* **Keccak-256:** FIPS PUB 202, *SHA-3 Standard: Permutation-Based Hash and
  Extendable-Output Functions* (August 2015): section 5.1 (pad10*1), 5.2
  (KECCAK[c] = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 - c]), 6.1 (SHA-3
  appends the suffix 01 first). Keccak-256 is KECCAK[512](M, 256), with no
  suffix. No published Keccak-256 vector was read; the tests use
  `ref/gen.py`'s sponge, checked first against hashlib's SHA-3 and SHAKE.
* **X25519:** RFC 7748, A. Langley, M. Hamburg and S. Turner, *Elliptic
  Curves for Security* (January 2016): section 5 (scalars clamped,
  u-coordinates with the top bit masked, non-canonical values accepted),
  6.1 (public keys, the shared secret, the all-zero check); vectors from
  5.2 and 6.1.
* **Ed25519:** RFC 8032, S. Josefsson and I. Liusvaara, *Edwards-Curve
  Digital Signature Algorithm (EdDSA)* (January 2017): sections 5.1.3
  (decoding: y >= p fails, x = 0 with x_0 = 1 fails), 5.1.5 to 5.1.7 (the
  cofactorless check allowed, S < L required); vectors from 7.1 (TEST 1, 2,
  3 and SHA(abc)).
* **Python's cryptography**, *Symmetric encryption* documentation: the
  ChaCha20 nonce is "a 4-byte little-endian block counter followed by a
  12-byte nonce", the IV layout used here.

## Files

| File | Holds |
|---|---|
| `collections-crypto.bend` | the entry file: bend-collections' `Maybe` answers as `Result`s (`CcRes`), and `CcBuf`, the state of a hash whose code is one-shot |
| `aead.bend` | AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305, XChaCha20-Poly1305 as AEADs (one key type, one seal, one open) |
| `gmac.bend` | GMAC over AES-128 and AES-256 as a MAC |
| `poly1305.bend` | Poly1305 as a MAC |
| `chacha.bend` | ChaCha with any round count and XChaCha as stream ciphers: a keystream generator for crypto's `CrXor` |
| `blake.bend` | BLAKE2b-512, BLAKE2b-n, BLAKE2s-256 and BLAKE3 as hashes, and the message packing and digest bytes they share |
| `keccak.bend` | Keccak-256 as a hash |
| `x25519.bend` | X25519 as a key agreement |
| `ed25519.bend` | Ed25519 as a signature scheme |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | every instance through crypto's interfaces on its specification's vectors, with expected output |
| `gen/instances.py` | the table of instances: writes their laws in `LAWS.bend`, their proofs and the bit lemma in `PROOF.bend` (`--check` checks them) |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's cryptography and hashlib |
| `AUDIT.md` | the audit of the adapted bend-collections code |

Bend imports do not re-export: import the files you use.

## Public interface

The instances, as the interfaces' template arguments:

| Instance | Interface | Template arguments |
|---|---|---|
| AES-128-GCM, AES-256-GCM | AEAD | `~CcAeadKey, ~CcGcm.key128` (or `key256`), `~CcAead.seal, ~CcAead.open` |
| ChaCha20-Poly1305, XChaCha20-Poly1305 | AEAD | `~CcAeadKey, ~CcChaPoly.key` (or `CcXChaPoly.key`), `~CcAead.seal, ~CcAead.open` |
| ChaCha with r double rounds | stream cipher | `~CcChaState, ~St.CrXorOut<CcChaState>, ~CcChacha.start, ~CcChacha.update(~r), ~CcChacha.out_state, ~CcChacha.out_data` |
| XChaCha with r double rounds | stream cipher | the same with `~CcChacha.start_x(~r)` |
| Poly1305 | MAC | `~CcPolyKey, ~CcPoly1305.key, ~CcPoly1305.mac, ~CcPoly1305.verify` |
| GMAC-AES-128, GMAC-AES-256 | MAC | `~CcGmacKey, ~CcGmac.key128` (or `key256`), `~CcGmac.mac, ~CcGmac.verify` |
| BLAKE2b-512 (block 128, digest 64) | hash | `~CcBuf, ~128n, ~64n, ~CcBuf.init(), ~CcBuf.update, ~CcBuf.final(~CcBlake.blake2b), ~CcBlake.blake2b` |
| BLAKE2b-n (block 128, digest nn) | hash | the same with `~CcBlake.blake2b_n(~nn)` |
| BLAKE2s-256, BLAKE3 (block 64, digest 32) | hash | the same with `~CcBlake.blake2s`, `~CcBlake.blake3` |
| Keccak-256 (block 136, digest 32) | hash | the same with `~CcKeccak.keccak256` |
| X25519 | key agreement | `~CcX25519Sk, ~CcX25519Pk, ~CcX25519.secret, ~CcX25519.public, ~CcX25519.pk_of, ~CcX25519.pk_to, ~CcX25519.shared` |
| Ed25519 | signature | `~CcEdSk, ~CcEdPk, ~CcEd25519.secret, ~CcEd25519.public, ~CcEd25519.pk_of, ~CcEd25519.pk_to, ~CcEd25519.sign, ~CcEd25519.verify` |

The other public defs and types:

| File | Defs and types |
|---|---|
| `collections-crypto.bend` | `CcRes.of_maybe(e, m)`, `CcRes.or_empty(m)`; `CcBuf` (opaque), `CcBuf.init`, `CcBuf.update`, `CcBuf.bytes`, `CcBuf.final(~digest, s)` |
| `aead.bend` | `CcAeadKey` (opaque); `CcAead.sealed`, `CcAead.opened`, `CcAead.masked` (bend-collections' own answers, which the round-trip law's hypotheses name) |
| `chacha.bend` | `CcChaState` (opaque), `CcChacha.next(~r)` (the keystream generator), `CcChacha.xchacha20_start`, `CcChacha.chacha20_update` (the named ChaCha20 and XChaCha20 instances) |
| `blake.bend` | `CcBlake.pack(o)` (four little-endian bytes to a word, bend-collections' packing), `CcBlake.out(n, m)` (a digest's n words as bytes), `CcBlake.blake2b_256`, `CcBlake.blake2b_384` |
| `poly1305.bend`, `gmac.bend`, `x25519.bend`, `ed25519.bend` | the key types `CcPolyKey`, `CcGmacKey`, `CcX25519Sk`, `CcX25519Pk`, `CcEdSk`, `CcEdPk` (opaque) |

Everything else (`cc.*`) is internal. Lengths: AEAD keys 16 (AES-128-GCM)
or 32 bytes, nonces 12 (24 for XChaCha20-Poly1305), tags 16, appended to the
ciphertext; ChaCha keys 32 bytes, IVs 16 (the initial counter, 32 bits
little-endian, then the 12-byte nonce) or 24 for XChaCha (the nonce,
counter 0); Poly1305 keys 32 bytes; GMAC keys 16 or 32 bytes, the message's
first 12 bytes its nonce; X25519 keys and Ed25519 seeds and public keys 32
bytes, Ed25519 signatures 64. Refusals: `CrBadKeyLength`, `CrBadIvLength`,
`CrBadNonceLength`, `CrTagMismatch` (also for data shorter than a tag),
`CrBadPublicKey` (a public key of the wrong length), `CrBadKey` (an all-zero
X25519 shared secret).

## Extension points

* **The ChaCha round count** is the template argument `~r` of
  `CcChacha.update`, `CcChacha.next` and `CcChacha.start_x` (ChaCha12 and
  XChaCha12 with `~6n`, as Adiantum uses them); the stream laws hold for
  every `r`.
* **The BLAKE2b digest length** is the template argument `~nn` (1 to 64) of
  `CcBlake.blake2b_n`.
* **Any one-shot digest is a streaming hash** through `CcBuf`
  (`~CcBuf.final(~digest)`), with its streaming and split laws already
  proved (`buf_*`, for every digest).
* **A new bend-collections algorithm** plugs in as these do: a file of
  adapters with an opaque key or state type, its `Maybe` answers mapped with
  `CcRes`, and a row in `gen/instances.py`'s table (`HASH`, `STREAM`, `MAC`,
  `SIGN`, `KEX`, `FMT`).
* **Verification** is crypto's named default (`CrMac.verify_tag`, every byte
  compared) for the MACs; bend-collections' own constant-time comparison
  (`subtle.eq`) takes lists, and the AEADs use it inside.
* **Streaming:** the hashes stream through `CcBuf` and the stream ciphers
  through `CrXor`, data in pieces of any size; the AEADs and MACs are
  one-shot, as crypto's AEAD and MAC interfaces are and as
  bend-collections' code is.

## Laws

`LAWS.bend` has 39 laws, all proved and all accepted by `--verdict`.

**For every input** (`buf_*` by hand, the rest generated by
`gen/instances.py`):

* `buf_streaming` (the hash interface's streaming law, for every state),
  `buf_final`, `buf_split`, `buf_split3` (for every one-shot digest), and
  `<h>_hash_split`, `<h>_hash_split3` for h = blake2b, blake2s, blake3,
  blake2b_n (every nn) and keccak256;
* `chacha_stream_involution`, `chacha_stream_streaming_data`,
  `chacha_stream_streaming_state`: the stream interface's three laws, for
  every round count, state and data (so ChaCha20, XChaCha20, ChaCha12...).
  each is crypto's law for every keystream generator, from its
  `LAWS_xor.bend` pair (crypto's `PROOF.bend` takes over 2 GB);
* `poly1305_accepts`, `poly1305_agrees`, `gmac_accepts`, `gmac_agrees`: the
  MAC interface's two laws;
* `x25519_pk_format`, `ed25519_pk_format`: a public key read from bytes is
  read again from the bytes written for it;
* **from bend-collections-laws-crypto's laws** (the proof files that pass
  `--verdict`): `keccak256_spec` (Keccak-256 is bend-collections' executable
  sponge specification, `spec/crypto/keccak/main.bend`, of the packed
  message);
  `x25519_public_spec`, `x25519_shared_spec` (the public key and the shared
  secret from bytes are RFC 7748's X25519, the all-zero secret refused, for
  every 32-byte input); `ed25519_public_spec`, `ed25519_sign_spec`,
  `ed25519_verify_spec` (RFC 8032's key generation, signature and verdict,
  for every 32-byte seed or key, message and 64-byte signature). These
  name bend-collections' executable specifications (`spec/...`), and take
  its symbolic `one` (h1: one == 1), as its own laws do.

**Conditional** (a property of the algorithm at the very arguments used, an
ordinary hypothesis used once):

* `aead_round_trip_if`, for every key of all four AEADs, nonce, associated
  data and plaintext: open accepts what seal produced and gives the
  plaintext back, and refuses alike when seal refuses, given (hr)
  bend-collections' own round trip at these arguments and (h) that its
  ciphertext is a byte string. bend-collections-laws-crypto proves hr for
  every input (its `roundtrip`, and `encrypt.invalid` for other lengths),
  but in a proof file that fails `--verdict` (AUDIT.md), so the two are not
  joined in `PROOF.bend`, as crypto's `ccm_round_trip_if` is not joined to
  ccm's; joined, they are the round trip given h. h is needed
  because `Octets` masks every element to 8 bits and bend-collections
  proves no law that its ciphertext elements are below 256 (AUDIT.md); it
  holds on every vector and differential case (`check.bend` prints it);
* `ed25519_verify_bytes_if` (crypto's `sign_verify_bytes_if`) and
  `x25519_agree_if` (crypto's `kex_agree_if`), given that the scheme
  accepts its own signature and that both parties' secrets agree: number
  theory, which bend-collections does not prove (it proves its code equal to
  the RFCs' algorithms, not those identities); tested on every vector and
  differential case.

**Vectors** (proved by computation): ChaCha20's block (RFC 8439 2.3.2,
through the stream interface), Poly1305 (2.5.2), BLAKE2s-256 of "abc" (RFC
7693 appendix B), BLAKE3 of the empty message (the BLAKE3 team's vectors);
the refusal of a 31-byte ChaCha20 key, a 32-byte AES-128-GCM key and a
31-byte X25519 public key.

**Not proved, and tested:**

* the algorithms' values where bend-collections' proofs fail `--verdict`
  (ChaCha20, the AEADs, BLAKE2b, BLAKE2s, BLAKE3: AUDIT.md lists them), and
  Poly1305's, whose proof passes `--verdict` but alone takes 2.0 GB of the
  kernel's memory (with it, this package's `--verdict` peaked at 2.8 GB of
  the 3 GB a check may use): `check.bend`'s vectors and `ref/run.sh`;
* BLAKE2b-n: bend-collections proves no law about `blake2b/sized.bend`
  (tested against hashlib for nn = 1, 20, 32, 48, 63, 64);
* the hash interface's length law (a digest's length rests on bend-collections'
  `sized` answering `Some` for this package's packing, which takes the
  packing's array size); the AEAD and MAC refusal of changed input (a
  forgery succeeds with probability 2^-128, so it is no law for every input;
  bend-collections proves its own AEAD `forgery` law, in the file that fails
  `--verdict`); the X25519 agreement and Ed25519's acceptance of its own
  signatures (above).

## Tests

* `check.bend`, every instance through crypto's interfaces: ChaCha20 on RFC
  8439's 2.3.2 (the block), 2.4.2 (whole, in two pieces, and decrypted
  back) and 2.6.2 (the Poly1305 key, as keystream); XChaCha20 on the
  draft's A.3.2.1 (304 bytes); Poly1305 on 2.5.2, with verify accepting it
  and refusing a changed tag or message; GMAC on the GCM specification's
  test cases 1 and 13 (which seal nothing); AES-GCM on test cases 1 to 4 and
  13 to 16, test cases 4 and 16 opened, a changed tag, ciphertext or
  associated data refused; ChaCha20-Poly1305 on 2.8.2 and
  XChaCha20-Poly1305 on the draft's A.3.1, opened, and changed associated
  data or nonce refused; X25519 on RFC 7748's 5.2 vectors and one
  iteration, 6.1's public keys and shared secret both ways, an all-zero peer
  refused; Ed25519 on RFC 8032's TEST 1, 2, 3 and SHA(abc): public key,
  signature, verification from the public key's bytes, a changed message
  refused; BLAKE2b-512 and BLAKE2s-256 of "abc" (RFC 7693), whole and in
  pieces; BLAKE3 on 14 of the published vectors (lengths 0 to 31744, across
  the chunk and tree boundaries), in pieces; Keccak-256 of "" and "abc"
  (`ref/gen.py`'s model's values); every refusal; and, for each AEAD
  vector, that bend-collections' answer is a byte string. The published
  values were checked against the documents as read, and the AEAD values
  against cryptography too.
* `ref/run.sh` (291 cases with the default seed, about 80 s): AES-128-GCM,
  AES-256-GCM and ChaCha20-Poly1305 against cryptography (seal equal, open,
  changed tag, ciphertext and associated data refused, short nonce and key
  refused); XChaCha20-Poly1305 against `gen.py`'s (HChaCha20, then
  cryptography's ChaCha20Poly1305 under the subkey), checked first on the
  draft's A.3.1; ChaCha20 in two pieces against cryptography's ChaCha20
  with random initial counters, and the counter at its last value (32-bit
  wrap, `gen.py`'s ChaCha); XChaCha20, XChaCha12, ChaCha12 and ChaCha8
  against `gen.py`'s ChaCha (checked first against cryptography and the
  draft's HChaCha20 and XChaCha20 vectors); Poly1305 against cryptography;
  GMAC against AESGCM sealing nothing, with verify; BLAKE2b, BLAKE2s and
  BLAKE2b-n in two pieces against hashlib, across block boundaries;
  Keccak-256 against `gen.py`'s sponge (checked first against hashlib's
  SHA3-224/256/384/512 and SHAKE128/256 with their padding), across the
  rate; X25519's public keys and shared secrets both ways against
  cryptography, a peer key with its top bit set (masked), three
  non-canonical u-coordinates (accepted) and five small-order peer keys
  (refused, as cryptography refuses them); Ed25519's public keys and
  signatures against cryptography, its signatures accepted, refused for a
  changed message and with S + L; and five edge cases against RFC 8032's
  own rules, two of which cryptography (OpenSSL) decides otherwise
  (AUDIT.md). **gen.py's ChaCha, HChaCha and Keccak share an author with
  this package**: XChaCha20, ChaCha12, ChaCha8, the counter wrap and
  Keccak-256 are compared with them alone, after they are checked against
  cryptography, hashlib and the published vectors. BLAKE3 has no
  implementation in Python here: `check.bend`'s 14 published vectors stand
  in for a differential test.

## Not adapted

* **No DRBG instance:** crypto has no DRBG interface, and none is invented
  here. bend-collections' generator (ChaCha8Rand, `random.bend`) is not
  adapted.
* **Not in bend-collections@1.0.0.0:** P-256 ECDSA (its ECDSA and Schnorr
  signatures are over secp256k1; P-256 ECDSA is pubkey's), SHA3-224,
  SHA3-384, SHA3-512, SHAKE128 and SHAKE256 (it has SHA3-256, which crypto
  adapts, and Keccak-256), keyed BLAKE2 (RFC 7693 3.3), BLAKE3's keyed,
  key-derivation and extended-output modes, AES-192-GCM, GCM with IVs other
  than 96 bits or tags shorter than 128 bits.
* **Already in crypto:** HMAC and HKDF over any hash (bend-collections' are
  HMAC-SHA-256 and HKDF-SHA-256 only), and AES (through bend-osdev-aes).
* **Not asked for here:** secp256k1 ECDSA and Schnorr (a signature-interface
  instance), Argon2 (a KDF-interface instance); both would plug in as the
  others do.

## Notes on use

* Never reuse a nonce under one key (GCM, ChaCha20-Poly1305, GMAC), a ChaCha
  key and IV pair, or a Poly1305 key.
* Keep messages under the specifications' limits: 2^32 blocks for one
  ChaCha20 key and nonce (RFC 8439 2.3), P_MAX for ChaCha20-Poly1305 (2.8),
  2^39 - 256 bits for GCM (SP 800-38D 5.2.1.1). bend-collections does not
  enforce them: its counters wrap (AUDIT.md).
* A GMAC message shorter than its 12-byte nonce has the empty tag, as
  crypto's VMAC does; never accept an empty tag.
* The buffered hashes keep every byte until `final` (about 80 bytes of
  memory per byte held, natively): hash long messages in one call.
* None of this is proved constant-time: Bend has no timing model.
  bend-collections writes its code branch-free on secrets, which is a
  property of the code, not of the runtime.

## Dependencies

`DEPS`: `bytes` (Octets, and its laws in the proofs), `crypto` (the
interfaces, `CrError`, `CrXor`), and the hub package
`bend-collections-laws-crypto@1.0.0.0` (MIT; the algorithms, their
specifications and the laws used above).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(20 s, 1.10 GB peak; `--verdict` 1.0 minutes, 3.53 GB peak) ALL PROOFS
CHECK, with and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 15 s, 0.9 GB),
`--verdict` ALL PROOFS CHECK (about 40 s, 1.3 GB peak), `check.bend` passes
(about 25 s with its build), `ref/run.sh` 291 cases match (about 80 s),
`scripts/deps.sh` passes; `scripts/check.sh` with `VERDICT=1` about 160 s.
