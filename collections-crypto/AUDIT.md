# Audit of bend-collections' cryptography, as collections-crypto adapts it

The code is bend-collections@1.0.0.0's `src/crypto`, read and run through
bend-collections-laws-crypto@1.0.0.0's identical copy (README.md, "Where
the code comes from"). Each adapted algorithm is checked against REVIEW.md's
standard for a bend-osdev package: laws for every input where they can be
proved, the specification's own vectors, a differential test against an
independent implementation, and `--verdict` passing. Everything below was
run with the Bend 2.0.37 release on WSL2, Python 3.12.3, Python's
cryptography 41.0.7 and OpenSSL 3.0.13.

**Summary: no bug was found in the adapted code.** Every vector and all 291
differential cases agree; where bend-collections differs from Python's
cryptography it follows the specification (Ed25519's point decoding, the
ChaCha20 counter). The gaps are in assurance and scope: five of the proof
roots the adapters would rely on do not pass `--verdict` (one runs out of
memory), no law says the AEADs' outputs are bytes, the specifications'
message limits are neither documented nor refused, and BLAKE2b with a chosen
digest length has no law. Drafts for upstream are listed at the end.

## What bend-collections ships

bend-collections-laws-crypto states its laws in `proofs/crypto/*/laws.bend`
and in the executable specifications' clause types (`spec/crypto/*.bend`),
and proves them in `proofs/crypto/*/proof.bend`. The published packages
ship no test scripts (comments name `tools/...` generators and checkers that
are not in either package), so what bend-collections tests beyond its proofs
cannot be seen from the packages; the tests below are this package's.

The proof roots, each checked on its own (`--check-only`, then `--verdict`,
one at a time):

| Root | `--check-only` | `--verdict` |
|---|---|---|
| `proofs/crypto/chacha/proof.bend` | passes, 1 s, 0.18 GB | fails: "mismatch between the TypeScript implementation, and the formalized BendTT kernel", 40 s |
| `proofs/crypto/poly1305/proof.bend` | passes, 5 s, 0.54 GB | passes, 55 s, 2.0 GB |
| `proofs/crypto/aead/proof.bend` (ChaCha20-Poly1305, XChaCha20-Poly1305, AES-GCM) | passes, 13 s, 0.97 GB | fails: the same mismatch, 103 s |
| `proofs/crypto/blake/blake2b/proof.bend` | passes, 1 s, 0.31 GB | did not finish: 19 GB resident and swapping after about half an hour, stopped |
| `proofs/crypto/blake/blake2s/proof.bend` | passes, 1 s, 0.19 GB | fails: mismatch, 90 s |
| `proofs/crypto/blake/blake3/proof.bend` | passes, 0 s, 0.18 GB | fails: mismatch, 85 s |
| `proofs/crypto/keccak/proof.bend` | passes, 2 s, 0.20 GB | passes, 9 s, 0.25 GB |
| `proofs/crypto/curve25519/proof.bend` | passes, 5 s, 0.51 GB | passes, 13 s, 0.62 GB |
| `proofs/crypto/ed25519/proof.bend` | passes, 7 s, 0.61 GB | passes, 21 s, 0.82 GB |

The same mismatch message appears for closed computations past a size: a
Poly1305 tag of 64 bytes passes `--verdict` and one of 112 bytes does not;
ChaCha20 on RFC 8439 2.4.2's 114 bytes passes; ChaCha20-Poly1305 on 2.8.2
and AES-128-GCM on the GCM specification's test case 2 do not, while its
test case 1 (no data) does. All of them pass `--check-only`. That points at
the kernel giving up on long reductions (AGENTS.md: "very long closed
computations run out of kernel fuel") rather than at wrong proofs, but the
def in each failing root that triggers it was not located.

## AES-GCM (AES-128, AES-256) and GMAC

* **Code:** `aesgcm.bend`, `aes/gcm.bend`, `aes/aes.bend`, through the facade
  `aead.bend` (`encrypt`, `decrypt`).
* **Proved upstream** (`proofs/crypto/aead/laws.bend`, `proofs/crypto/aes/`):
  `aes128gcm.seal`/`open` and the AES-256 pair (the facade is
  `spec/crypto/aes/gcm.bend`'s GCM for a key and nonce of the right
  lengths), `roundtrip` (decrypt after encrypt), `forgery` (every other
  16-byte tag refused), `seal_layout`, `decrypt_sound`, and the checked
  API's `encrypt.valid`/`invalid`, `decrypt.valid`/`invalid`. The proof root
  fails `--verdict`.
* **Used here:** `aead_round_trip_if` takes bend-collections' round trip at
  the arguments as its hypothesis hr (not joined: the root fails
  `--verdict`), and that the ciphertext is a byte string as h (no law says
  so; below).
* **Tested here:** the GCM specification's test cases 1 to 4 (AES-128) and
  13 to 16 (AES-256), sealed and opened, changed tag, data and associated
  data refused; GMAC on test cases 1 and 13; against cryptography's AESGCM,
  12 random seals with their opens and the three tamperings, short nonce
  and key refused, 8 GMAC tags with verify. All agree.
* **Divergences:** within SP 800-38D. bend-collections takes only 96-bit
  IVs and 128-bit tags, and AES-128 and AES-256 (5.2.1.1 and 5.2.1.2 let an
  implementation restrict the supported lengths, and recommend 96-bit IVs);
  cryptography also takes other nonce lengths (8, 16 and 32 bytes tried)
  and AES-192, which are refused here.
* **Gap:** len(P) <= 2^39 - 256 bits (5.2.1.1) is not enforced or
  documented. The data counter starts at 2 (inc32(J0)) and wraps after
  2^32 - 2 blocks, exactly at that limit, onto J0, whose block masks the
  tag. A Bend program cannot hold a 64 GB message, so this is a
  documentation gap.
* **Bugs:** none found.

## ChaCha20 and XChaCha20 (stream)

* **Code:** `chacha/chacha20.bend`, `chacha/core.bend`. The adapter uses
  `keystream(r, key, counter, nonce)` (one block) as a keystream generator
  for crypto's `CrXor`, and `hchacha_rounds` for XChaCha.
* **Proved upstream** (`proofs/crypto/chacha/laws.bend`): `block_rounds`,
  `encrypt_rounds`, `hchacha_rounds`, `hchacha20` and `xencrypt` equal
  `spec/crypto/chacha.bend`'s RFC 8439 and draft-irtf-cfrg-xchacha-03
  algorithms, for every key, counter, nonce, round count and list;
  `involution`, `xinvolution`, `encrypt_length`, `block_length`; the checked
  API. The root fails `--verdict`.
* **Used here:** no upstream law (the root fails `--verdict`). The stream
  interface's three laws are proved here for every round count and state
  (`chacha_stream_*`), as for any keystream generator; the keystream's
  value is tested, and its RFC 8439 2.3.2 block is proved by computation
  (`chacha20_rfc8439_block`).
* **Tested here:** RFC 8439 2.3.2, 2.4.2 (whole, in pieces, back), 2.6.2;
  the XChaCha draft's A.3.2.1 (304 bytes); against cryptography's ChaCha20,
  8 cases in two pieces with random counters; XChaCha20, XChaCha12,
  ChaCha12 and ChaCha8 against `ref/gen.py`'s ChaCha (14 cases), which is
  first checked against cryptography and the draft's vectors. All agree.
* **Divergence from cryptography, not from RFC 8439:** at counter overflow.
  bend-collections' counter is 32 bits and wraps to 0 (`U32.add(counter,
  1)`). RFC 8439 2.3 limits one key and nonce to 2^32 blocks and does not say
  what happens past them. cryptography 41.0.7, started at counter
  0xffffffff, carries into the nonce's first word instead (measured here);
  its current documentation says it raises ValueError at overflow.
  `ref/run.sh` keeps a wrap case against `gen.py`'s 32-bit counter.
* **Gap:** the 2^32-block limit is neither refused nor documented (draft
  patch below).
* **Bugs:** none found.

## Poly1305

* **Code:** `poly1305/poly1305.bend`, `poly1305/limbs.bend`.
* **Proved upstream** (`proofs/crypto/poly1305/laws.bend`): `mac_correct`
  (the tag is RFC 8439's, for every key and message), `mac_length`,
  `verify_accepts`, `verify_rejects` (every other tag), `modp_mod`,
  `absorb_poly`, `mac_poly` (the tag is the polynomial reading). The root
  passes `--verdict`, at 2.0 GB.
* **Used here:** not imported: with it, this package's `--verdict` peaked at
  2.8 GB of the 3 GB a check may use. The MAC laws hold here for every key
  and message through crypto's default verify; RFC 8439 2.5.2 is proved by
  computation (`poly1305_rfc8439`).
* **Tested here:** 2.5.2, verify refusing a changed tag or message, 8 cases
  against cryptography's Poly1305. All agree.
* **Bugs:** none found.

## ChaCha20-Poly1305 and XChaCha20-Poly1305

* **Code:** `aead/chacha20poly1305.bend`, through `aead.bend`.
* **Proved upstream:** as for AES-GCM above (`chacha20poly1305.seal`/`open`,
  the X variants, `roundtrip`, `forgery`, `decrypt_sound`, `seal_layout`,
  and that the per-algorithm checked API agrees with the facade). The root
  fails `--verdict`.
* **Used here:** as for AES-GCM (`aead_round_trip_if`, hypotheses hr and
  h).
* **Tested here:** RFC 8439 2.8.2 and the draft's A.3.1, sealed and opened,
  changed associated data and nonce refused; 6 random cases each against
  cryptography's ChaCha20Poly1305 and against `gen.py`'s XChaCha20-Poly1305
  (HChaCha20, then cryptography under the subkey), with their opens and
  tamperings. All agree.
* **Gap:** P_MAX (RFC 8439 2.8: 274,877,906,880 bytes) is not refused or
  documented; the data counter starts at 1 and wraps after 2^32 - 1 blocks,
  exactly at P_MAX, onto block 0, the Poly1305 key block.
* **Bugs:** none found.

## BLAKE2b, BLAKE2s, BLAKE3, and BLAKE2b with a chosen digest length

* **Code:** `blake/blake2b/blake2b.bend`, `blake/blake2s/blake2s.bend`,
  `blake/blake3/blake3.bend` (one-shot, on a packed word array and a byte
  length); `blake/blake2b/sized.bend` (BLAKE2b-n, and the packing used
  here).
* **Proved upstream:** `blake2b_correct`, `blake2s`, `blake3_correct` (the
  digest is the specification's, RFC 7693 or the BLAKE3 paper's, for every
  array and length), the compression functions, digest sizes, the refusal of
  a length past the array. BLAKE2b's root ran out of memory under
  `--verdict`; BLAKE2s's and BLAKE3's fail with the mismatch.
  `sized.bend` (BLAKE2b-n, which Argon2 also uses) has no law, and does not
  check that 1 <= nn <= 64.
* **Used here:** no upstream law. The hash interface's streaming and split
  laws hold for every message through the buffered state; BLAKE2s-256 of
  "abc" and BLAKE3 of the empty message are proved by computation (both pass
  `--verdict` as closed computations).
* **Tested here:** RFC 7693's BLAKE2b-512 and BLAKE2s-256 of "abc", whole
  and in pieces; 14 of the BLAKE3 team's published vectors (lengths 0 to
  31744, across chunk and tree boundaries); against hashlib, 6 random
  messages and 7 boundary lengths each for BLAKE2b and BLAKE2s, and
  BLAKE2b-n for nn = 1, 20, 32, 48, 63, 64. All agree.
* **Scope:** unkeyed only. RFC 7693 3.3's keyed hashing and BLAKE3's keyed,
  key-derivation and extended-output modes are absent (the BLAKE3 vectors'
  keyed and derive_key outputs could not be tested).
* **Bugs:** none found.

## Keccak-256

* **Code:** `keccak/keccak.bend` (Keccak with the original pad10*1
  padding, rate 136, as Ethereum uses it; FIPS 202's KECCAK[512](M, 256),
  not SHA3-256).
* **Proved upstream:** `permutation_rounds` (the permutation is the
  specification's, for every round count and state), `packed_sponge_correct`,
  `ethereum_keccak256` (the digest is `spec/crypto/keccak/main.bend`'s
  sponge), digest size, capacity refusal. The root passes `--verdict`.
* **Used here:** `keccak256_spec` (from `ethereum_keccak256`).
* **Tested here:** against `gen.py`'s sponge (6 random messages and lengths
  135 to 137 and 271 to 273, in pieces), which is first checked against
  hashlib's SHA3-224/256/384/512 and SHAKE128/256 by giving it their
  padding. No published Keccak-256 vector was read. All agree.
* **Scope:** bend-collections has SHA3-256 (crypto adapts it) and Keccak-256
  only: no SHA3-224, SHA3-384, SHA3-512, SHAKE128 or SHAKE256.
* **Bugs:** none found.

## X25519

* **Code:** `curve25519/x25519.bend`, `curve25519/field.bend`, through
  `kex.bend`.
* **Proved upstream** (`spec/crypto/kex.bend`'s and
  `spec/crypto/curve25519/*.bend`'s clauses, `proofs/crypto/curve25519/`):
  the field operations, X25519 equal to RFC 7748's ladder for every pair of
  32-byte strings of bytes, the public key X25519(k, 9), the shared secret
  refused when all zero (6.1), malformed input refused. Not proved: that
  both parties' secrets agree (group theory). The root passes `--verdict`.
* **Used here:** `x25519_public_spec`, `x25519_shared_spec`; agreement
  stays conditional (`x25519_agree_if`).
* **Tested here:** RFC 7748 5.2's two vectors and one iteration (the
  1,000-iteration value was not run), 6.1's keys and secret both ways;
  against cryptography, 6 key pairs both ways, a peer key with its top bit
  set (masked, as section 5 requires, as cryptography does), three
  u-coordinates at or above p (accepted as u mod p, as section 5 allows, as
  cryptography does), five small-order peer keys (all-zero secret, refused,
  as cryptography refuses them). All agree.
* **Bugs:** none found.

## Ed25519

* **Code:** `ed25519/ed25519.bend`, `point.bend`, `scalar.bend`, SHA-512
  from `hash.bend`, through `sign.bend`.
* **Proved upstream** (`spec/crypto/sign.bend`'s and
  `spec/crypto/ed25519.bend`'s clauses, `proofs/crypto/ed25519/`): key
  generation, signing and verification equal to RFC 8032 5.1's (the
  cofactorless check, S < L), scalar reduction and multiply-add mod L,
  refusals of malformed keys and signatures. Not proved: that a signature
  verifies under its key. The root passes `--verdict`.
* **Used here:** `ed25519_public_spec`, `ed25519_sign_spec`,
  `ed25519_verify_spec`; acceptance stays conditional
  (`ed25519_verify_bytes_if`).
* **Tested here:** RFC 8032 7.1's TEST 1, 2, 3 and SHA(abc); against
  cryptography, 6 keys: public key and signature equal, cryptography's
  signature accepted, refused for a changed message and with S + L.
* **Divergence from cryptography, not from RFC 8032:** cryptography
  (OpenSSL 3.0.13) accepts two public keys that RFC 8032 5.1.3 says fail to
  decode, and bend-collections refuses them: the non-canonical encoding of
  y = p + 1, and x = 0 with the sign bit set. With the identity as public
  key and R, and S = 0, both accept (the cofactorless equation holds, and
  RFC 8032 does not require refusing small-order keys). A non-canonical R
  and S = L are refused by both. `ref/run.sh` keeps these five cases,
  against RFC 8032's rules.
* **Bugs:** none found.

## Across the algorithms

* **No law that outputs are bytes.** Every function takes and returns
  `List<&2, U32>` with elements below 256 by convention, and every law is
  stated for any `U32` lists. A typed byte string (bend-osdev's `Octets`
  masks every element) needs to know the AEADs' ciphertexts are bytes for
  the round trip to survive it; this package states that as the hypothesis
  h of `aead_round_trip_if`, and `check.bend` prints it for every vector.
* **Constant time** is by construction, as bend-collections says: Bend has
  no timing model. The AEADs compare tags with `subtle.eq` (no early exit);
  this package's MACs use crypto's default verify, which compares every
  byte too.
* **The DRBG** (`random.bend`, ChaCha8Rand) was not adapted: crypto has no
  DRBG interface.

## Upstream drafts (not posted)

In `C:\Users\scomo\Bend\bend-audit\pr\collections\`:

* `ISSUE-verdict.md`, with `repro_gcm_tc1.bend`, `repro_gcm_tc2.bend`,
  `repro_chapoly_2_8_2.bend`, `probe_chacha_2_4_2.bend`,
  `probe_poly_64.bend` and `probe_poly_112.bend`: the five proof roots that
  do not pass `--verdict`, and the size-dependent mismatch on closed
  computations;
* `ISSUE-byte-range.md`: a proposed law that the AEADs' outputs are bytes;
* `ISSUE-length-limits.md` and `0001-document-message-limits.diff`: the
  message limits, documented in `aead.bend`'s and `chacha20.bend`'s headers
  (comments only).
