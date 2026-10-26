# bend-osdev-ecrdsa

GOST R 34.10-2012 digital signatures (EC-RDSA, the Linux kernel's
`ecrdsa`): signing (with the caller's random k, or a deterministic k by RFC
6979's construction) and verification, over any curve of the ecc package
(RFC 4357's CryptoPro A, B and C, and RFC 7091's example curve, are named
there) and any hash (Streebog-256 and Streebog-512 by default); public keys
and signatures in RFC 4491's forms. Verification is the main concern.

The directory is `ecrdsa` and the entry file `ecrdsa/ecrdsa.bend`; the hub
name is `bend-osdev-ecrdsa`. As an instance of crypto's signature
interface, it is in bend-osdev-pubkey (`pubkey/ecrdsa.bend`).

## Specifications

* RFC 7091 (V. Dolmatov, A. Degtyarev, *GOST R 34.10-2012: Digital
  Signature Algorithm*, December 2013): sections 6.1 (signature
  generation: e = alpha mod q, e = 1 if that is 0; C = k P, r = x_C mod q,
  s = (r d + k e) mod q), 6.2 (verification: v = e^-1, z1 = s v, z2 = -r v,
  C = z1 P + z2 Q), section 7 (the test example: the parameters in 7.1,
  then the key, e, k, r and s).
  **The GOST standard itself was not read**; RFC 7091 is its English text.
* RFC 4357 (V. Popov, I. Kurepkin, S. Leontiev, January 2006), section 11.4:
  the CryptoPro A, B and C parameter sets (in ecc's `curves.bend`).
* RFC 4491 (S. Leontiev, D. Shefanovski, *Using the GOST R 34.10-94, GOST R
  34.10-2001, and GOST R 34.11-94 Algorithms with the Internet X.509 Public
  Key Infrastructure Certificate and CRL Profile*, May 2006): section 2.2.2
  (a signature as s then r, each big-endian) and 2.3.2 (a public key as x
  then y, each little-endian).
* RFC 6986 (V. Dolmatov, A. Degtyarev, *GOST R 34.11-2012: Hash Function*,
  August 2013), section 4.2: the numbering of a hash vector's components,
  which fixes how the digest's bytes become alpha (least significant
  first). Streebog itself is the streebog package's.
* RFC 6979 (T. Pornin, August 2013), section 3.2, for `Ecrdsa.sign_det`
  (through ecc's `rfc6979.bend`, with e in place of the message hash): not
  part of GOST R 34.10-2012, which asks for a random k; a verifier cannot
  tell the difference.

## Files

| File | Holds |
|---|---|
| `ecrdsa.bend` | the errors, e from a hash, keys, signing and verification, RFC 4491's forms |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | RFC 7091's example and CryptoPro A, with expected output |
| `gen/exhaustive.py` | writes the small-parameter exhaustive law and its proof |
| `ref/gen.py`, `ref/run.sh` | the differential test against `gen.py`'s model of RFC 7091 |

## Public interface

| File | Defs and types |
|---|---|
| `ecrdsa.bend` | `EcrdsaError` (`EcrdsaBadNonce`, `EcrdsaBadPrivateKey`, `EcrdsaBadPublicKey`); `EcrdsaError.check`; `Ecrdsa.streebog256`, `Ecrdsa.streebog512` (the default hashes); `Ecrdsa.e(c, h)` (from a hash value); `Ecrdsa.public(c, d)`, `Ecrdsa.private_of(c, o)` (big-endian, d in [1, q - 1]); `Ecrdsa.sign_e(c, d, e, k)`, `Ecrdsa.verify_e(c, Q, e, sig)` (on e); `Ecrdsa.sign(~digest, c, d, m, k)`, `Ecrdsa.sign_det(~digest, ~mac, c, d, m)`, `Ecrdsa.verify(~digest, c, Q, m, sig)` (on messages); `Ecrdsa.sig_to`, `Ecrdsa.sig_of` (s \|\| r, `None` for another length), `Ecrdsa.public_to`, `Ecrdsa.public_of` (x \|\| y little-endian; `EcrdsaBadPublicKey` off the curve), `Ecrdsa.verify_bytes(~digest, c, Q, m, o)` |

Signatures are ecc's `EcSig{r, s}` and points ecc's `EcPoint`. Everything
named `ecrdsa.*` is internal.

## Extension points

* **Any curve** of the ecc package (the 256-bit CryptoPro sets with
  Streebog-256, a 512-bit curve with Streebog-512), **any hash**
  (`~digest`), **the per-message secret** (the caller's random k, or the
  deterministic one over any HMAC `~mac`).
* **Formats:** RFC 4491's raw forms here; the ASN.1 around them
  (SubjectPublicKeyInfo, the OCTET STRING of the key) belongs in an ASN.1
  package. The 512-bit parameter sets of RFC 7836 are not named (not read);
  they plug in as `EcParams`.

## Laws

`LAWS.bend` has 2 laws, both proved (`PROOF.bend`) and accepted by
`--verdict`.

* **For every input:** `public_round_trip`: for every curve and bytes, a
  public key read from RFC 4491's form (`Ecrdsa.public_of`) is read again,
  the same, from the bytes `Ecrdsa.public_to` writes for it (as ecc's
  `point_round_trip` for SEC 1's form). The proof shows more: those bytes
  are the bytes it was read from, since each coordinate's little-endian
  bytes come back from its number (bignum's `octets_round_trip`, with the
  bytes reversed twice: bytes' `rev_rev`). pubkey's EC-RDSA instance
  states its pk_format law from it.
* **Small-parameter exhaustive** (`gen/exhaustive.py`, each case by
  computation): `toy_sign_verify`: on the curve y^2 = x^3 + 2x + 7 over
  GF(11) with base point (6, 2) of prime order 7, every signature of the
  message value e = 3 made with a private key d and a per-message secret k
  in [1, 6] verifies under d's public key (a k that gives r = 0 or s = 0 is
  refused).

**Not proved, and tested:** that every signature verifies for every key of
every curve (the group law: ecc's README).

## Tests

* `check.bend`: RFC 7091's test example (section 7): the public key, the
  signature (r, s) from its e and k, equal to the RFC's, verified, and a
  changed r refused; a deterministic signature over CryptoPro A with
  Streebog-256 verified through the byte forms; the public key's RFC 4491
  form read back; a zero public key and a k of 0 refused.
* `ref/run.sh` (136 cases with the default seed): no implementation of GOST
  R 34.10-2012 is installed here (cryptography and the openssl command have
  none without the GOST engine), so the reference is `gen.py`'s model of RFC
  7091 sections 6.1 and 6.2 on ecc's affine model, with Streebog from the
  streebog package's model. **That model shares an author with this
  package**; it checks itself first on RFC 7091's example. For CryptoPro
  A, B and C and the example curve: Bend's signature with a given k equals
  the model's (for e given, and for messages through Streebog-256); Bend
  verifies the model's signatures and refuses them changed; RFC 4491's
  forms round-trip.

## Sizes and speed

Native builds (Bend 2.0.37, WSL2), CryptoPro A with Streebog-256, through
pubkey's instance (5 repetitions in one program): verification about 44
ms, signing about 44 ms.

## Notes on use

None of this is constant-time. A random k must come from a cryptographic
random source (this package has none).

## Dependencies

`DEPS`: `bytes` (`Octets`, and its laws in the proofs), `bignum` (the
integers, and its `octets_round_trip` in the proofs), `ecc` (the curves,
points, signatures and RFC 6979), `streebog` (Streebog).

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(54 s, 0.45 GB peak; `--verdict` 2.9 minutes, 0.55 GB peak) ALL PROOFS
CHECK, with and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK
(about 165 s, 0.44 GB peak), `check.bend` passes, `ref/run.sh` 136 cases match,
`scripts/deps.sh` passes.
