# bend-osdev-sm2

The SM2 digital signature algorithm: the signer's identity hash Z_A, e =
H(Z_A || M), signing (with the caller's random k, or a deterministic k by
RFC 6979's construction) and verification, over any curve of the ecc
package (SM2's recommended curve by default) and any hash (SM3 by
default). Verification is the main concern.

The directory is `sm2` and the entry file `sm2/sm2.bend`; the hub name is
`bend-osdev-sm2`. As an instance of crypto's signature interface, SM2 is in
bend-osdev-pubkey (`pubkey/sm2.bend`).

## Specifications

* draft-shen-sm2-ecdsa-02 (S. Shen, X. Lee, *SM2 Digital Signature
  Algorithm*, IETF Internet-Draft, February 2014): section 5.1.4.4 (Z_A,
  the hash of the signer's identity and the curve), 5.2.1 (signature
  generation), 5.3.1 (verification), Appendix A.2 (the
  worked example: curve, key, identity "ALICE123@YAHOO.COM", Z_A, e, k, r,
  s), Appendix D (SM2's recommended 256-bit curve, in ecc's `curves.bend`).
  The draft sets out GB/T 32918.2-2016; **the GB/T standard itself was not
  read.**
* RFC 6979 (T. Pornin, August 2013), section 3.2, for the deterministic k
  of `Sm2.sign_det` (through ecc's `rfc6979.bend`, with e in place of the
  message hash). This is not part of SM2, which asks for a random k; a
  verifier cannot tell the difference.
* SM3 is the sm3 package's (`sm3/sm3.bend`, GB/T 32905-2016 as that
  package's README cites it).

## Files

| File | Holds |
|---|---|
| `sm2.bend` | the errors, Z_A and e, keys, signing and verification |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | the draft's Appendix A.2 example, and SM2's curve, with expected output |
| `gen/exhaustive.py` | writes the small-parameter exhaustive law and its proof |
| `ref/gen.py`, `ref/run.sh` | the differential test against the openssl command's SM2 |

## Public interface

| File | Defs and types |
|---|---|
| `sm2.bend` | `Sm2Error` (`Sm2BadNonce`, `Sm2BadPrivateKey`, `Sm2IdTooLong`); `Sm2Error.check`; `Sm2.sm3` (the default hash); `Sm2.id_ok(id)` (ENTL_A, its length in bits, fits two bytes); `Sm2.za(~digest, c, id, P_A)`, `Sm2.e(~digest, c, id, P_A, m)`; `Sm2.public(c, d)`, `Sm2.private_ok(c, d)` (1 <= d <= n - 2), `Sm2.private_of(c, o)`; `Sm2.sign_e(c, d, e, k)`, `Sm2.verify_e(c, P_A, e, sig)` (on e); `Sm2.sign(~digest, c, d, id, m, k)`, `Sm2.sign_det(~digest, ~mac, c, d, id, m)`, `Sm2.verify(~digest, c, P_A, id, m, sig)` (on messages) |

Signatures are ecc's `EcSig{r, s}`, travelling as r || s (`EcDsa.sig_to`,
`EcDsa.sig_of`); public keys are ecc's points (SEC 1's uncompressed form,
`EcCurve.point_to`, `point_of`). Everything named `sm2.*` is internal.

## Extension points

* **Any curve** of the ecc package (`EcCurves.sm2()` is the standard's; the
  draft's example curve is `EcCurves.sm2_example()`), **any hash**
  (`~digest`), **any identity** (`id`; "1234567812345678" is the usual
  default, pubkey's `PkSm2.default_id`).
* **The per-message secret**: the caller's random k (`Sm2.sign`), or the
  deterministic one (`Sm2.sign_det`, over any HMAC `~mac`).
* **Formats:** DER signatures and SubjectPublicKeyInfo belong in an ASN.1
  package; SM2 encryption and key exchange (GB/T 32918.3, .4) are not
  covered.

## Laws

`LAWS.bend` has 1 law, proved (`PROOF.bend`) and accepted by `--verdict`.

* **Small-parameter exhaustive** (`gen/exhaustive.py`, each case by
  computation): `toy_sign_verify`: on the curve y^2 = x^3 + 2x + 7 over
  GF(11) with base point (6, 2) of prime order 7, every signature of the
  message value e = 3 made with a private key d in [1, 5] and a per-message
  secret k in [1, 6] verifies under d's public key (a k that gives r = 0,
  r + k = n or s = 0 is refused).

**Not proved, and tested:** that every signature verifies for every key of
every curve: it rests on the group law (ecc's README explains why that is
not formalised). It holds exhaustively on the toy curve; `check.bend` runs
the draft's example and `ref/run.sh` tests SM2's curve against openssl.

## Tests

* `check.bend`: draft-shen-sm2-ecdsa-02 Appendix A.2: the public key from
  the example's private key, Z_A for "ALICE123@YAHOO.COM", e for "message
  digest", the signature (r, s) with the example's k, all equal to the
  draft's; that signature verified, and refused for another message; a
  deterministic signature on SM2's curve verified; a k of 0 and an
  identity of 8192 bytes refused.
* `ref/run.sh` (62 cases with the default seed, about 19 s): for keys the
  openssl command generates on SM2's curve, with SM3 and several
  identities, Bend verifies openssl's signatures (`openssl pkeyutl -sign
  -rawin -digest sm3 -pkeyopt distid:...`) and refuses them changed, under
  another identity, or for another message; Bend's signature with a given k
  equals `gen.py`'s computation of the draft's algorithm (with hashlib's
  SM3), which `openssl pkeyutl -verify` accepts first; Bend's Z_A equals
  `gen.py`'s.

## Sizes and speed

Native builds (Bend 2.0.37, WSL2), SM2's curve with SM3, through pubkey's
instance (5 repetitions in one program): verification about 42 ms; signing
about 72 ms (it computes the public key for Z_A, a second scalar
multiplication).

## Notes on use

None of this is constant-time. A random k must come from a cryptographic
random source (this package has none).

## Dependencies

`DEPS`: `bytes` (`Octets`), `bignum` (the integers), `ecc` (the curves,
points, signatures and RFC 6979), `sm3` (SM3).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(50 s, 0.19 GB peak; `--verdict` 2.4 minutes, 0.23 GB peak) ALL PROOFS
CHECK, with and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK
(about 113 s), `check.bend` passes, `ref/run.sh` 62 cases match,
`scripts/deps.sh` passes.
