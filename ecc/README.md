# bend-osdev-ecc

Elliptic curves y^2 = x^3 + a x + b over a prime field, generic over the
curve's domain parameters: point arithmetic in Jacobian coordinates over
Montgomery-form field elements, scalar multiplication, public-key
validation, SEC 1's uncompressed point form; the named curves NIST P-192,
P-224, P-256, P-384 and P-521, SM2's curve, and the GOST CryptoPro A, B and
C curves (with the SM2 and GOST R 34.10-2012 example curves); ECDH (SP
800-56A) and ECDSA (FIPS 186-5) with RFC 6979's deterministic per-message
secret. The `sm2` and `ecrdsa` packages build on the same curve layer.

The directory is `ecc` and the entry file `ecc/ecc.bend`; the hub name is
`bend-osdev-ecc`. As instances of crypto's signature and key-agreement
interfaces, ECDSA and ECDH are in bend-osdev-pubkey (`pubkey/ecc.bend`).

## Specifications

* **ECDSA:** FIPS 186-5 (*Digital Signature Standard*, NIST, February
  2023), sections 6.4.1 (signature generation) and 6.4.2 (verification),
  Appendix A.2.1 (key pairs from extra random bits) and A.3.3 (which adopts
  RFC 6979's deterministic k).
* **Deterministic k:** RFC 6979 (T. Pornin, *Deterministic Usage of the
  Digital Signature Algorithm (DSA) and Elliptic Curve Digital Signature
  Algorithm (ECDSA)*, August 2013), sections 2.3.2 to 2.3.4 (bits2int,
  int2octets, bits2octets) and 3.2 (the HMAC_DRBG steps), with its Appendix
  A.2.5 (P-256) vectors in `check.bend`.
* **ECDH and validation:** NIST SP 800-56A Rev. 3 (*Recommendation for
  Pair-Wise Key-Establishment Schemes Using Discrete Logarithm
  Cryptography*, April 2018), sections 5.6.1.2 (ECC key pairs), 5.6.2.3.3
  (full public-key validation), 5.6.2.3.4 (partial validation), 5.7.1.2
  (the ECC CDH primitive, P = h d Q), Appendix C.2 (the field element as
  bytes).
* **The curves:** NIST SP 800-186 (*Recommendations for Discrete
  Logarithm-based Cryptography: Elliptic Curve Domain Parameters*, February
  2023), sections 3.2.1.2 to 3.2.1.5 (P-224, P-256, P-384, P-521); FIPS
  186-4 (July 2013), Appendix D.1.2.1 (P-192, which SP 800-186 keeps for
  legacy use only); draft-shen-sm2-ecdsa-02 (S. Shen, X. Lee, *SM2 Digital
  Signature Algorithm*, February 2014), Appendix D (SM2's curve) and
  Appendix A.2 (its example curve); RFC 4357 (V. Popov, I. Kurepkin, S.
  Leontiev, *Additional Cryptographic Algorithms for Use with GOST
  28147-89, GOST R 34.10-94, GOST R 34.10-2001, and GOST R 34.11-94
  Algorithms*, January 2006), section 11.4 (CryptoPro A, B and C); RFC 7091
  (V. Dolmatov, A. Degtyarev, *GOST R 34.10-2012: Digital Signature
  Algorithm*, December 2013), section 7.1 (its example curve).
* **Point formulas:** the Explicit-Formulas Database (D. J. Bernstein, T.
  Lange), "Jacobian coordinates for short Weierstrass curves"
  (hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html): dbl-2007-bl and
  add-2007-bl, with the cases they exclude (infinity, P + P, P + (-P))
  taken first.
* **The point form:** SEC 1's uncompressed form (0x04 || X || Y, each the
  field's length). **SEC 1 itself (SECG, *Elliptic Curve Cryptography*) was
  not read**: the form is written as described here, and `ref/run.sh`
  checks it against the encoding cryptography writes and reads (its X9.62
  uncompressed point). The compressed form is not supported.

The curve constants are transcribed by `gen/curves.py`, which checks every
curve before writing it (p and n prime, G on the curve, n G the point at
infinity, the group order within Hasse's bound): a transcription error in
CryptoPro A was caught that way. `ref/run.sh` compares the NIST and SM2
curves with the openssl command's.

## Files

| File | Holds |
|---|---|
| `ecc.bend` | the errors, domain parameters, points, curves (with their Montgomery contexts), Jacobian arithmetic, scalar multiplication, validation, the point form |
| `curves.bend` | the named curves (generated region) |
| `ecdh.bend` | ECDH key pairs, the primitive and agreement |
| `ecdsa.bend` | ECDSA signatures, signing and verification, the r \|\| s form |
| `rfc6979.bend` | RFC 6979's deterministic k over any HMAC |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | the curves' checks, RFC 6979's P-256 vectors, ECDH, refusals, with expected output |
| `gen/curves.py` | writes `curves.bend` from the specifications' tables, after checking each curve |
| `gen/exhaustive.py` | writes the small-parameter exhaustive laws and their proofs |
| `ref/gen.py`, `ref/run.sh` | the differential test against cryptography and the openssl command |

Bend imports do not re-export: import the files you use.

## Public interface

| File | Defs and types |
|---|---|
| `ecc.bend` | `EcError` (`EcBadPoint`, `EcInfinity`, `EcBadEncoding`, `EcBadPrivateKey`, `EcBadNonce`); `EcParams{p, a, b, gx, gy, n, h}` (open), `EcParams.p`, `.n`, `.h`, `.a`, `.b`; `EcPoint` (open: `EcInf`, `EcAff{x, y}`), `EcPoint.is_inf`, `.is_eq`, `.x`, `.y`; `EcCurve` (opaque), `EcCurve.of(prm)`, `.params`, `.p`, `.n`, `.h`, `.generator`, `.field_len`, `.order_len`, `.field` (the Montgomery context of p), `.am`, `.bm`; `EcCurve.add`, `.dbl`, `.neg`, `.mul(c, k, P)`, `.base_mul(c, k)`, `.mul2(c, u, P, v, Q)` (Shamir's trick); `EcCurve.on_curve` (a finite point, coordinates below p, on the curve: partial validation), `.validate` (full: and n Q = infinity), `.check` (the domain parameters: p and n odd and above 3, a and b below p, a nonzero discriminant, G valid; primality of p and n is bignum's `BnPrime`); `EcCurve.point_to`, `.point_of` (SEC 1 uncompressed; partial validation); `EcError.check` |
| `curves.bend` | `EcCurves.p192`, `.p224`, `.p256`, `.p384`, `.p521`, `.sm2`, `.sm2_example`, `.gost_cp_a`, `.gost_cp_b`, `.gost_cp_c`, `.gost_example` (each an `EcParams`) |
| `ecdh.bend` | `EcDh.private_ok`, `.private_of` (big-endian bytes, `EcBadPrivateKey` outside [1, n - 1]), `.private_to`, `.private_from_bits` (5.6.1.2.1: (c mod (n - 1)) + 1), `.public(c, d)`, `.primitive(c, d, Q)` (Z, the field's length; `EcInfinity`), `.agree(c, d, Q)` (full validation first, `EcBadPoint`) |
| `ecdsa.bend` | `EcSig{r, s}` (open); `EcDsa.hash_int(c, h)`, `EcDsa.sign_hash(c, d, h, k)` (`EcBadNonce` for k outside [1, n - 1] or r = 0 or s = 0), `EcDsa.verify_hash(c, Q, h, sig)`, `EcDsa.sign(~digest, c, d, m, k)`, `EcDsa.sign_det(~digest, ~mac, c, d, m)`, `EcDsa.verify(~digest, c, Q, m, sig)`, `EcDsa.sig_to(c, sig)`, `EcDsa.sig_of(c, o)` (`None` unless twice n's length), `EcDsa.verify_bytes(~digest, c, Q, m, o)` |
| `rfc6979.bend` | `EcRfc6979.int2octets`, `.bits2int`, `.bits2octets`, `.k(~mac, q, x, h1)`; `EcDrbgT{v, t}` (open), `EcDrbgT.v`, `.t` |

The hash is `~digest: B.Octets -> B.Octets` (one-shot) and the MAC for RFC
6979 is `~mac: B.Octets -> B.Octets -> B.Octets` (raw key, data), HMAC
over the message's hash (pubkey's `PkHmac.raw` makes one from any hash).
Everything named `ec.*`, `ecdsa.*`, `ecdh.*` and `EcJac` is internal.

## Extension points

* **Any curve** in short Weierstrass form over a prime field:
  `EcParams` is open, `EcCurve.check` checks it, `EcCurve.of` prepares it
  (once: keep the `EcCurve`). The named curves are defs that can be template
  arguments (`~EcCurves.p256()`).
* **Any hash and HMAC** for ECDSA; **the per-message secret** is the
  caller's random k (`EcDsa.sign`) or RFC 6979's (`EcDsa.sign_det`).
* **Validation** is a choice: `point_of` validates partially,
  `EcCurve.validate` fully, `EcDh.agree` does the full one.
* **Formats:** points in SEC 1's uncompressed form, signatures as r || s
  (the IEEE P1363 form). The compressed form, DER signatures (an ASN.1
  SEQUENCE of two INTEGERs) and SubjectPublicKeyInfo belong in an ASN.1
  package, whose results go to `EcCurve.point_of`'s checks and `EcSig`.
* **Curves of other shapes** (Montgomery and Edwards curves: X25519,
  Ed25519) are not covered; they would be packages of their own on bignum.

## Laws

`LAWS.bend` has 6 laws, all proved (`PROOF.bend`) and all accepted by
`--verdict`.

* **For every curve and input:** `point_of_on_curve` (every point
  `point_of` accepts is on the curve: point-validation soundness);
  `validate_on_curve` (every point full validation accepts is on the
  curve); `point_round_trip` (a point read from bytes is read again, the
  same, from the bytes `point_to` writes for it).
* **On the toy curve** y^2 = x^3 + 2x + 7 over GF(11), G = (6, 2) of prime
  order 7 (`ecclaw.toy`): `toy_check` (its parameters pass
  `EcCurve.check`); `toy_ecdh` (both sides agree, for every pair of private
  keys in [1, 6]); `toy_ecdsa` (every signature of the hash 0xa0 made with
  a private key d and a per-message secret k in [1, 6] verifies under d's
  public key, or is refused when r or s is 0). The exhaustive laws are
  written by `gen/exhaustive.py`, each case by computation.

**Not proved, and tested:** agreement and verification for every key of
every curve. Both rest on the group law (associativity of point addition
and n G = O), which is algebra on the field elements that the limbs stand
for and is not formalised here (bignum's README). They hold exhaustively on
the toy curve, and `ref/run.sh` tests them on the named curves against
cryptography. That the Jacobian formulas compute the affine sum is likewise
tested (against `ref/gen.py`'s affine model and cryptography), not proved.

## Tests

* `check.bend`: `EcCurve.check` on every named curve; RFC 6979 Appendix
  A.2.5's P-256 key: its public key, k for "sample" and "test" with
  SHA-256, and both signatures (r, s), equal to the RFC's; verification of
  the "sample" signature, and of a zero signature refused; ECDH both ways;
  n G = infinity; a peer key off the curve refused.
* `ref/run.sh` (238 cases with the default seed): every NIST curve's and
  SM2's parameters against the openssl command's (`openssl ecparam
  -param_enc explicit`, read with cryptography); d G against cryptography's
  public key for P-192 to P-521, and the SEC 1 round trip; ECDH against
  cryptography's exchange, both ways; Bend verifies cryptography's ECDSA
  signatures (SHA-256, SHA-512) and refuses them changed; Bend's signature
  with a given k equals `gen.py`'s FIPS 186-5 computation, which
  cryptography verifies first; invalid points refused (off the curve, a
  coordinate of p or more, a wrong length or first byte); for the GOST and
  SM2 curves, k G and u G + v Q against `gen.py`'s affine model, which
  checks itself on the curves' orders first.

## Sizes and speed

Native builds (Bend 2.0.37, WSL2), P-256 with SHA-256, through pubkey's
instances (5 repetitions in one program): **ECDSA verification about 44
ms**, signing (RFC 6979's k) about 36 ms, an ECDH shared secret (with full
validation of the peer's key, itself a scalar multiplication) about 70 ms.
`EcCurve.of` builds the field's Montgomery context; keep the curve value
instead of rebuilding it per operation.

## Notes on use

None of this is constant-time: scalar multiplication is double-and-add
over the scalar's bits, so its time depends on the scalar. Private keys
and random k must come from a cryptographic random source (this package
has none); RFC 6979's k needs none.

## Dependencies

`DEPS`: `bytes` (`Octets`), `bignum` (the integers and Montgomery
arithmetic), `bend-collections-laws-crypto@1.0.0.0` (SHA-256 and SHA-512 for
`check.bend` and `ref/`: no hash is part of this package's interface).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK
(about 320 s), `check.bend` passes, `ref/run.sh` 238 cases match,
`scripts/deps.sh` passes.
