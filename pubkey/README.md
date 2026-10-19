# bend-osdev-pubkey

The public-key algorithms of bend-osdev as instances of bend-osdev-crypto's
signature and key-agreement interfaces (`crypto/sign.bend`,
`crypto/kex.bend`): RSASSA-PKCS1-v1_5 and RSASSA-PSS (the `rsa` package),
ECDSA (`ecc`), SM2 (`sm2`) and GOST R 34.10-2012 (`ecrdsa`) as signatures;
finite-field Diffie-Hellman (`dh`) and ECDH (`ecc`) as key agreements. Each
is generic over its parameters (the hash, the curve or group, the salt
length, the identity), with named instances over the usual choices, and
the interfaces' laws are written out for each.

The directory is `pubkey` and the entry file `pubkey/pubkey.bend`; the hub
name is `bend-osdev-pubkey`.

**Why a package of its own** rather than `inst_*` files in crypto (as the
symmetric instances are): the instances bring in bignum and the curve and
group tables, and crypto's `PROOF.bend` already takes about 2 GB of the
checker's memory. With these instances in it, its check outgrew the 3 GB
a check process is allowed (killed at 3.1 GB). Kept apart, crypto stays
free of big-integer dependencies, and the instances' laws check in about a
second.

## Specifications

The algorithms' specifications are their packages' (rsa, dh, ecc, sm2,
ecrdsa READMEs); the interfaces' are crypto's. HMAC from a raw key, for
RFC 6979's deterministic k, is crypto's `hmac.bend` (RFC 2104, as crypto's
README cites it). Choices made here, beyond the specifications:

* **Deterministic signing.** The interface's `sign` is a function of the key
  and message, so the per-message randomness is derived: ECDSA, SM2 and
  GOST R 34.10-2012 use RFC 6979's k (section 3.2; for SM2 and GOST, which
  ask for a random k, this is a choice a verifier cannot tell); RSASSA-PSS
  uses the salt `PkRsa.pss_salt` = the first sLen bytes of MGF1(Hash(the
  private key's form || M)) (RFC 8017's verification accepts any salt of
  the expected length). A signature that cannot be made is empty, which
  every verifier refuses.
* **Key forms.** RSA keys are rsa's raw form (`rsa/keys.bend`); EC public
  keys SEC 1's uncompressed form (ecc), except GOST's, which are RFC 4491's
  (x then y, little-endian); private keys big-endian integers; DH public
  keys big-endian of p's length. DER and X.509 belong in an ASN.1 package.
* **Validation.** ECDH validates the peer's key in full (SP 800-56A
  5.6.2.3.3), DH by the Legendre symbol (5.6.2.3.1, footnote 22; the named
  groups are safe-prime groups).

## Files

| File | Holds |
|---|---|
| `pubkey.bend` | the entry file: HMAC from a raw key (`PkHmac.raw`), shared by the RFC 6979 signers |
| `rsa.bend` | RSASSA-PKCS1-v1_5 and RSASSA-PSS as signatures |
| `dh.bend` | finite-field DH as a key agreement |
| `ecc.bend` | ECDH as a key agreement and ECDSA as a signature |
| `sm2.bend` | SM2 as a signature |
| `ecrdsa.bend` | GOST R 34.10-2012 as a signature |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | every instance through the interfaces, with expected output |
| `gen/instances.py` | the table of instances: writes their laws in `LAWS.bend` and proofs in `PROOF.bend` (`--check` checks them) |
| `ref/gen.py`, `ref/run.sh` | the differential test against cryptography and the openssl command |

Bend imports do not re-export: import the files you use.

## Public interface

As the interfaces' template arguments (signature: `~SK, ~PK, ~secret,
~public, ~pk_of, ~pk_to, ~sign, ~verify`; key agreement: `~SK, ~PK,
~secret, ~public, ~pk_of, ~pk_to, ~shared`):

| Instance | Template arguments |
|---|---|
| RSASSA-PKCS1-v1_5 over a hash and its DigestInfo prefix | `~R.RsaPrivate, ~R.RsaPublic, ~PkRsa.secret, ~R.Rsa.public, ~PkRsa.pk_of, ~K.RsaKeys.public_to, ~PkRsa.pkcs1_sign(~digest, ~prefix), ~PkRsa.pkcs1_verify(~digest, ~prefix)` |
| RSASSA-PSS over a hash (MGF1 over it), sLen-byte salts | the same with `~PkRsa.pss_sign(~digest, ~slen), ~PkRsa.pss_verify(~digest, ~slen)` |
| ECDSA over a curve, hash and HMAC | `~N.BnNat, ~E.EcPoint, ~PkEcdh.secret(~prm), ~PkEcdh.public(~prm), ~PkEcdh.pk_of(~prm), ~PkEcdh.pk_to(~prm), ~PkEcdsa.sign(~prm, ~digest, ~mac), ~PkEcdsa.verify(~prm, ~digest)` |
| SM2 over a curve, hash, HMAC and identity | `~N.BnNat, ~E.EcPoint, ~PkSm2.secret(~prm), ~PkEcdh.public(~prm), ~PkEcdh.pk_of(~prm), ~PkEcdh.pk_to(~prm), ~PkSm2.sign(~prm, ~digest, ~mac, ~id), ~PkSm2.verify(~prm, ~digest, ~id)` |
| GOST R 34.10-2012 over a curve, hash and HMAC | `~N.BnNat, ~E.EcPoint, ~PkEcrdsa.secret(~prm), ~PkEcdh.public(~prm), ~PkEcrdsa.pk_of(~prm), ~PkEcrdsa.pk_to(~prm), ~PkEcrdsa.sign(~prm, ~digest, ~mac), ~PkEcrdsa.verify(~prm, ~digest)` |
| DH over a group | `~N.BnNat, ~N.BnNat, ~PkDh.secret(~grp), ~PkDh.public(~grp), ~PkDh.pk_of(~grp), ~PkDh.pk_to(~grp), ~PkDh.shared(~grp)` |
| ECDH over a curve | `~N.BnNat, ~E.EcPoint, ~PkEcdh.secret(~prm), ~PkEcdh.public(~prm), ~PkEcdh.pk_of(~prm), ~PkEcdh.pk_to(~prm), ~PkEcdh.shared(~prm)` |

The named instances: `PkRsa.pkcs1_sha256_sign`/`_verify` and
`PkRsa.pss_sha256_sign`/`_verify` (SHA-256, 32-byte salts);
`PkEcdsa.p256_sha256_sign`/`_verify`; `PkSm2.sm3_sign`/`sm3_verify` (SM2's
curve, SM3, identity `PkSm2.default_id()` = "1234567812345678");
`PkEcrdsa.cp_a_streebog256_sign`/`_verify` (CryptoPro A, Streebog-256);
with `~DhGroups.ffdhe2048()` and `~EcCurves.p256()` (or any other named
group or curve) for DH and ECDH.

The other public defs: `PkHmac.raw(~bsize, ~digest, k, m)`;
`PkRsa.err`, `PkRsa.err_pk`, `PkRsa.pss_salt`; `PkDh.err`, `PkDh.public_of`
(the raw reader, dh's error); `PkEcc.err`, `PkEcdh.point_of` (the raw
reader, ecc's error), `PkEcdsa.sig`; `PkSm2.err`, `PkSm2.sig`,
`PkSm2.check`; `PkEcrdsa.err`, `PkEcrdsa.sig`. Errors are crypto's
`CrError`: a bad private key `CrBadKey`, a bad public key
`CrBadPublicKey`.

## Extension points

* **Every parameter is a template argument**: the hash (`~digest`) and its
  HMAC (`~mac`, `PkHmac.raw(~bsize, ~digest)` for any hash), the curve
  (`~prm`, any `EcParams`), the group (`~grp`, any `DhGroup`), the PSS salt
  length, the DigestInfo prefix, the SM2 identity.
* **A new public-key algorithm** plugs in as these do: a file of adapters
  mapping its errors onto `CrError`, and a row in `gen/instances.py`'s SIGN
  or KEX table (and FMT, if its package proves a public-key format round
  trip).
* **Random signing** (a caller's k or salt) is not the interface's shape;
  use the algorithm packages directly for it.

## Laws

`LAWS.bend` has 10 laws, all proved (`PROOF.bend`) and all accepted by
`--verdict`. They hold for every value of the instances' parameters (every
hash, curve, group, salt length...), so the named instances are special
cases, and the checker never computes with a concrete curve or group.

* `lift_pk_format` (by hand, for every reader, writer and error mapping): a
  public-key reader survives the mapping of its errors onto `CrError`: a
  key p read from bytes is read again from the bytes written for it when
  the reader's own round trip holds at those bytes.
* **The signature interface's verify-from-bytes law** (crypto's
  `sign_verify_bytes_if`, written out per instance by `gen/instances.py`):
  `rsa_pkcs1_verify_bytes_if`, `rsa_pss_verify_bytes_if`,
  `ecdsa_verify_bytes_if`, `sm2_verify_bytes_if`, `ecrdsa_verify_bytes_if`:
  a signature checked from the public key's bytes is accepted, for every
  key and message, when the public key survives its bytes (`hf`) and the
  scheme accepts its signature (`ha`).
* **The key-agreement law** (crypto's `kex_agree_if`): `dh_agree_if`,
  `ecdh_agree_if`: two parties agree from each other's public-key bytes,
  for every pair of keys, when the keys parse, the public keys survive
  their bytes and the shared secrets agree.
* **The pk_format law**: `ecdh_pk_format_if` (ECDH's public keys, which
  ECDSA and SM2 share, for every curve) and `dh_pk_format_if` (every
  group): a public key read from bytes is read again from the bytes written
  for it, given ecc's `point_round_trip` or dh's `public_round_trip` at
  those bytes (`hr`). Those package laws hold for every input; they are
  hypotheses here only because importing the packages' `PROOF.bend` files
  would bring their exhaustive cases into this check.

**Not proved, and tested:** the hypotheses `ha` and `h` (that a scheme
accepts its own signatures, and that both parties' shared secrets agree,
for every key) are number theory: the group law and Euler's theorem, on
the integers the limbs stand for, which bend-osdev does not formalise
(bignum's README). They hold exhaustively for the packages' toy
parameters (rsa's `toy_round_trip`, ecc's `toy_ecdsa` and `toy_ecdh`,
dh's `toy_agree`, sm2's and ecrdsa's `toy_sign_verify`), and are tested on
the named instances by `check.bend` and `ref/run.sh`. GOST's RFC 4491 key
form and rsa's raw form have no proved round trip (their packages' READMEs
say why), so their instances have no pk_format law.

## Tests

* `check.bend`, every instance from bytes through the interfaces: ECDSA
  over P-256 with SHA-256 signs RFC 6979 Appendix A.2.5's "sample" with its
  key and gives the RFC's r || s, verified from the public key's bytes, and
  refused for another message and for a zero public key; SM2 with SM3 and
  GOST R 34.10-2012 over CryptoPro A sign and verify, and refuse another
  message; RSA-2048 (rsa's check key, made by cryptography): PKCS #1 v1.5
  signing gives cryptography's signature, which verifies (another message
  refused); PSS verifies its own signature and cryptography's; ECDH over
  P-256 and DH over ffdhe2048 agree from each other's bytes, and refuse a
  bad peer key (and a zero private key for ECDH).
* `ref/run.sh` (63 cases with the default seed, about 70 s): keys and
  signatures from Python's cryptography, every key as bytes: Bend accepts
  cryptography's ECDSA P-256 signatures and refuses them for a changed
  message; Bend's ECDH P-256 shared secret equals cryptography's exchange;
  Bend's DH shared secret over ffdhe2048 (p from the openssl command's
  group) equals cryptography's, and p - 1 is refused; RSA keys of 1024 to
  2048 bits: Bend's PKCS #1 v1.5 signature equals cryptography's and
  verifies, Bend accepts cryptography's PSS signatures and refuses them for
  a changed message, and Bend's own PSS signature (with its derived salt)
  equals `gen.py`'s RFC 8017 encoding signed with the raw key, which
  cryptography verifies first.

## Sizes and speed

Native builds (Bend 2.0.37, WSL2), through these instances, 5 repetitions
in one program (100 for RSA verification): RSA-2048 PKCS #1 v1.5
verification about 24 ms and signing about 0.30 s (rsa's README); ECDSA
P-256 verification about 44 ms and signing about 36 ms; ECDH P-256 about
70 ms (with full validation); SM2 verification about 42 ms, signing about
72 ms; GOST R 34.10-2012 (CryptoPro A) about 44 ms either way; DH ffdhe2048
with a 256-bit private key, a public key about 140 ms and a shared secret
about 160 ms. `check.bend` takes about 27 s with its build. Each call
prepares its curve (`EcCurve.of`) again; a caller doing many operations on
one curve can use the ecc package directly with one prepared curve.

## Notes on use

None of this is constant-time. Private keys must come from a cryptographic
random source; the signers need none (their randomness is derived).

## Dependencies

`DEPS`: `bytes`, `bignum`, `crypto` (the interfaces, `CrError`, HMAC and
SHA-256), `rsa`, `dh`, `ecc`, `sm2`, `ecrdsa` (the algorithms; SM3 and
Streebog come through sm2's and ecrdsa's defs).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 1 s), `--verdict` ALL
PROOFS CHECK (about 3 s), `check.bend` passes, `ref/run.sh` 63 cases match,
`scripts/deps.sh` passes.
