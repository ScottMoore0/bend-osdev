# bend-osdev-rsa

RSA as RFC 8017 (PKCS #1 v2.2) specifies it: the primitives RSAEP, RSADP
(with the Chinese remainder theorem), RSASP1 and RSAVP1; the signature
schemes RSASSA-PKCS1-v1_5 and RSASSA-PSS with their encodings; the
encryption schemes RSAES-OAEP and RSAES-PKCS1-v1_5; MGF1; key generation
from the caller's random bytes; and a raw byte form of the keys. Every
scheme takes its hash (and mask generation function) as a template
argument, so it runs over any hash of bend-osdev-crypto's hash interface.
Verification is the main concern; signing, decryption and key generation
are there for tests and completeness.

The directory is `rsa` and the entry file `rsa/rsa.bend`; the hub name is
`bend-osdev-rsa`. As instances of crypto's signature interface, the schemes
are in bend-osdev-pubkey (`pubkey/rsa.bend`).

## Specifications

* RFC 8017 (K. Moriarty, B. Kaliski, J. Jonsson, A. Rusch, *PKCS #1: RSA
  Cryptography Specifications Version 2.2*, November 2016): section 3 (keys:
  3.1, 3.2), section 4 (I2OSP, OS2IP), section 5 (RSAEP 5.1.1, RSADP 5.1.2
  with step 2.b's CRT, RSASP1 5.2.1, RSAVP1 5.2.2), section 7.1 (RSAES-OAEP,
  with the decryption's single error of 7.1.2's Note), section 7.2
  (RSAES-PKCS1-v1_5), section 8.1 (RSASSA-PSS), section 8.2
  (RSASSA-PKCS1-v1_5), section 9.1 (EMSA-PSS), section 9.2
  (EMSA-PKCS1-v1_5 and the DigestInfo prefixes of its Note 1), Appendix
  B.2.1 (MGF1).
* FIPS 186-5 (*Digital Signature Standard*, NIST, February 2023): Appendix
  A.1.1 (d = e^-1 mod lcm(p - 1, q - 1)) and A.1.3 (random probable primes:
  the top bits, gcd(p - 1, e) = 1, |p - q| > 2^(nlen/2 - 100)), with
  bignum's Miller-Rabin (Appendix B.3.1).

RFC 8017's example vectors (the pkcs-1v2-1-vec files) were not used: they
are a separate download, which this work does not do. Python's
cryptography stands in (below).

## Files

| File | Holds |
|---|---|
| `rsa.bend` | the errors, the keys (checked as section 3 asks) and the four primitives, on numbers and on octet strings |
| `octets.bend` | byte-string helpers the encodings share: XOR, a repeated byte, the leftmost bits cleared, all-zero and no-zero tests, the first and last byte |
| `mgf1.bend` | MGF1 over any hash |
| `pkcs1.bend` | EMSA-PKCS1-v1_5 and RSASSA-PKCS1-v1_5, and the DigestInfo prefixes |
| `pss.bend` | EMSA-PSS and RSASSA-PSS |
| `oaep.bend` | EME-OAEP and RSAES-OAEP |
| `es15.bend` | EME-PKCS1-v1_5 and RSAES-PKCS1-v1_5 |
| `keygen.bend` | key generation from the caller's random bytes |
| `keys.bend` | the keys' raw byte form |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | an RSA-2048 key through every scheme, with expected output |
| `gen/exhaustive.py` | writes the small-parameter exhaustive law and its proof (`--check` checks it) |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's cryptography |

Bend imports do not re-export: import the files you use.

## Public interface

| File | Defs and types |
|---|---|
| `rsa.bend` | `RsaError` (`RsaMessageTooLong`, `RsaDecryptionError`, `RsaEncodingError`, `RsaOutOfRange`, `RsaIntegerTooLarge`, `RsaBadKey`, `RsaBadFormat`, `RsaNoPrime`); `RsaPublic{n, e}` and `RsaPrivate{n, e, d, p, q, dp, dq, qinv}` (open for reading; build them with the checked defs); `RsaError.check`; `Rsa.public_of(n, e)` (n odd above 3, e odd in [3, n - 1]), `Rsa.private_of(n, e, d, p, q)` (n = p q, d e = 1 modulo p - 1 and q - 1; the CRT values computed), `Rsa.private_of_primes(p, q, e)`, `Rsa.public`, `Rsa.k` (the modulus's bytes), `Rsa.k_of`, `Rsa.mod_bits`; `Rsa.ep`, `Rsa.vp1`, `Rsa.dp` (CRT), `Rsa.sp1` (CRT), `Rsa.dp_plain` (the first form, n and d), `Rsa.i2osp`, `Rsa.ep_octets`, `Rsa.dp_octets` |
| `octets.bend` | `RsaOct.xor`, `.rep`, `.all_zero`, `.no_zero`, `.mask_first`, `.clear_left`, `.first`, `.last` |
| `mgf1.bend` | `RsaMgf1.mask(~digest, seed, len)` |
| `pkcs1.bend` | `RsaDigestInfo.md2`, `.md5`, `.sha1`, `.sha224`, `.sha256`, `.sha384`, `.sha512`, `.sha512_224`, `.sha512_256`; `RsaPkcs1.encode(~digest, prefix, m, emlen)`, `RsaPkcs1.sign(~digest, prefix, sk, m)`, `RsaPkcs1.verify(~digest, prefix, pk, m, s)` |
| `pss.bend` | `RsaPss.em_len(embits)`, `RsaPss.encode(~digest, ~mgf, m, salt, embits)`, `RsaPss.check(~digest, ~mgf, m, em, embits, slen)` (EMSA-PSS-VERIFY), `RsaPss.sign(~digest, ~mgf, sk, m, salt)`, `RsaPss.verify(~digest, ~mgf, pk, m, s, slen)` |
| `oaep.bend` | `RsaOaep.encode(~digest, ~mgf, label, m, seed, k)`, `RsaOaep.decode`, `RsaOaep.encrypt(~digest, ~mgf, pk, label, m, seed)`, `RsaOaep.decrypt(~digest, ~mgf, sk, label, c)` |
| `es15.bend` | `RsaEs15.encode(m, ps, k)`, `RsaEs15.decode(em)`, `RsaEs15.encrypt(pk, m, ps)`, `RsaEs15.decrypt(sk, c)` |
| `keygen.bend` | `RsaKeygen.prime(seed, bits, e, bases, f)`, `RsaKeygen.generate(e, nlen, seed_p, seed_q, bases, f)` |
| `keys.bend` | `RsaKeys.public_to`, `RsaKeys.private_to`, `RsaKeys.public_of`, `RsaKeys.private_of` (`RsaBadFormat` for a malformed form, `RsaBadKey` for a key that fails the checks); `RsaField{x, rest}`, `RsaField.x`, `RsaField.rest` |

The hash is `~digest: B.Octets -> B.Octets` (one-shot, the shape of
crypto's hash interface's digest); the mask generation function is `~mgf:
B.Octets -> Nat -> B.Octets` (seed, length), MGF1 over the hash being
`~RsaMgf1.mask(~digest)`. Salts, OAEP seeds and PKCS #1 v1.5 padding strings
are the caller's random bytes. Everything named `rsa.*` is internal.

## Extension points

* **Any hash** (`~digest`) and **any mask generation function** (`~mgf`) for
  PSS and OAEP; **any DigestInfo prefix** for PKCS #1 v1.5 (the DER of a
  hash's DigestInfo up to the digest; the RFC's are named).
* **The randomness** is the caller's: PSS salts (any length, empty
  included), OAEP seeds, PKCS #1 v1.5 padding, key-generation seeds and
  Miller-Rabin bases. pubkey's signature instance derives a deterministic
  PSS salt from the key and message.
* **Key formats:** the keys are plain integers. Reading PKCS #1 DER (RFC
  8017 Appendix A.1, RSAPublicKey and RSAPrivateKey) or an X.509
  SubjectPublicKeyInfo belongs in an ASN.1 package, whose results go to
  `Rsa.public_of` and `Rsa.private_of`; `keys.bend`'s raw form is what
  pubkey carries meanwhile.
* **Multi-prime keys** (RFC 8017's r > 2) are not supported; `RsaPrivate`
  would gain the extra primes' triples.

## Laws

`LAWS.bend` has 7 laws, all proved (`PROOF.bend`) and all accepted by
`--verdict`.

* **For every input:**
  * `mgf1_length`, `mgf1_prefix`: MGF1 over every hash gives the length
    asked for, and a shorter mask is a prefix of a longer one;
  * `es15_round_trip`: EME-PKCS1-v1_5 decoding undoes encoding, for every
    message, padding string and modulus length (when encoding refuses, both
    sides refuse alike);
  * `oaep_round_trip`: EME-OAEP decoding undoes encoding, for every hash,
    mask generation function, label, message, seed and modulus length;
  * `pss_round_trip`: EMSA-PSS verification accepts every encoding, for
    every mask generation function, message, salt and emBits, and every hash
    whose output length does not depend on its input (hypothesis `hd`, at
    M and M');
  * `pkcs1_sign_verify_if`: an RSASSA-PKCS1-v1_5 signature verifies, for
    every hash, prefix, key and message, wherever the encoding succeeds and
    RSAVP1 undoes RSASP1 on the encoded message (hypotheses).
* **Small-parameter exhaustive** (`gen/exhaustive.py`): `toy_round_trip`:
  for the key p = 5, q = 11, e = 3, every message below 55 goes through
  RSADP and back through RSAEP and the other way, and the CRT's RSADP equals
  the first form.

**Not proved, and tested:** that RSAVP1 undoes RSASP1 (and RSADP undoes
RSAEP) for every key: that is Euler's theorem with the CRT, number theory on
the integers that bignum's limbs stand for, which is not formalised here
(bignum's README explains why). It is the hypothesis of
`pkcs1_sign_verify_if` and holds exhaustively for the toy key; for real keys
`check.bend` and `ref/run.sh` test it against cryptography. Unconditional
sign-then-verify laws for PSS and PKCS #1 v1.5 follow from it and are
likewise not stated for every key.

## Tests

* `check.bend`: an RSA-2048 key (e = 65537) made by Python's cryptography
  for the file, with cryptography's signatures of "abc" over SHA-256:
  RSASSA-PKCS1-v1_5 signing gives cryptography's signature exactly, and
  verifies it (and refuses another message); RSASSA-PSS verifies
  cryptography's signature (MGF1-SHA-256, 32-byte salt) and refuses
  another message, and verifies its own; RSAES-OAEP and RSAES-PKCS1-v1_5
  round trips; RSADP by the CRT equals the first form (and Python's pow);
  the raw key forms read back; an out-of-range ciphertext refused.
* `ref/run.sh` (195 cases with the default seed, about 120 s and 2.1 GB at
  peak): keys of 512 to 2048 bits from cryptography (e = 3 and 65537);
  RSASSA-PKCS1-v1_5 over SHA-256 and SHA-512 (Bend's signature equals
  cryptography's; Bend verifies cryptography's and refuses it changed);
  RSASSA-PSS (Bend verifies cryptography's signatures with random salts of
  several lengths; Bend's own signature with a given salt equals
  `gen.py`'s RFC 8017 encoding signed with the raw key, which cryptography
  verifies first); RSAES-OAEP and RSAES-PKCS1-v1_5 (Bend decrypts
  cryptography's ciphertexts; Bend's ciphertext with a given seed or
  padding equals `gen.py`'s encoding, which cryptography decrypts first);
  RSADP by the CRT against the first form and pow; key generation from
  seeds (the primes checked by cryptography's own key check), and refusals
  of bad keys and ciphertexts.

## Sizes and speed

Native builds (Bend 2.0.37, WSL2), RSA-2048, from 100 and 10 repetitions
in one program: **verification (RSASSA-PKCS1-v1_5, SHA-256, e = 65537)
about 24 ms; signing by the CRT about 0.30 s.** `check.bend` takes about
18 s with its build. A modulus has no size limit beyond memory and time.

## Notes on use

* Use RSAES-OAEP for new encryption (RFC 8017, section 7); decryption of
  both schemes answers one error for every failure. None of this code is
  constant-time, so neither decryption is a defence against timing attacks
  (Bleichenbacher's or Manger's), whatever the single error.
* Salts, seeds, padding and key-generation seeds must come from a
  cryptographic random source; this package has none.

## Dependencies

`DEPS`: `bytes` (`Octets`, and its laws in the proofs), `bignum` (the
integers, Montgomery exponentiation, inverses, Miller-Rabin),
`bend-collections-laws-crypto@1.0.0.0` (SHA-256 and SHA-512 for
`check.bend` and `ref/`: no hash is part of this package's interface).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 195 cases match, `scripts/deps.sh`
passes.
