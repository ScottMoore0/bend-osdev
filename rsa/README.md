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
| `keys.bend` | the keys' raw byte form (each integer as a four-byte length and its shortest bytes; the reader refuses any other form of an integer) |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `LAWS_prim.bend`, `PROOF_prim.bend` | the primitives' laws (RSAVP1 undoes RSASP1 and RSADP undoes RSAEP, by the CRT and in the first form, for every key `Rsa.private_of` accepts with prime p and q), and their proofs |
| `gen/proof_prim.py` | writes `PROOF_prim.bend` (Nat chains by `scripts/natproof.py`) |
| `LAWS_sign.bend`, `PROOF_sign.bend` | the primitives on octet strings undo each other, and RSASSA-PKCS1-v1_5's signatures verify, for every such key; and their proofs |
| `LAWS_pss.bend`, `PROOF_pss.bend` | RSASSA-PSS's signatures verify, for every such key; and its proof |
| `gen/proof_sign.py` | writes `PROOF_sign.bend` and `PROOF_pss.bend` (Nat chains by `scripts/natproof.py`) |
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
| `keys.bend` | `RsaKeys.public_to`, `RsaKeys.private_to`, `RsaKeys.public_of`, `RsaKeys.private_of` (`RsaBadFormat` for a malformed form, including an integer not in its shortest form, `RsaBadKey` for a key that fails the checks); `RsaField{x, rest}`, `RsaField.x`, `RsaField.rest` |

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

`LAWS.bend` has 13 laws, all proved (`PROOF.bend`) and all accepted by
`--verdict`; `LAWS_prim.bend` has 6, `LAWS_sign.bend` 3 and
`LAWS_pss.bend` 1, likewise (`PROOF_prim.bend`, `PROOF_sign.bend`,
`PROOF_pss.bend`).

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
    RSAVP1 undoes RSASP1 on the encoded message (hypotheses;
    `LAWS_sign.bend`'s `pkcs1_sign_verify` discharges them for every key
    `Rsa.private_of` accepts with prime p and q);
  * `public_form_read_write`, `private_form_read_write`: every form the
    reader accepts is the form the writer writes for the key it read
    (`RsaKeys.public_to(k)` is the bytes read, for every byte string the
    reader takes as k; where it refuses, both sides refuse alike), with no
    hypotheses: the reader takes an integer only where the form holds
    exactly the field the writer writes for it, its four-byte length and
    then its shortest bytes (`keys.bend`), and the field and the bytes
    after it are then the form (bytes' `octets_take_drop`);
  * `public_form_write_read`, `private_form_write_read`: so the form
    written for a key the reader read is read as the same key;
  * `public_form_round_trip_if`, `private_form_round_trip_if`: the keys'
    raw forms (`keys.bend`) read back from the other side: the form of
    `RsaPublic{n, e}` is read as `Rsa.public_of(n, e)`, and the form of a
    private key as `Rsa.private_of(n, e, d, p, q)` (the key checked and its
    CRT values recomputed, whatever dP, dQ and qInv it held), for every key
    whose integers each read back from their shortest big-endian bytes
    (hypotheses `hn`, `he`, ...: `BnNat.of_octets(BnNat.to_octets_min(x))`
    is x) and whose byte counts fit the four-byte length field (`ln`,
    `le`, ...: `U32.from_nat` of each count is exact). Each field is read
    back from bytes' laws: the length at offset 0 of the joined bytes,
    then the integer's bytes cut at that length, and the field compared
    with the writer's. pubkey's RSA instance states its pk_format law from
    the public one.
* **For every key** (`LAWS_prim.bend`): for every key `Rsa.private_of(n,
  e, d, p, q)` accepts (`Done{sk}`) whose p and q are primes (bignum's
  `bnlaw.prime` of their values: `Rsa.private_of` does not test primality,
  key generation's Miller-Rabin does), with valid integers (bignum's
  `bnlaw.valid`, which every number bignum's public defs make is), and every
  valid representative m below n:
  * `vp1_sp1`: RSAVP1(RSASP1(m)) = m, RSASP1 by the CRT (dP, dQ, qInv);
  * `dp_ep`: RSADP(RSAEP(m)) = m, RSADP by the CRT;
  * `ep_dp_plain`, `dp_plain_ep`: the same with RSADP in the first form (n,
    d);
  * `dp_crt_plain`: RSADP by the CRT has the first form's value, c^d mod n;

  all as values (bignum's `bnlaw.value`; a result may differ from m in zero
  limbs on top). The number theory is bignum's `LAWS_rsa.bend` (`rsa_nat`,
  `rsa_nat_rev`, `crt_exp_nat`); its hypotheses are the checks
  `Rsa.private_of` makes, read through bignum's value laws: n = p q,
  `is_odd(n)` (so p q is odd, `is_odd_value`, and neither prime is 2, which
  the CRT form needs: d mod 1 = 0), d e = 1 modulo p - 1 and modulo q - 1
  (`BnMod.mul`, `BnNat.mod` and `BnNat.sub`'s values), and qInv =
  `BnMod.inv(q, p)` with q qInv = 1 mod p (`inv_value`), which makes p and
  q distinct (`mod_inv_ne`). The key's dP, dQ and qInv are the ones
  `Rsa.private_of` computes (the accepted key is the `RsaPrivate` of its
  integers with them), and every result is below n (`nat_mod_lt`), so the
  range checks pass. A key from `Rsa.private_of_primes` (d = e^-1 mod lcm(p
  - 1, q - 1), as `RsaKeygen.generate` makes it) is one `Rsa.private_of`
  accepts, with that d (`private_of_primes_key`), so the laws hold for it
  too: its d is checked modulo p - 1 and q - 1 like any other (bignum's
  `mod_lcm_l` and `mod_lcm_r` are why such a d passes).
* **For every key, on octet strings and for the signature schemes**
  (`LAWS_sign.bend`, `LAWS_pss.bend`), for every such key (`Rsa.private_of`
  accepts it, p and q prime, the integers valid):
  * `ep_dp_octets`, `dp_ep_octets`: wherever `Rsa.dp_octets` (OS2IP,
    RSADP or RSASP1 by the CRT, I2OSP to k bytes) gives a string, RSAEP (or
    RSAVP1) on octet strings gives its input back, and the other way:
    bignum's `to_octets_len` and `to_octets_value` read the k-byte result
    back as the number, which is below n, and `to_octets_of_value` writes
    the value back as the input;
  * `pkcs1_sign_verify`: an RSASSA-PKCS1-v1_5 signature verifies, for every
    hash, DigestInfo prefix and message (where signing refuses, both sides
    refuse alike): `pkcs1_sign_verify_if` without hypotheses on the
    primitives;
  * `pss_sign_verify`: an RSASSA-PSS signature verifies, for every mask
    generation function, message and salt, and every hash whose digest of
    M' is as long as its digest of M (`hdg`, as in `pss_round_trip`): the
    encoding has emLen bytes, so I2OSP of RSAVP1's value to emLen bytes is
    the encoding again, which `pss_round_trip` accepts.
* **Small-parameter exhaustive** (`gen/exhaustive.py`): `toy_round_trip`:
  for the key p = 5, q = 11, e = 3, every message below 55 goes through
  RSADP and back through RSAEP and the other way, and the CRT's RSADP equals
  the first form.

**Not proved, and tested:** that p and q are primes, which the laws above
take as hypotheses (`pp`, `pq`): `Rsa.private_of` does not test it, and
key generation's Miller-Rabin is a probabilistic test, whose "composite"
answer is bignum's open question (its README). The encryption schemes'
decrypt-after-encrypt (RSAES-OAEP, RSAES-PKCS1-v1_5) for every key is not
stated; it would follow in the same way from `dp_ep_octets` and the
encodings' round trips (`oaep_round_trip`, `es15_round_trip`).
`check.bend` and `ref/run.sh` test all of it against cryptography.

**The key reader is strict.** An integer whose bytes are not its
shortest form is refused with `RsaBadFormat` (the malformed-form error; no
new error): a field with a leading zero byte (`00000002 00c5 00000001 03`,
n = 197 written with a leading zero byte), and zero written as a byte
(`00000001 00`); zero is no bytes (`00000000`), which is what
`BnNat.to_octets_min` writes for it. The reader compares each field with
the field the writer writes for the integer it read, so that is exactly
what it accepts, and the read-write laws above hold for every byte string.

The conditional form laws' hypotheses are not proved here:

* that an integer reads back from its shortest bytes is a law bignum would
  state, and it needs a number's bit length (`BnNat.byte_len`, from its top
  limb's bits) related to its limbs, which bignum does not reason about for
  every value (its README, Laws). It holds for every `BnNat` without zero
  limbs on top, which is every value bignum's arithmetic, `of_hex` and a
  shortest form make, and for every key the reader returns (the read-write
  laws). The other half, that every byte string without a leading zero
  byte is the shortest form of its number (so the reader refuses only the
  forms above), is the same reasoning; `check.bend` tests it, and the
  differential test reads back every key cryptography makes.
* that a byte count fits the length field is a bound of 2^32, which a key
  read from a form always meets but which cannot be stated as a closed
  number (u32's README, Laws, "Stating the bounds"); the read-write laws
  need no such bound, since their lengths are the form's own.

## Tests

* `check.bend`: an RSA-2048 key (e = 65537) made by Python's cryptography
  for the file, with cryptography's signatures of "abc" over SHA-256:
  RSASSA-PKCS1-v1_5 signing gives cryptography's signature exactly, and
  verifies it (and refuses another message); RSASSA-PSS verifies
  cryptography's signature (MGF1-SHA-256, 32-byte salt) and refuses
  another message, and verifies its own; RSAES-OAEP and RSAES-PKCS1-v1_5
  round trips; RSADP by the CRT equals the first form (and Python's pow);
  the raw key forms read back; short forms read (n = 197, e = 3, and the
  key p = 5, q = 11, e = 3), and written back the same; a leading zero byte
  in n, in e and in a private key's d refused, n = 0 written as no bytes
  read (and then refused as a key), as a byte refused; an out-of-range
  ciphertext refused.
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
integers, Montgomery exponentiation, inverses, Miller-Rabin), `u32` (its
value laws, in the proofs: a word comparison is the comparison of values),
`bend-collections-laws-crypto@1.0.0.0` (SHA-256 and SHA-512 for
`check.bend` and `ref/`: no hash is part of this package's interface).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (13 laws; about 100 s, peak
0.48 GB), `--verdict` ALL PROOFS CHECK; Bend 2.0.39: `PROOF_prim.bend`
ALL PROOFS CHECK (6 laws; about 7 s, peak 0.78 GB), `--verdict` ALL PROOFS
CHECK (about 24 s, peak 0.79 GB); `PROOF_sign.bend` ALL PROOFS CHECK (3
laws; about 10 s, peak 0.88 GB), `--verdict` ALL PROOFS CHECK (about 28 s,
peak 0.89 GB); `PROOF_pss.bend` ALL PROOFS CHECK (1 law; about 117 s, peak
1.10 GB: it imports `PROOF.bend` for `pss_round_trip`), `--verdict` ALL
PROOFS CHECK (about 341 s, peak 1.13 GB); `check.bend` passes, `ref/run.sh`
195 cases match (the whole `VERDICT=1 scripts/check.sh rsa` about 580 s,
peak 1.15 GB, on 2.0.37; about 1014 s, peak 1.13 GB, on 2.0.39 with the
new proof files), `scripts/deps.sh` passes.
