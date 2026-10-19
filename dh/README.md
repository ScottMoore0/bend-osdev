# bend-osdev-dh

Finite-field Diffie-Hellman as NIST SP 800-56A Rev. 3 specifies it: key
pairs, public-key validation (full, partial, and by the Legendre symbol for
safe-prime groups), the FFC DH primitive and the shared secret; and the
named groups of RFC 7919 (ffdhe2048 to ffdhe8192) and RFC 3526 (MODP groups
5 and 14 to 18). Any group (p, g, q) can be given; the named ones are defs
that can be passed as template arguments.

The directory is `dh` and the entry file `dh/dh.bend`; the hub name is
`bend-osdev-dh`. As an instance of crypto's key-agreement interface, DH is
in bend-osdev-pubkey (`pubkey/dh.bend`).

## Specifications

* NIST SP 800-56A Rev. 3 (*Recommendation for Pair-Wise Key-Establishment
  Schemes Using Discrete Logarithm Cryptography*, April 2018): section 5.6.1.1 (FFC key
  pairs; 5.6.1.1.3's extra random bits for `Dh.private_from_bits`), 5.6.2.3.1
  (full public-key validation, and footnote 22: for a safe-prime group the
  subgroup test may be the Legendre symbol), 5.6.2.3.2 (partial
  validation), 5.7.1.1 (the FFC DH primitive, z = y^x mod p refused when z
  <= 1 or z = p - 1), Appendix C.1 (integers as bytes of p's length).
* RFC 7919 (D. Gillmor, *Negotiated Finite Field Diffie-Hellman Ephemeral
  Parameters for TLS*, August 2016): Appendix A (the ffdhe groups' formula
  p = 2^b - 2^(b-64) + {[2^(b-130) e] + X} 2^64 - 1 and each group's X, g =
  2, q = (p - 1) / 2), section 5.1 (the peer key's range check).
* RFC 3526 (T. Kivinen, M. Kojo, *More Modular Exponential (MODP)
  Diffie-Hellman groups for Internet Key Exchange (IKE)*, May 2003):
  sections 2 to 7 (groups 5, 14, 15, 16, 17 and 18: p = 2^b - 2^(b-64) - 1 +
  2^64 {[2^(b-130) pi] + X}, g = 2).

The primes are not copied from the RFCs' hex: `gen/groups.py` computes them
from the formulas (pi by Machin's formula, e by its series), checks that
each is a safe prime, and writes `groups.bend`; `ref/run.sh` compares them
with the openssl command's named groups.

## Files

| File | Holds |
|---|---|
| `dh.bend` | the errors, groups, private keys, public keys, validation, the primitive and agreement, and the public key's bytes |
| `groups.bend` | the named groups (generated region) |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | ffdhe2048 agreement, validation and refusals, with expected output |
| `gen/groups.py` | writes `groups.bend`'s primes from the RFCs' formulas (`--check` checks them) |
| `gen/exhaustive.py` | writes the small-parameter exhaustive laws and their proofs |
| `ref/gen.py`, `ref/run.sh` | the differential test against the openssl command and cryptography |

Bend imports do not re-export: import the files you use.

## Public interface

| File | Defs and types |
|---|---|
| `dh.bend` | `DhError` (`DhBadPrivateKey`, `DhBadPublicKey`, `DhBadSharedSecret`, `DhBadLength`); `DhGroup{p, g, q}` (open); `DhError.check`; `DhGroup.p`, `.q`, `.len` (p's bytes); `Dh.private_ok(grp, x)` (1 <= x <= q - 1), `Dh.private_of(grp, o)` (big-endian bytes), `Dh.private_from_bits(grp, c, nbits)` (5.6.1.1.3: (c mod (M - 1)) + 1, M = min(2^nbits, q)), `Dh.public(grp, x)` (g^x mod p); `Dh.check_partial` (2 <= y <= p - 2), `Dh.check_full` (and y^q = 1 mod p), `Dh.check_safe` (and the Legendre symbol (y/p) = 1; safe-prime groups only); `Dh.primitive(grp, x, y)` (Z as bytes of p's length), `Dh.agree(grp, x, y)` (full validation, then the primitive), `Dh.agree_safe` (validation by the Legendre symbol); `Dh.public_to(grp, y)`, `Dh.public_of(grp, o)` (exactly p's length, `DhBadLength`; partial validation) |
| `groups.bend` | `DhGroups.ffdhe2048`, `.ffdhe3072`, `.ffdhe4096`, `.ffdhe6144`, `.ffdhe8192`, `.modp1536`, `.modp2048`, `.modp3072`, `.modp4096`, `.modp6144`, `.modp8192` |

Everything named `dh.*` is internal.

## Extension points

* **Any group:** `DhGroup{p, g, q}` is open; a group whose q is not (p -
  1) / 2 needs `Dh.agree` (y^q = 1), the safe-prime groups can use
  `Dh.agree_safe`.
* **Validation** is a choice: `check_partial`, `check_full`, `check_safe`
  are public, and `primitive` takes an already validated key.
* **Private keys** from bytes (`private_of`) or from extra random bits
  (`private_from_bits`, with the size N as a parameter); the randomness is
  the caller's.
* **Formats:** public keys travel as bytes of p's length. Reading the
  groups' or keys' ASN.1 (PKCS #3 DHParameter, X9.42) belongs in an ASN.1
  package.

## Laws

`LAWS.bend` has 4 laws, all proved (`PROOF.bend`) and all accepted by
`--verdict`.

* **For every group and input:** `public_round_trip` (a public key read
  from bytes is read again, the same, from the bytes `Dh.public_to` writes
  for it); `agree_if` (both sides compute the same shared secret wherever
  (g^y)^x = (g^x)^y mod p: the hypothesis).
* **Small-parameter exhaustive** (`gen/exhaustive.py`), in the safe-prime
  group p = 23, q = 11, g = 2: `toy_agree` (both sides agree for every
  pair of private keys in [1, 10]); `toy_check_safe` (validation by the
  Legendre symbol equals validation by y^q mod p = 1 for every y below 23,
  which is footnote 22's claim at that group).

**Not proved, and tested:** that the exponentiations commute for every
group and key ((g^y)^x = g^(xy) = (g^x)^y mod p) is number theory on the
integers bignum's limbs stand for, which is not formalised (bignum's
README); likewise footnote 22's equivalence for every safe prime. Both are
tested on every named group against cryptography (`ref/run.sh`).

## Tests

* `check.bend`: the named groups' sizes; ffdhe2048 public keys of two
  private keys and the shared secret both ways (one by full validation, one
  by the Legendre symbol); full and Legendre validation of a valid key; the
  peer keys 1 and p - 1 refused; a public key of the wrong length refused,
  and one read back from its bytes; a private key of 0 refused.
* `ref/run.sh` (136 cases with the default seed): every named group's p
  against the openssl command's group of that name (`openssl genpkey
  -genparam -pkeyopt group:...`, read with cryptography); for keys made by
  cryptography's DH over each group (private keys of 256 to 2048 bits),
  Bend's public key equals cryptography's and Bend's shared secret equals
  cryptography's exchange, both ways; full and Legendre validation agree on
  valid keys and non-residues; 0, 1, p - 1 and p and a public key of the
  wrong length refused.

## Sizes and speed

Native builds (Bend 2.0.37, WSL2), ffdhe2048 with a 256-bit private key
(through pubkey's instance, 5 repetitions in one program): a public key
about 140 ms; the shared secret, the peer's key validated by the Legendre
symbol, about 160 ms. The exponentiations are bignum's Montgomery method;
validation by the Legendre symbol costs a fraction of y^q mod p.

## Notes on use

None of this is constant-time. Private keys must come from a cryptographic
random source (this package has none).

## Dependencies

`DEPS`: `bytes` (`Octets`), `bignum` (the integers, modular
exponentiation, the Jacobi symbol).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 136 cases match, `scripts/deps.sh`
passes.
