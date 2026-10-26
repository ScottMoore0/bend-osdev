# bend-osdev-gf

Finite-field arithmetic: GF(2^8) with the reduction polynomial as a
parameter (AES's and Reed–Solomon's as named defaults), its logarithm and
exponential tables, GF(2^128) in the three bit orders GCM, CMAC/LRW and XTS
use, and GF(2^m) for the small m of BCH codes. It is the field layer for
Reed–Solomon, BCH, RAID-6, GCM and LRW.

Written from the mathematics (GF(2)[x] modulo a polynomial) and the public
specifications: FIPS 197 section 4 (AES's field and its worked products),
NIST SP 800-38D (GCM's bit order and Algorithm 1), NIST SP 800-38B and RFC
4493 (CMAC's subkey doubling), IEEE Std 1619 section 5.2 (XTS's
multiplication by α), the GCM specification's test cases (McGrew and Viega),
and Lin and Costello, *Error Control Coding* (primitive polynomials for
GF(2^m)). No GPL source was read.

## Files

| File | Holds |
|---|---|
| `gf.bend` | GF(2^8): `Gf8Field`, the named fields, add, multiply, xtime, power, inverse, divide, exponential and logarithm (the reference, on a byte's eight bits) |
| `tables.bend` | the table-driven fast path for GF(2^8): `Gf8Tab`, exp/log tables, multiply, inverse, divide through them |
| `gf128.bend` | GF(2^128): `Gf128`, GCM's multiplication and GHASH, multiplication by x in each bit order, the big-endian product |
| `gfm.bend` | GF(2^m), 2 ≤ m ≤ 16: `GfmField`, the named BCH fields, add, multiply, power, inverse, divide, exponential and logarithm |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`PROOF.bend` is written by `gen/proof.py`) |
| `LAWS_gfm.bend`, `PROOF_gfm.bend` | a GF(2^m) law whose proof needs none of `PROOF.bend`'s, in a pair of its own so that a proof elsewhere can use it without importing `PROOF.bend` (rs does) |
| `proof_tab.bend` | the tables' proof helpers: the fills as lists through bend-osdev-array's laws, the exp table's entries, U32 and `Nat` counting |
| `proof_tab_cases.bend` | the named fields' facts for the table proofs, by computation (written by `gen/proof_tab.py`) |

## API

GF(2^8) (`gf.bend`). Elements are bytes in `U32`; only an argument's low 8
bits are read, and every result is below 256.

| Def | Meaning |
|---|---|
| `Gf8Field{poly, gen}` | a field: the polynomial with all nine bits (0x11B is 283), and a generator |
| `Gf8.aes()`, `Gf8.rs()`, `Gf8.raid6()` | x^8+x^4+x^3+x+1 (0x11B) with generator 3; x^8+x^4+x^3+x^2+1 (0x11D) with generator 2 (`raid6` is `rs`) |
| `Gf8.poly(f)`, `Gf8.gen(f)` | the field's parameters |
| `Gf8.elt(a)`, `Gf8.is_zero(a)` | the element a (its low byte); whether it is 0 |
| `Gf8.add(a, b)`, `Gf8.sub(a, b)` | XOR |
| `Gf8.mul(f, a, b)`, `Gf8.xtime(f, a)` | the product; a times x |
| `Gf8.pow(f, a, n)` | a^n for a `Nat` n (a^0 = 1) |
| `Gf8.inv(f, a)`, `Gf8.div(f, a, b)` | a^254 (0 for 0); a times b's inverse |
| `Gf8.exp(f, i)`, `Gf8.log(f, a)` | gen^i; the least i < 255 with gen^i = a (0 for a = 0) |
| `Gf8Bits`, `Gf8Bits.of`, `Gf8Bits.to`, `Gf8Bits.mul`, ... | a byte as eight `Bool`s, and the operations on it (the representation the laws are proved on) |

Tables (`tables.bend`): `Gf8Tab.new(f)` builds `exp[i] = gen^i` (i < 510)
and `log[a]`; `Gf8Tab.mul`, `Gf8Tab.inv`, `Gf8Tab.div`, `Gf8Tab.exp`,
`Gf8Tab.log` take the table and hand it back beside the result
(`Gf8Tab & U32`), since a `Gf8Tab` holds `Array`s and has one owner.
`Gf8Tab.exp_table(f)` and `Gf8Tab.log_table(f)` give the bare arrays.

GF(2^128) (`gf128.bend`):

| Def | Meaning |
|---|---|
| `Gf128{w0, w1, w2, w3}` | a 16-byte block as big-endian words (byte 0 is the top byte of `w0`); the type is open |
| `Gf128.zero()`, `Gf128.of_words`, `Gf128.words`, `Gf128.xor`, `Gf128.is_eq` | building and comparing |
| `Gf128.of_octets(o)`, `Gf128.to_octets(x)`, `Gf128.hex(x)` | 16 bytes (`Fail{Gf128BadLength{n}}`, a `Gf128Error`, otherwise); hex text |
| `Gf128.mul_gcm(x, y)` | GCM's product (SP 800-38D, Algorithm 1) |
| `Gf128.mul_x_gcm(x)` | x times x in GCM's order (a right shift; 0xE1 on the carry) |
| `Gf128.ghash_update(h, y, x)`, `Gf128.ghash(h, xs)` | one GHASH step (y + x) * h, and GHASH over a list of blocks |
| `Gf128.double_be(x)` | times x in big-endian order: CMAC's subkey doubling, LRW (a left shift; 0x87 on the carry) |
| `Gf128.double_le(x)` | times x in little-endian order: XTS's α (IEEE 1619) |
| `Gf128.mul_be(a, b)` | the product in big-endian order, by Horner's rule over b's bits with `double_be` |

GF(2^m) (`gfm.bend`): `GfmField{m, poly}` (poly with the x^m bit); the
named fields `Gfm.gf16()` (x^4+x+1), `Gfm.gf32()` (x^5+x^2+1),
`Gfm.bch13()` (0x201B) and `Gfm.bch14()` (0x4443), all primitive;
`Gfm.m`, `Gfm.mask` (2^m − 1), `Gfm.elt`, `Gfm.add`, `Gfm.xtime`,
`Gfm.mul`, `Gfm.pow(f, a, e)` (e a `U32`, by squaring), `Gfm.inv`,
`Gfm.div`, `Gfm.exp(f, i)` (x^i) and `Gfm.log(f, a)`.

## Extension points

* **Any GF(2^8):** build a `Gf8Field` with the polynomial and a generator.
  The ring laws hold for every polynomial; inverses and logarithms need an
  irreducible polynomial and a generator of its multiplicative group.
* **Any GF(2^m) up to m = 16:** build a `GfmField`; `exp`/`log` are to base x,
  so they need a primitive polynomial.
* **Fast paths:** `tables.bend` is the first, beside the bit-level reference.
  Others (a 64 KB product table, carry-less multiply on a CPU that has one,
  a 4-bit GHASH table) can be added the same way and tied to the reference.
* **Bit orders:** GF(2^128) has one multiplication per convention, all
  reducing by x^128 + x^7 + x^2 + x + 1; a further convention is one more
  shift function.

## Laws

`LAWS.bend`:

* **GF(2^8), for every polynomial and every input:** multiplication is
  commutative and associative and distributes over addition, 1 is its
  identity and 0 its zero; addition is commutative and associative, 0 is its
  identity and every element its own negative; `xtime` is multiplication by
  x; `pow(a, m + n) = pow(a, m) * pow(a, n)`; the inverse of 0 is 0. These
  are proved on the bits (`gen/proof.py` explains the steps): a Horner step
  is linear, so the product is linear in each factor; every byte is a sum of
  basis elements; commutativity on the basis is computation; associativity
  follows from (x·b)·c = x·(b·c).
* **GF(2^8), for the named fields and every nonzero input:** `a * inv(a) = 1`
  and `exp(log(a)) = a`, checked over all 255 nonzero bytes (32 cases per
  def, to stay within `--verdict`'s fuel).
* **The tables, for the named fields and every input:** the table that
  `Gf8Tab.new` builds is handed back unchanged beside each result (each law
  says what the returned pair *is*, so a caller follows a run of lookups on
  one table), and the result is the reference's: `Gf8Tab.mul(t, a, b)` is
  `Gf8.mul(a, b)` for every `a` and `b` (`tab_mul_aes`, `tab_mul_rs`),
  `Gf8Tab.log(t, a)` is `U32.from_nat(Gf8.log(a))` for every `a`
  (`tab_log_aes`, `tab_log_rs`), and `Gf8Tab.exp(t, i)` is `Gf8.exp(i)` for
  every `U32` `i` below 510 (`tab_exp_aes`, `tab_exp_rs`, with
  `witness_tab_exp`). The method is bend-osdev-blockdev's and
  bend-osdev-ringbuf's: array's `of_list_new` and `of_list_set` turn each
  fill, write by write, into `Arrays.of_list(d, l, 0)` for a Data list `l`
  (`proof_tab.bend`; the exp table's list holds `gen^i` at `i`, for every
  field), and every read is array's `of_list_get`, a literal pair of the same
  table and `l`'s entry. The log table's list is computed for each named
  field and checked against the fill's model; its entry at each byte is
  `Gf8.log` of the byte (256 cases, 32 per def). A product of nonzero bytes
  is then `exp[log a + log b] = gen^(log b + log a) = gen^(log b) *
  gen^(log a)` (`pow_add`) `= b * a` (`exp_log`) `= a * b`; with a zero
  byte the table answers 0, as does `Gf8.mul` (`mul_zero`).
* **GF(2^m):** addition commutes for every field and input; in GF(2^4)
  multiplication commutes (all 256 pairs) and every nonzero element has an
  inverse; in GF(2^5) every nonzero element has an inverse. `LAWS_gfm.bend`:
  for every field and input, a product is unchanged when a factor is first
  reduced to its element (`gfm_mul_elt`).
* **Vectors:** FIPS 197's products ({57}·{83} = {c1}, {57}·{13} = {fe}, the
  xtime chain), the AES inverse of {53}; GCM Test Case 2 (X1 and GHASH);
  the CMAC subkeys K1 and K2 of SP 800-38B D.1; the XTS wrap-around; the
  BCH fields' x^13, order 8191, a product, an inverse and a logarithm; and
  the tables on sample products and inverses.

Not proved for every input:

* **GF(2^128):** vectors only. A law for every input would compute on 128
  symbolic bits through 128 rounds; `ref/run.sh` compares every function
  with an independent model and with Python's `cryptography` (AES-GCM tags,
  AES-CMAC, AES-XTS), and the vectors fix the bit orders against each other.
* **The tables, beyond the named fields' products, logarithms and
  exponentials:** `Gf8Tab.inv` and `Gf8Tab.div` are tied to the reference
  by vectors, by the exhaustive check at run time in `check.bend` (all
  65,536 products and 256 inverses of both named fields agree) and by
  `ref/run.sh`. Their laws would follow the product's, with the further step
  `exp[255 - log a] = a^254`, which needs `gen^255 = 1` and powers of
  powers; that step is not done yet. The tables of a field given as a
  parameter (any `Gf8Field`) are not proved: they are right only when the
  generator generates the field, and `--verdict`'s kernel compares
  `Gf8Tab.exp_table(f)` with its fill by running the fill, which it can do
  for a named field (both sides closed) but not for a field `f` given as a
  variable (it runs out of fuel), so each table's first step is stated per
  field (`proof_tab_cases.bend`).
* **GF(2^m) beyond the small fields:** vectors and `ref/run.sh`.

## Dependencies

bend-osdev-bytes (`gf128.bend`'s octet conversions) and bend-osdev-array,
whose laws the table proofs use (`proof_tab.bend`; no run-time code
imports it).

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`).

## Tests

`ref/run.sh` (764 cases with the default seed) compares, on random inputs:
GF(2^8) products, inverses, quotients, powers, logarithms, xtime and sums,
reference and table-driven, in both named fields; GF(2^m) products,
inverses, exponentials and logarithms in all four named fields; GF(2^128)
products in GCM and big-endian order and every doubling, against an
independent model (carry-less multiplication and reduction, written in
`ref/gen.py`), whose GCM product is also checked against SP 800-38D's
Algorithm 1 literally; and GHASH, CMAC's K1 and XTS's second tweak against
Python's `cryptography` package.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(3.1 minutes, 0.75 GB peak; `--verdict` 5.9 minutes, 0.76 GB peak) and
`PROOF_gfm.bend` (1 s, 0.12 GB peak; `--verdict` 1 s, 0.13 GB peak) ALL
PROOFS CHECK, with and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 764 cases match, `scripts/deps.sh` passes.
`PROOF.bend` takes about 3 minutes to check and its kernel check about 3
minutes more (WSL2).
