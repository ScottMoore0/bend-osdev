# bend-osdev-bch

Binary BCH codes: encoding as polynomial division over GF(2), and
decoding with the Berlekamp-Massey algorithm and the Chien search, on bits
and on byte strings (NAND sectors and their ECC bytes), the counterpart of
the kernel's BCH library. A code's field GF(2^m) (any primitive field
polynomial of bend-osdev-gf), its t and its first root m0 are parameters,
with named codes as defaults.

Written from:

* J. L. Massey, "Shift-Register Synthesis and BCH Decoding", IEEE
  Transactions on Information Theory, vol. IT-15, no. 1, January 1969,
  pp. 122-127 (http://crypto.stanford.edu/~mironov/cs359/massey.pdf),
  section V: a BCH code's generator has alpha^m0 .. alpha^(m0+2t-1) as
  roots; the syndromes (equations 22 and 23); the error locator is the
  shortest LFSR generating them (Theorem 5 and its corollary), found by
  the section III algorithm; for binary codes the error values are all 1;
* Shan-Yuan Ho, "BCH Codes", April 24, 2010
  (https://math.mit.edu/~shor/18.310/BCH.pdf): the generator as a product
  of minimal polynomials, Q(x) = p(x) p3(x) ... p(2t-1)(x) (section 2,
  equations 3 and 4, with the (15,7) and (15,5) generators), and the
  3-error-correcting example (section 4), used as test vectors;
* W. A. Geisel, "Tutorial on Reed-Solomon Error Correction Coding", NASA
  Technical Memorandum 102162, August 1990
  (https://ntrs.nasa.gov/api/citations/19900019023/downloads/19900019023.pdf),
  section 3.1: systematic encoding as the remainder of D(X) X^(n-k) by
  g(X), the same construction here with coefficients in GF(2).

The decoder's Berlekamp-Massey and Chien search are bend-osdev-rs's
(`bm.bend`, `chien.bend`), which are written from Massey and Geisel; see
that package's README. No kernel source was read.

The NAND defaults are this package's own choice, not taken from a NAND or
controller specification (the vendor documents tried could not be read):
GF(2^13) is the smallest field whose codewords (8191 bits) hold a
512-byte sector (4096 bits) and 13t parity bits for every t up to 16;
the field polynomial is gf's `Gfm.bch13()` (x^13 + x^4 + x^3 + x + 1),
the codes are narrow-sense (m0 = 1), and t is 4, 8 or 16. The bit order
of bytes is a parameter (most significant bit first by default), and the
ECC's last byte is padded with zero bits at its end.

## Files

| File | Holds |
|---|---|
| `code.bend` | `BchCode`, its parameters, the named codes, the roots (cyclotomic cosets) and the generator |
| `bits.bend` | `BchOrder`: bytes as bits and bits as bytes |
| `encode.bend` | `BchError`, the shift-register encoder, `Bch.parity`, `Bch.codeword`, `Bch.encode_bits` |
| `syndrome.bend` | `Bch.syndromes` |
| `bch.bend` | the decoder (`Bch.locate`, `Bch.flip`, `Bch.correct`, `Bch.decode_bits`) and the byte interface (`Bch.encode`, `Bch.decode`) |

## API

Bits are `List<&2, Bool>`, highest power first: the data bits, then the
deg(g) parity bits. A word may be shortened: it has more than deg(g) and
at most n = 2^m - 1 bits, and its last bit is position 0.

| Def | Meaning |
|---|---|
| `BchCode{field, t, m0}`, `Bch.code(f, t, m0)` | a code: the field (a `GfmField` whose element x is primitive), the errors corrected, and the first root's exponent |
| `Bch.field`, `Bch.t`, `Bch.m0`, `Bch.n` | the parameters; n = 2^m - 1 |
| `Bch.nand(t)`, `Bch.nand_t4()`, `Bch.nand_t8()`, `Bch.nand_t16()` | the narrow-sense codes over GF(2^13) for 512-byte sectors |
| `Bch.bch7_4()`, `Bch.bch15_7()`, `Bch.bch15_5()` | the (7,4) code (t = 1) over GF(8), and the (15,7) and Ho's (15,5) codes (t = 2, 3) over GF(16) |
| `BchRoots{exps, elts}`, `Bch.roots(c)`, `Bch.exponents(c)` | g's roots: the cyclotomic cosets of m0 .. m0 + 2t - 1, as exponents and elements |
| `Bch.generator(c)`, `Bch.parity_bits(c)` | g(X) as bits, lowest coefficient first; deg g |
| `BchOrder`: `BchMsbFirst{}`, `BchLsbFirst{}`; `Bch.order()` | which bit of a byte comes first; the default, most significant |
| `Bch.bits_of(o, octets)`, `Bch.octets_of(o, bits)` | bytes as bits; bits as bytes, the last padded with zeros |
| `BchError`: `BchBadLength{len}`, `BchUncorrectable{}` | why encoding or decoding failed |
| `Bch.gen_desc(c)`, `Bch.parity(c, bits)`, `Bch.codeword(c, bits)` | g's coefficients below the leading one; the parity bits; the data then the parity |
| `Bch.encode_bits(c, bits)` | `Done` of the codeword of at most n - deg(g) data bits, else `Fail{BchBadLength}` |
| `Bch.syndromes(c, bits)` | S_m0 .. S_(m0+2t-1) |
| `Bch.locate(c, synd, npos)` | the error positions for these syndromes in a word of `npos` bits |
| `Bch.flip(ps, bits)`, `Bch.flip_at(bits, i)` | the bits at positions `ps` flipped; the bit at index i flipped (a test helper) |
| `Bch.length_ok(c, len)` | deg(g) < len <= n |
| `BchOpts{verify}`, `Bch.opts()` | a policy: whether to check that the corrected word's syndromes are zero (the default: yes) |
| `BchFixed{bits, count}`, `Bch.correct_with(opts, c, bits)`, `Bch.correct(c, bits)` | the corrected word and the number of bits flipped |
| `Bch.decode_bits(c, bits)` | the data bits of a received word |
| `Bch.encode_with(o, c, data)`, `Bch.encode(c, data)` | the ECC bytes of a byte string: its parity bits, packed |
| `BchDecoded{data, ecc, count}`, `Bch.decode_with(o, c, data, ecc)`, `Bch.decode(c, data, ecc)` | the corrected data and ECC bytes (the ECC's padding bits kept as they were) and the number of bits flipped |

Decoding fails (`BchUncorrectable`) when the shortest LFSR is longer than
t, when the locator does not have as many roots in the word as its
degree, or, under the default policy, when the corrected word's syndromes
are not zero; more than t errors are then detected, or corrected to
another codeword when the word is within t of one.

## Extension points

* **Codes:** any field, t and m0 (m0 = 0 includes the root 1); the named
  codes are defaults. Other NAND layouts (1024-byte sectors need m = 14:
  gf's `Gfm.bch14()`) are one `Bch.code` away.
* **Bit order and padding:** `BchOrder` is a parameter of the byte
  interface; a controller that packs ECC bits differently (reversed, or
  padded at the front) needs another packing beside `Bch.octets_of`.
* **Speed:** the encoder is bit-serial and the syndromes Horner's rule
  over bits; table-driven encoders (several bits a step) and syndromes
  from the remainder modulo each minimal polynomial compute the same
  results and can be tied to these by the laws' vectors or a differential
  test.

## Laws

`LAWS.bend`, proved for every input:

* `encode_short`, `codeword_message`: for every code, at most n - deg(g)
  data bits encode to their codeword, which begins with the data bits;
* `small7_syndromes`, `small7_roundtrip`, `small7_error`: for the (7,4)
  code (t = 1) and every message of up to 4 bits (shortened or not): its
  codeword's syndromes are zero, and the codeword decodes to the message,
  as it is and with any one of its bits flipped;
* `small15_syndromes`, `small15_roundtrip`: for the (15,7) code (t = 2)
  and every message of up to 7 bits: its codeword's syndromes are zero and
  it decodes to the message;
* vectors: the generators of the (7,4), (15,7) and (15,5) codes (the last
  two Ho's), Ho's example corrected, three errors in the (15,7) code
  detected, the 52 and 104 parity bits of the t = 4 and t = 8 NAND codes,
  both bit orders, the padding, and the length refusals.

Not proved: that every pattern of at most t flipped bits is corrected for
codes with t > 1. For the (15,7) code that is 128 messages times 121
patterns; it is tested exhaustively instead (see Tests). The laws' small
cases are computed one def each (the kernel has a step budget per def);
`gen/proof.py` writes them. The t = 16 NAND code's parity size and the
NAND codes' ECC bytes are left to the tests (`check.bend` and `ref/`):
the GF(2^13) generators of those are too large a computation for the
proof checkers.

## Tests

`check.bend` checks the generators, the NAND parity sizes, Ho's syndromes
and correction, every message of the (15,7) code with every pattern of at
most 2 flipped bits (15360 decodes) and every message of the (15,5) code
with every pattern of at most 3 (21760), the ECC of a 512-byte sector for
t = 4 and t = 8, and the sector decoded back with 4, 8 and 16 bits flipped
for t = 4, 8 and 16 and refused with 9 for t = 8. `ref/run.sh` (65 cases
with the default seed) compares bit encoding and decoding on the (15,7),
(15,5), (31,16), (63,39) codes and a (31,20) code with m0 = 0, and
byte encoding and decoding (both bit orders, padding bits flipped too) on
the NAND codes with random sectors of 1 to 512 bytes, with errors up to
and past t, with an independent model in `ref/gen.py` (long division on
integers, and Peterson's direct method with Gaussian elimination instead
of Berlekamp-Massey).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 65 cases match, `scripts/deps.sh` passes.
