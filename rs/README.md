# bend-osdev-rs

Reed-Solomon codes over GF(2^m): systematic encoding, and decoding of
errors and erasures with the Berlekamp-Massey algorithm, the Chien search
and Forney's formula, the counterpart of the kernel's Reed-Solomon
library. Every parameter of a code is a parameter here: the field (any
primitive field polynomial of bend-osdev-gf's GF(2^m)), the first
consecutive root, the root spacing and the number of parity symbols, with
named codes as defaults.

Written from:

* W. A. Geisel, "Tutorial on Reed-Solomon Error Correction Coding", NASA
  Technical Memorandum 102162, Lyndon B. Johnson Space Center, August 1990
  (https://ntrs.nasa.gov/api/citations/19900019023/downloads/19900019023.pdf):
  the code's parameters (section 3.3, table 3.3-1) and generator
  g(X) = (X + (alpha^G)^FCR) ... (X + (alpha^G)^(FCR+2t-1)) (section
  3.3.1); systematic encoding CK(X) = X^(n-k) M(X) mod g(X) (section 3.1,
  table 3.1-1, and appendix A's shift-register divider); the syndromes
  (section 4.2.1); the Chien search (section 4.4.1); the corrected word
  (section 4.6); erasures and the modified syndromes (chapter 5, section
  5.3.3); and the (15,9) example used as test vectors throughout
  (sections 3.3.1, 3.3.2, 4.2.1, 4.3.1.1, 4.4.1, 4.6 and chapter 5);
* J. L. Massey, "Shift-Register Synthesis and BCH Decoding", IEEE
  Transactions on Information Theory, vol. IT-15, no. 1, January 1969,
  pp. 122-127 (http://crypto.stanford.edu/~mironov/cs359/massey.pdf): the
  LFSR synthesis algorithm (section III, steps 1 to 6), its use for BCH
  and Reed-Solomon decoding (section V, Theorem 5 and its corollary), and
  the error values from equations 24 to 29, from which Forney's formula is
  derived in `forney.bend`; figure 2's example sequence;
* CCSDS 131.0-B-5, "TM Synchronization and Channel Coding", Recommended
  Standard (Blue Book), September 2023 (https://ccsds.org/Pubs/131x0b5.pdf),
  section 4.3: the field polynomial x^8 + x^7 + x^2 + x + 1 and the
  generator's roots alpha^(11 j), j = 128 - E .. 127 + E, for E = 16 and
  E = 8, in the conventional representation (the dual-basis
  transformation of the standard is not implemented).

Massey cites R. T. Chien's and G. D. Forney's papers (IEEE Trans. IT-10,
1964, and IT-11, 1965); they were not read, and the Chien search and the
error values are implemented from Geisel's and Massey's descriptions. No
kernel source was read. Python's reedsolo was to be compared with if
installed; it is not installed here (nothing was installed), and its PyPI
page does not document the meaning of its fcr, prim and generator
parameters, so the differential test uses an independent model instead
(see Tests).

## Files

| File | Holds |
|---|---|
| `poly.bend` | `RsPoly`: polynomials over GF(2^m), lowest degree first |
| `arith.bend` | `RsGf.pow_nat`, `RsGf.inv`, `RsGf.div`: powers and inverses in few products |
| `code.bend` | `RsCode` and its parameters, the roots and generator, the named codes |
| `encode.bend` | `RsError`, `Rs.mask`, the shift-register encoder, `Rs.parity`, `Rs.codeword`, `Rs.encode` |
| `syndrome.bend` | `Rs.eval_word`, `Rs.syndromes` |
| `bm.bend` | `RsLfsr`, `RsBm.lfsr`: Massey's LFSR synthesis (Berlekamp-Massey) |
| `chien.bend` | `RsChien.roots`: the Chien search |
| `forney.bend` | `RsForney.value`: one error value |
| `rs.bend` | the decoder: `RsFix`, `RsFixed`, `RsOpts`, `Rs.plan`, `Rs.apply`, `Rs.check`, `Rs.correct_with`, `Rs.correct`, `Rs.decode`, `Rs.inject` |

## API

Symbols are `U32`s read modulo 2^m. Words are `List<&2, U32>`, highest
power first, as transmitted: the message symbols, then the 2t parity
symbols. A word may be shortened (a message of fewer than k symbols: the
missing leading ones count as zero and are not sent); its length npos is
more than 2t and at most n = 2^m - 1. Its last symbol is position 0 (a
power of X); erasures are given as indexes into the word (0 the first
symbol).

| Def | Meaning |
|---|---|
| `RsCode{field, fcr, prim, nroots}`, `Rs.code(f, fcr, prim, nroots)` | a code: the field (a `GfmField`, whose element x must be primitive), the first consecutive root FCR, the root spacing alpha^G = alpha^prim, and 2t |
| `Rs.field`, `Rs.fcr`, `Rs.prim`, `Rs.nroots`, `Rs.n`, `Rs.k` | the parameters; n = 2^m - 1, k = n - 2t |
| `Rs.beta(c)`, `Rs.beta_inv(c)`, `Rs.roots(c)`, `Rs.generator(c)` | alpha^G and its inverse; the 2t roots; g(X), lowest coefficient first |
| `Rs.gf256()`, `Rs.gf256_ccsds()` | the fields 0x11D and 0x187 |
| `Rs.rs255_223()` | RS(255,223) over 0x11D, FCR = 1, alpha^G = alpha, 32 parity symbols |
| `Rs.rs8_p16()` | an 8-bit code over 0x11D with 16 parity symbols, FCR = 0 |
| `Rs.ccsds()`, `Rs.ccsds_e8()` | CCSDS's E = 16 and E = 8 codes (FCR 112 and 120, alpha^11) |
| `Rs.geisel15_9()` | Geisel's (15,9) example code over GF(16) |
| `Rs.gf4()`, `Rs.gf8()`, `Rs.small4()`, `Rs.small8()` | GF(4) and GF(8); the codes with 2 and 4 parity symbols over them (used by the laws) |
| `RsError`: `RsBadLength{len}`, `RsTooManyErasures{count}`, `RsBadErasure{index}`, `RsUncorrectable{}` | why encoding or decoding failed |
| `Rs.mask(c, w)` | every symbol modulo 2^m |
| `Rs.parity(c, msg)`, `Rs.codeword(c, msg)` | the parity symbols; the (masked) message followed by them |
| `Rs.encode(c, msg)` | `Done` of the codeword of at most k symbols, else `Fail{RsBadLength}` |
| `Rs.eval_word(f, w, x)`, `Rs.syndromes(c, w)` | the word as a polynomial at x; S_FCR .. S_(FCR+2t-1) |
| `RsLfsr{conn, len}`, `RsBm.lfsr(f, seq)` | the shortest LFSR generating `seq` (connection polynomial C(D), lowest first, and length L) |
| `RsChien.roots(f, lam, binv, npos)` | the positions p < npos with lam(binv^p) = 0 |
| `RsForney.value(f, omega, dpsi, fcr, beta, binv, p)` | the error value at position p (`None` if the derivative is zero there) |
| `RsFix{pos, value}`, `Rs.plan(c, synd, eras, npos)` | the corrections for these syndromes and erasure positions |
| `Rs.apply(c, fixes, w)` | the word with the corrections added |
| `Rs.check(c, len, eras)` | `None` if a word of `len` symbols with these erasures can be decoded, else `Some` of the reason |
| `RsOpts{verify}`, `Rs.opts()` | a policy: whether to check that the corrected word's syndromes are zero (the default: yes) |
| `RsFixed{word, count}`, `Rs.correct_with(opts, c, w, eras)`, `Rs.correct(c, w, eras)` | the corrected word and the number of symbols changed |
| `Rs.decode(c, w, eras)` | the message of a received word |
| `Rs.inject(w, i, v)` | a test helper: v added to the symbol at index i |
| `RsPoly.add(f, p, q)`, `RsPoly.scale(f, c, p)`, `RsPoly.shift(k, p)`, `RsPoly.mul(f, p, q)`, `RsPoly.trunc(n, p)`, `RsPoly.eval(f, p, x)`, `RsPoly.deriv(p)` | polynomials over the field (`poly.bend`), lists of coefficients lowest degree first (trailing zeros allowed): p + q, c p, x^k p, p q, p mod x^n, p(x), the formal derivative |
| `RsPoly.is_zero(f, p)`, `RsPoly.norm(f, p)`, `RsPoly.deg(p)` | whether every coefficient is 0; p without its trailing zeros; the degree of a normalised polynomial (0 for zero) |
| `RsPoly.locator(f, rs)`, `RsPoly.from_roots(f, rs)` | the product of (1 + r x), and of (x + r), over the elements r |

Decoding fails (`RsUncorrectable`) when 2 (errors) + (erasures) > 2t, when
the locator does not have as many roots in the word as its degree, when an
error value cannot be computed, or, under the default policy, when the
corrected word's syndromes are not zero.

## Extension points

* **Codes:** any field, FCR, root spacing and number of parity symbols;
  the named codes are defaults, not limits. A field polynomial must be
  primitive (x must generate the field), which gf's named fields are.
* **Policy:** `RsOpts` turns off the final syndrome check (Geisel's
  optional sixth stage) for speed.
* **Fast paths:** the encoder and syndromes use gf's bit-level
  multiplication; gf's log/exp tables, or a table-driven encoder, compute
  the same symbols faster and can be tied to these by the laws' vectors or
  a differential test.
* **CCSDS's dual basis:** CCSDS transmits symbols in a dual-basis
  representation (its section 4.3); that transformation is a byte map
  around `encode` and `decode`, not implemented yet.
* **Byte strings:** words are symbol lists; for 8-bit codes, a wrapper
  over bytes' `Octets` (one symbol per byte) is a small addition.

## Laws

`LAWS.bend`, proved for every input:

* `encode_short`, `codeword_message`: for every code, a message of at
  most k symbols encodes to its codeword, which begins with the (masked)
  message;
* `small4_syndromes`, `small4_roundtrip`, `small4_error`,
  `small4_erasure`: for the GF(4) code with 2 parity symbols (t = 1), for
  every message symbol: the codeword's syndromes are zero, it decodes to
  the message, and so it does with any symbol changed by any value (one
  error, at any index; past the end changes nothing), or with any one
  symbol erased and changed;
* `small8_syndromes_linear`, `small8_parity_linear`: for the GF(8) code
  with 4 parity symbols (t = 2), syndromes and parity are linear, for
  words and messages of every length;
* `small8_codeword_syndromes`, `small8_roundtrip`: every codeword of every
  message of up to k = 3 symbols has zero syndromes, and decodes to its
  message;
* `inv_gf8`, `inv_gf16`, `v_inv_bch13`: a a^-1 = 1 for every nonzero
  element of GF(8) and GF(16), and gf's vector 1234^-1 = 2297 in GF(2^13);
* vectors: Geisel's (15,9) example (generator, codeword, syndromes,
  sigma(X), Chien search, the corrected word, the erasure example, and a
  word with too many errors), Massey's figure 2, parity of the named
  8-bit codes from the independent model, and each of `Rs.check`'s
  refusals.

How: the small codes' encoder and decoder read every symbol modulo 2^m,
so each law first masks the message (and the injected change), then
splits the symbol into its 32 bits and tries the low m bits, computing
each case in a def of its own on literals (`gen/proof.py` writes these
parts; `python3 gen/proof.py --check` fails if a generated part is not
what it writes). The GF(8) laws are proved by induction (Horner's rule
and the shift register are linear, from (x + y) k = x k + y k for each
constant k, tried on all 64 pairs), and every message is a sum of
messages with one nonzero symbol, whose codewords are computed. No law of
another package is needed.

`LAWS_errors.bend`, proved for every input in `PROOF_errors.bend` (a pair
of its own, checked in a process of its own: its proofs take in
`PROOF.bend`'s, whose linearity and codeword laws they use, and 1079
computed patterns), for the GF(8) code with 4 parity symbols (t = 2):

* `small8_syndromes_shift`: for every message of up to k = 3 symbols and
  every word e as long as its codeword, the codeword plus e
  (`RsPoly.add`) has e's syndromes;
* `small8_decode_shift`, the reduction: for every message of 3 symbols
  and every word e of 7 symbols that decodes, alone, to the zero message,
  the codeword plus e decodes to the message. The decoder's corrections
  are a function of the syndromes (`Rs.plan`), which are e's; applying
  them to the codeword plus e adds them to e; and the final check reads
  the corrected word's syndromes, which are e corrected's;
* `small8_two_errors`: every codeword of a message of 3 symbols with any
  two of its symbols changed by any values (`Rs.inject` twice: two
  errors, one or none, since the indexes may be equal, a value may be
  zero, and an index past the end changes nothing) decodes to its message.
  So every pattern of at most t = 2 errors is corrected, for all 512
  messages.

How: a codeword with two symbols changed, read modulo 2^3 as the decoder
reads it, is the codeword plus the pattern of the two changes; each of the
1079 patterns of at most two errors (1 + 49 + 1029) is corrected alone in
a def of its own, on literals (`proof_pat8.bend`, written whole by
`gen/proof.py`), and the law takes the changes apart into them: each
value's low three bits, then each index, then the pattern rewritten into
its list of symbols. Closed facts the generic steps need (the zero word
passes the final check) are computed in defs of their own and rewritten
in: `--verdict`'s kernel computes closed terms far faster than terms with
unknowns, and runs out of fuel on such a computation inside a proof about
unknown words.

Not proved: that every error pattern of weight at most t is corrected for
the other codes beyond t = 1, and for the GF(8) code's shortened words
(messages of 1 or 2 symbols, words of 5 or 6) and its errors with
erasures; they are left to the tests (see Tests). The method above takes
one def per pattern, so each shortened length needs patterns of its own
(526 and 778 of them), and the larger codes have far more patterns than
one def each can cover (Geisel's (15,9) code, t = 3, has 1,559,476 of
weight at most 3).

## Tests

`check.bend` checks Geisel's example step by step (generator, codeword,
syndromes, Berlekamp-Massey, Chien search, correction with and without
erasures, and failure with too many errors), Massey's figure 2, every
error pattern of weight at most 2 (every pair of positions and every pair
of values) on three messages of the GF(8) code with t = 2 (1792, 1792 and
960 patterns) and on one message of Geisel's code (30720), every set of
erasures up to 2t on two codes, and the refusals. `ref/run.sh` (76 cases
with the default seed) compares encoding and decoding with errors and
erasures (sometimes more than the code corrects) on Geisel's code,
RS(255,223), the 16-parity 8-bit code, both CCSDS codes, and codes over
GF(8), GF(32) and GF(2^13), with an independent model in `ref/gen.py`
(long division instead of a shift register, and Peterson's direct method
with Gaussian elimination instead of Berlekamp-Massey and Forney).

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`).

## Status

Bend 2.0.37: `PROOF.bend` and `PROOF_errors.bend` ALL PROOFS CHECK,
`--verdict` ALL PROOFS CHECK for both, `check.bend` passes, `ref/run.sh`
76 cases match, `scripts/deps.sh` passes. `PROOF_errors.bend` takes in
`PROOF.bend`'s proofs: alone it checks in about 10 minutes and 1.2 GB
peak, and its `--verdict` takes about 28 minutes (the kernel's part about
18) at the same peak; `PROOF.bend`'s is about 1 GB and 2 minutes.
