# bend-osdev-jitter

The pure core of a CPU Jitter random number generator, after Stephan
Müller's jitterentropy: it takes a list of time deltas (measured elsewhere;
jitterclock reads a clock) and holds the noise processing, the SP 800-90B
health tests, the stuck test and the conditioning. The conditioner is a
parameter: SHA3-256 through the crypto package's hash interface by default
(jitterentropy 3.0 to 3.6), or the XDRBG over SHAKE256 of jitterentropy
3.7.0's documentation.

Nothing here reads a clock: every def takes deltas and a state and answers
a new state, so the same deltas always give the same bytes, and the effects
live in jitterclock.

The directory is `jitter` and the entry file `jitter/jitter.bend`; the hub
name is `bend-osdev-jitter`.

## Sources

Written from the documents below; no jitterentropy source (the library's or
Linux's) was read.

* Stephan Müller, *CPU Time Jitter Based Non-Physical True Random Number
  Generator*, 4 May 2026 (the documentation of jitterentropy 3.7.0, CC BY
  4.0), https://www.chronox.de/jent/CPU-Jitter-NPTRNG.pdf, sections 3.1
  (the entropy collection loop: 256 deltas plus a safety factor of 65,
  times the oversampling rate), 3.1.1 (the insertion buffer: the time
  delta, a one-byte domain separator, the SHA3-256 digest of the hash
  loop's data, zeros to the 1,088-bit rate, so that every insertion runs
  the Keccak permutation; the separators 1, 2 and 3), 3.1.2 (the safety
  factor of 65), 3.1.4 (deltas; the pool's previous contents reused for the
  next block), 3.1.5 (the auxiliary data: the RCT count, the APT count,
  cutoff, window and base), 3.1.6 (the stuck test: the delta and its first
  and second derivatives; stuck deltas not counted; the APT window of 512
  and its cutoffs for alpha = 2^-30 by oversampling rate), 3.1.7 (the
  1,088-bit buffer), 3.2 (bytes as blocks concatenated, the last cut),
  3.3 (one block generated and discarded when a collector is allocated),
  and the change log (appendix G). For the XDRBG option: section 3.1.1
  (the XDRBG conditioning component: the seed as the concatenation of the
  insertion buffers, "XDRBG-256 with SHAKE-256 as XOF", seeding V <-
  XOF(encode(seed, alpha, 0), |V|), reseeding V <- XOF(encode(V' || seed,
  alpha, 1), |V|), generating T <- XOF(encode(V', alpha, 2), l + |V|), V
  the first |V| bits of T and the output the last l, alpha a NULL buffer,
  |V| = 512 bits, l = 256 bits), section 3.1 (its note that "the XDRBG is
  seeded with 512 bits of entropy before the first generation
  operation"), 3.1.7 ("XDRBG-256: 1,088 bits – i.e. the size of the
  SHAKE-256 rate") and appendix G ("Replace SHA3-256 with XDRBG",
  2026-05-04, version 3.7.0).
* John Kelsey, Stefan Lucks and Stephan Müller, *XDRBG: A Proposed
  Deterministic Random Bit Generator Based on Any XOF*, IACR Transactions
  on Symmetric Cryptology 2024(1), pp. 5-34, DOI 10.46586/tosc.v2024.i1.5-34
  (read from NIST's copy, https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=956236):
  section 2.6 (a XOF's output for x and l bits is the first l bits of one
  sequence), section 3 and Algorithm 2 (INSTANTIATE, RESEED, GENERATE),
  section 7.3 (XDRBG-256: SHAKE256, |V| = 512 bits) and appendix B (the
  encoding ENCODE(S, alpha, n) = S || alpha || (n * 85 + |alpha|/8) as one
  byte, alpha at most 84 bytes).
* NIST FIPS 202, *SHA-3 Standard: Permutation-Based Hash and
  Extendable-Output Functions* (August 2015), section 6.2 (SHAKE256 =
  KECCAK[512](M || 1111, d)) and appendix B.2 (Table 6: an XOF's padding
  is 0x1F, zeros and 0x80, or 0x9F for a single byte), and
  NIST's example file *SHAKE-256 sample of 0-bit message*
  (SHAKE256_Msg0.pdf, Cryptographic Standards and Guidelines, examples):
  the output the laws `shake256_empty` and `shake256_empty_second_block`
  take their bytes from.
* NIST SP 800-90B, *Recommendation for the Entropy Sources Used for Random
  Bit Generation* (Turan, Barker, Kelsey, McKay, Baish, Boyle, January
  2018), section 4.4.1 (the Repetition Count Test and its cutoff C = 1 +
  ceil(-log2(alpha) / H)) and section 4.4.2 (the Adaptive Proportion Test,
  window 512 for a non-binary source).
* EWA-Canada for CACI, *Userspace CPU Time Jitter RNG Entropy Source, SP
  800-90B Public Use Document*, version 2, 25 November 2025 (NIST CMVP
  entropy certificate E300): jitterentropy 3.4.1 conditions with SHA3-256
  (its "SHA3-256 Vetted Conditioning Component"), and `JENT_MIN_OSR` is 3.
* *JITTERENTROPY(3)*, Library Functions Manual, 2021-03-08 (as packaged
  with jitterentropy 3.7.0): the library's API takes no time stamps or
  deltas from its caller.

## The conditioner

The conditioner is a template parameter of the core (`JitCore.*`): the
pool's state `~H`, the insertion buffer's size `~bsize`, the pool update
`~update` and the block step `~take` (below). Two are provided:

* **SHA3-256, the named default** (`Jitter.*` over any hash of crypto's
  interface, `JitSha3.*` with SHA3-256 filled in). jitterentropy 3.0 to 3.6
  condition with SHA3-256. The SHA-3-era document (1 July 2022, cited by
  NIST's certificates) could not be read: the URL above now serves the 2026
  version. So the insertion layout is the 2026 document's (delta,
  separator, auxiliary digest, zeros to the rate) with SHA3-256 in place of
  the XDRBG; SHA3-256's rate is the same 1,088 bits. A block is the pool's
  digest, and the next pool starts from it.
* **XDRBG-256 over SHAKE256** (`JitXdrbg256.*`; `xdrbg.bend` over any XOF,
  `shake.bend` for SHAKE256), the 2026 document's (version 3.7.0)
  conditioner. The pool is the XOF fed the insertion buffers as they arrive
  (the same buffer as the default's: delta, separator, SHA3-256 of the
  auxiliary data, zeros to 136 bytes, the SHAKE256 rate). A block
  instantiates the XDRBG from that seed (its first block) or reseeds it
  (after, with the V the block before left), generates 512 + 256 bits, keeps
  the first 512 as V and gives the last 256 as the block, and starts the
  next pool from V. With `JitParams.default()` one block is discarded, so
  the first output comes after two collections, which is how this package
  reads the document's note in section 3.1 (above): seed, generate
  (discarded), reseed, generate. The XDRBG's own parameters
  (`JitXdrbgParams`: |V|, l and the additional input alpha) are open, with
  jitterentropy's as `JitXdrbgParams.default()`.

crypto has a hash interface but no XOF interface, so the XOF interface
(`~X`, `~xinit`, `~xupdate`, `~xread`) and the SHAKE256 adapter live here,
in `shake.bend`, as crypto's `inst_sha3.bend` adapts SHA3-256; neither
crypto's interfaces nor its code change. The Keccak-f[1600] permutation and
the absorbing are bend-collections-laws-crypto@1.0.0.0's (the same package
crypto's SHA3-256 comes from): no hub package publishes SHAKE, so the
adapter uses that package's permutation (`keccak/permutation.bend`, proved
equal to FIPS 202's in its `proofs/crypto/keccak/`), its SHA-3 sponge
helpers (`sha3/core.bend`) and its streaming absorb (`hash.bend`'s `step3`
and `Sha3State`), and adds SHAKE256's padding and squeezing.

**What matches what.**

* The SHA3-256 path matches `ref/model.py` (written from the documents,
  with hashlib's SHA3-256), and no jitterentropy release, whose conditioner,
  buffer layout and auxiliary data differ.
* The XDRBG path matches `ref/model_xdrbg.py`, written from the 2026
  document's section 3.1.1 and the XDRBG paper's Algorithm 2 and appendix B,
  with hashlib's SHAKE256 (the model hashes the whole seed in one call; the
  package feeds it as it comes). Its conditioner is jitterentropy 3.7.0's as
  the document describes it. The match is to the documents, not to the
  3.7.0 release: the document's sections on the conditioner and the XDRBG
  give no test data, nor does its table of contents list any (and the
  XDRBG paper's ToSC version has none for XDRBG-256; the document's section
  6.5.3 points to an appendix F of the XDRBG specification, which that
  version, appendices A to E, does not have), the library is not installed
  here, and its API cannot be fed recorded deltas. What the
  package itself leaves out (below: the auxiliary data's RCT-with-memory
  count, the lag predictor, the NTG.1 startup) differs from 3.7.0 on either
  path.
* SHAKE256 matches hashlib's, and NIST's example for the empty message
  (two laws).

## What differs from jitterentropy

* The noise source is outside: no memory access loop or hash loop runs
  here (jitterclock times a hash loop and passes the deltas in).
* Each health test has one cutoff (alpha = 2^-30), and a failure is
  permanent: no intermittent error, no reset with a higher oversampling
  rate, no FIPS or NTG.1 modes, no NTG.1 startup with separate sources.
* The RCT counts identical consecutive deltas, as SP 800-90B 4.4.1 states
  it; the library's RCT counts consecutive stuck deltas (a repeated delta
  is a stuck one, so a run of C identical deltas trips both). Its cutoff is
  1 + 30 * osr, SP 800-90B's formula with H = 1/osr.
* No lag predictor test and no RCT with memory; the auxiliary data has the
  RCT count, the APT count, cutoff and window and the APT base (3.7.0's
  also has the RCT-with-memory count).

## Files

| File | Holds |
|---|---|
| `jitter.bend` | the parameters, the state, absorbing deltas, blocks, reading bytes |
| `stuck.bend` | the stuck test |
| `health.bend` | the SP 800-90B Repetition Count and Adaptive Proportion Tests |
| `sample.bend` | the equality of two samples (time deltas) |
| `sha3.bend` | the core with SHA3-256 filled in (crypto's `inst_sha3.bend`), the default |
| `shake.bend` | the XOF interface, and SHAKE256 as an XOF (the adapter for bend-collections-laws-crypto's Keccak) |
| `xdrbg.bend` | the XDRBG conditioner over any XOF, and its parameters |
| `xdrbg256.bend` | the core with XDRBG-256 over SHAKE256 filled in |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/model.py`, `ref/gen.py`, `ref/run.sh` | the model from the documents, and the differential test |
| `ref/model_xdrbg.py`, `ref/gen_xdrbg.py` | the XDRBG model (on model.py), and the SHAKE256 and XDRBG differential tests |
| `ref/record.py`, `ref/recorded.txt` | how the recorded deltas were made, and the recording |

## API

The core takes the conditioner as template arguments: `~H` (the pool's
state), `~bsize` (the buffer size, the rate the buffer is padded to),
`~init` (the pool before any delta), `~update` (the pool after a buffer),
`~take: H -> JitTaken<H>` (the block step: the block's bytes and the next
pool), and `~digest` (the auxiliary data's digest). `Jitter.*` take a
hash's `~init`, `~update`, `~final` instead of `~take`, and use
`JitCond.hash`; `sha3.bend`'s `JitSha3.*` fill in SHA3-256 and
`xdrbg256.bend`'s `JitXdrbg256.*` XDRBG-256 over SHAKE256.

| Def | Meaning |
|---|---|
| `JitParams{osr, safety, rct_cutoff, apt_window, apt_cutoff, domain, prime}` | the parameters (open) |
| `JitParams.default()`, `JitParams.for_osr(osr)` | osr 3; any osr with its cutoffs (below) |
| `JitParams.need(p)` | the counted deltas per block, (256 + safety) * osr |
| `Jitter.init(~H, ~init, p)` | a new state: an empty pool, the tests before any sample, `prime` blocks to discard |
| `Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)`, `Jitter.absorb_all(..., p, st, ds)` | the state after a delta, after deltas |
| `Jitter.count(st)`, `Jitter.failed(st)`, `Jitter.can_block(p, st)`, `Jitter.why(p, st)` | deltas counted; whether a health test has failed; whether a block can be taken; why not |
| `Jitter.block(~H, ~init, ~update, ~final, p, st)` | a block (`JitBlock{out, state}`), or `Fail{why}` |
| `Jitter.read(~H, ~bsize, ~init, ~update, ~final, ~digest, p, st, ds, n)` | n bytes from the deltas: `JitOut{out, state, rest}` (the deltas not used), or `Fail` |
| `Jitter.generate(..., p, ds, n)` | `read` from a new state |
| `JitCore.block(~H, ~take, p, st)`, `JitCore.read(~H, ~bsize, ~update, ~digest, ~take, p, st, ds, n)`, `JitCore.generate(~H, ~bsize, ~init, ~update, ~digest, ~take, p, ds, n)` | the same, for any conditioner |
| `JitTaken{out, pool}` (open), `JitTaken.out`, `.pool` | a block step's result |
| `JitCond.hash(~H, ~init, ~update, ~final)` | a hash's block step: the digest, and a new state that has absorbed it |
| `JitBlock.out`, `.state`; `JitOut.out`, `.state`, `.rest` | accessors |
| `JitError` | `JitRctFailure{}`, `JitAptFailure{}`, `JitNotEnough{have, need}`, `JitNeedMore{have}` (the deltas ran out with `have` bytes collected) |
| `JitStuck.new`, `.is_stuck(s, t)`, `.next(s, t)` (`stuck.bend`) | the stuck test |
| `JitRct.new`, `.feed(c, r, x)`, `.run(c, r, xs)`, `.failed`, `.count` (`health.bend`) | the Repetition Count Test with cutoff c |
| `JitApt.new`, `.feed(w, c, t, x)`, `.run(w, c, t, xs)`, `.failed`, `.count`, `.base` (`health.bend`) | the Adaptive Proportion Test with window w and cutoff c |
| `JitSample.eq` (`sample.bend`) | sample equality |
| `JitSha3.init`, `.absorb`, `.absorb_all`, `.block`, `.read`, `.generate` (`sha3.bend`) | with SHA3-256 |
| `JitShakeState` (opaque), `JitShake.init()`, `.update(s, o)`, `.read(s, i, n)`, `.shake256(m, n)` (`shake.bend`) | SHAKE256 as an XOF: the n output bytes at offset i; the first n bytes for m |
| `JitXdrbgParams{vsize, outsize, alpha}` (open), `JitXdrbgParams.default()`, `.vsize`, `.outsize`, `.alpha` (`xdrbg.bend`) | the sizes of V and of the output in bytes, and alpha; the default 64, 32, empty |
| `JitXdrbgPool<X>` (opaque), `JitXdrbg.init(~X, ~xinit)`, `JitXdrbg.update(~X, ~xupdate)`, `JitXdrbg.take(~X, ~xinit, ~xupdate, ~xread, ~xp)` (`xdrbg.bend`) | the XDRBG conditioner over an XOF: the `~init`, `~update` and `~take` for `JitCore.*` |
| `JitXdrbg256.init`, `.absorb`, `.absorb_all`, `.block`, `.read`, `.generate`, and its conditioner `.pool()`, `.update`, `.take` (`xdrbg256.bend`) | with XDRBG-256 over SHAKE256 |

The XOF interface (`shake.bend`): `~X: Data` (the state), `~xinit: X`,
`~xupdate: X -> B.Octets -> X`, `~xread: X -> Nat -> Nat -> B.Octets`
(`xread(s, i, n)`: the n bytes at offset i of the output for the bytes so
far). The SHAKE256 instance is `~JitShakeState, ~JitShake.init(),
~JitShake.update, ~JitShake.read`.

`JitState<H>`, `JitXdrbgPool<X>` and `JitShakeState` are opaque; `jit.*`
defs (and `JitShakeOut`) are internal.

## Parameters

| | osr | safety | rct_cutoff | apt_window | apt_cutoff | domain | prime |
|---|---|---|---|---|---|---|---|
| `JitParams.default()` | 3 | 65 | 91 | 512 | 459 | 2 | 1 |
| `JitParams.for_osr(o)` | o | 65 | 1 + 30 o | 512 | Müller's table for o (325, 422, 459, 477, 488, 494, 499, 502, 505, 507, 508, 509, 510, 511 for o = 1 to 14; 512 from 15) | 2 | 1 |

`domain` is 2, the hash loop's separator, because jitterclock times a hash
loop; 1 is the memory access loop's and 3 both.

## Extension points

* **The conditioner:** any block step through `JitCore.*` (`~H`,
  `~bsize`, `~init`, `~update`, `~take`, `~digest`); the core laws hold for
  every one. A hash of crypto's interface through `Jitter.*` (SHA3-256, the
  named default, in `sha3.bend`); the XDRBG over any XOF through
  `xdrbg.bend` (XDRBG-256 over SHAKE256, jitterentropy 3.7.0's, in
  `xdrbg256.bend`), with its |V|, l and alpha in `JitXdrbgParams`.
* **The XOF:** any XOF of the interface in `shake.bend` (SHAKE128, or an
  Ascon XOF, as the XDRBG paper's section 7 proposes, would plug in the
  same way); SHAKE256 is provided.
* **The parameters:** every number above, and `JitParams.for_osr` for the
  derived cutoffs.
* **The noise source:** the deltas come from the caller, so any timer and
  any timed work feed the same core; jitterclock is one.
* **The tests:** `stuck.bend` and `health.bend` stand alone, for other
  noise sources.

## Laws

`LAWS.bend`, 31 laws, all proved:

* **The stuck test:** `stuck_zero` (a zero delta is stuck, after any
  deltas), `stuck_repeat` (a delta equal to the one before is stuck);
  vectors `stuck_vec_second`, `stuck_vec_moving`.
* **The RCT:** `rct_trips` (C identical samples fail the test with cutoff
  C, for every C >= 2 and sample), `rct_below_cutoff` (C - 1 do not),
  `rct_latch` (a failure stays).
* **The APT:** `apt_trips` (C identical samples fail the test with cutoff
  C in a window of at least C, for every such C, window and sample),
  `apt_latch`; vectors `apt_vec_window`, `apt_vec_restart` (the window
  restarts).
* **The generator, for every hash, parameters and state:**
  `absorb_all_append` (the same deltas give the same state however they
  arrive), `absorb_failed` (a health failure stays), `stuck_source` (a
  constant source never lets a block be taken, after any number of
  deltas, when a block needs two or more counted deltas), `block_refused`,
  `read_failed` (a failed generator refuses every read of one or more
  bytes), `read_length` (a read that succeeds gives exactly n bytes).
* **Vectors:** `params_default`, `need_default` (963).
* **The core, for every conditioner** (any `~take`): `core_block_refused`,
  `core_read_failed`, `core_read_length`, the generator laws above for
  `JitCore.*` (those for `Jitter.*` are their instances).
* **SHAKE256, for every state:** `shake_read_length` (a read of n bytes
  gives n bytes, at any offset), `shake_read_split` (the n = a + b bytes at
  offset i are the a bytes there followed by the b bytes at offset i + a:
  the output is one stream, so the XDRBG's two reads of T are T cut in
  two); vectors `shake256_empty` (the first 32 bytes for the empty message)
  and `shake256_empty_second_block` (its bytes 136 to 143, from the second
  block squeezed), from NIST's example.
* **XDRBG-256 over SHAKE256, for every parameter set, state and delta
  list:** `xdrbg_absorb_append` (the same deltas give the same state
  however they arrive), `xdrbg_block_append` (and so the same block),
  `xdrbg_block_length` (a block is 32 bytes), `xdrbg_read_length`,
  `xdrbg_read_failed`.

Not laws: anything about entropy (a property of the noise source, not of
this code), the digest values (crypto's SHA3-256 laws and tests stand for
them), SHAKE256 in pieces equalling SHAKE256 whole (the absorbing is
bend-collections-laws-crypto's streaming SHA-3 absorb, whose laws are
stated for SHA3-256's digest; the tests feed SHAKE256 in pieces), the
XDRBG's values (the tests stand for them: the documents give none), and
that a constant source makes `read` fail rather than run out of deltas (it
does: `stuck_source` and `block_refused` say no block comes; the tests
show the RCT failing).

## Tests

* `check.bend`: the parameters, the stuck test, both health tests at
  their cutoffs, 32 bytes from 2000 pseudo-random deltas, a read in two
  parts, 50 equal deltas counting once, a constant source refused (RCT),
  and too few deltas. The values are `ref/model.py`'s too. Then SHAKE256
  of "abc" (hashlib's value), and with XDRBG-256: 32 bytes from the same
  2000 deltas, a read in two parts, a constant source refused (the values
  are `ref/model_xdrbg.py`'s).
* `ref/run.sh`: 19 cases, 39,081 deltas, against `ref/model.py` (written
  from the documents, with hashlib's SHA3-256): 4000 deltas recorded on
  this machine (`ref/record.py`), read whole and in two reads carrying the
  state; pseudo-random deltas of several spreads, 64-bit ones included;
  osr 1, 2, 3 and 5, no block or two blocks discarded, the other domain
  separators, no safety factor; and failing sources: a constant delta,
  zeros, a run of 91 equal deltas among good ones (the RCT fails) and of 90
  (it does not), one value half the time (the APT fails with cutoff 200,
  and not with 459), too few deltas, zero bytes. Every output, error and
  count of deltas left matches.
* `ref/run.sh` then runs `gen_xdrbg.py`: 72 SHAKE256 reads against
  hashlib (messages of 0 to 300 bytes, around the 136-byte rate, fed in
  three pieces; reads at offsets 0 to 270 of 0 to 300 bytes, across
  squeezed blocks), and 18 XDRBG cases, 36,191 deltas, against
  `ref/model_xdrbg.py`: the recorded deltas read whole and in two reads,
  pseudo-random deltas, osr 1, 2 and 5, no block or two blocks discarded,
  the common domain separator, the XDRBG's own parameters through
  `JitXdrbg.take` (alpha of 16 and of 84 bytes, the encoding's limit; |V|
  of 32 bytes with blocks of 64, and of 200 with blocks of 150, longer than
  the rate), and failing sources (a constant delta, a run of 91, the APT,
  too few deltas, zero bytes).
* The jitterentropy library is not installed here (no `libjitterentropy`
  or `jitterentropy.h`), and its API cannot take recorded deltas, so there
  is no comparison with it.

## Speed

A native build reads a 32-byte block from about 1000 deltas (two
SHA3-256 permutations per delta) in about 0.2 s; building a program that
uses the package takes about a minute (the Keccak code). XDRBG-256 costs
the same per delta (one SHA3-256 permutation for the auxiliary digest, one
SHAKE256 permutation for the buffer) and a few permutations more per
block.

## Dependencies

`bytes` (Octets, field encodings, and its laws in the proofs), `word64`
(deltas are `W64`), `crypto` (`sha3.bend`, `xdrbg256.bend` and the tests
use its SHA3-256 instance; the core uses only the interface's shape, not
the package), and `bend-collections-laws-crypto@1.0.0.0` (pure Bend, MIT;
the package crypto's SHA3-256 already comes from), for the Keccak-f[1600]
permutation and sponge under `shake.bend`.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 19 cases (SHA3-256), 72 SHAKE256 reads
and 18 XDRBG cases match, `scripts/deps.sh` passes.
