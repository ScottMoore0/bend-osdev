# bend-osdev-jitter

The pure core of a CPU Jitter random number generator, after Stephan
Müller's jitterentropy: it takes a list of time deltas (measured elsewhere;
jitterclock reads a clock) and holds the noise processing, the SP 800-90B
health tests, the stuck test and the conditioning. The conditioner is a
hash through the crypto package's hash interface, SHA3-256 by default.

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
  and the change log (appendix G).
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

**Which conditioner.** jitterentropy 3.0 to 3.6 condition with SHA3-256;
the 2026 document (version 3.7.0) replaces it with an XDRBG over SHAKE-256
(its change log: "Replace SHA3-256 with XDRBG"). This package uses
SHA3-256, as planned, through crypto's hash interface. The SHA-3-era
document (1 July 2022, cited by NIST's certificates) could not be read: the
URL above now serves the 2026 version. So the insertion layout is the 2026
document's (delta, separator, auxiliary digest, zeros to the rate) with
SHA3-256 in place of the XDRBG; SHA3-256's rate is the same 1,088 bits.

**Not the library's output.** The byte values are this package's own:
they match no jitterentropy release, whose conditioner, buffer layout and
auxiliary data differ, and whose API cannot be fed recorded deltas (above).
The tests compare the package with a model written from the documents
(`ref/model.py`), not with the library, which is not installed here either.

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
  RCT count, the APT count, cutoff and window and the APT base.

## Files

| File | Holds |
|---|---|
| `jitter.bend` | the parameters, the state, absorbing deltas, blocks, reading bytes |
| `stuck.bend` | the stuck test |
| `health.bend` | the SP 800-90B Repetition Count and Adaptive Proportion Tests |
| `sample.bend` | the equality of two samples (time deltas) |
| `sha3.bend` | the core with SHA3-256 filled in (crypto's `inst_sha3.bend`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/model.py`, `ref/gen.py`, `ref/run.sh` | the model from the documents, and the differential test |
| `ref/record.py`, `ref/recorded.txt` | how the recorded deltas were made, and the recording |

## API

The core takes the crypto hash interface's template arguments it uses:
`~H` (the state), `~bsize` (the block size, the rate the buffer is padded
to), `~init`, `~update`, `~final`, `~digest`. `sha3.bend`'s `JitSha3.*` are
the same defs with SHA3-256 filled in.

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
| `JitBlock.out`, `.state`; `JitOut.out`, `.state`, `.rest` | accessors |
| `JitError` | `JitRctFailure{}`, `JitAptFailure{}`, `JitNotEnough{have, need}`, `JitNeedMore{have}` (the deltas ran out with `have` bytes collected) |
| `JitStuck.new`, `.is_stuck(s, t)`, `.next(s, t)` (`stuck.bend`) | the stuck test |
| `JitRct.new`, `.feed(c, r, x)`, `.run(c, r, xs)`, `.failed`, `.count` (`health.bend`) | the Repetition Count Test with cutoff c |
| `JitApt.new`, `.feed(w, c, t, x)`, `.run(w, c, t, xs)`, `.failed`, `.count`, `.base` (`health.bend`) | the Adaptive Proportion Test with window w and cutoff c |
| `JitSample.eq` (`sample.bend`) | sample equality |
| `JitSha3.init`, `.absorb`, `.absorb_all`, `.block`, `.read`, `.generate` (`sha3.bend`) | with SHA3-256 |

`JitState<H>` is opaque; `jit.*` defs are internal.

## Parameters

| | osr | safety | rct_cutoff | apt_window | apt_cutoff | domain | prime |
|---|---|---|---|---|---|---|---|
| `JitParams.default()` | 3 | 65 | 91 | 512 | 459 | 2 | 1 |
| `JitParams.for_osr(o)` | o | 65 | 1 + 30 o | 512 | Müller's table for o (325, 422, 459, 477, 488, 494, 499, 502, 505, 507, 508, 509, 510, 511 for o = 1 to 14; 512 from 15) | 2 | 1 |

`domain` is 2, the hash loop's separator, because jitterclock times a hash
loop; 1 is the memory access loop's and 3 both.

## Extension points

* **The conditioner:** any hash of crypto's interface (`~H`, `~bsize`,
  `~init`, `~update`, `~final`, `~digest`); the laws hold for every one.
* **The parameters:** every number above, and `JitParams.for_osr` for the
  derived cutoffs.
* **The noise source:** the deltas come from the caller, so any timer and
  any timed work feed the same core; jitterclock is one.
* **The tests:** `stuck.bend` and `health.bend` stand alone, for other
  noise sources.

## Laws

`LAWS.bend`, 19 laws, all proved:

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

Not laws: anything about entropy (a property of the noise source, not of
this code), the digest values (crypto's SHA3-256 laws and tests stand for
them), and that a constant source makes `read` fail rather than run out of
deltas (it does: `stuck_source` and `block_refused` say no block comes;
the tests show the RCT failing).

## Tests

* `check.bend`: the parameters, the stuck test, both health tests at
  their cutoffs, 32 bytes from 2000 pseudo-random deltas, a read in two
  parts, 50 equal deltas counting once, a constant source refused (RCT),
  and too few deltas. The values are `ref/model.py`'s too.
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
* The jitterentropy library is not installed here (no `libjitterentropy`
  or `jitterentropy.h`), and its API cannot take recorded deltas, so there
  is no comparison with it.

## Speed

A native build reads a 32-byte block from about 1000 deltas (two
SHA3-256 permutations per delta) in about 0.2 s; building a program that
uses the package takes about a minute (the Keccak code).

## Dependencies

`bytes` (Octets, field encodings, and its laws in the proofs), `word64`
(deltas are `W64`), `crypto` (`sha3.bend` and the tests use its SHA3-256
instance; the core uses only the interface's shape, not the package).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 19 cases match, `scripts/deps.sh`
passes.
