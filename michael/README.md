# bend-osdev-michael

Michael, the message integrity code of TKIP (IEEE Std 802.11i-2004): a
64-bit tag under a 64-bit key, streaming (init, update, final) and in one
call, through md-engine's engine with four-byte blocks. The crypto package
takes it as an instance of its MAC interface (`crypto/inst_michael.bend`).
**Michael was designed for a security level of only about 20 bits**, to fit
TKIP's old hardware: it is here for TKIP.

The directory is `michael` and the entry file `michael/michael.bend`; the
hub name is `bend-osdev-michael`. It is one of the packages split from
bend-osdev-hashes@0.1.0.0, which they supersede (that version stays on the
hub as it was): md-engine (the Merkle–Damgård engine and what the hashes
share) and one package per hash.

## Specifications

Written from the public specifications only; no GPL source was read.

* **Michael:** defined by IEEE Std 802.11i-2004 (TKIP's MIC), whose Annex
  H.2 holds a Michael reference implementation and test vectors (so says the
  Wi-Fi Alliance's *Wi-Fi Protected Access (WPA): Enhanced Security
  Implementation Based on IEEE P802.11i standard*, version 3.1, August 2004,
  Appendix B, https://www.wi-fi.org/system/files/WPA_80211_v3_1_090922.pdf);
  IEEE Std 802.11-2024 keeps them as Annex J.2. The algorithm was first
  written from two published descriptions, before any edition of 802.11
  could be read here: A. Wool, "A Note on the Fragility of the 'Michael'
  Message Integrity Code", *IEEE Transactions on Wireless Communications*
  3(5), pp. 1459–1462, September 2004, section II-B and Fig. 1; and J.
  Huang, J. Seberry, W. Susilo and M. Bunder, "Security Analysis of Michael:
  the IEEE 802.11i Message Integrity Code", EUC 2005 Workshops, LNCS 3823,
  pp. 423–432, section 2, Algorithms 2.1 and 2.2 and Fig. 2
  (https://documents.uow.edu.au/~jennie/WEB/WEB05/Michael.pdf). Both agree
  with `michael.bend`: the key as two 32-bit words (K0, K1); the message
  padded with 0x5a and four to seven zero bytes to a multiple of four; per
  word l ^= M_i, then b(l, r); b as R ^= L <<< 17, L += R, R ^= XSWAP(L), L
  += R, R ^= L <<< 3, L += R, R ^= L >>> 2, L += R, with XSWAP(ABCD) = BADC;
  the tag (l, r). Neither states the byte order (key bytes into K0 and K1,
  message bytes into words, the tag's bytes). **The algorithm and its byte
  order are verified end to end** by IEEE Std 802.11-2012's M.6.3 TKIP test
  vector, as the test data of hostap's `wlantest/test_vectors.c`
  (`test_vector_tkip`; BSD-licensed, Jouni Malinen, 2012;
  https://fuchsia.googlesource.com/third_party/hostap/+/fuchsia/wlantest/test_vectors.c)
  reproduces it, read as data only: TK = 12 34 56 78 90 repeated (32 bytes);
  a FromDS data frame with DA = 02:03:04:05:06:08 and SA =
  02:03:04:05:06:07, no QoS (priority 0); a 92-byte MSDU; and the 8 bytes
  that follow the MSDU in the plaintext MPDU (commented out in that file,
  unlabelled), 68 81 a3 f3 d6 48 d0 3c. Michael over DA, SA, the priority
  and three zero bytes, then the MSDU (TKIP's input, as both papers describe
  it), under TK bytes 16 to 23, gives exactly those 8 bytes (TK bytes 24 to
  31 do not); the 108-byte input also exercises the longest padding, 0x5a
  and seven zeros. It is a law (`michael_tkip_m63`) and in `check.bend`.
  **The six test vectors are verified** against IEEE Std 802.11-2024, Annex
  J.2.1.3, Table J-2 (read on 2026-10-24): key 0 and message ""; then each
  key the previous output, with the messages "M", "Mi", "Mic", "Mich" and
  "Michael". `michael_vector_1` to `_6` are exactly those six rows. They
  were first written from memory, before any copy could be read, and the
  table agrees with every byte. Table J-1's vectors for the block function b
  are laws too (`michael_block_1` to `_4`, one application each, the pair
  read as (l, r)), and its last row, b applied 1000 times to (1, 0), is in
  `check.bend`. The annex notes that its vectors had yet to be confirmed by
  an independent implementation; `michael.bend` and `ref/model.py` agree
  with all of them.

## Files

| File | Holds |
|---|---|
| `michael.bend` | Michael: `HsMichael.*` |
| `gen/laws.py` | writes `LAWS.bend` and `PROOF.bend` |
| `gen/check.py` | writes `check.bend` and its expected output |
| `ref/model.py`, `ref/gen.py`, `ref/run.sh` | the differential test (Tests below) |

`python3 gen/<script>.py` rewrites what a generator writes, and `--check`
checks it is up to date. Bend imports do not re-export: import md-engine's
`md-engine.bend` beside `michael.bend` to name the key type `HsW2`, the
state type and the error `HsError`.

## Public interface

| Def | Meaning |
|---|---|
| `HsMichael.key(o)` | the key from eight bytes (md-engine's `HsW2`; `Fail{HsBadKeyLength{n}}` for another length) |
| `HsMichael.init(k)` | the state before any byte, under a key (`HsMdState<HsW2>`) |
| `HsMichael.update(s, o)` | the state after more bytes, in any pieces |
| `HsMichael.final(s)` | the tag of the bytes so far (8 bytes) |
| `HsMichael.mic(k, o)` | the tag in one call |
| `HsMichael.compress(lr, block)` | one four-byte word taken in |
| `hs.michael.b(lr)` | the block function b on the pair (l, r), which Table J-1's vectors and the `michael_block_*` laws state |

Everything else (`hs.michael.*` but `b`) is internal. As a MAC, crypto's
adapter maps the key error onto its own (`crypto/inst_michael.bend`):

```
~Hs.HsW2, ~CrMichael.key, ~HsMichael.mic, ~CrMichael.verify
```

## Extension points

* **The key** is any `HsW2`; `HsMichael.key` reads it from bytes, and a
  caller that holds the two words already builds the key directly.
* **TKIP's input** (DA, SA, the priority and three zero bytes, then the
  MSDU) is the caller's to build: the tag is over any bytes.
* **The engine** is md-engine's (four-byte blocks, `~last = 3`).

## Laws

`LAWS.bend` (written by `gen/laws.py`) has 16 laws.

**For every input**, with no hypothesis, under every key:

* `michael_streaming`: update over `a ++ b` is update over `a`, then `b`,
  from every state (md-engine's `md_streaming` at Michael's defs);
* `michael_split`: the tag in two pieces is the one-call tag;
* `michael_length` and `michael_mic_length`: the tag of every state, and of
  every message under every key, has 8 bytes (md-engine's
  `w2_le_length`).

**Vectors**, by computation: the refusal of a 7-byte key
(`michael_short_key`); the six vectors of IEEE Std 802.11-2024's Table J-2
(`michael_vector_1` to `_6`) and the four single applications of its block
function in Table J-1 (`michael_block_1` to `_4`; Specifications above); and
the MIC on IEEE 802.11-2012 M.6.3's TKIP frame (`michael_tkip_m63`,
verified: above).

The proofs need nothing from another package beyond its public interface and
laws: md-engine's `md_streaming` and `w2_le_length`.

## Tests

* `check.bend` (written by `gen/check.py`): the six vectors of Table J-2,
  whole and in three pieces, the block function 1000 times on (1, 0) (Table
  J-1's last row), the M.6.3 TKIP MIC (whole and in pieces) and a short key
  refused. The expected lines are the specifications' values.
* `ref/run.sh` (27 cases with the default seed): Michael under random keys
  on 27 message lengths (1000 and 4103 bytes among them), whole and cut into
  three pieces at random points, against `ref/model.py`, since Python has
  no Michael. **The model shares an author with the package**: it is
  checked first against Table J-2's six vectors, Table J-1's block function
  values and M.6.3's MIC, but the differential test is against that model
  alone.
* The crypto package's tests run Michael through its MAC interface (the
  tag, verify of it and of it changed) against this model.

## Notes on use

* **Michael is weak by design:** it was designed for a security level of
  only about 20 bits, to fit TKIP's old hardware. It is here to read and
  write what already uses it (TKIP).
* None of this code is constant-time, and Bend's runtime promises nothing
  about running time.

## Dependencies

`DEPS`: `bytes` (`Octets`) and `md-engine` (the engine, the key type
`HsW2` and its bytes, the word helper `hs.le`, the error type `HsError`,
and its laws in the proofs). No hub package.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(3 s, 0.37 GB peak; `--verdict` 5 s, 0.42 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s), `--verdict` ALL PROOFS
CHECK (5 s, 0.43 GB peak, with md-engine's proofs), `check.bend` passes,
`ref/run.sh` 27 cases match (against the model), `gen/laws.py --check` and
`gen/check.py --check` up to date, `scripts/deps.sh` and
`scripts/publish.py --dry-run` pass.
