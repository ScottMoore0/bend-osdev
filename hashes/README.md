# bend-osdev-hashes

The hashes Linux's `crypto/` has beyond SHA-2: MD4, MD5, SHA-1,
RIPEMD-160, SM3, Streebog-256 and Streebog-512, and Michael, TKIP's MIC.
Every one streams (init, update, final) and has a one-shot form, through
one Merkle–Damgård engine whose streaming law is proved once for every
compression function. The crypto package takes them as instances of its
hash interface (and Michael of its MAC interface), with HMAC and PBKDF2
over them.

The directory is `hashes` and the entry file `hashes/hashes.bend`; the hub
name is `bend-osdev-hashes`.

## Specifications

Written from the public specifications only; no GPL source was read.

* **MD4:** RFC 1320, R. Rivest, *The MD4 Message-Digest Algorithm* (April
  1992), section 3 (the algorithm) and appendix A.5 (the test suite).
* **MD5:** RFC 1321, R. Rivest, *The MD5 Message-Digest Algorithm* (April
  1992), section 3 and appendix A.5.
* **SHA-1:** FIPS 180-4, *Secure Hash Standard (SHS)* (NIST, August 2015),
  sections 4.1.1, 4.2.1, 5.1.1, 5.3.1 and 6.1; NIST's SHA-1 example values
  ("abc" and the 448-bit message), and FIPS 180-2's third example (a
  million bytes "a").
* **RIPEMD-160:** H. Dobbertin, A. Bosselaers and B. Preneel, *RIPEMD-160:
  A Strengthened Version of RIPEMD*, Fast Software Encryption 1996, LNCS
  1039, pp. 71–82 (the pseudo-code: word orders r and r', rotations s and
  s', constants K and K'), and the test values on Bosselaers' RIPEMD-160
  page (homes.esat.kuleuven.be/~bosselae/ripemd160.html).
* **SM3:** GB/T 32905-2016, *Information security techniques — SM3
  cryptographic hash algorithm*; in English, draft-shen-sm3-hash-01, S.
  Shen and X. Lee, *SM3 Hash Function* (February 2014), sections 3.1 to
  3.3 and examples 1 and 2.
* **Streebog:** RFC 6986, V. Dolmatov and A. Degtyarev, *GOST R
  34.11-2012: Hash Function* (August 2013): sections 6 (Pi', tau, A, C_1 to
  C_12), 7 (X, S, P, L), 8 (g_N), 9 (the procedure) and 10 (examples 1 and
  2, with their intermediate values).
* **Michael:** defined by IEEE Std 802.11i-2004 (TKIP's MIC), whose Annex
  H.2 holds a Michael reference implementation and test vectors (so says
  the Wi-Fi Alliance's *Wi-Fi Protected Access (WPA): Enhanced Security
  Implementation Based on IEEE P802.11i standard*, version 3.1, August
  2004, Appendix B, https://www.wi-fi.org/system/files/WPA_80211_v3_1_090922.pdf). No copy of 802.11i or of a
  later 802.11 edition could be read here (the copies found were
  unreachable, refused the fetch, or were larger than the fetch limit), so
  the algorithm was checked instead against two published descriptions:
  A. Wool, "A Note on the Fragility of the 'Michael' Message Integrity
  Code", *IEEE Transactions on Wireless Communications* 3(5), pp.
  1459–1462, September 2004, section II-B and Fig. 1; and J. Huang, J.
  Seberry, W. Susilo and M. Bunder, "Security Analysis of Michael: the IEEE
  802.11i Message Integrity Code", EUC 2005 Workshops, LNCS 3823, pp.
  423–432, section 2, Algorithms 2.1 and 2.2 and Fig. 2
  (https://documents.uow.edu.au/~jennie/WEB/WEB05/Michael.pdf). Both agree with
  `michael.bend`: the key as two 32-bit words (K0, K1); the message padded
  with 0x5a and four to seven zero bytes to a multiple of four; per word
  l ^= M_i, then b(l, r); b as R ^= L <<< 17, L += R, R ^= XSWAP(L),
  L += R, R ^= L <<< 3, L += R, R ^= L >>> 2, L += R, with XSWAP(ABCD) =
  BADC; the tag (l, r). Neither states the byte order (key bytes into K0
  and K1, message bytes into words, the tag's bytes). **The algorithm and
  its byte order are verified end to end** by IEEE Std 802.11-2012's M.6.3
  TKIP test vector, as the test data of hostap's `wlantest/test_vectors.c`
  (`test_vector_tkip`; BSD-licensed, Jouni Malinen, 2012;
  https://fuchsia.googlesource.com/third_party/hostap/+/fuchsia/wlantest/test_vectors.c) reproduces it,
  read as data only: TK = 12 34 56 78 90 repeated (32 bytes); a FromDS
  data frame with DA = 02:03:04:05:06:08 and SA = 02:03:04:05:06:07, no
  QoS (priority 0); a 92-byte MSDU; and the 8 bytes that follow the MSDU in
  the plaintext MPDU (commented out in that file, unlabelled), 68 81 a3 f3
  d6 48 d0 3c. Michael over DA, SA, the priority and three zero bytes, then
  the MSDU (TKIP's input, as both papers describe it), under TK bytes 16 to
  23, gives exactly those 8 bytes (TK bytes 24 to 31 do not); the 108-byte
  input also exercises the longest padding, 0x5a and seven zeros. It is a
  law (`michael_tkip_m63`) and in `check.bend`.
  **The six test vectors are unverified.** No published copy of them could
  be read; they were written from memory (as the standard's chained
  vectors: key 0, message ""; then each key the previous tag, messages "M",
  "Mi", "Mic", "Mich", "Michael"), and `ref/model.py` was written from the
  same memory, so the model's agreement with them is not independent
  evidence. They are laws (`michael_vector_1` to `_6`), which proves that
  `michael.bend` computes those values, not that the values are the
  standard's. Sources tried for them, none readable here (October 2026):
  * IEEE 802.11i-2004 itself: IEEE's old GET IEEE 802 download URL
    (https://standards.ieee.org/getieee802/download/802.11i-2004.pdf) now
    answers the GET Program's landing page, and the Internet Archive's
    copies cannot be fetched from here; no other public copy of 802.11i,
    802.11-2007 or 802.11-2012 was found (smartgrid.gov's page for 802.11-2007
    no longer resolves).
  * The IEEE 802.11 TGi documents behind the annex: N. Ferguson,
    *Michael: an improved MIC for 802.11 WEP*, IEEE 802.11-02/020r0
    (January 2002), and M. Sabin and P. Lambert, *Proposed Test Vectors
    for IEEE 802.11 TGi*, IEEE 802.11-02/362 (r0 to r6, 2002), are on
    https://mentor.ieee.org/802.11/dcn/02/, which refuses the fetch (HTTP
    418); a library mirror of the same documents (bibliotheek.ehb.be, on
    port 3499) was refused by this session's permission checks, and both
    are Word files.
  * Permissively licensed test data: FreeBSD's
    `tools/regression/net80211/tkip/test_tkip.c` (Sam Leffler, 2004;
    BSD-3-Clause, or GPL v2 at the recipient's choice; read as data only;
    https://github.com/freebsd/freebsd-src/blob/main/tools/regression/net80211/tkip/test_tkip.c) has 802.11i's TKIP MPDU, whose MIC is the same
    68 81 a3 f3 d6 48 d0 3c as M.6.3's above, but not the six chained
    vectors; hostap's `wlantest/test_vectors.c` likewise (above). No
    BSD-, MIT- or Apache-licensed project with the chained vectors was
    found; the copies the searches found are GPL (the Linux kernel's
    crypto self-tests), which are not read.
  * Published papers: M. Beck, *Enhanced TKIP Michael Attacks*
    (arXiv:1410.6295, 2014) prints none.

  To settle them, obtain the current IEEE Std 802.11 through the IEEE GET
  Program (free, with an IEEE account sign-in;
  https://standards.ieee.org/about/get/802/802.11.html; superseded
  editions such as 802.11i-2004 are sold, not in the programme) and
  compare the Michael test vectors of its TKIP annex (802.11i-2004's
  Annex H.2.1) with `michael_vector_1` to `_6`.

**SM3 and bend-collections.** bend-collections-laws-crypto@1.0.0.0 (an
allowed hub package) was searched file by file for SM3 (and MD4, MD5,
SHA-1, RIPEMD-160, Streebog and PBKDF2) before anything was written: it has
none of them, so SM3 is written here rather than adapted.

## Files

| File | Holds |
|---|---|
| `hashes.bend` | the engine (`HsMdState`, `HsMd.*`), the chaining-value types `HsW2`, `HsW4`, `HsW5`, `HsW8`, their digest bytes, and the error type `HsError` |
| `md4.bend` | MD4: `HsMd4.*` |
| `md5.bend` | MD5: `HsMd5.*` |
| `sha1.bend` | SHA-1: `HsSha1.*` |
| `ripemd160.bend` | RIPEMD-160: `HsRipemd160.*` |
| `sm3.bend` | SM3: `HsSm3.*` |
| `streebog.bend` | Streebog-256 and Streebog-512: `HsStreebog.*`, its chaining value `HsStbCv` and tables |
| `michael.bend` | Michael: `HsMichael.*` |
| `gen/spec.py` | the specifications' tables (shifts, word orders, constants, Pi', tau, A, C_i), with their sources |
| `gen/rounds.py` | writes the unrolled compression functions of MD4, MD5, SHA-1, RIPEMD-160 and SM3 (the "rounds" regions) from `spec.py` |
| `gen/streebog.py` | writes Streebog's eight LPS tables, LPS and the constants from `spec.py`, after checking the tables against S, P and L applied one by one |
| `gen/laws.py` | writes `LAWS.bend` and `PROOF.bend` (`--check` checks they are current) |
| `gen/check.py` | writes `check.bend` and its expected output |
| `ref/model.py`, `ref/gen.py`, `ref/run.sh` | the differential test (Tests below) |

Bend imports do not re-export: import `hashes.bend` and the algorithm's
file. The generated regions lie between `# BEGIN GENERATED by
gen/<script>.py: <name>` and `# END GENERATED: <name>`.

## API

Every hash `X` (`HsMd4`, `HsMd5`, `HsSha1`, `HsRipemd160`, `HsSm3`) has

| Def | Meaning |
|---|---|
| `X.init()` | the state before any byte (`HsMdState<C>`, C its chaining value) |
| `X.update(s, o)` | the state after more bytes (`Octets`), in any pieces |
| `X.final(s)` | the digest of the bytes so far |
| `X.digest(o)` | the digest in one call (`final(update(init(), o))`) |
| `X.compress(cv, block)` | the compression function on one 64-byte block (a list of bytes) |
| `X.iv()` | the initial chaining value |

Streebog: `HsStreebog.init256()`, `HsStreebog.init512()`,
`HsStreebog.update`, `HsStreebog.final256`, `HsStreebog.final512`,
`HsStreebog.digest256`, `HsStreebog.digest512`, `HsStreebog.compress`;
the transformations on 512-bit vectors as 64-byte strings in memory order
(byte i is RFC 6986's a_i; a shorter string is a number's low bytes):
`HsStreebog.lps(x)`, `HsStreebog.g(n, h, m)` (g_N(h, m)); and
`HsStreebog.tables()`. A state from `init256` is finished with `final256`,
one from `init512` with `final512`. Digests are in memory order, a_0
first: RFC 6986 prints its examples the other way round, most significant
byte first.

Michael: `HsMichael.key(o)` (eight bytes, `Fail{HsBadKeyLength{n}}`
otherwise; the key is an `HsW2`), `HsMichael.init(k)`, `HsMichael.update`,
`HsMichael.final` (8 bytes), `HsMichael.mic(k, o)`, `HsMichael.compress`.

Digest sizes: MD4 and MD5 16 bytes, SHA-1 and RIPEMD-160 20, SM3 32,
Streebog 32 or 64, Michael 8. Every block is 64 bytes (Michael's 4).

The engine (`hashes.bend`), for a new hash: `HsMdState<C>` (opaque),
`HsMd.start(~C, cv)`, `HsMd.update(~C, ~compress, ~last, s, o)` and
`HsMd.update_list` (bytes as a list), the state's parts `HsMd.cv`,
`HsMd.pending`, `HsMd.count`, `HsMd.blocks`, `HsMd.bits(~C, ~last, s)` (the
length so far in bits, modulo 2^64), `HsMd.md_pad(~last, cnt, field)` and
`HsMd.final_md(~C, ~compress, ~last, ~field, ~out, s)` (the
Merkle–Damgård padding with a length field, then the digest of the chaining
value). The types `HsW2` to `HsW8` are open; `HsW2.le`, `HsW4.le`,
`HsW5.le`, `HsW5.be`, `HsW8.be` are their digest bytes. `HsError`:
`HsBadKeyLength{got}`.

Everything else (`hs.*`, `HsW16`, `HsStbTab`, `HsStbTabs`) is internal.

## Extension points

* **A new Merkle–Damgård hash** is a chaining value type, a compression
  function on 64-byte blocks (or any power-of-two block size, through
  `~last`) and a final step: `HsMd.final_md` with its length field and
  digest bytes for the usual padding (as MD5 and SHA-1 do), or its own (as
  Streebog and Michael do). Its streaming law is the engine's
  `md_streaming` at its defs, with nothing more to prove; a row in
  `gen/laws.py` writes its laws and proofs.
* **Compression functions are replaceable.** Each is one def
  (`X.compress`) written from tables in `gen/spec.py`; a faster one (a
  different unrolling, a Streebog without its tables in the chaining value)
  can replace it, and the laws hold for every compression function.
* **Streebog's tables** are part of its chaining value, built by init from
  `HsStreebog.tables()` (from RFC 6986's Pi', tau and A, by
  `gen/streebog.py`); LPS reads only them, so another representation of
  LPS replaces the tables and `hs.stb.lps` alone.
* **Michael's key** is any `HsW2`; `HsMichael.key` reads it from bytes.

## Laws

`LAWS.bend` (written by `gen/laws.py`) has 77 laws.

**For every input**, with no hypothesis:

* `md_streaming`: the engine's update over `a ++ b` is update over `a`,
  then `b`, from every state, for every chaining value type, compression
  function and block size. The update is a fold of a step over the bytes,
  so this holds by induction on `a`, whatever the step does.
* For each of md4, md5, sha1, ripemd160, sm3, streebog256 and streebog512:
  `<h>_streaming` (the same at the hash's own defs, for every state),
  `<h>_split` and `<h>_split3` (the streaming digest of any split into two
  or three pieces is the one-shot digest), `<h>_length` (the final digest
  of every state has the digest's size) and `<h>_digest_length` (so has
  the one-shot digest of every message).
* Michael: `michael_streaming`, `michael_split` (under every key),
  `michael_length` and `michael_mic_length` (8 bytes).

**Vectors**, by computation: all seven of RFC 1320's and RFC 1321's test
suites (`md4_rfc1320_1` to `_7`, `md5_rfc1321_1` to `_7`); FIPS 180-4's
two SHA-1 examples; the eight values of the RIPEMD-160 page (all but the
million "a"); SM3's two examples; Streebog's LPS(0), and the first two
compressions of RFC 6986's example 1 (g_N(h, m) and g_0(h, N), as the RFC
prints them); Michael's six vectors (unverified against a published
copy: Specifications above), its MIC on IEEE 802.11-2012 M.6.3's TKIP
frame (`michael_tkip_m63`, verified: above) and the refusal of a 7-byte
key.

**Not laws, and why.** Streebog's whole digests: one compression runs within
`--verdict`'s kernel fuel and two do not, and a digest is at least three;
so RFC 6986's four digests (M1 and M2, both sizes) are checked by
`check.bend` and the ref test, and the laws take the RFC's printed
intermediate values instead. The digests' agreement with the algorithms'
definitions for every message: a hash has no specification beyond its
algorithm, so the vectors and the differential test hold it (as khash
does).

## Tests

* `check.bend` (written by `gen/check.py`): every specification vector
  above through the public interface, the digest in one call and in three
  pieces through init/update/final, including Streebog's four RFC 6986
  digests and the intermediate values, a million bytes "a" through SHA-1
  and RIPEMD-160, Michael's six vectors (whole and in pieces; unverified,
  above), the M.6.3 TKIP MIC (whole and in pieces) and its short key
  refused. The expected lines are the specifications' values.
* `ref/run.sh` (216 cases with the default seed): each hash on 27 message
  lengths (around every block boundary up to three blocks, and 1000 and
  4103 bytes), whole and cut into three pieces at random points, and
  Michael under random keys on the same lengths, against
  * Python's `hashlib` (OpenSSL) for MD5, SHA-1, RIPEMD-160 and SM3;
  * `ref/model.py` for MD4 (OpenSSL 3 keeps it in its legacy provider, so
    hashlib lacks it here), Streebog-256, Streebog-512 and Michael (Python
    has neither). **The model shares an author with the package**: it is
    checked first against every specification vector above (RFC 1320's,
    RFC 6986's digests and intermediate values, and the six Michael
    vectors, which are themselves unverified: Specifications above),
    and its MD5, SHA-1, RIPEMD-160 and SM3 against hashlib, but where
    Python lacks an algorithm the differential test is against that model
    alone. Its tables are `gen/spec.py`'s, so a wrong table would show in
    the specifications' vectors (which agree) rather than in the
    differential test.
* The crypto package's tests run these hashes, HMAC and PBKDF2 over them,
  and Michael as a MAC, against Python's `hmac`, `hashlib.pbkdf2_hmac` and
  `cryptography` (crypto/README.md).

## Sizes

Native builds (Bend 2.0.37, WSL2), a 1 MB pseudo-random message (its
building included): MD5, SHA-1, RIPEMD-160 and SM3 0.12 s each and 84 MB,
Streebog-512 2.8 s and 101 MB (each 64-byte block is 25 LPS
transformations of 64 table lookups). Updates are tail calls over the
bytes, so a message has no length limit beyond memory. `check.bend` takes
about 11 s with its build, the ref test about 21 s; `PROOF.bend` about
70 s, and `--verdict` about 70 s.

## Notes on use

* **MD4, MD5 and SHA-1 are broken for collisions**, and Michael was
  designed for a security level of only about 20 bits, to fit TKIP's old
  hardware. They are here to read and
  write what already uses them (NTLM, legacy file formats, HMAC-SHA-1 in
  existing protocols, TKIP). Use SHA-256 or SHA-512 (crypto's
  `inst_sha2.bend`), SM3 or Streebog for new designs.
* None of this code is constant-time, and Bend's runtime promises nothing
  about running time.

## Dependencies

`DEPS`: `bytes` (Octets, and its laws in the proofs) and `word64` (the
engine's 64-bit block count and the length fields). No hub package.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 216 cases match, `scripts/deps.sh`
passes.
