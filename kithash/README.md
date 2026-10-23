# bend-osdev-kithash

An adapter for bend-kit-hash@0.2.0.0 (FNV-1a, xxHash, SipHash-1-3, CRC-32
and Adler-32 over bend-kit's `Bytes`), and SipHash's instances of
bend-osdev-crypto's MAC interface:

* every bend-kit-hash function on `Octets`, with bend-osdev's `W64` for
  64-bit seeds, keys and results, so that no other package sees bend-kit's
  types (`kithash.bend`);
* CRC-32, Adler-32, FNV-1a 32 and 64, XXH32 and XXH64 (any seed) as
  instances of crypto's hash interface (`inst_hash.bend`): non-cryptographic
  hashes, as crypto's CRC rows are;
* bend-kit-hash's SipHash-1-3, and bend-osdev-siphash's SipHash-c-d and
  HalfSipHash-c-d for every parameter set (SipHash-2-4, Linux's `siphash`,
  among them), as instances of crypto's MAC interface (`inst_mac.bend`);
* laws that bend-kit-hash's CRC-32, Adler-32, XXH64 and SipHash-1-3 agree
  with bend-osdev's own (crc's, deflate's, zstd's, siphash's), so either
  can be swapped for the other, and a differential test on random inputs;
* `AUDIT.md`: an audit of bend-kit-hash@0.2.0.0 against REVIEW.md.

The directory is `kithash` and the entry file `kithash/kithash.bend`; the
hub name is `bend-osdev-kithash`. It is a package of its own, with its own
`gen/instances.py` (as pubkey is), so that crypto's check, near its memory
limit, takes no more rows.

## Specifications

* **The algorithms:** CRC-32/ISO-HDLC (the reveng CRC catalogue's
  parameters and check value, as crc/README.md cites it); Adler-32 (RFC
  1950, section 2.2 and section 9); FNV-1a (RFC 9923, *The FNV
  Non-Cryptographic Hash Algorithm*, 2026, sections 2 and 5, and the
  section 8.3 test values); XXH32 and XXH64 (*xxHash fast digest
  algorithm*, xxhash_spec.md of the xxHash project, Yann Collet, version
  0.2.0, which has no test values); SipHash (bend-osdev-siphash/README.md:
  the Aumasson-Bernstein paper and the reference implementation).
* **The interfaces:** crypto/README.md's hash and MAC interfaces and their
  laws.
* **bend-kit-hash itself:** its published `hash.bend` (BendHub,
  bend-kit-hash@0.2.0.0), whose header names its sources.

## Files

| File | Holds |
|---|---|
| `kithash.bend` | the adapter: each bend-kit-hash function on `Octets` and `W64` (`Kh*.value`) |
| `inst_hash.bend` | the buffered state `KhBuf` and the six hashes' digests: the hash interface's instances |
| `inst_mac.bend` | the SipHash and HalfSipHash keys and tags: the MAC interface's instances |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (the per-instance ones in generated regions) |
| `check.bend` | every instance through the interfaces, and the agreement on 10,000 bytes |
| `gen/instances.py` | the table of instances: writes their laws in `LAWS.bend` and proofs in `PROOF.bend` (`--check` checks them) |
| `ref/model.py` | XXH32, XXH64 and FNV-1a in Python, from their specifications |
| `ref/gen.py`, `ref/run.sh` | the differential test (below) |
| `AUDIT.md` | the audit of bend-kit-hash@0.2.0.0 |

## Public interface

**`kithash.bend`**: `KhCrc32.value(o)`, `KhAdler32.value(o)`,
`KhFnv1a32.value(o)` (each a `U32`), `KhFnv1a64.value(o)` (a `W64`),
`KhXxh32.value(seed, o)` (a `U32` seed), `KhXxh64.value(seed, o)` (a `W64`
seed and result), `KhSip13.value(k0, k1, o)` (the key's two little-endian
64-bit words; a `W64`).

**`inst_hash.bend`**: `KhBuf` (opaque), `KhBuf.init()`, `KhBuf.update(s,
o)`, `KhBuf.final(~digest, s)`, `KhBuf.bytes(s)`; the one-shot digests
`KhCrc32.digest`, `KhAdler32.digest`, `KhFnv1a32.digest`,
`KhFnv1a64.digest`, `KhXxh32.digest(~seed)`, `KhXxh64.digest(~seed)` (the
value big-endian: crypto's CRC-32 digest form, and xxHash's canonical
form). As the hash interface's template arguments (`~H, ~bsize, ~dsize,
~init, ~update, ~final, ~digest`):

| Instance | Template arguments |
|---|---|
| CRC-32 | `~KhBuf, ~64n, ~4n, ~KhBuf.init(), ~KhBuf.update, ~KhBuf.final(~KhCrc32.digest), ~KhCrc32.digest` |
| Adler-32, FNV-1a 32 | the same with `KhAdler32.digest`, `KhFnv1a32.digest` |
| FNV-1a 64 | the same with `~8n` and `KhFnv1a64.digest` |
| XXH32, XXH64 with a seed | `~4n` / `~8n` and `KhXxh32.digest(~seed)` / `KhXxh64.digest(~seed)` |

**`inst_mac.bend`**: `KhSip.err` (onto `CrError`), `KhSip.key`,
`KhHsip.key` (`CrBadKeyLength` for a key that is not 16, or 8, bytes);
`KhSip.compute(~prm)`, `KhSip.verify(~prm)`, `KhSip13.compute`,
`KhSip13.verify`, `KhHsip.compute(~prm)`, `KhHsip.verify(~prm)`. As the
MAC interface's template arguments (`~K, ~key, ~compute, ~verify`):

| Instance | Template arguments |
|---|---|
| SipHash-c-d (siphash), any `S.SipParams`: `sip24()`, `sip13()`, `sip48()`, `sip24_wide()` | `~S.SipKey, ~KhSip.key, ~KhSip.compute(~prm), ~KhSip.verify(~prm)` |
| bend-kit-hash's SipHash-1-3 | `~S.SipKey, ~KhSip.key, ~KhSip13.compute, ~KhSip13.verify` |
| HalfSipHash-c-d (siphash): `HS.HalfSipParams.hsip24()`, `hsip13()`, `hsip24_wide()` | `~HS.HsipKey, ~KhHsip.key, ~KhHsip.compute(~prm), ~KhHsip.verify(~prm)` |

The SipHash instances share siphash's 16-byte key and tag form (8 bytes,
little-endian), so bend-kit-hash's SipHash-1-3 and siphash's are
interchangeable. Everything else (`kh.*`) is internal.

## How bend-kit-hash is reached

* **Bytes** cross through bend-kit-hash's own byte-string forms (`*.str`:
  bend-kit-bytes' `from_string`, one Char per octet), as lz4 does for
  XXH32; kitbytes' `of_octets` would do as well, and would add a second
  adapter to the path for nothing.
* **64-bit words** cross through bend-kit-hash's arithmetic (`mul32`,
  `W64.swap`, `W64.add`, `W64.lo`), never its `W64` constructor: it
  publishes no constructor def and no accessor for the high half, and the
  arithmetic survives a change of representation (AUDIT.md).

## Extension points

* **The digest of the buffered state** is any one-shot `~digest`: the
  streaming and split laws hold for every one (`khbuf_*`), so another
  one-shot hash plugs in with a digest def and a row in `gen/instances.py`
  (its length law needs its value's width).
* **Seeds** are template arguments (`~seed`); **SipHash's parameters** are
  siphash's `SipParams` (any c, d and output width).
* **Swapping implementations:** each bend-kit-hash hash with a bend-osdev
  counterpart can be replaced by it (crypto's `CrCrc32` instance for
  CRC-32, deflate's `Adler32` and zstd's `ZstdXxh64` for streaming, siphash
  for SipHash-1-3), as the agreement laws and ref test show.
* **A MAC** plugs in with a key def mapping its errors onto `CrError` and a
  row in `gen/instances.py`'s MAC table.

## Laws

`LAWS.bend` has 57 laws, all proved and accepted by `--verdict`.

* **The buffered state, for every digest function and input:**
  `khbuf_streaming` (the state after a ++ b is the state after a, then b,
  for every state), `khbuf_split` and `khbuf_split3` (in two or three
  pieces, the one-shot digest of the whole), `khbuf_bytes`. Proved from
  bytes' `octets_append_list` and `octets_of_to` (associativity of
  `Octets.append`, and the empty string as its unit).
* **Per instance** (`gen/instances.py`): `<h>_hash_split`,
  `<h>_hash_split3`, `<h>_hash_length` (the digest has 4 or 8 bytes, from
  every state) for h = crc32, adler32, fnv1a32, fnv1a64, xxh32 (every
  seed), xxh64 (every seed); `<m>_mac_accepts` and `<m>_mac_agrees` (verify
  accepts exactly the computed tag, for every key and message) for m =
  siphash (every parameter set), kit_siphash13, halfsiphash (every
  parameter set).
* **Agreement with bend-osdev's own implementations, by computation:**
  `crc32_agrees_*` (bend-kit-hash's CRC-32 instance and crypto's
  `CrCrc32` over crc, on the empty input and the check string; the values
  on 37 bytes), `adler32_agrees_*` (with deflate's, on the empty input,
  "Wikipedia" and 300 bytes of ff, where the sums wrap), `xxh64_agrees_*`
  (with zstd's, on the empty input, "abc", 12 bytes with a seed, and 45
  bytes: a stripe, a lane, a word and a byte), `sip13_agrees_*` (the
  SipHash-1-3 MAC instances, on 0, 1, 7, 8, 12 and 15 bytes). Each input
  reaches a different branch of bend-kit-hash's code.
* **Published vectors through the adapter:** CRC-32's check value; RFC
  9923 section 8.3's FNV-1a 32 and 64 values for "a", "foobar" and
  "Hello!" 01 ff ed; XXH32 of the empty input, "abc" and 00 .. 13, the lz4
  command's values; SipHash-1-3 of 00 .. 0e, the openssl command's value;
  the refusal of a 15-byte SipHash key and a 16-byte HalfSipHash key.

**Not proved, and tested:** agreement for every input. bend-kit-hash
computes over `Array` words through bend-kit-bytes' buffer invariant
(every byte past `len` is zero), and neither Base's `Array` nor
bend-kit-bytes publishes laws a proof could use. So the agreement holds by
computation on the vectors above, and is tested on random inputs below. The hash values of bend-kit-hash for every input
(its correctness) are likewise tested, not proved.

## Tests

* `check.bend`: each hash instance on "123456789" one-shot and in three
  pieces through crypto's `CrHash.of_pieces` (XXH32 and XXH64 with seeds 0
  and 1); bend-kit-hash and bend-osdev's own CRC-32, Adler-32, XXH64 and
  SipHash-1-3 on 10,000 pseudo-random bytes, side by side, and XXH32 and
  FNV-1a 64 on them; the MAC instances through `CrMac.compute_with` from
  raw keys: SipHash-2-4 on the paper's Appendix A, with verify accepting
  its tag and refusing it changed, SipHash-2-4 with the 128-bit output,
  both SipHash-1-3s (verify likewise), HalfSipHash-2-4 and -1-3; keys of
  the wrong length refused. Expected values: Python's zlib (CRC-32,
  Adler-32), `ref/model.py` (XXH32, XXH64, FNV-1a; checked against the lz4
  and zstd commands and RFC 9923), the openssl command and `vectors.h`
  (SipHash), siphash's `ref/model.py` (HalfSipHash-1-3).
* `ref/run.sh` (592 cases with the default seed): 74 inputs: lengths 0 to
  3, lengths at bend-kit-bytes' buffer sizes (4 * 2^d bytes for d = 1 to
  8, and 5 and 1 below, 1 and 3 above, where bend-kit-hash's readers fetch
  a word past the buffer and Base's `Array` wraps to word 0), and 30
  random lengths up to 300 bytes, random contents: bend-kit-hash's CRC-32
  and crc's against Python's `zlib.crc32`; bend-kit-hash's Adler-32 and
  deflate's against `zlib.adler32`; bend-kit-hash's XXH32 (seed 0) against
  the lz4 command's frame checksum, and with a random seed against
  `ref/model.py`; bend-kit-hash's XXH64 and zstd's, seed 0 and a random
  seed, against `ref/model.py`, whose low 32 bits match the zstd command's
  frame checksum on every input; FNV-1a 32 and 64 against `ref/model.py`;
  bend-kit-hash's SipHash-1-3 and siphash's against the openssl command
  (random keys); CRC-32 and XXH64 through the hash interface in two pieces.
  **`ref/model.py` shares an author with this package** (not with
  bend-kit-hash or bend-osdev's crc, deflate and zstd); it is checked
  first against RFC 9923's values and the lz4 and zstd commands.

## Sizes

bend-kit-hash's functions are tail-recursive word loops; the buffered
state holds the whole message (about 80 bytes per byte held, natively),
and each digest copies it into a bend-kit-bytes buffer through a string.
Native build (Bend 2.0.37, WSL2), 1 MB of pseudo-random bytes, each run
including building the input (0.95 s and 131 MB alone): bend-kit-hash's
XXH64 1.22 s and 163 MB, zstd's 1.44 s and 167 MB; bend-kit-hash's CRC-32
1.09 s and 176 MB, crc's 1.01 s and 159 MB (results checked against the
zstd command and zlib). `check.bend` takes about 6 s with its build.

## Notes on use

None of these hashes is cryptographic, and HMAC over one is not a secure
MAC (crypto/README.md's note on CRCs applies to all six). SipHash-2-4 is a
MAC; SipHash-1-3 and HalfSipHash are for hash tables (siphash/README.md).
bend-kit-hash's SipHash-1-3 assumes the buffer's bytes past its length are
zero: through this adapter they always are (AUDIT.md).

## Dependencies

`DEPS`: `bytes`, `word64`, `crypto` (the interfaces, `CrError`; crypto's
CRC-32 instance in the agreement laws), `siphash` (the SipHash MACs, and
the key form shared with bend-kit-hash's SipHash-1-3), `crc`, `deflate`,
`zstd` (their CRC-32, Adler-32 and XXH64, in the agreement laws and tests
only), and the hub package `bend-kit-hash@0.2.0.0` (approved at exactly
that version; it brings bend-kit-bytes@0.3.2.0 and bend-kit-int@0.2.0.0).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 23 s, 324 MB),
`--verdict` ALL PROOFS CHECK (about 40 s, 381 MB), `check.bend` passes,
`ref/run.sh` 592 cases match, `scripts/deps.sh` passes.
