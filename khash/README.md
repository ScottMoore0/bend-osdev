# bend-osdev-khash

Non-cryptographic hashes for hash tables: Bob Jenkins' lookup3 in the forms
the kernel calls `jhash`, `jhash2` and `jhash_1word` to `jhash_3words`, and
the golden-ratio multiplicative hashes `hash_32`, `hash_64` and `hash_long`.

Written from Jenkins' public-domain description of lookup3 ("Hash functions
for hash table lookup", burtleburtle.net/bob/hash/doobs.html, and the
lookup3 description of mix, final, the initial value 0xdeadbeef + length +
initval and the little-endian tail) and from Knuth, *The Art of Computer
Programming* vol. 3, section 6.4 (multiplicative hashing). No GPL source was
read.

## Files

| File | Holds |
|---|---|
| `khash.bend` | lookup3: `Jhash.jhash` (bytes), `Jhash.jhash2` (words), `Jhash.jhash_3words`, `Jhash.jhash_2words`, `Jhash.jhash_1word`; the state `JhashState`, `jhash.mix`, `jhash.final` |
| `golden.bend` | `KHash.hash32_raw`, `KHash.hash_32`, `KHash.hash_64`, `KHash.hash_long`, and the constants `KHash.golden32`, `KHash.golden64` |

## API

| Def | Meaning |
|---|---|
| `Jhash.jhash(o, initval)` | lookup3 of the bytes `o` (`Octets`), as Jenkins' `hashlittle`: twelve-byte blocks, a little-endian tail padded with zeros, no finish for an empty input |
| `Jhash.jhash2(ws, initval)` | lookup3 of a list of `U32` words, as `hashword` |
| `Jhash.jhash_3words(a, b, c, iv)`, `jhash_2words`, `jhash_1word` | `jhash2` of three, two or one words, without the list |
| `KHash.hash32_raw(v)` | v × 0x61C88647 modulo 2^32 (`__hash_32`) |
| `KHash.hash_32(v, bits)` | its top `bits` bits (0 to 32) |
| `KHash.hash_64(v, bits)`, `KHash.hash_long(v, bits)` | the top `bits` bits (0 to 32) of v × 0x61C8864680B583EB modulo 2^64, for a `W64` |

## Extension points

* **Seeds:** every lookup3 form takes its `initval`, so independent hash
  functions are different seeds.
* **Other constants:** `golden.bend`'s constants are defs; a multiplicative
  hash with another multiplier is the same two lines with it.
* **Streaming:** lookup3 mixes whole blocks, so a streaming form would keep
  `JhashState` and a partial block between pieces; not provided yet, since
  the kernel's jhash takes its key whole.

## Laws

`LAWS.bend`:

* **for every input:** `jhash_3words(a, b, c, iv) = jhash2([a, b, c], iv)`,
  and likewise for two words and one; `hash_32(v, bits)` fits in `bits` bits
  for every v and every `bits` ≤ 32 (shifted right by `bits` it is 0: two
  shifts add, and a U32 shifted right 32 times is 0, by computation on its
  32 bits).
* **vectors:** the values Jenkins publishes with lookup3 (`hashlittle("", 0)`
  = 0xdeadbeef, `hashlittle("", 0xdeadbeef)` = 0xbd5b7dde, "Four score and
  seven years ago" from 0 and 1: 0x17770551 and 0xcd628161), `jhash2` and the
  golden-ratio hashes on values from the independent model.

The hash values for every input are not laws: a hash has no specification
beyond its algorithm, so the differential test holds it.

## Tests

`ref/run.sh` (840 cases with the default seed) compares every function with
a Python model written from Jenkins' description (itself checked against his
published values) on random byte strings (block boundaries 12, 13, 24 and 25
included), word lists, words and seeds, and the golden-ratio hashes with
Python's integers. `check.bend` also hashes 100,000 bytes.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 840 cases match, `scripts/deps.sh` passes.
