# bend-osdev-bytes

Byte strings, and the fixed-width fields that binary formats store in them.
The shared helpers every bend-osdev parser uses.

A byte string is an `Octets`: bytes 0 to 255, convertible to and from a
`List<&2, U32>`, the shape Base's own I/O uses (`File.read_bytes`, `TCP.send_bytes`). Readers take the
low 8 bits of each element, so a malformed element is masked, never trusted.

## Octets: the byte-string interface

Public interfaces in bend-osdev take and answer `Octets`. Its storage (today a
list of masked bytes) is internal, so it can change without touching any other
package.

| Def | Meaning |
|---|---|
| `Octets.of_list`, `Octets.to_list` | convert from and to `List<&2, U32>` (`of_list` masks each element to 8 bits) |
| `Octets.of_string`, `Octets.to_string`, `Octets.hex` | text |
| `Octets.empty`, `Octets.zeros(n)`, `Octets.cons(b, o)`, `Octets.append`, `Octets.concat` | building |
| `Octets.len`, `Octets.take`, `Octets.drop`, `Octets.slice(i, n, o)`, `Octets.at`, `Octets.is_eq` | slicing and reading |
| `Octets.le16 … be64`, `Octets.le16_at … be64_at` | fields, written and read |

## The list layer

The same operations on `List<&2, U32>` directly. Packages written before
`Octets` use these; new code uses `Octets`.

| Def | Meaning |
|---|---|
| `len`, `take(n, xs)`, `drop(n, xs)`, `append`, `zeros(n)` | list basics |
| `at(xs, i)` | the byte at offset `i`, or `None` |
| `byte(b)` | the low 8 bits of a word |
| `le16 be16 le32 be32` (of a `U32`), `le64 be64` (of a `W64`) | a field's bytes, in storage order |
| `le16_at be16_at le32_at be32_at le64_at be64_at` | read a field at an offset; `None` if the string is too short |
| `low16(v)` | the low 16 bits of a word |
| `of_string`, `to_string`, `hex` | text: one byte per character; two hex digits per byte |

## Extension points

* **The storage of `Octets` is internal.** Only `bytes.bend` knows it; other
  packages use the `Octets.*` defs, and their proofs use this package's laws
  (in particular `octets_append_list`), never the inside of `Octets`. Packed
  words or arrays can replace the list without changing any other package.
* **Fast paths can be added behind the same defs,** with a law (or a
  differential test) tying each to the bit-slicing reference.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every value:** each of the five field formats reads back what was
  written (16-bit reads give `low16(v)`); `byte(b)` is below 256; and
  `append(take(n, xs), drop(n, xs)) == xs` for every `n` and `xs`;
* **the same round trips and slicing on `Octets`**, plus: `of_list` masks
  once (converting back and forth changes nothing), and `Octets.is_eq` is
  reflexive;
* **an interface law for dependents' proofs:** `octets_append_list`, how
  `append` and `to_list` relate;
* **vectors:** the byte orders, reading at an offset, short inputs, masking an
  element above 255, slicing, and hex text.

## Speed

The field readers and writers are built from bit slicing, not shifts and
masks, so their round trips can be proved for every value. That costs speed:
use them for header fields, not bulk data.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes.
