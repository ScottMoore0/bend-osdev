# bend-osdev-bytes

Byte strings, and the fixed-width fields that binary formats store in them.
The shared helpers every bend-osdev parser uses.

A byte string is a `List<&2, U32>` whose elements are 0 to 255, the shape
Base's own I/O uses (`File.read_bytes`, `TCP.send_bytes`). Readers take the
low 8 bits of each element, so a malformed element is masked, never trusted.

## API

| Def | Meaning |
|---|---|
| `len`, `take(n, xs)`, `drop(n, xs)`, `append`, `zeros(n)` | list basics |
| `at(xs, i)` | the byte at offset `i`, or `None` |
| `byte(b)` | the low 8 bits of a word |
| `le16 be16 le32 be32` (of a `U32`), `le64 be64` (of a `W64`) | a field's bytes, in storage order |
| `le16_at be16_at le32_at be32_at le64_at be64_at` | read a field at an offset; `None` if the string is too short |
| `low16(v)` | the low 16 bits of a word |
| `of_string`, `to_string`, `hex` | text: one byte per character; two hex digits per byte |

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every value:** each of the five field formats reads back what was
  written (16-bit reads give `low16(v)`); `byte(b)` is below 256; and
  `append(take(n, xs), drop(n, xs)) == xs` for every `n` and `xs`;
* **vectors:** the byte orders, reading at an offset, short inputs, masking an
  element above 255, and hex text.

## Speed

The field readers and writers are built from bit slicing, not shifts and
masks, so their round trips can be proved for every value. That costs speed:
use them for header fields, not bulk data.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes.
