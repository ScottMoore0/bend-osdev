# bend-osdev-bytes

Byte strings, and the fixed-width fields that binary formats store in them.
The shared helpers every bend-osdev parser uses.

A byte string is an `Octets`: bytes 0 to 255, convertible to and from a
`List<&2, U32>`, the shape Base's own I/O uses (`File.read_bytes`, `TCP.send_bytes`). Readers take the
low 8 bits of each element, so a malformed element is masked, never trusted.

## Octets: the byte-string interface

Public interfaces in bend-osdev take and answer `Octets`. Its storage is
internal, so it can change without touching any other package. Today it is a
list of 8-bit words (`Word(8n)`), so every value of the type is a valid byte
string: no element can be 256 or more, and converting to a list and back gives
every `Octets` back unchanged.

| Def | Meaning |
|---|---|
| `Octets.of_list`, `Octets.to_list` | convert from and to `List<&2, U32>` (`of_list` masks each element to 8 bits) |
| `Octets.of_string`, `Octets.to_string`, `Octets.hex` | text |
| `Octets.empty`, `Octets.zeros(n)`, `Octets.cons(b, o)`, `Octets.append`, `Octets.concat` | building |
| `Octets.len`, `Octets.take`, `Octets.drop`, `Octets.slice(i, n, o)`, `Octets.at`, `Octets.is_eq` | slicing and reading |
| `Octets.split_at(n, o)` | `Some{OctetsSplit{head, rest}}` (the first `n` bytes and the rest), or `None` if `o` is shorter than `n` |
| `mask(xs)` | each element of a list masked to 8 bits (what `of_list` keeps) |
| `Octets.le16` to `Octets.be64`, `Octets.le16_at` to `Octets.be64_at` | fields, written and read (a reader walks to its offset and reads only the field's bytes) |

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
  (the interface laws below), never the inside of `Octets`. Packed words, or
  chunks of an `Array`, can replace the list of words without changing any
  other package, as long as the interface laws still hold.
* **Fast paths can be added behind the same defs,** with a law (or a
  differential test) tying each to the bit-slicing reference.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every value:** each of the five field formats reads back what was
  written (16-bit reads give `low16(v)`); `byte(b)` is below 256; and
  `append(take(n, xs), drop(n, xs)) == xs` for every `n` and `xs`;
* **the same round trips and slicing on `Octets`**, and `Octets.is_eq` is
  reflexive;
* **interface laws, for every input, for dependents' proofs** (how `Octets`
  relates to lists, whatever its storage):
  * `octets_of_to`: `of_list(to_list(o)) == o`;
  * `octets_to_of`: `to_list(of_list(xs)) == mask(xs)`;
  * `octets_append_list`: `to_list(append(a, b)) == append(to_list(a), to_list(b))`;
  * `octets_len_list`: `len(o) == len(to_list(o))`;
  * `octets_zeros_list`, `octets_cons_list`: `zeros` and `cons` as lists;
  * `octets_take_append`, `octets_drop_append`: `take(len(a), append(a, b)) == a`
    and `drop(len(a), append(a, b)) == b`;
  * `octets_split_at_append`: `split_at(len(a), append(a, b)) == Some{OctetsSplit{a, b}}`;
* **vectors:** the byte orders, reading at an offset, short inputs, masking an
  element above 255, slicing, splitting, and hex text.

## Speed

The field readers and writers are built from bit slicing, not shifts and
masks, so their round trips can be proved for every value. That costs speed:
use them for header fields, not bulk data.

Bend 2.0.37's runtime overflows its own fixed stack (raising `ulimit -s`
does not help) somewhere between 10,000 and 40,000 nested non-tail calls.
So `Octets` runs tail-recursive forms (`w8s.*.fast`, `w8s.len.go`, `w8s.eq`,
and the text and hex builders), and each is proved equal to its structural
form for every input in `PROOF.bend`, which is what the laws reason about.
`Octets.of_list`, `to_list`, `append`, `take`, `drop`, `len`, `zeros`,
`split_at`, `is_eq`, `hex` and `to_string` have no length limit.
`Octets.concat` recurses on the number of pieces, not their size.

Measured on the reference machine (native build): a 2,000,000-byte `Octets`
built, appended, cut and printed in 4 s, peaking at 1.7 GB. Storage is the
cost now: each byte is an 8-bit `Word`, about 940 bytes of memory per byte,
against about 57 for an element of a `List<&2, U32>`. Hold images of more
than a few MB a block at a time (blockdev's `MemDev`).

The list layer (`take`, `drop`, `append`, `len`, `mask`, `hex`, ... on
`List<&2, U32>`) is still structural, because other packages' proofs compute
through it; use it on header-sized lists, and `Octets` for bulk data.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes.
