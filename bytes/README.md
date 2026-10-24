# bend-osdev-bytes

Byte strings, and the fixed-width fields that binary formats store in them.
The shared helpers every bend-osdev parser uses.

A byte string is an `Octets`: bytes 0 to 255, convertible to and from a
`List<&2, U32>`, the shape Base's own I/O uses (`File.read_bytes`, `TCP.send_bytes`). Readers take the
low 8 bits of each element, so a malformed element is masked, never trusted.

## Octets: the byte-string interface

Public interfaces in bend-osdev take and answer `Octets`. Its storage is
internal, so it can change without touching any other package. Today it is a
list of `OctByte` records (eight bits each), so every value of the type is a
valid byte string: no element can be 256 or more, and converting to a list and back gives
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
| `len.fast`, `take.fast`, `append.fast`, `zeros.fast`, `mask.fast`, `of_string.fast`, `to_string.fast`, `hex.fast`, `list_eq.fast`, `rev`, `rev_onto` | the same, tail-recursive, for long lists; each equals its structural form by a law |

## Extension points

* **The storage of `Octets` is internal.** Only `bytes.bend` knows it; other
  packages use the `Octets.*` defs, and their proofs use this package's laws
  (the interface laws below), never the inside of `Octets`. Packed words, or
  chunks of an `Array`, can replace the list of words without changing any
  other package, as long as the interface laws still hold.
* **Fast paths can be added behind the same defs,** with a law (or a
  differential test) tying each to the bit-slicing reference.

## Laws

`LAWS.bend`:

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
  * `octets_hex_list`, `octets_to_string_list`: `Octets.hex` and `to_string` are the
    list layer's on `to_list(o)`; `octets_concat_nil`, `octets_concat_cons`: `concat`
    joins its pieces in order;
* **reading at an offset, for every input, for dependents' proofs** (what a
  byte, a slice or a field read inside joined, cut or sliced bytes gives,
  whatever the storage):
  * lengths: `octets_len_append`, `octets_len_take` (`min(n, len o)`) and
    `octets_len_take_le`, `octets_len_drop`, `octets_len_slice` and
    `octets_len_slice_le` (a slice inside `o` has its length),
    `octets_len_zeros`, `octets_len_of_list`, and each field writer's width
    (`octets_len_le16` to `octets_len_be64`);
  * joining: `octets_append_assoc`, `octets_append_empty_l`,
    `octets_append_empty_r`, `octets_drop_zero`, `octets_take_len`;
  * take and drop composed: `octets_drop_drop` (`drop(i, drop(j, o)) ==
    drop(j + i, o)`), `octets_take_take` (`take(min(i, j), o)`),
    `octets_take_drop_comm`, `octets_drop_take_comm`;
  * at an offset inside joined bytes: `octets_take_append_le`,
    `octets_take_append_add`, `octets_drop_append_le`,
    `octets_drop_append_add`, `octets_slice_append_le` (a slice ending
    inside `a` is `a`'s), `octets_slice_append_add` (a slice at
    `len(a) + i` of `a ++ b` is `b`'s at `i`); inside cut bytes:
    `octets_slice_drop`, `octets_slice_take`;
  * a byte: `octets_at_list` (`Octets.at` is the list layer's `at` on
    `to_list`), `octets_at_append_add`, `octets_at_append_lt`,
    `octets_at_drop`, `octets_at_take`, and the list layer's `at_append_add`,
    `at_append_lt`, `at_drop`, `at_take`;
  * every field reader (`le16_at` to `be64_at`): `octets_F_at_append_add`,
    `octets_F_at_append_le` (a field ending inside `a`), `octets_F_at_drop`,
    `octets_F_at_take` (a field ending inside the cut);
  * `low16_mask`: a value already masked to 16 bits is its own `low16`;
* **the tail-recursive list layer, for every input:** `len_fast`, `take_fast`,
  `append_fast`, `zeros_fast`, `mask_fast`, `of_string_fast`, `to_string_fast`,
  `hex_fast`, `list_eq_fast` (each stated structural == fast, the direction a
  rewrite uses to turn running code back into what the other laws are about),
  and `rev_rev`;
* **vectors:** the byte orders, reading at an offset, short inputs, masking an
  element above 255, slicing, splitting, and hex text.

## Speed

The field readers and writers are built from bit slicing, not shifts and
masks, so their round trips can be proved for every value. That costs speed:
use them for header fields, not bulk data.

Bend 2.0.37's JavaScript lane (`bend file.bend`) overflows its stack
somewhere between 10,000 and 40,000 nested non-tail calls; a native build
(`bend file.bend -o prog`) has a 2 GB stack and does not (the structural
`len`, `take` and `append` of the list layer run over 10,000,000 elements
natively in 0.26 s and 310 MB).
So that it runs on both lanes, `Octets` uses tail-recursive forms (`w8s.*.fast`, `w8s.len.go`, `w8s.eq`,
and the text and hex builders), and each is proved equal to its structural
form for every input in `PROOF.bend`, which is what the laws reason about.
`Octets.of_list`, `to_list`, `append`, `take`, `drop`, `len`, `zeros`,
`split_at`, `is_eq`, `hex` and `to_string` have no length limit.
`Octets.concat` is tail-recursive too, in the number of pieces and their size.

Measured on a native build (Bend 2.0.37, WSL2): a 2,000,000-byte `Octets`
built, appended to itself, cut and printed as hex in 0.66 s, peaking at
380 MB (about 3 s on the JavaScript lane). Storage: each byte is one
`OctByte` record (eight `Bool` fields); natively a 16 MB `Octets` built from
a list peaks at 1.31 GB, about 80 bytes of memory per byte held (on the
JavaScript lane about 150; an 8-bit `Word`, used before, cost about 450 there,
and a `List<&2, U32>` element about 60). A pipeline that builds, copies and
reads 1 MB peaks at 166 MB natively (about 1 GB on the JavaScript lane).
Hold images of more than a few tens of MB a block at a time (blockdev's
`MemDev`).

The list layer's structural forms (`take`, `append`, `len`, `mask`, `hex`, ...
on `List<&2, U32>`) stay structural, because other packages' proofs compute
through them; use them on header-sized lists. For long lists use the `*.fast`
forms (or `Octets`), and turn them back into the structural forms in proofs
with the `*_fast` laws.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes.
