# bend-osdev-packing

Bit fields at arbitrary bit positions of a byte buffer, packed and
unpacked: the counterpart of Linux's `lib/packing` (`packing()`, `pack()`,
`unpack()`), which drivers use for hardware tables whose fields do not fall
on byte boundaries.

## What it implements

The behaviour follows the documentation of the kernel's packing helpers
(the "Generic bitfield packing and unpacking functions" page of its core API
documentation), restated here in this package's own words; no kernel source
was read.

* **Bit numbering.** A buffer of `L` bytes is one number of `8L` bits.
  Without quirks it is big-endian: byte 0 holds the most significant bits,
  and bit 0 of the buffer is the least significant bit of byte `L - 1`. A
  field is given by its first and last bit, `start >= end`, both inclusive;
  bit `end` of the buffer is bit 0 of the field's value.
* **Quirks** (`PkQuirks{msb_right, little_endian, lsw32_first}`, each a
  `Bool`), as the documentation describes them:
  * `little_endian`: within each 4-byte word, the bytes are in the opposite
    order (the word's least significant byte first);
  * `lsw32_first`: the 4-byte words are in the opposite order (the least
    significant word first);
  * `msb_right`: within each byte, the bits are in the opposite order (the
    field's bit 0 is the byte's most significant bit).
  `packing.quirks_none()` is the plain layout. The two word-wise quirks need
  a buffer whose length is a multiple of 4.
* **Errors**, where the kernel answers `-EINVAL` or `-ERANGE`: `PkBadRange`
  (`start < end`), `PkTooWide` (a field of more than 64 bits), `PkOutOfBuffer`
  (`start` past the buffer's last bit), `PkBadLength` (a word-wise quirk on a
  buffer whose length is not a multiple of 4), `PkOverflow` (`pack` of a
  value that does not fit in the field). `packing.pack_masked` keeps the
  value's low bits instead of refusing.
* **Values** are `W64` (bend-osdev-word64), so a field holds up to 64 bits.

## Files

| File | Holds |
|---|---|
| `packing.bend` | the entry file: `PkError`, the checks, `pack`, `pack_masked`, `unpack`, `bit` |
| `view.bend` | the quirks and the logical view of a buffer: its bits listed from bit 0, and back (`PkQuirks`, `view`, `unview`, the reorderings) |
| `field.bend` | runs of bits (`slice`, `splice`, `nth`) and a `W64` as its 64 bits (`w64_bits`, `bits_w64`, `fits`, `low`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `proof_list.bend`, `proof_view.bend`, `proof_val.bend` | the lemmas: reversals, the 4-byte swap and runs of bits; bytes to bits and back; values to bits and back |
| `check.bend` | examples, with their expected output |
| `ref/model.py`, `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `PkQuirks{msb_right, little_endian, lsw32_first}` (view.bend) | the layout; open |
| `packing.quirks_none()` (view.bend) | no quirks: one big-endian number |
| `PkError`: `PkBadRange`, `PkTooWide`, `PkOutOfBuffer`, `PkBadLength`, `PkOverflow` | why a field cannot be packed or unpacked |
| `packing.pack(q, buf, start, end, v)` | `Result<&2, &2, PkError, Octets>`: `buf` with the field set to `v` |
| `packing.pack_masked(q, buf, start, end, v)` | the same, `v` cut to the field's width |
| `packing.unpack(q, buf, start, end)` | `Result<&2, &2, PkError, W64>`: the field's value |
| `packing.bit(q, buf, k)` | bit `k` of the buffer, as the quirks number the bits |
| `packing.check(q, l, start, end)` | the error a field has on a buffer of `l` bytes, if any |
| `packing.width(start, end)` | `start - end + 1` |
| `packing.view(q, xs)`, `packing.unview(q, bs)` (view.bend) | a buffer's bytes as its bits from bit 0, and back |
| `packing.w64_bits(v)`, `packing.bits_w64(bs)`, `packing.fits(v, w)`, `packing.low(v, w)` (field.bend) | a value as 64 bits from bit 0, and back; whether it fits in `w` bits; its low `w` bits |
| `packing.slice`, `packing.splice`, `packing.nth` (field.bend) | runs of bits |

`packing.put`, `packing.pack.go`, `packing.unpack.go`, the `packing.check.*`
steps, `packing.le_swap`, `packing.order`/`unorder`, `packing.byte_bits`,
`packing.bits_byte`, `packing.bits_of`, `packing.bytes_of` and the word
helpers are internal.

## Extension points

* **The layout is a parameter** (`PkQuirks`); a new layout is a new view:
  `view.bend` is the one place that maps buffer bytes to logical bits, and
  every law about fields is stated through `packing.view` and
  `packing.bit`, so a new quirk changes `view.bend` and its lemmas only.
* **The overflow policy** is the choice between `pack` (refuse) and
  `pack_masked` (cut).
* **Values** are `W64`; a wider value type would replace `w64_bits` and
  `bits_w64` in `field.bend`.
* **No streaming interface:** a field lies inside one buffer.

## Laws

`LAWS.bend`, for **every** quirk setting, buffer, field and value:

* `view_unview`: bits made into bytes and viewed again are themselves (for a
  multiple of 8 bits); `view_mask`: the view reads only each element's low 8
  bits (bytes' `mask` changes nothing); `view_len`, `unview_len`: 8 bits per
  byte;
* `value_bits`: a `W64` made into its 64 bits and back is itself;
* `unpack_pack`: when `pack` answers `Done{b}`, unpacking the same field of
  `b` answers `Done{v}`; `unpack_pack_masked`: after `pack_masked`, the
  value's low bits;
* `pack_rest`, `pack_masked_rest`: every bit outside the field (below `end`
  or above `start`), as `packing.bit` numbers it, is unchanged;
* `pack_len`: the buffer keeps its length;
* **vectors:** a field under each quirk, an unpack across bytes, and each
  error.

**What the proofs rely on.** Beyond bytes' laws (`octets_to_of`,
`octets_len_list`) and word64's `parts_of`, the proofs compute through
bytes' public `byte` and `mask` on symbolic bits (as cipher-modes' and
acpi's proofs do): `mask` keeps a byte's low 8 bits. bytes has no law saying
so; if bytes changed how it computes `byte`, `proof_view.bend` and
`proof_list.bend` would need those lemmas proved again.

## Tests

* `check.bend`: a field under each quirk and their combination, unpacking
  across bytes and in little-endian order, a 64-bit field across 9 bytes,
  every error, a masked pack, and a bit read under `msb_right`.
* `ref/run.sh` compares 300 random cases (`pack`, `pack_masked`, `unpack` and
  `bit` on buffers of 1 to 16 bytes, every quirk combination, fields of 1 to
  64 bits and some invalid ones, values that fit and that do not) with
  `ref/model.py`, which computes where each bit lies as index arithmetic from
  the quirks' documented meaning (the package itself reorders lists of bytes
  and bits). There is no implementation outside the kernel to run; the model
  shares an author with the package but not its method.

## Limitations

* Fields are at most 64 bits wide (the kernel's `u64` value).
* Each pack or unpack rebuilds the buffer's whole bit list, so it is linear
  in the buffer's size; meant for descriptor-sized buffers.

## Dependencies

`bend-osdev-bytes` (buffers are `Octets`) and `bend-osdev-word64` (values
are `W64`).

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 300 cases match, `scripts/deps.sh packing`
ok.
