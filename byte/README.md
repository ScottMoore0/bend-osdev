# bend-osdev-byte

Typed 8- and 16-bit words for Bend: `ByteU8` and `ByteU16`, built as Base
builds `U32` (a `Word(8n)` and a `Word(16n)`), with wrapping arithmetic and
bit operations, comparisons, `Nat`, `U32` and decimal views; the low 8 and
16 bits of a `U32`; and a `U32`'s four bytes, split and joined in either
order. Wrapping at 8 or 16 bits, and the range, are part of the type, which
suits proofs about encodings.

The directory is `byte` and the entry file `byte/byte.bend`; the hub name
is `bend-osdev-byte`.

## Background

This is the code of bendlang/bend#1660, *feat(base): Byte and Word16, with
byte conversions for U32* (Scott Moore, 17 October 2026; commit 3d33c01,
written under Bend's Apache-2.0 licence and published here by its author
under MIT), which proposed `Byte` and `Word16` for Base. The Bend team
closed it (the collaborator Lorenzobattistela's comment of 22 October 2026)
and asked for a hub package instead: Base's byte APIs (`File.read_bytes`, TCP and UDP, `args_bytes`) all
take and answer `U32`, so a byte type in Base would be a second
representation that nothing in Base produces or consumes, every check
would pay for it (Base 8% larger, and 52 names reserved for every module),
and without natives it would be too slow for I/O; a hub package gives the
packages that roll their own `U8` one shared, proved byte type.

As a package rather than a Base section, every name carries this package's
prefix (CONVENTIONS.md, Names): Base's names are global and a redeclared
one is refused (bendlang/bend#1042), so a package declaring `Byte`,
`Word.lo` or `U32.to_byte` would break the day Base adds them. It uses only
Base's public types and defs (`U32`'s constructor, `Word.*`, `Cmp.*`,
`U32.from_nat`, `U32.shrn`, `U32.show`, and the law `Word.add_comm`).

| bendlang/bend#1660 (Base) | This package |
|---|---|
| `Byte`, `Byte{data}`, `Byte.add` … `Byte.show` | `ByteU8`, `ByteU8{data}`, `ByteU8.add` … `ByteU8.show` (`byte.bend`) |
| `Word16`, `Word16{data}`, `Word16.add` … `Word16.show`, `Word16.of_bytes` | `ByteU16`, `ByteU16{data}`, `ByteU16.add` … `ByteU16.show`, `ByteU16.of_bytes` (`word16.bend`) |
| `U32.to_byte`, `U32.byte`, `U32.of_bytes`, `U32.of_bytes_be` | `ByteU32.to_byte`, `ByteU32.byte`, `ByteU32.of_bytes`, `ByteU32.of_bytes_be` (`byte.bend`) |
| `U32.to_word16` | `ByteU32.to_word16` (`word16.bend`) |
| `Word.lo`, `Word.hi`, `Word.cat` | `ByteBits.lo`, `ByteBits.hi`, `ByteBits.cat` (`bits.bend`) |
| law `Byte.to_u32_to_byte` | law `u8_to_u32_to_byte` |

## Files

| File | Holds |
|---|---|
| `byte.bend` | `ByteU8`, and a `U32`'s bytes (`ByteU32.*`) |
| `word16.bend` | `ByteU16`, and a `U32`'s low 16 bits |
| `bits.bend` | splitting a `Word(m + n)` into its low and high bits, and joining them |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, with their expected output (bendlang/bend#1660's test line first) |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's integers |

## API

| Def | Meaning |
|---|---|
| `ByteU8{data: Word(8n)}` (open) | an 8-bit word, least significant bit first |
| `ByteU8.add`, `.sub`, `.mul` | arithmetic modulo 2^8 |
| `ByteU8.and`, `.or`, `.xor`, `.not`, `.inc`, `.shl`, `.shr` | bits; increments and shifts by one bit wrap |
| `ByteU8.cmp`, `.is_eq`, `.is_lt`, `.is_le`, `.is_gt`, `.is_ge` | comparisons |
| `ByteU8.to_nat`, `.to_u32`, `.from_nat(n)`, `.show` | the value as a `Nat` and a `U32` (0 to 255); n mod 256; decimal |
| `ByteU32.to_byte(a)` | the low 8 bits of a `U32` |
| `ByteU32.byte(a, i)` | byte i of a `U32`, 0 the least significant |
| `ByteU32.of_bytes(b0, b1, b2, b3)`, `ByteU32.of_bytes_be(b3, b2, b1, b0)` | the `U32` of four bytes, least significant first; most significant first |
| `ByteU16{data: Word(16n)}` (open), `ByteU16.add` … `ByteU16.show` | the same for 16 bits (`word16.bend`) |
| `ByteU32.to_word16(a)` | the low 16 bits of a `U32` (`word16.bend`) |
| `ByteU16.of_bytes(b0, b1)` | the `ByteU16` of two bytes, least significant first |
| `ByteBits.lo(m, n, w)`, `.hi(m, n, w)`, `.cat(m, n, a, b)` | the low m bits and the high n bits of a `Word(m + n)`; their join (`bits.bend`) |

The types are open, as Base's `U32` is: the bits are the representation, so
proofs about bytes can split them with a deep pattern (`PROOF.bend` does).

## Adapting a package that rolls its own U8

Several hub packages declare their own `U8` (bendlang/bend#1660 counted 11,
eight of them UTF-8 decoders whose `U8` is the decoder's state rather than
a byte). Such a package can keep its type and convert at its boundary,
through `U32`, the shape Base's byte I/O uses:

```
import bend-osdev-byte@0.1.0.0/byte.bend as By

def MyU8.to_byte(x: MyU8) -> By.ByteU8:
  By.ByteU32.to_byte(MyU8.to_u32(x))      # the low 8 bits

def MyU8.of_byte(b: By.ByteU8) -> MyU8:
  MyU8.from_u32(By.ByteU8.to_u32(b))      # 0 to 255
```

If its `U8` already holds a `Word(8n)`, the conversion is the constructor
itself (`By.ByteU8{w}`, and a match on `By.ByteU8{w}` back), with no
arithmetic. The laws `u8_to_u32_to_byte` and `u32_to_byte_low` say the
`U32` route loses nothing for a byte and keeps the low 8 bits of anything
else.

## Extension points

* **Widths:** `ByteBits.lo`, `.hi` and `.cat` split and join words of any
  width, so a 24- or 48-bit word built the same way needs only its type and
  defs.
* **The representation:** the defs are plain Bend over `Word`, with no
  natives; a faster representation would change only `byte.bend` and
  `word16.bend`, and the laws say what it must keep.
* **Other byte types:** convert through `U32` (above) or the constructor.

## Laws

`LAWS.bend`, 12 laws, all proved:

* **Properties, for every input:** `u8_to_u32_to_byte` (bendlang/bend#1660's
  law: a byte to a `U32` and back is itself), `u16_to_u32_to_word16` (the
  same for 16 bits), `u32_to_byte_low` and `u32_to_word16_low` (a `U32` to a
  byte or 16-bit word and back is `U32.and(255, a)` or `U32.and(65535, a)`),
  `u32_bytes_join` (a `U32`'s four bytes join back to it),
  `u32_join_bytes` (the bytes of four bytes joined are those four),
  `u16_of_bytes_u32` (two bytes joined as a `ByteU16` are the `U32` with
  those low bytes), `u8_add_comm` and `u16_add_comm` (from Base's
  `Word.add_comm`).
* **Vectors** (bendlang/bend#1660's test, `tests/base/byte_word16.bend`):
  `vec_bytes_join` (0x12345678 split and joined), `vec_of_bytes_be`,
  `vec_add_wraps` (250 + 10 = 4).

The bit laws split their words into bits with a deep pattern and compute;
the rest of the arithmetic is Base's `Word` arithmetic at 8 and 16 bits,
tested rather than proved here.

## Tests

* `check.bend`: bendlang/bend#1660's test line (`[4, 254, 16, 85, 2, 120,
  18, 1, 4660, 305419896, 305419896]`), then comparisons, `Nat` views,
  `from_nat` past 256 and 65536, wrapping at 16 bits, and the low bits of
  0xDEADBEEF.
* `ref/run.sh` (1904 cases with the default seed) compares every operation
  with Python's integers: for both widths, arithmetic, bit operations,
  shifts, increments, the five comparisons, `to_nat`, `to_u32` and
  `from_nat` of numbers up to 2^20, on edge values (0, 1, the maximum, the
  top bit alone and one below it) and random ones; for `U32`s (edge values
  and random), the low 8 and 16 bits and the four bytes; and random bytes
  joined both ways and as a 16-bit word.

## Dependencies

None: Base only.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 1904 cases match, `scripts/deps.sh`
passes.
