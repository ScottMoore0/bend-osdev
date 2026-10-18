# bend-osdev-kstr

Text conversions for kernel-style interfaces: strict number parsing in the
manner of `kstrtox`, number formatting (a subset of `vsprintf`), hex dump
lines in the layout of `hex_dump_to_buffer` and `print_hex_dump`, and
`match_token`-style option parsing.

Written from the documented behaviour (the kernel's kernel-doc for kstrtox,
printk's format specifiers, hex_dump_to_buffer and match_token) and from ISO
C99 7.19.6.1 for the printf conversions. No GPL source was read.

## Files

| File | Holds |
|---|---|
| `kstr.bend` | `KStrError`; parsing: `KStr.to_u32`, `KStr.to_s32`, `KStr.to_u64`, `KStr.to_s64`, `KStr.to_bool`; the byte classifier `KStr.tok` |
| `format.bend` | `KFmt`, `KConv`; `KStr.format`, `KStr.format32`, `KStr.sprintf`, `KStr.hex32`, `KStr.hex_digit`, `KStr.nib` |
| `hexdump.bend` | `KDump`, `KDumpPrefix`; `KStr.hex_dump_line`, `KStr.hex_dump` |
| `options.bend` | `KStrPattern`, `KStrMatch`; `KStr.match_one`, `KStr.match_token`, `KStr.match_int`, `KStr.match_uint`, `KStr.match_octal`, `KStr.match_hex`, `KStr.split_options` |

## API

Parsing (`kstr.bend`), each taking the bytes (`Octets`) and a base:

* the whole input must be the number, with one optional trailing newline;
* a leading `+`, and for the signed forms a leading `-`;
* base 8, 10 or 16 (2 to 16 also work), or 0 to take it from the prefix:
  `0x`/`0X` and a hex digit is 16, a leading `0` is 8, otherwise 10; in base
  16 an optional `0x`;
* at least one digit; a value out of range is refused, never wrapped.

Errors (`KStrError`): `KStrEmpty` (no digits), `KStrBadChar{pos}` (the
first byte that cannot be there), `KStrRange` (out of range);
`KStrBadFormat{pos}` and `KStrMissingArg` come from `sprintf`.

| Def | Meaning |
|---|---|
| `KStr.to_u32(o, base)`, `KStr.to_u64` | unsigned, 32 or 64 bits (`W64`) |
| `KStr.to_s32(o, base)`, `KStr.to_s64` | signed, two's complement in the result |
| `KStr.to_bool(o)` | `y`, `Y`, `1`, `on` true; `n`, `N`, `0`, `off` false (the first one or two bytes, as kstrtobool) |
| `KStr.format(f, v)`, `KStr.format32(f, v)` | one value (`W64`, or `U32` with `%d` signed 32-bit) by a `KFmt{conv, width, zero, left, plus, space}` |
| `KStr.sprintf(fmt, args)` | `%d %i %u %x %X %o` with the flags `- 0 + space` and a width, and `%%`; arguments are `W64` (`%d`/`%i` read as signed) |
| `KStr.hex32(v)` | the eight lower-case hex digits of a `U32` (`%08x`) |
| `KStr.hex_dump_line(f, o)` | one line of up to `rowsize` bytes: groups in hex separated by spaces, then the text at column rowsize·2 + rowsize/groupsize + 1 |
| `KStr.hex_dump(f, prefix, o)` | every line, each after its prefix (`KDumpOffset`: `%.8x: `) |
| `KStr.match_token(s, table)` | the first `KStrPattern{token, pattern}` matching the whole of s, with its arguments as `Octets` |
| `KStr.match_int`, `match_uint`, `match_octal`, `match_hex` | an argument as a number (bases 0, 0, 8, 16) |
| `KStr.split_options(o)` | the pieces between commas, empty ones skipped |

A `KDump` is `{rowsize (16 or 32), groupsize (1, 2, 4 or 8; 1 when the line
is not a multiple of it), ascii, little}`; `KDump.default()` is 16 bytes,
single bytes, with text. Multi-byte groups print as little-endian numbers
by default, as hex_dump_to_buffer does on little-endian machines; `little =
False` prints them as stored. In a pattern, `%d` (an optional `-` and
decimal digits), `%u`, `%o`, `%x` (at least one digit each, greedy), `%s`
(the rest of the piece, at least one byte) and `%%`; other bytes match
themselves.

## Extension points

* **Bases:** the parsers take any base from 2 to 16.
* **Formats:** `KFmt` is a plain record, so a caller can build conversions
  without a format string; further conversions are a constructor of `KConv`
  and a case in `kfmt.base`.
* **Dump layouts:** `KDump` and `KDumpPrefix` hold the layout's choices.
* **Option tables:** a table is a list of `KStrPattern`s; arguments come back
  as bytes, to be read by the `match_*` helpers or any parser.

## Laws

`LAWS.bend`:

* **for every input:** parse after format gives the value back: for every
  `U32` v, `to_u32(hex32(v), 16) = Done{v}`. The proof splits v into its 32
  bits; each digit byte reads as the digit token of its nibble (16 cases a
  nibble, through bytes' law `octets_to_of`), and on the tokens the parse
  computes, putting the nibbles back four bits at a time.
* **vectors:** kstrtox's rules (the base-0 prefixes, a trailing newline and
  a second one, the signs, empty input, bad bytes, an empty `0x`, out of
  range in bases 8 and 16 and at the signed bounds, 64-bit, booleans);
  sprintf's width, zero-padding with a sign, left-justifying, `+`, space, the
  conversions, `%%`, a missing argument and malformed conversions; the
  kernel documentation's hex dump example, groups of 4, a short line and
  offsets; match_token, `%d` and `%x` arguments, and splitting options.

Not proved for every input: decimal round trips (the digits come from
64-bit division) and the other formats; `ref/run.sh` checks them.

## Tests

`ref/run.sh` (1,430 cases with the default seed) compares: formatting with
Python's own printf-style `%` operator, on random flags, widths and values
(including 0, 2^63 and 2^64 − 1); `hex32` and its parse; parsing, through
all four parsers, of formatted numbers in every base and of random strings
of digits, signs, prefixes, newlines and junk, with Python's integers under
the rules above; and hex dump lines of random lengths, row sizes, group
sizes and orders against a model of the documented layout.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 1430 cases match, `scripts/deps.sh` passes.
