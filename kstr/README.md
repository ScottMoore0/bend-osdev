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
| `LAWS.bend`, `PROOF.bend` | the hex round trip and the vectors, and their proofs |
| `LAWS_dec.bend`, `PROOF_dec.bend` | the decimal round trips |
| `LAWS_oct.bend`, `PROOF_oct.bend` | the octal round trips |
| `LAWS_hex.bend`, `PROOF_hex.bend` | the hexadecimal round trips (`%x` and `%X`) |
| `LAWS_pad.bend`, `PROOF_pad.bend` | the field width's padding |
| `gen/proof.py` | writes the five proof files (`gen/proof_dec.py`, `gen/proof_fmt.py`, `gen/proof_pad.py`; ring identities by `scripts/natproof.py`) |

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

`LAWS_dec.bend`, **for every input:** parse after format in decimal: for
every `W64` v, `to_u64(format(KFmt.plain(KConvU{}), v), 10) = Done{v}`
(`dec64_round_trip`), and for every `U32` v, `to_u32(format32(KFmt.plain(
KConvU{}), v), 10) = Done{v}` (`dec32_round_trip`). `kfmt.digits` puts
down the remainders of v by 10 (word64's division laws, or the `U32` ones
when v fits) in front of the digits already down, so the tokens of the
digits are the token list of v's quotient followed by `KTDigit{r}`; each
masked digit byte reads as its token (the ten cases of r); and the parse
of the quotient's digits leaves the quotient, one more step, acc 10 + r,
giving v back without overflow (in 64 bits since v < 2^64, in 32 bits
since v < 2^32).

**A bug, found by the proof and fixed:** `KStr.format32` sign-extended
every value, so `%u`, `%x`, `%X` and `%o` of a `U32` with its top bit set
printed the 64-bit two's complement (`%u` of 4294967295 gave
18446744073709551615, `%x` of 2^31 gave ffffffff80000000); only `%d`
reads a 32-bit value as signed. It now extends with zeros for the other
conversions (`kfmt.hi32`), and `check.bend` tests the four cases.

`LAWS_oct.bend` and `LAWS_hex.bend`, **for every input:** the same round
trips in base 8 and base 16: `to_u64(format(KFmt.plain(KConvO{}), v), 8)
= Done{v}` and `to_u32(format32(KFmt.plain(KConvO{}), v), 8) = Done{v}`
(`oct64_round_trip`, `oct32_round_trip`); with `KConvX{}` and
`KConvXUpper{}` in base 16 (`x64_round_trip`, `x32_round_trip`,
`xu64_round_trip`, `xu32_round_trip`). `gen/proof_fmt.py` runs the decimal
generator with its base and its letters' case set, and adds what differs: a
remainder from 10 to 15 is a letter (87 + r for `%x`, 55 + r for `%X`) and
reads back as `KTDigit{r}` (its 16 cases); base 16's front end looks for an
`x` at the second token, and the digits' second token is a digit or there
is none; and the 32-bit accumulator shifts the digit in, in base 8 and 16,
instead of multiplying. With q·B + r = v < 2^32, q < 2^29 (2^28), so the
accumulator's top bits are clear and the test passes, and the shifted value
is q·2^3 + r (u32's `shln`, `or` and low-bits laws) or, for base 16's
`kstr.ins4` (the bits of r below those of q), r + 2^4·q: a word's value is
that of its low m bits plus 2^m that of the rest (on a copy of word64's bit
concatenation).

`LAWS_pad.bend`, **for every input** of `KStr.format` (every conversion,
flags, width and value; `sprintf` pads each conversion with the same
`kfmt.list`), with u the unpadded form (the same conversion and sign flags,
width 0): the output has max(w, len(u)) bytes (`pad_len`); left-justified,
its first len(u) bytes are u (`pad_left`); right-justified with spaces,
dropping its first w − len(u) bytes leaves u (`pad_right`). `kfmt.pad`
puts sign ++ digits ++ fill spaces, sign ++ fill zeros ++ digits, or fill
spaces ++ sign ++ digits, with fill = w − len(sign ++ digits); the proofs
(`gen/proof_pad.py`) take the lengths of an append and of `kfmt.repeat`,
show that the bytes of a list append are the append of the bytes (from
bytes' `octets_to_of`, `octets_append_list` and `octets_of_to`), and cut
with bytes' take and drop laws.

Not proved for every input: where zero padding puts its zeros (between the
sign and the digits: its length is in `pad_len`), the text of `%d` (the
sign and the magnitude of a negative value), what the padding bytes are,
`KStr.sprintf`'s reading of a format string, and the signed parsers;
`ref/run.sh` checks them.

## Tests

`ref/run.sh` (1,430 cases with the default seed) compares: formatting with
Python's own printf-style `%` operator, on random flags, widths and values
(including 0, 2^63 and 2^64 − 1); `hex32` and its parse; parsing, through
all four parsers, of formatted numbers in every base and of random strings
of digits, signs, prefixes, newlines and junk, with Python's integers under
the rules above; and hex dump lines of random lengths, row sizes, group
sizes and orders against a model of the documented layout.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(4 s, 0.38 GB peak; `--verdict` 9 s, 0.39 GB peak), `PROOF_dec.bend` (5 s,
0.45 GB peak; `--verdict` 6 s, 0.56 GB peak), `PROOF_hex.bend` (3 s, 0.46 GB
peak; `--verdict` 6 s, 0.53 GB peak), `PROOF_oct.bend` (3 s, 0.41 GB peak;
`--verdict` 6 s, 0.56 GB peak) and `PROOF_pad.bend` (2 s, 0.34 GB peak;
`--verdict` 4 s, 0.38 GB peak) ALL PROOFS CHECK, with and without
`--verdict`.

Bend 2.0.37: `PROOF.bend` (20 laws), `PROOF_dec.bend` (2), `PROOF_hex.bend`
(4), `PROOF_oct.bend` (2) and `PROOF_pad.bend` (3) ALL PROOFS CHECK;
`--verdict` ALL PROOFS CHECK on each (`PROOF.bend` about 8 s, peak 0.43 GB;
`PROOF_dec.bend` about 6 s, 0.54 GB; `PROOF_hex.bend` about 6 s, 0.56 GB;
`PROOF_oct.bend` about 6 s, 0.52 GB; `PROOF_pad.bend` about 5 s, 0.38 GB);
`check.bend` passes, `ref/run.sh` 1430 cases match, `scripts/deps.sh`
passes.
