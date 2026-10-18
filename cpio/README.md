# bend-osdev-cpio

The "new ASCII" (newc, magic `070701`) and "crc" (`070702`) cpio archive
formats: the formats the Linux initramfs is written in. Build an archive from
a list of entries, parse an archive back into its entries, and compute the crc
format's checksum. Byte strings are `Octets` (bend-osdev-bytes).

## Specification

* The cpio(5) manual page of libarchive / FreeBSD ("New ASCII Format" and
  "New CRC Format"; BSD-licensed documentation).
* The Linux kernel's documentation of the initramfs buffer format
  (`Documentation/driver-api/early-userspace/buffer-format.rst`): the
  documentation only, not the kernel's code.

Each entry is a 110-byte header, the name, and the data. The header is the
six-byte magic and thirteen fields of eight ASCII hex digits each: `ino`,
`mode`, `uid`, `gid`, `nlink`, `mtime`, `filesize`, `devmajor`, `devminor`,
`rdevmajor`, `rdevminor`, `namesize` and `check`. The name is `namesize` bytes,
its terminating NUL included, padded with NULs so that header and name end on
a multiple of four bytes; the data is `filesize` bytes, padded to a multiple of
four. The archive ends with an entry named `TRAILER!!!`. In the crc format,
`check` is the sum of the data bytes modulo 2^32; in newc it is zero and
readers ignore it.

Choices this package makes where the specification leaves them open: it
writes upper-case hex digits and reads either case; it writes the trailer
with `nlink` 1 and every other field 0; it does not pad the archive to a
block (an initramfs may be padded; `Cpio.parse` ignores everything after the
trailer's name); it skips padding without checking that it is zero.

## Files

| File | Holds |
|---|---|
| `cpio.bend` | the archive format: entries, headers, `Cpio.build`, `Cpio.parse`, the checksum |
| `hexfield.bend` | a 32-bit value as eight ASCII hex digits, the encoding of every header field |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

## Public interface

`cpio.bend`:

| Def or type | Meaning |
|---|---|
| `CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}` | an entry; `name` (without its NUL) and `data` are `Octets` |
| `CpioEntry.file(name: String, mode, data)` | an entry with the usual defaults (inode 0, one link, owner and time 0) |
| `CpioEntry.name_string(e)` | the name as a `String` |
| `CpioFormat`: `CpioNewc{}`, `CpioCrc{}`; `CpioFormat.default()` | the format to write; the default is newc, as the initramfs uses |
| `Cpio.build(fmt, es) -> Octets` | the archive: each entry, then the trailer |
| `Cpio.parse(o) -> Result<&2, &2, CpioError, List<&2, CpioEntry>>` | the entries up to the trailer, in either format |
| `CpioError`: `CpioTruncated`, `CpioBadMagic`, `CpioBadHex`, `CpioBadNameSize`, `CpioNoNul`, `CpioBadChecksum`, `CpioNoTrailer` | why an archive was refused: it ends inside an entry; a magic other than 070701 or 070702; a field that is not eight hex digits; a name size of 0; a name without its NUL; a crc entry whose data does not sum to its check; no trailer before the end |
| `CpioHeader{format, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}` | a header, as stored |
| `CpioHeader.encode(h) -> Octets`, `CpioHeader.decode(o) -> Result<…, CpioHeaderAt>` | one header's 110 bytes, and reading one back (`CpioHeaderAt{header, rest}`) |
| `CpioEntry.header(fmt, e)` | the header `Cpio.build` writes for an entry |
| `Cpio.checksum(o)` | the crc format's check: the sum of the bytes, modulo 2^32 |
| `Cpio.trailer_name()`, `Cpio.is_trailer_name(name)` | `TRAILER!!!` |
| `CpioEntry.valid(e)`, `CpioEntry.valid_all(es)` | the entries an archive can hold (see Laws) |

`hexfield.bend`:

| Def | Meaning |
|---|---|
| `hexfield_encode(v) -> Octets` | the eight upper-case hex digits of `v` |
| `hexfield_decode(o) -> Maybe<&2, U32>` | the value of the eight hex digits at the head of `o`, either case; `None` if there are fewer than eight or one is not a hex digit (a low-level field reader, so it answers `Maybe`) |

Everything else in the two files (the list-level `fields.*`, `hdr.*`,
`entry.*`, `parse.go`, `split`, `skip`, `pad4`, `size32`, …) is internal.

## Extension points

* **The format is a parameter:** `Cpio.build` takes a `CpioFormat`, with
  `CpioFormat.default()` (newc) for the usual choice. `Cpio.parse` reads both,
  entry by entry.
* **Entries are plain data:** a caller building an initramfs makes
  `CpioEntry` values (or uses `CpioEntry.file`) and sets inode numbers,
  owners, times and device numbers as it needs; hard links are entries that
  share an inode, as the format defines them.
* **The header layer is separate:** `CpioHeader.encode`/`decode` and
  `hexfield_encode`/`decode` can be used on their own, for a reader that
  streams entries or skips their data.
* **Not covered yet:** the old binary and "odc" (`070707`) formats, writing
  the trailer padded to a block, and an incremental parser that takes the
  archive in pieces. Each would be an addition beside the current defs.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every input:**
  * `hexfield_round_trip`: for every `U32`, its eight digits read back as it
    (proved by splitting the value into its 32 bits and the 16 cases of a
    digit);
  * `header_round_trip`: for every header, `CpioHeader.decode` of
    `CpioHeader.encode` gives it back, with nothing after it;
  * `parse_build`: for every format and every list of entries that
    `CpioEntry.valid_all` admits, `Cpio.parse(Cpio.build(fmt, es)) ==
    Done{es}`, proved by induction on the list. `CpioEntry.valid` asks that
    the data, and the name with its NUL, are shorter than 2^32 bytes (they
    must fit their size fields); and that the name is not `TRAILER!!!`.
    Reading the name and data back as `Octets` uses bytes' interface law
    `octets_of_to` (`of_list(to_list(o)) == o` for every `o`).
  * `valid_example`: the hypothesis is satisfiable (an ordinary one-file
    archive meets it), so `parse_build` is not vacuous;
* **vectors:** hex digits in both cases, a non-digit and a short field
  refused; the checksum of `hello`; the 240 bytes of a one-file archive
  (checked against `ref/gen.py`); empty archives in both formats; bytes after
  the trailer ignored; and one archive for each error: empty input, no
  trailer, a truncated header, truncated data, the `070707` magic, a non-hex
  digit, a bad checksum, a name size of 0, a name without its NUL; and the
  newc format ignoring its check field.

## Tests

`ref/run.sh` (100 cases) compares the package with `ref/gen.py`, an
independent encoder and decoder written in Python from the same
specification, in both directions: `Cpio.build` on 40 random entry lists
(random names, modes, sizes up to 160 bytes, data, and field values,
in both formats) must give the bytes the Python encoder gives; `Cpio.parse`
on 60 archives from the Python encoder (either case of digit, sometimes
padded to 512 bytes), half of them corrupted (truncated, a bad magic, a
non-hex digit, a zero name size, a missing NUL, changed data, no trailer),
must give the entries or the error the Python decoder gives.

There is no cpio tool in the test environment, so this reference **shares an
author with the package**: it was written from the same reading of the
specification, so it can catch slips of implementation but not a shared
misreading. It is weaker than a third-party tool (GNU cpio, bsdcpio, the
kernel's `gen_init_cpio`) would be. The one-file archive vector was also
checked by hand against cpio(5).

## Sizes

**Lanes.** The figures in this section were measured on bend's JavaScript lane
(`bend file.bend`, which runs `main` inside the bend process). That lane's
stack overflows at some tens of thousands of nested non-tail calls, and it
uses several times the memory of a native build (`bend file.bend -o prog`),
which has a 2 GB stack; see AGENTS.md, "Runtime and checker limits". They
will be re-measured natively once W64-heavy code builds natively
(bendlang/bend#1069).

Every loop over an archive's bytes or entries is a tail call (Bend 2.0.37's
runtime overflows its stack at some tens of thousands of nested calls), so
neither a file's length nor the number of entries has a limit beyond
memory. The structural forms the proofs reason about stay beside the loops
in `cpio.bend` (`split.ref`, `nat.half.ref`, `parse.go.ref`,
`Cpio.build.ref`), and `PROOF.bend` proves each equal to its loop for every
input (`split_eq`, `half_eq`, `parse_eq`, `build_eq`).

Measured on Bend 2.0.37's JavaScript lane (WSL2), building an archive in the crc
format and parsing it back (the archive's length, byte sum and entries
checked against a Python encoder):

| Archive | Time | Peak RAM |
|---|---|---|
| 1 MB: one 512 KB file and 2,790 files of 64 bytes | 6.9 s | 2.6 GB |
| 1 MB: 8,000 empty files | 15.7 s | 1.3 GB |

Most of the memory is `Octets` (about 940 bytes per byte
when measured; bytes' compact `OctByte` storage, merged since, holds an
`Octets` in about a third of that, about 150 bytes per byte, and these
figures have not been re-measured) and the list
forms the parser reads. Before this, a 64 KB file overflowed the stack (the
data was split and measured by structural recursion), and so did parsing
3,000 entries. `check.bend` builds and parses a 96 KB archive (a 48 KB file
and 250 small ones) as a regression test.

## Limitations

* The proof of `parse_build` reaches the entries' bytes only through bytes'
  interface laws (`octets_append_list`, `octets_zeros_list`,
  `octets_of_to`). The hexfield and header laws compute through
  `Octets.of_list` and `Octets.to_list` on lists of known length, so their
  proofs would need revisiting if `Octets` changed representation again; the
  laws themselves would not change.
* Sizes are computed on `Nat`, and lengths are counted by walking the lists:
  linear in the archive's size (see Sizes).
* `Cpio.build` does not refuse an entry whose data is 2^32 bytes or longer, or
  whose name is `TRAILER!!!`; such an archive does not parse back.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 100 cases match, `scripts/deps.sh cpio` ok.
