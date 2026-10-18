# bend-osdev-elf

Reading and writing ELF files: the ELF header, program headers, section
headers, section names through the section-name string table, and symbol
tables (`.symtab`, `.dynsym`). Both classes (ELF32, ELF64) and both data
encodings (little- and big-endian).

Every reader answers a `Result`: malformed input fails with an `ElfError`
that names what was wrong, never with a wrong value. Every 64-bit field is a
`W64` (bend-osdev-word64); in ELF32 the 32-bit addresses, offsets and sizes
are widened to `W64`, so one record type serves both classes. Byte strings are
`Octets` (bend-osdev-bytes).

## Specifications

* System V Application Binary Interface, generic ABI (gABI), chapter 4
  "Object Files" (ELF Header, Sections, String Table, Symbol Table) and
  chapter 5 "Program Loading" (Program Header), including extended section
  numbering (`e_shnum` 0, `SHN_XINDEX`, `PN_XNUM`).
* ELF-64 Object File Format, version 1.5 (the 64-bit layouts).

## Files

| File | Holds |
|---|---|
| `elf.bend` | the entry file and main concern: `ElfFile`, a whole file at once; finding a section by name; a section's symbols and string table |
| `fields.bend` | `ElfError`; internal byte-order field readers and writers and exact slicing |
| `header.bend` | `ElfHeader`, `ElfOptions`: the ELF header, read and written |
| `sections.bend` | `ElfShdr`: section headers, the section header table, the counts held in section 0, section contents, strings and section names |
| `segments.bend` | `ElfPhdr`: program headers and the program header table |
| `symbols.bend` | `ElfSym`: symbol table entries, a section's symbols, binding/type/visibility, names |

Import only what you need: `header.bend` alone reads and writes headers.

Generated files, and how to regenerate them (from the repository root or
from `elf/`; Python 3, standard library only):

| Generator | Writes |
|---|---|
| `gen/accessors.py` | `elf.bend`, `header.bend`, `sections.bend`, `segments.bend`, `symbols.bend` from `gen/src/*.bend.in`, expanding each `#@ACCESSORS Type` line into that record's field accessors; edit the `.bend.in` templates, not the outputs (`fields.bend` is not generated) |
| `gen/pgen2.py` | `PROOF.bend` (the round trips' deep bit patterns) |
| `ref/gen.py` | `ref/cases.bend` and `ref/expected.txt`, run by `ref/run.sh` (git-ignored); `ref/dump.bend` is the dump they print |

## API

The records `ElfHeader`, `ElfPhdr`, `ElfShdr`, `ElfSym`, `ElfOptions` and
`ElfFile` are open: build them with their constructors (fields in the gABI's
order, as declared) to write a file. Each field has an accessor
(`ElfHeader.e_entry(h)`, `ElfShdr.sh_size(s)`, ...). In `ElfHeader`, `is64`
is ELFCLASS64 and `big` is ELFDATA2MSB.

| Def | Meaning |
|---|---|
| `ElfHeader.parse(o)`, `ElfHeader.parse_with(opts, o)` | the ELF header at the start of `o` |
| `ElfHeader.write(h)` | the header's 52 or 64 bytes (e_ident padding zero) |
| `ElfHeader.normal(h)` | the header as the file stores it (what `parse` gives back after `write`) |
| `ElfHeader.has_magic(o)`, `ElfHeader.size(is64)` | the magic check; 52 or 64 |
| `ElfOptions{check_version}`, `ElfOptions.default()` | how strictly to read (default: EI_VERSION must be EV_CURRENT) |
| `ElfPhdr.parse / write / normal (is64, big, ...)`, `ElfPhdr.size(is64)` | one program header |
| `ElfPhdr.read_table(is64, big, n, step, o)`, `write_table`, `normal_table` | `n` entries `step` bytes apart; a packed table |
| `ElfPhdr.all(o, h)` | the program headers of file `o` with header `h` |
| `ElfShdr.parse / write / normal / read_table / write_table / normal_table / size` | the same for section headers |
| `ElfShdr.all(o, h)` | the section headers of the file |
| `ElfShdr.count(o, h)`, `ElfShdr.phnum(o, h)`, `ElfShdr.shstrndx(o, h)` | the counts and the name-table index, resolved through section 0 when the header holds `0`, `PN_XNUM` or `SHN_XINDEX` |
| `ElfShdr.bytes(o, s)`, `ElfShdr.bytes_at(o, shdrs, i)` | a section's bytes (none for `SHT_NOBITS`) |
| `ElfShdr.string(strtab, i)` | the NUL-terminated string at offset `i` of a string table |
| `ElfShdr.shstrtab(o, h, shdrs)`, `ElfShdr.name(shstrtab, s)` | the section-name string table; a section's name |
| `ElfSym.parse / write / normal / read_table / write_table / normal_table / size` | symbol table entries |
| `ElfSym.all(o, h, s)` | the symbols of a `SHT_SYMTAB` or `SHT_DYNSYM` section |
| `ElfSym.name(strtab, y)` | a symbol's name, given its string table (the section at `sh_link`) |
| `ElfSym.bind`, `ElfSym.type`, `ElfSym.visibility`, `ElfSym.info(bind, type)` | `st_info` and `st_other` split and joined |
| `ElfFile.read(o)`, `ElfFile.read_with(opts, o)` | header, program headers, section headers and section names |
| `ElfFile.header / segments / sections / shstrtab` | its parts |
| `ElfFile.section_name(f, s)`, `ElfFile.find_section(f, name)` | names; the first section with a name |
| `ElfFile.symbols(o, f, s)`, `ElfFile.strtab(o, f, s)` | a section's symbols; its linked string table |

### Errors

`ElfError` (in `fields.bend`): `ElfTruncated` (the input ends inside the
header or a table entry), `ElfBadMagic`, `ElfBadClass`, `ElfBadData`,
`ElfBadVersion`, `ElfOffsetOutOfRange` (an offset or size past the end of the
file, or of 2^32 or more), `ElfBadEntrySize` (an entry size smaller than the
entry, or `sh_entsize` not dividing `sh_size`), `ElfBadIndex` (a section index
past the table), `ElfBadString` (a string offset past its table, or no NUL),
`ElfNoSectionTable` (a count is in section 0 but there is no section table).

## Extension points

* **Strictness** is a parameter: `ElfOptions` (with `ElfOptions.default()`)
  decides whether EI_VERSION is checked. Further choices belong there.
* **Building files.** Every structure has a writer, and tables have
  `write_table`; with `B.Octets.concat` they build any layout (see
  `check.bend`).
* **Pieces on their own.** `ElfPhdr.read_table`, `ElfShdr.read_table` and
  `ElfSym.read_table` read a table from any bytes, so a caller that has
  already sliced the file (or reads it with `File.read_at`) need not hand over
  the whole file.
* **Representations are other packages'.** `Octets` and `W64` are opaque; this
  package uses only their public defs, and its proofs only their interface
  laws (`octets_append_list`, `parts_of`), so either can change storage
  without touching this package.
* Not streaming: ELF is read by offset, so there is no incremental reader.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every input:**
  * each writer and its reader agree, in both classes and both byte orders,
    with any bytes following: `parse(write(x) ++ rest) == Done{normal(x)}` for
    the ELF header, program headers, section headers and symbols;
  * the same for whole tables: `read_table(..., length(xs), size, write_table(xs))
    == Done{normal_table(xs)}`, by induction on the entries;
  * the header reader answers `ElfBadMagic` for anything without the magic,
    fails on anything shorter than 52 bytes, and answers `ElfTruncated` for
    every header with its last byte cut off;
* **vectors:** the header of a real gcc x86-64 executable and of a
  hand-written ELF32 big-endian PowerPC header; a bad class, data encoding and
  version, and the version accepted when unchecked; the section count held in
  section 0; a program header table past the end of the file; strings,
  including missing NULs and offsets past the end; `st_info`; and a whole
  ELF32 big-endian file built with the writers, read with `ElfFile.read`, its
  `.text` section found by name.

The round trips never look inside `W64` or `Octets`: they rewrite with
bytes' `octets_append_list` and word64's `parts_of`, then split every 32-bit
field into its bits so that the readers compute on symbolic bits.

## Tests

`check.bend` builds small ELF64 little-endian, ELF32 big-endian and ELF32
little-endian files with the writers and dumps them, plus malformed inputs.

`ref/run.sh` (needs `python3` and `readelf`; uses `gcc` when installed) dumps
45 files and compares every field (740 lines with the default seed) with
`ref/gen.py`, which holds a second reader written independently from the
specification. That reader is itself checked field by field against
`readelf -h -l -S -s --wide` (GNU binutils) on the 20 well-formed files:

* built by gcc: a static executable, the same with `-n`, a PIE, a shared
  object, an object file, and a dynamically linked executable (`.dynsym` with
  symbol versions);
* written by `gen.py` from the specification: three random files in each of
  ELF64/ELF32 by little/big-endian (program headers, `SHT_NOBITS`, merge
  strings, symbols of every binding), and two with extended numbering;
* malformed (25, not compared with readelf, which warns and carries on): bad
  magic, class, data and version, empty and short inputs, a cut ELF64 header,
  cut and misplaced tables, offsets past the end and above 2^32, small entry
  sizes, a name-table index past the table, `PN_XNUM` without sections, bad
  name and string table offsets and sizes, bad `sh_entsize` and `sh_link`, an
  unterminated string table.

Eight further seeds (`SEED=1..8`) also match.

## Sizes

**Lanes.** The figures in this section were measured on bend's JavaScript lane
(`bend file.bend`, which runs `main` inside the bend process). That lane's
stack overflows at some tens of thousands of nested non-tail calls, and it
uses several times the memory of a native build (`bend file.bend -o prog`),
which has a 2 GB stack; see AGENTS.md, "Runtime and checker limits". They
will be re-measured natively once W64-heavy code builds natively
(bendlang/bend#1069).

Every loop over a file's bytes or a table's entries is a tail call (Bend
2.0.37's JavaScript lane overflows its stack at some tens of thousands of nested
calls), so neither a section's size nor the number of sections or symbols has
a limit beyond memory. The tables' structural forms stay beside the loops as
the reference the proofs reason about (`table.list.ref`, `write_table.ref`,
`normal_table.ref` for each of `ElfPhdr`, `ElfShdr` and `ElfSym`), and
`PROOF.bend` proves each equal to its loop for every input (`*_table_eq`,
`*_write_eq`, `*_normal_eq`). The whole-file readers (`ElfFile.read`,
`ElfPhdr.all`, `ElfShdr.all`, `ElfShdr.count`, `ElfShdr.bytes`, ...) walk
to what they read through `Octets` and convert only those bytes to a list,
and a string is looked for in the 256 bytes at its offset before the rest of
its table is converted.

Measured on Bend 2.0.37's JavaScript lane (WSL2) on files built by gcc, read
from disk, every count and sum checked against `readelf`:

| File | Run | Time | Peak RAM |
|---|---|---|---|
| 1.27 MB executable, 20,006 symbols | `ElfFile.read`, `.symtab` found, its symbols read | 3.6 s | 1.6 GB |
| the same | and every symbol's name looked up | 14.0 s | 1.7 GB |
| 1.13 MB object (`-ffunction-sections`), 6,013 sections, 12,004 symbols | `ElfFile.read`, `.symtab` found by name, its symbols read | 4.5 s | 1.6 GB |
| 480 KB symbol table, 20,000 symbols | `ElfSym.write_table`, then `read_table` and compared with `normal_table` | 2.8 s | 1.1 GB |

Most of the memory is the file's `Octets` (about 940 bytes per byte
when measured; bytes' compact `OctByte` storage, merged since, holds an
`Octets` in about a third of that, about 150 bytes per byte, and these
figures have not been re-measured)
and the list `File.read_bytes` gives; files of a few MB need a compact
`Octets`. Before this, a 164 KB executable (2,506 symbols) overflowed the
stack, and every reader converted the whole file to a list. `check.bend`
builds and reads a file with 3,001 symbols (a 72 KB symbol table) as a
regression test. `ElfHeader.parse` converts all of its input: give it a
file's first 64 bytes, as `ElfFile.read` does.

## Limitations

* Reading at an offset walks the bytes (`Octets` is a list today), so each
  lookup costs time in proportion to its offset: naming every symbol of a
  table costs the table's length times its string table's (see Sizes).
* The reference test links gcc's binaries with `-z noseparate-code`, so
  that its inputs stay small (all under 8 KB); the sizes below were measured
  separately.
* Programs that build a record with four or more `W64` fields (`ElfPhdr`,
  `ElfShdr`) do not compile to native code in Bend 2.0.37 ("an arity over
  247"; `crc/check.bend` is affected the same way); `bend` runs them anyway,
  more slowly.
* Offsets and sizes of 2^32 or more are rejected (`ElfOffsetOutOfRange`).
* Relocations, dynamic sections, notes, versions and groups are not decoded;
  their bytes are available through `ElfShdr.bytes`.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 45 files (740 lines) match, of which 20
checked against readelf; `scripts/deps.sh elf` ok.
