# bend-osdev-elf

Reading and writing ELF files: the ELF header, program headers, section
headers, string tables (looked up directly, or through an index built once),
symbol tables (`.symtab`, `.dynsym`), relocations (`SHT_REL`, `SHT_RELA`),
the dynamic section, notes (`SHT_NOTE`, `PT_NOTE`) and symbol versions
(`.gnu.version`, `.gnu.version_d`, `.gnu.version_r`). Both classes (ELF32,
ELF64) and both data encodings (little- and big-endian).

Every reader answers a `Result`: malformed input fails with an `ElfError`
that names what was wrong, never with a wrong value. Every 64-bit field is a
`W64` (bend-osdev-word64); in ELF32 the 32-bit addresses, offsets and sizes
are widened to `W64`, so one record type serves both classes. Byte strings are
`Octets` (bend-osdev-bytes).

## Specifications

* System V Application Binary Interface, generic ABI (gABI), chapter 4
  "Object Files" (ELF Header, Sections, String Table, Symbol Table,
  Relocation) and chapter 5 "Program Loading" (Program Header, Note Section,
  Dynamic Section), including extended section numbering (`e_shnum` 0,
  `SHN_XINDEX`, `PN_XNUM`).
* ELF-64 Object File Format, version 1.5 (the 64-bit layouts: `Elf64_Rel`,
  `Elf64_Rela`, `Elf64_Dyn`).
* Linux Standard Base Core Specification, generic part, "Symbol Versioning"
  (`Elfxx_Verdef`, `Elfxx_Verdaux`, `Elfxx_Verneed`, `Elfxx_Vernaux`, the
  `.gnu.version` array, `VER_FLG_BASE`, `VER_FLG_WEAK`, the hidden bit) and
  "Dynamic Section" (`DT_VERSYM`, `DT_VERDEF`, `DT_VERDEFNUM`, `DT_VERNEED`,
  `DT_VERNEEDNUM`, `DT_RELACOUNT`, `DT_RELCOUNT`, `DT_FLAGS_1`).
* elf(5), Linux man-pages 6.7: "Relocation entries", "Dynamic tags",
  "Notes (Nhdr)" (the note layout, `n_namesz` counting the NUL,
  `NT_GNU_BUILD_ID`).
* Black-box behaviour of readelf (GNU binutils 2.42), where the documents
  stop (below).

Where the documents are incomplete, and what this package does:

* **Note alignment.** The gABI and elf(5) pad a note's name and descriptor
  to 4 bytes. GNU property notes in ELF64 (`.note.gnu.property`, in sections
  and `PT_NOTE` segments aligned to 8) are padded to 8: in a gcc x86-64
  executable the descriptor of a note named "GNU" starts at 16, not 12 + 4,
  and readelf reads it so. The alignment is a parameter (`ElfNoteAlign`, 4 by
  default); `ElfNote.all` and `ElfNote.segment` take 8 for a section or
  segment aligned to 8 and 4 otherwise, which agrees with readelf on every
  gcc-built file in the reference test. Padding is counted from the note's
  start (`note_align8` is the observed case).
* **Tag values.** `DT_GNU_HASH` (0x6ffffef5) and `DT_RELRSZ`, `DT_RELR`,
  `DT_RELRENT` (35 to 37) are not in the documents above; every named tag's
  value is checked against readelf's name for it (all 46, in
  `spec_dynamic_tags` below).
* **Version chains.** A chain has a count (`sh_info`, `vd_cnt`, `vn_cnt`) and
  next offsets (0 at the end). The readers stop at whichever comes first; an
  offset past the section is `ElfOffsetOutOfRange`. readelf is compared only
  on well-formed chains.
* **ELF32 addends.** `Elf32_Rela.r_addend` is an `Elf32_Sword`; it is
  sign-extended, so `r_addend` is the addend as a 64-bit two's complement
  value in both classes. `d_tag` (also signed) is widened without sign
  extension: no tag is negative.

## Files

| File | Holds |
|---|---|
| `elf.bend` | the entry file and main concern: `ElfFile`, a whole file at once; finding a section by name; a section's symbols and string table |
| `fields.bend` | `ElfError`; internal byte-order field readers and writers, exact slicing, the reference string lookup, chains linked by offsets |
| `header.bend` | `ElfHeader`, `ElfOptions`: the ELF header, read and written |
| `sections.bend` | `ElfShdr`: section headers, the section header table, the counts held in section 0, section contents, strings and section names |
| `segments.bend` | `ElfPhdr`: program headers and the program header table |
| `symbols.bend` | `ElfSym`: symbol table entries, a section's symbols, binding/type/visibility, names |
| `strtab.bend` | `ElfStrtab`: a string table indexed by offset |
| `relocs.bend` | `ElfReloc`: `Elf32_Rel`, `Elf32_Rela`, `Elf64_Rel`, `Elf64_Rela`; `r_info`'s symbol and type; the relocation sections |
| `dynamic.bend` | `ElfDyn`, `ElfDynTag`: the dynamic section, its named tags and strings |
| `notes.bend` | `ElfNote`, `ElfNoteAlign`: notes of sections and segments; the GNU build ID |
| `versions.bend` | `ElfVersym`, `ElfVerdef`, `ElfVerdaux`, `ElfVerneed`, `ElfVernaux`, `ElfVerdefEntry`, `ElfVerneedEntry`: symbol versions |

Import only what you need: `header.bend` alone reads and writes headers;
`notes.bend` reads notes without the symbol code.

Generated files, and how to regenerate them (from the repository root or
from `elf/`; Python 3, standard library only):

| Generator | Writes |
|---|---|
| `gen/accessors.py` | `elf.bend`, `header.bend`, `sections.bend`, `segments.bend`, `symbols.bend`, `relocs.bend`, `dynamic.bend`, `notes.bend`, `versions.bend` from `gen/src/*.bend.in`, expanding `#@ACCESSORS Type` (a record's field accessors), `#@TABLE Type P N` (an entry type's table code: the one-entry reader, the structural table reader and writer and their tail-recursive forms) and `#@ENUM Name` (named codes, from the table in `accessors.py`); edit the `.bend.in` templates, not the outputs (`fields.bend` and `strtab.bend` are not generated) |
| `gen/pgen2.py` | `PROOF.bend`: the round trips' deep bit patterns and table proofs for every entry type, the named-code proof, `gen/pnotes.py`'s note proofs, the hand-written `gen/proof/*.bend.part`, and a `{==}` proof for every law of `LAWS.bend` without a `for` |
| `ref/gen.py` | `ref/cases.bend` and `ref/expected.txt`, run by `ref/run.sh` (git-ignored); `ref/dump.bend` is the dump they print |

## API

The records `ElfHeader`, `ElfPhdr`, `ElfShdr`, `ElfSym`, `ElfReloc`,
`ElfDyn`, `ElfNote`, `ElfVersym`, `ElfVerdef`, `ElfVerdaux`, `ElfVerneed`,
`ElfVernaux`, `ElfVerdefEntry`, `ElfVerneedEntry`, `ElfOptions` and `ElfFile`
are open: build them with their constructors (fields in the specification's
order, as declared) to write a file. Each field has an accessor
(`ElfHeader.e_entry(h)`, `ElfReloc.r_info(r)`, ...). In `ElfHeader`, `is64`
is ELFCLASS64 and `big` is ELFDATA2MSB. The enumerations `ElfDynTag`,
`ElfNoteAlign` and `ElfError` are open too. `ElfStrtab` is opaque.

Each entry type `T` has the same table interface, with the Bool parameters
its layout depends on (`P`: `is64, big` for program and section headers,
symbols and dynamic entries; `is64, big, rela` for relocations; `big` for the
version records):

| Def | Meaning |
|---|---|
| `T.parse(P, o)` | the entry at the start of `o` |
| `T.write(P, x)`, `T.normal(..., x)` | its bytes; the entry as the file stores it (what `parse` gives back) |
| `T.read_table(P, n, step, o)`, `T.write_table(P, xs)`, `T.normal_table(..., xs)` | `n` entries `step` bytes apart; a packed table |
| `T.size(...)` | an entry's size |

The rest:

| Def | Meaning |
|---|---|
| `ElfHeader.parse(o)`, `ElfHeader.parse_with(opts, o)`, `ElfHeader.write(h)`, `ElfHeader.normal(h)` | the ELF header (52 or 64 bytes) |
| `ElfHeader.has_magic(o)`, `ElfHeader.size(is64)` | the magic check; 52 or 64 |
| `ElfOptions{check_version}`, `ElfOptions.default()` | how strictly to read (default: EI_VERSION must be EV_CURRENT) |
| `ElfPhdr.all(o, h)`, `ElfShdr.all(o, h)` | the program headers, section headers of file `o` with header `h` |
| `ElfShdr.count(o, h)`, `ElfShdr.phnum(o, h)`, `ElfShdr.shstrndx(o, h)` | the counts and the name-table index, resolved through section 0 when the header holds `0`, `PN_XNUM` or `SHN_XINDEX` |
| `ElfShdr.bytes(o, s)`, `ElfShdr.bytes_at(o, shdrs, i)` | a section's bytes (none for `SHT_NOBITS`) |
| `ElfShdr.string(strtab, i)` | the NUL-terminated string at offset `i` of a string table (the reference lookup: a walk of the table) |
| `ElfShdr.shstrtab(o, h, shdrs)`, `ElfShdr.name(shstrtab, s)`, `ElfShdr.name_in(ix, s)` | the section-name string table; a section's name, directly or through an index |
| `ElfStrtab.of(strtab)`, `ElfStrtab.string(ix, i)` | a string table's index, built once; the string at offset `i`, the same answer as `ElfShdr.string` |
| `ElfSym.all(o, h, s)` | the symbols of a `SHT_SYMTAB` or `SHT_DYNSYM` section |
| `ElfSym.name(strtab, y)`, `ElfSym.name_in(ix, y)` | a symbol's name, given its string table (the section at `sh_link`) or its index |
| `ElfSym.bind`, `ElfSym.type`, `ElfSym.visibility`, `ElfSym.info(bind, type)` | `st_info` and `st_other` split and joined |
| `ElfReloc.sym(is64, r)`, `ElfReloc.type(is64, r)`, `ElfReloc.info(is64, sym, type)` | `ELF32_R_SYM`/`ELF64_R_SYM`, `..._R_TYPE`, `..._R_INFO` |
| `ElfReloc.is_section(s)`, `ElfReloc.is_rela(s)`, `ElfReloc.sections(ss)` | relocation sections, found by `sh_type` |
| `ElfReloc.all(o, h, s)` | the relocations of a `SHT_REL` or `SHT_RELA` section |
| `ElfDyn.all(o, h, s)`, `ElfDyn.until_null(ds)` | the entries of a `SHT_DYNAMIC` section; those up to and including the first `DT_NULL` |
| `ElfDyn.is_section(s)`, `ElfDyn.section(ss)` | the dynamic section, found by `sh_type` |
| `ElfDyn.tag(d)`, `ElfDyn.is_null(d)`, `ElfDyn.string(ix, d)` | the entry's named tag, if any; the string `DT_NEEDED`, `DT_SONAME`, `DT_RPATH` or `DT_RUNPATH` points to |
| `ElfDynTag` (`ElfDtNull{}` ... `ElfDtVerneednum{}`), `ElfDynTag.code(k)`, `ElfDynTag.name(k)`, `ElfDynTag.of_code(c)`, `ElfDynTag.all()` | the 46 named tags of the gABI and LSB, their codes and names (`"DT_NEEDED"`) |
| `ElfNote.parse(big, al, o)`, `ElfNote.write(big, al, n)` | one note; `n_namesz` and `n_descsz` are written as they are |
| `ElfNote.read_all(big, al, o)`, `ElfNote.write_all(big, al, ns)` | the notes filling some bytes |
| `ElfNote.make(type, owner, desc)`, `ElfNote.sized(n)`, `ElfNote.all_sized(ns)` | a note with consistent sizes (the owner's NUL added); whether the sizes are the lengths |
| `ElfNote.owner(n)`, `ElfNote.build_id(n)`, `ElfNote.find_build_id(ns)` | the name up to its NUL; the GNU build ID (owner "GNU", `NT_GNU_BUILD_ID`) |
| `ElfNote.all(o, h, s)`, `ElfNote.segment(o, h, p)`, `ElfNote.is_section(s)`, `ElfNote.is_segment(p)` | the notes of a `SHT_NOTE` section or `PT_NOTE` segment, aligned as it is |
| `ElfNoteAlign` (`ElfAlign4{}`, `ElfAlign8{}`), `ElfNoteAlign.default()`, `ElfNoteAlign.of(a)` | the alignment; 4; the alignment for a section or segment aligned to `a` |
| `ElfVersym.index(v)`, `ElfVersym.hidden(v)`, `ElfVerdef.is_base(d)`, `ElfVerdef.is_weak(d)` | a version index and its hidden bit; `VER_FLG_BASE`, `VER_FLG_WEAK` |
| `ElfVerdef.chain(big, n, o)`, `ElfVerneed.chain(big, n, o)` | `n` definitions (each with its names) or needed files (each with its versions), following the chains' offsets |
| `ElfVerdef.pack(es)`, `ElfVerneed.pack(es)`, `ElfVerdef.write_chain(big, es)`, `ElfVerneed.write_chain(big, es)` | the links of a packed chain set; its bytes |
| `ElfVersym.all`, `ElfVerdef.all`, `ElfVerneed.all` (`o, h, s`), and `.is_section(s)` | the three version sections |
| `ElfFile.read(o)`, `ElfFile.read_with(opts, o)` | header, program headers, section headers and section names |
| `ElfFile.header / segments / sections / shstrtab` | its parts |
| `ElfFile.section_name(f, s)`, `ElfFile.section_names(f)`, `ElfFile.find_section(f, name)` | a name; the names' index; the first section with a name (through the index) |
| `ElfFile.symbols(o, f, s)`, `ElfFile.strtab(o, f, s)` | a section's symbols; its linked string table |

### Errors

`ElfError` (in `fields.bend`): `ElfTruncated` (the input ends inside the
header, a table entry, a note or a version entry), `ElfBadMagic`,
`ElfBadClass`, `ElfBadData`, `ElfBadVersion`, `ElfOffsetOutOfRange` (an
offset or size past the end of the file or section, or of 2^32 or more),
`ElfBadEntrySize` (an entry size smaller than the entry, or `sh_entsize` not
dividing `sh_size`), `ElfBadIndex` (a section index past the table),
`ElfBadString` (a string offset past its table, or no NUL),
`ElfNoSectionTable` (a count is in section 0 but there is no section table),
`ElfBadSectionType` (a section or segment of another type than the reader
needs: relocations from a section neither `SHT_REL` nor `SHT_RELA`, ...).

## Extension points

* **Strictness** is a parameter: `ElfOptions` (with `ElfOptions.default()`)
  decides whether EI_VERSION is checked. Further choices belong there.
* **Note alignment** is a parameter (`ElfNoteAlign`, `ElfNoteAlign.default()`
  4); `ElfNoteAlign.of` is the rule the section and segment readers use.
* **String lookups** have two implementations behind the same answer: the
  reference walk (`ElfShdr.string`, `ElfSym.name`, `ElfShdr.name`) and the
  index (`ElfStrtab`, `ElfSym.name_in`, `ElfShdr.name_in`), proved equal for
  every table and offset. Another index (a different trie, a cache) can
  replace `strtab.bend` behind `ElfStrtab.of` and `ElfStrtab.string` with the
  same law.
* **Named codes** are a table in `gen/accessors.py` (`ENUMS`): a new tag is a
  row there, and its law follows by regeneration.
* **New entry types** take a template with `#@ACCESSORS` and `#@TABLE`, a
  `TYPES` row in `accessors.py` and an `ENTRIES` row in `pgen2.py`: the
  table code and its for-all round-trip proofs are generated.
* **Building files.** Every structure has a writer, tables have
  `write_table`, notes `write_all`, version chains `pack` and `write_chain`;
  with `B.Octets.concat` they build any layout (see `check.bend`).
* **Pieces on their own.** Every `read_table`, `ElfNote.read_all` and the
  version `chain`s read from any bytes, so a caller that has already sliced
  the file (or reads it with `File.read_at`) need not hand over the whole
  file.
* **Representations are other packages'.** `Octets` and `W64` are opaque; this
  package uses only their public defs, and its proofs only their interface
  laws (`octets_append_list`, `octets_of_to`, `octets_to_of`,
  `octets_len_list`, `octets_zeros_list`, `take_fast`, `parts_of`,
  `hi_from_parts`, `lo_from_parts`), so either can change storage without
  touching this package.
* Not streaming: ELF is read by offset, so there is no incremental reader.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer) has 61 laws.

**31 hold for every input:**

* each writer and its reader agree, in both classes and both byte orders,
  with any bytes following: `parse(write(x) ++ rest) == Done{normal(x)}` for
  the ELF header, program headers, section headers, symbols, relocations
  (with and without addends), dynamic entries and the five version records
  (`*_round_trip`);
* the same for whole tables: `read_table(..., length(xs), size,
  write_table(xs)) == Done{normal_table(xs)}`, by induction on the entries,
  for each of those entry types (`*_table_round_trip`);
* a note whose sizes are its name's and descriptor's lengths is read back
  from its bytes followed by any bytes, with either alignment and byte order
  (`note_round_trip`), and so is a list of such notes written one after
  another (`notes_round_trip`);
* the string table index answers what the reference lookup answers, for
  every table and every offset (`strtab_string`), and so do symbol and
  section names through it (`sym_name_indexed`, `shdr_name_indexed`);
* every named dynamic tag's code is read back as that name (`dyn_tag_code`);
  `ELF64_R_INFO`'s symbol and type come back out of `r_info` (`rel_info64`);
* the header reader answers `ElfBadMagic` for anything without the magic,
  fails on anything shorter than 52 bytes, and answers `ElfTruncated` for
  every header with its last byte cut off.

**30 are vectors:** the header of a real gcc x86-64 executable and of a
hand-written ELF32 big-endian PowerPC header; a bad class, data encoding and
version, and the version accepted when unchecked; the section count held in
section 0; a program header table past the end of the file; strings,
including missing NULs and offsets past the end, directly and indexed;
`st_info`; a whole ELF32 big-endian file built with the writers, read with
`ElfFile.read`, its `.text` section found by name; `ELF32_R_INFO` and a
negative ELF32 addend; `DT_NEEDED` with its string and the end of the
dynamic array; an unnamed tag; packed version definition and need chains,
written and read back; a hidden version index; a build ID note made, written
and found; a GNU property note aligned to 8. Four of them are witnesses that
the hypotheses of `rejects_bad_magic`, `rejects_short`, `note_round_trip` and
`notes_round_trip` can hold.

Not for every input: `ELF32_R_INFO` (its bit operations on a symbolic word
do not compute to the fields' bits, so `rel_info32` is a vector), and the
packed version chains (`verdef_chain`, `verneed_chain`: their links are
`20 + 8 * vd_cnt` and the like, and a for-all law would need `U32`
arithmetic laws, `to_nat(a + b) == to_nat(a) + to_nat(b)` below 2^32, that
neither Base nor this repository states yet). Both are also covered by the
differential test.

How the proofs go (`PROOF.bend`, written by `gen/pgen2.py`): the round trips
never look inside `W64` or `Octets`: they rewrite with bytes'
`octets_append_list` and word64's `parts_of`, then split every 32-bit field
into its bits so that the readers compute on symbolic bits. The index is a
binary trie keyed by the offset's bits, least significant first, built by
splitting the table's suffixes into those at even and odd offsets; its proof
follows Base's `Word.to_nat`, which reads a word in the same order: a lookup
in the trie is `List.get` of the suffixes at `to_nat(i)`, and the suffix at
offset `n`, cut at its NUL, is the reference lookup's answer. The note proofs
(`gen/pnotes.py`) flatten a note's bytes into its seven pieces, read the
header on symbolic bits and the name and descriptor by the sizes'
hypotheses; the list of notes walks, a byte at a time, the bytes a note takes
(its length is one more than the size the reader computes) to the next note.

## Tests

`check.bend` builds small ELF64 little-endian, ELF32 big-endian and ELF32
little-endian files with the writers and dumps them, plus malformed inputs, a
file with 3,001 symbols, and an ELF64 little-endian and an ELF32 big-endian
file holding relocations with addends, a dynamic section, a build ID note and
the three version sections, built with their writers and read back (86
lines).

`ref/run.sh` (needs `python3`; uses `readelf` and `gcc` when installed) dumps
62 files and compares every field (2,760 lines with the default seed) with
`ref/gen.py`, which holds a second reader written independently from the
specifications (by the same author as the package). That reader is itself
checked field by field against `readelf -h -l -S -s --wide` (GNU binutils)
on the 26 well-formed files, and against `readelf -r -d -n -V --wide` on the
11 gcc-built files and `spec_dynamic_tags` (220 relocations, dynamic entries,
notes and version entries, and the names of all 46 named tags):

* built by gcc: a static executable, the same with `-n`, a PIE, a shared
  object, an object file, a dynamically linked executable (`.dynsym`, version
  needs, `.rela.dyn`, `.rela.plt`, notes), the same with a build ID; object
  files with relocations with addends (x86-64, negative addends) and without
  (i386, `gcc -m32 -c`); shared objects with version definitions (a version
  script, a `.symver` alias, a hidden version) and a build ID in both classes
  (`-m32` for ELF32, REL);
* written by `gen.py` from the specification: three random files in each of
  ELF64/ELF32 by little/big-endian (program headers, `SHT_NOBITS`, merge
  strings, symbols of every binding, `SHT_RELA` and `SHT_REL` sections, a
  dynamic section with named, unnamed and string tags and `DT_NULL` padding,
  notes aligned to 4 or 8, `.gnu.version`, `.gnu.version_d` and
  `.gnu.version_r` chains), two with extended numbering, and one with every
  named dynamic tag;
* malformed (36, not compared with readelf, which warns and carries on): bad
  magic, class, data and version, empty and short inputs, a cut ELF64 header,
  cut and misplaced tables, offsets past the end and above 2^32, small entry
  sizes, a name-table index past the table, `PN_XNUM` without sections, bad
  name and string table offsets and sizes, bad `sh_entsize` and `sh_link`, an
  unterminated string table; relocation and version sections with bad entry
  sizes, a dynamic section past the end, notes whose name or descriptor runs
  past the section, version chains whose next or auxiliary offset runs past
  it or that are cut, and a version need count larger than its chain.

Eight further seeds (`SEED=1..8`) also match.

## Speed and sizes

Measured natively (`bend file.bend -o prog`, Bend 2.0.37, WSL2), reading the
file from disk, every count checked against `readelf`:

| File | Run | Time | Peak RAM |
|---|---|---|---|
| 1.27 MB executable (gcc `-static -nostdlib`, 20,000 functions), 20,006 symbols, a 160 KB `.strtab` | `ElfFile.read`, `.symtab` found, its symbols read | 0.62 s | 166 MB |
| the same | and every symbol's name looked up with `ElfSym.name` (the reference walk) | 49.4 s | 166 MB |
| the same | and every symbol's name looked up with `ElfSym.name_in` through `ElfStrtab.of(strtab)`, built once | 0.70 s | 166 MB |
| 1.15 MB object (`-ffunction-sections`), 6,012 sections, 12,002 symbols | `ElfFile.read`, `.symtab` found by name (indexed), its symbols read and named through the index | 0.97 s | 148 MB |

Naming every symbol cost the table's length times its string table's: each
lookup walks the string table to its offset (on average 80 KB here). The
index is built once in time in proportion to the string table's length times
the trie's depth (about 18 levels for 160 KB), holds each suffix of the
table shared with the table's byte list rather than copied, and answers each
lookup in at most 32 steps plus the string's length: 49.4 s became 0.08 s
for the names, 70 times faster for the whole run. `ElfFile.find_section` names the sections
through an index of `.shstrtab` built for the call.

Every loop over a file's bytes or a table's entries is a tail call (Bend
2.0.37's JavaScript lane overflows its stack at some tens of thousands of
nested calls; a native build has a 2 GB stack), so on either lane neither
a section's size nor the number of sections, symbols, relocations, dynamic
entries or notes has a limit beyond memory. The tables' structural forms stay beside the loops as the reference the
proofs reason about (`table.list.ref`, `write_table.ref`, `normal_table.ref`
for each entry type, `ElfNote.write_all.ref`, `elf_suffixes` and `elf_alt`
in `strtab.bend`), and `PROOF.bend` proves each equal to its loop for every
input. The whole-file readers walk to what they read through `Octets` and
convert only those bytes to a list; `ElfShdr.string` converts its table to a
list on each call (use the index for many lookups). `ElfHeader.parse`
converts all of its input: give it a file's first 64 bytes, as
`ElfFile.read` does.

Most of the memory is the file's `Octets` (bytes' `OctByte` storage, about
80 bytes per byte held natively; about 150 on the JavaScript lane) and the
list `File.read_bytes` gives.

## Dependencies

`bytes` and `word64` (`DEPS`). The index is this package's own trie, not
xarray: the offsets to index are dense (every byte of the table), so the trie
is built by splitting a list rather than by one store per offset (each of
which would copy a 32-node path), and its proof needs no arithmetic on `U32`
indices (counting offsets up as `U32`s would need laws such as `to_nat(i + 1)
== to_nat(i) + 1` below 2^32, which neither Base nor xarray's laws state).

## Limitations

* `ElfShdr.string` (the reference) walks its table on every call; name many
  strings through `ElfStrtab`.
* The reference test links gcc's binaries with `-z noseparate-code`, so
  that its inputs stay small (all under 8 KB); the sizes above were measured
  separately. The i386 files need `gcc -m32` (multilib); without it they are
  left out.
* Offsets and sizes of 2^32 or more are rejected (`ElfOffsetOutOfRange`).
* Relocation types are processor-specific and not named; note types are
  named only for the GNU build ID; `DT_FLAGS` and `DT_FLAGS_1` bits are not
  decoded; section groups, hash tables (`.hash`, `.gnu.hash`) and `SHT_RELR`
  are not decoded (their bytes are available through `ElfShdr.bytes`).
* The packed version chains and `ELF32_R_INFO` have vectors and the
  differential test, not for-all laws (see Laws).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 62 files (2,760 lines) match, of which 26
checked against readelf (`-h -l -S -s`) and 12 also against `readelf -r -d -n
-V` (220 entries); `scripts/deps.sh elf` ok. Every program runs natively (no
JavaScript-lane fallback).
