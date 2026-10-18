# bend-osdev-iso9660

A read-only ISO 9660 reader, with the Rock Ridge and Joliet extensions and
El Torito boot records, over bend-osdev-blockdev's device interface. It
reads a volume's descriptors, walks its directories, names their entries
(plain ISO 9660, Joliet or Rock Ridge), finds paths, and reads files a block
at a time or by byte range, never past a file's data length.

## Specifications

* **ECMA-119**, "Volume and File Structure of CDROM for Information
  Interchange", 4th edition (June 2019), the free edition of ISO 9660:
  7.2 and 7.3 (both-endian numbers), 7.4 (a- and d-characters), 8 (volume
  descriptors: 8.2 boot record, 8.4 primary, 8.5 supplementary, 8.3
  terminator), 9.1 (directory records), 9.1.5 and 8.4.26.1 (the 7- and
  17-byte dates), 6.8 (directories, records never crossing a sector).
* **SUSP**, IEEE P1281 "System Use Sharing Protocol", version 1.12 (1994):
  the SP, CE, ER, ST and PD entries.
* **RRIP**, IEEE P1282 "Rock Ridge Interchange Protocol", version 1.12
  (1994): PX, PN, SL, NM, CL, PL, RE and TF.
* **Joliet**, Microsoft, "Joliet Specification" (1995): the escape sequences
  `%/@`, `%/C` and `%/E` and UCS-2 (big-endian) identifiers.
* **El Torito**, Phoenix and IBM, "El Torito Bootable CD-ROM Format
  Specification", version 1.0 (1995): the boot record, the boot catalog's
  validation entry and its initial/default entry.

Written from these documents only; no GPL source (no Linux `fs/isofs`, no
genisoimage, xorriso or libisofs source) was read. MIT licensed (`LICENSE`).

Dependencies: bend-osdev-bytes (`Octets`), bend-osdev-blockdev (the device
interface, `Dev.read_bytes` for byte ranges, `MemDev`) and
bend-osdev-word64 (a file's total size, which several extents can take past
32 bits).

## Files

| File | Holds |
|---|---|
| `fields.bend` | `IsoError`; both-endian numbers (`IsoEndian`); the 7-byte directory date `IsoDirDate` and the 17-byte volume date `IsoVolDate`; identifier text; reading a sector of the device |
| `joliet.bend` | the Joliet level of a descriptor's escape sequences; UCS-2 names |
| `dirrec.bend` | directory records `IsoDirRec`: reading, writing, flags |
| `susp.bend` | SUSP entries `IsoSuspEntry`: one area, SP, CE (following continuation areas on the device), ER |
| `rockridge.bend` | RRIP: what a record's entries say (`IsoRr`), and whether a volume has Rock Ridge |
| `volume.bend` | options (`IsoOptions`, `IsoNaming`), volume descriptors (`IsoPvd`, `IsoDescriptor`), El Torito (`IsoBootCatalog`), opening a volume (`Iso.open`, `IsoVolume`) |
| `dir.bend` | the directory walk (`Iso.dir_records`), entries (`IsoEntry`, `IsoExtent`), listing and finding |
| `file.bend` | file data: streaming (`IsoCursor`, `IsoChunk`) and byte ranges |
| `fence.bend` | `IsoFence`, an in-memory device answering only a range of blocks (the laws use it) |
| `iso9660.bend` | the entry concern: mounting, reading and walking by path |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/genproof.py`, `gen/proof.tmpl.bend` | `PROOF.bend` is generated: the template writes each 32-bit split pattern as `{U32:x}`, and `python3 gen/genproof.py` expands them into `PROOF.bend` (LF line endings) |
| `check.bend` | a runnable check on an image built with the package's own writers |
| `ref/gen.py`, `ref/harness.bend`, `ref/run.sh` | the differential test |

Bend imports do not re-export: import the file whose defs you use.

## The device

Every reading def takes blockdev's template interface, `~D: Data`,
`~block_size: D -> Nat` and `~read_block: D -> Nat -> Result<&2, &2,
DevError, Octets>`, so it is specialised to its device at compile time.
`Iso.open` refuses a device whose blocks are not 2048 bytes
(`IsoBadBlockSize`) and a volume whose logical block size is not 2048
(`IsoBadLogicalBlockSize`). Device errors come back as `IsoDev{e}`. Only
the blocks a request needs are read: the descriptors from sector 16 to the
terminator; a directory's own sectors (plus, with Rock Ridge, its records'
continuation areas and, for a relocated directory, the first sector of the
directory its CL entry names); a file's blocks.

blockdev now also has an owned interface, in which every operation hands the
device back, so that a device may be a single-owner value (an `Array` image,
later a file), and which has `write_block`. This package stays on the pure
interface, unchanged: it only reads, and each of its laws that mentions a
device is a statement about a pure read's `Result`, which on the owned
interface would become a pair (changing the laws). The pure interface is the
owned one's special case for `Data` devices (blockdev's adapters, with laws
that the owned helpers on an adapted device answer what the pure ones do). A
device on the owned interface, such as blockdev's array image `ImgDev`, is
read here through `ImgDev.freeze` (a copy into a `MemDev`). `MemDev` now
finds a block in O(log n) (a balanced tree of blocks) instead of walking a
list of them.

## API

Byte strings are `Octets` (bend-osdev-bytes); a file's total size is a
`W64` (bend-osdev-word64). The records and sum types below are open: their
fields and constructors are part of the interface. Everything not listed is
internal.

### fields.bend

| Def | Meaning |
|---|---|
| `IsoError`, `IsoError.show` | why something was refused, one constructor per failure (see `fields.bend`) |
| `IsoEndian`: `IsoEndianCheck{}`, `IsoEndianLittle{}`, `IsoEndianBig{}`; `IsoEndian.default()` | read both halves of a both-endian field and refuse a mismatch (the default), or trust one half |
| `Iso.both32_encode(v)`, `Iso.both16_encode(v)`, `Iso.both32_encode_pair(lo, hi)`, `Iso.both16_encode_pair(lo, hi)` | a field's 8 or 4 bytes (a pair writes different halves, for tests) |
| `Iso.both32_decode(mode, o, at)`, `Iso.both16_decode(mode, o, at)` | the field at byte `at`: `IsoBothEndianMismatch{at}`, `IsoTruncated` |
| `IsoDirDate{year, month, day, hour, minute, second, offset}` and `.encode`, `.decode`, `.norm`, `.bytes`, `.show` | the 7-byte date (years since 1900; offset: the signed byte as stored) |
| `IsoVolDate{year, month, day, hour, minute, second, hundredths, offset}` and `.encode`, `.decode`, `.norm`, `.fits`, `.unspecified`, `.is_unspecified`, `.show` | the 17-byte date (`IsoBadDate` for a byte that is not a digit) |
| `Iso.text(o)` | an a-/d-character field as text, trailing spaces dropped |

### joliet.bend

| Def | Meaning |
|---|---|
| `Iso.joliet_level(escapes)` | 1, 2 or 3 for `%/@`, `%/C`, `%/E`; 0 otherwise |
| `Iso.ucs2_decode(o)`, `Iso.ucs2_encode(s)`, `Iso.ucs2_norm(s)`, `Iso.ucs2_text(o)` | UCS-2 big-endian text (`IsoBadJolietName` for an odd length); one character per code unit |

### dirrec.bend

| Def | Meaning |
|---|---|
| `IsoDirRec{ext_attr, extent, size, date, flags, unit_size, gap, vol_seq, ident, system_use}` | a directory record |
| `IsoDirRec.decode(mode, o)` | the record at the start of `o` (any bytes may follow): `IsoTruncated`, `IsoBadIdentifierLength`, `IsoBadRecordLength`, both-endian errors |
| `IsoDirRec.encode(r)`, `IsoDirRec.length(r)`, `IsoDirRec.norm(r)`, `IsoDirRec.fits(r)` | writing a record, its length (LEN_DR), the record as stored, and the class the round-trip law covers |
| `IsoDirRec.is_dir`, `.is_hidden`, `.is_associated`, `.is_multi_extent`, `.is_self`, `.is_parent`; `.extent_of`, `.size_of`, `.flags_of`, `.ident_of`, `.system_use_of` | flags and fields |
| `Iso.blocks(size)` | the logical blocks `size` bytes take |

### susp.bend

| Def | Meaning |
|---|---|
| `IsoSuspEntry{sig1, sig2, version, data}`, `.sig`, `.is(e, a, b)`, `.data_of`, `.ce(mode, e)`, `.er(e)` | an entry; a CE's `IsoCe{block, offset, length}`; an ER's `IsoEr{id, descriptor, source, version}` |
| `Iso.susp_parse(o)` | the entries of one area (`IsoBadSusp` for a length below 4 or past the area; a zero byte or ST ends it) |
| `Iso.susp_sp(o)` | LEN_SKP, when the area starts with an SP entry |
| `Iso.susp_entries(~dev, d, mode, fuel, skip, area)` | the entries of an area and of every continuation area it leads to (`IsoBadContinuation`, `IsoContinuationLimit` past `fuel`) |

### rockridge.bend

| Def | Meaning |
|---|---|
| `IsoRr{px, name, link, stamps, dev, child, parent, relocated}`, `IsoRr.empty()`, `IsoRr.name_of`, `IsoRr.link_of` | what a record's entries say: `IsoPx{mode, links, uid, gid, serial}`, the NM name, the SL target, `IsoRrStamp{kind, long, raw}`s, `IsoPn{high, low}`, CL and PL locations, RE |
| `Iso.rr_of(mode, entries)` | the entries folded (NM and SL continued across entries; `IsoBadRrip{sig}` for a short entry) |
| `Iso.rr_link_text(components)`, `IsoSlComp{flags, text}` | an SL target's text |
| `Iso.rr_present(entries)` | an ER with an RRIP identifier (`RRIP_1991A`, `IEEE_P1282`, `IEEE_1282`), or an RR or PX entry |
| `IsoPx.is_dir`, `IsoPx.is_link` | the file type in a PX mode |

### volume.bend

| Def | Meaning |
|---|---|
| `IsoNaming`: `IsoNamingAuto{}`, `IsoNamingPlain{}`, `IsoNamingJoliet{}`, `IsoNamingRockRidge{}`; `IsoNaming.show` | which names entries get |
| `IsoOptions{naming, endian, strip_version, follow_relocation, max_descriptors, max_continuations, max_depth}`, `IsoOptions.default()`, `.with_naming`, `.with_endian`, `.with_strip_version`, `.with_follow_relocation` | the choices (see Extension points) |
| `IsoPvd{system_id, volume_id, space_size, set_size, seq_number, block_size, path_table_size, path_table_l, path_table_m, root, volume_set_id, publisher_id, preparer_id, application_id, copyright_file, abstract_file, biblio_file, created, modified, expires, effective, file_structure}`, `.root_of`, `.block_size_of`, `.space_size_of`, `.volume_id_of` | a primary or supplementary descriptor (the dates are the raw 17 bytes: `IsoVolDate.decode` them) |
| `IsoDescriptor`: `IsoDescPrimary`, `IsoDescSupplementary{flags, escapes, joliet, svd}`, `IsoDescBoot{system_id, catalog}`, `IsoDescPartition`, `IsoDescUnknown`, `IsoDescTerminator`; `.show` | a descriptor |
| `Iso.descriptor_parse(mode, sector, o)`, `Iso.descriptors(~D, ~read_block, d, opts)` | one descriptor (`IsoNotIso`, `IsoBadDescriptorVersion`), the set from sector 16 (`IsoNoTerminator`) |
| `Iso.open(~dev, d, opts)`, `IsoVolume{opts, naming, pvd, root, joliet, rr_skip, boot_catalog, descriptors}`, `.naming_of`, `.pvd_of` | a volume opened: the naming chosen, the root of its hierarchy (`IsoNoPrimary`, `IsoNoJoliet`, `IsoNoRockRidge`) |
| `Iso.boot_catalog(~dev, d, v)`, `Iso.boot_catalog_parse(o)`, `IsoBootCatalog{platform, id, initial}`, `IsoBootEntry{bootable, media, load_segment, system_type, sectors, rba}` | El Torito (`IsoBadBootCatalog`) |

### dir.bend

| Def | Meaning |
|---|---|
| `Iso.dir_records(~dev, d, mode, extent, size)` | every record of a directory, in order, `\0` and `\1` included |
| `IsoEntry{name, is_dir, size, extents, rec, rr}`, `IsoExtent{block, size}`; `.name_of`, `.is_dir_of`, `.size_of`, `.extents_of`, `.rec_of`, `.rr_of`, `.link` | an entry: a multi-extent file is one entry with all its extents |
| `Iso.root(v)`, `Iso.list(~dev, d, v, dir)`, `Iso.find(~dev, d, v, path)`, `Iso.list_path(~dev, d, v, path)` | listing (`IsoNotDirectory`; `IsoExtentOutOfRange` for a directory past the volume space) and finding (`IsoNotFound`, `IsoDepthLimit`); symbolic links are reported, not followed |

### file.bend

| Def | Meaning |
|---|---|
| `Iso.file_start(e)`, `Iso.file_next(~dev, d, c)`, `IsoCursor{extents, block, left}`, `IsoChunk`: `IsoChunkEnd{}`, `IsoChunkData{data, next}` | a stream: one block per step, the last of each extent cut at its data length (`IsoIsDirectory`, `IsoInterleaved`) |
| `Iso.file_read(~dev, d, e, off, len)` | the bytes from `off` to `off + len`, fewer where the file ends |

### fence.bend and iso9660.bend

| Def | Meaning |
|---|---|
| `IsoFence{dev, first, count}`, `IsoFence.block_size`, `IsoFence.read_block` | a `MemDev` answering blocks `first` to `first + count - 1` only |
| `Iso.mount(~dev, d)` | `Iso.open` with the default options |
| `Iso.read_path(~dev, d, v, path, off, len)`, `Iso.stream_path(~dev, d, v, path)` | reading by path |
| `Iso.walk(~dev, d, v)`, `IsoWalkItem{path, entry}`, `IsoWalkItem.show` | every entry, depth first |

## Naming

* **Plain**: the file identifier; with `strip_version` (the default) the
  `;n` version and a trailing `.` (a file with no extension) are dropped.
* **Joliet**: the identifier as UCS-2, `;n` dropped likewise.
* **Rock Ridge**: the NM name (NM entries joined across CONTINUE, across
  continuation areas); a record with no NM gets its plain name. With
  `follow_relocation` (the default) a record with a CL entry is the
  directory the CL names and a directory with RE is left out of its
  (`rr_moved`) parent; without it both are listed as stored, and every
  entry's `IsoRr` reports CL, PL and RE either way.
* **Auto** (the default): Rock Ridge if the primary root's `\0` record starts
  with SP and its entries mark RRIP, else Joliet if there is a Joliet
  descriptor (the highest level), else plain.

## Extension points

* **Any device**: pass its type and its `block_size` and `read_block` as
  template arguments. A device of other block sizes can be adapted by a
  wrapper device that answers 2048-byte blocks.
* **Options** (`IsoOptions`, named default `IsoOptions.default()`): the
  naming, which both-endian half to trust (or both, checked), version
  stripping, following relocated directories, and the limits on
  descriptors, continuation areas and depth.
* **Pieces on their own**: every record type has its own reader (and the
  fields, dates, directory records and UCS-2 names their writers), so a
  caller can read a volume differently (by path tables, say) with the same
  parts. `IsoFence` keeps any reader to a region of a device.
* **Writing images** is out of scope; the single-record writers
  (`Iso.both32_encode`, `IsoDirDate.encode`, `IsoVolDate.encode`,
  `IsoDirRec.encode`, `Iso.ucs2_encode`) are where an image writer starts.
* **Names**: Rock Ridge names are taken one character per byte, and Joliet
  names one character per UCS-2 code unit; decoding UTF-8 (or UTF-16
  surrogate pairs) belongs in a layer on top.
* **Streaming**: files stream a block at a time. Directories are read whole
  (`Iso.dir_records` reads a directory's sectors and answers its records),
  which holds every record in memory (see Speed and size limits); a
  sector-at-a-time walk would be a cursor like `IsoCursor` over
  `iso.dir.records`.

Not done yet: SUSP ES (extension selection) and RRIP SF (sparse files) are
not interpreted; El Torito section entries after the initial entry are not
read; interleaved files are refused; the path tables are not read (the
directory records are); volume sets of more than one volume are not joined.

## Laws

`LAWS.bend`:

* **for every input**:
  * both-endian fields: 32-bit write-then-read gives the value, 16-bit its
    low 16 bits; trusting the LSB (or MSB) half reads that half whatever the
    other holds; halves that differ are refused under `IsoEndianCheck`, at
    both widths (with a witness that such halves exist);
  * the 7-byte date: every `IsoDirDate` reads back as stored (each field to
    8 bits), and every 7 bytes read and written again are the same bytes;
  * the 17-byte date: every `IsoVolDate` whose fields fit their digits
    (year below 10000, the rest below 100) reads back exactly, its offset
    to 8 bits (with a witness); proved by induction on the digit counter,
    not by enumeration;
  * UCS-2: every text reads back, each code to 16 bits;
  * directory records: every record with a non-empty identifier and a
    length below 256 reads back as stored, whatever bytes follow it (with a
    witness);
  * reading only what is needed: `Iso.dir_records` gives the same on a
    device fenced to the directory's own blocks (so the walk never reads
    outside the directory's extent); a stream step gives the same on a
    device fenced to the one block it is at; the end of a stream reads
    nothing. `Iso.dir_records` runs a loop over the sectors
    (`iso.dir.walk`); the fence is proved on the structural reference
    (`iso.dir.walk.ref`) and carried over by a lemma, for every device and
    input, that the two are equal (`dw_eq` in `PROOF.bend`, used for both
    the `MemDev` and the `IsoFence` side);
* **vectors**: a root record, a file record with its Rock Ridge entries and
  a creation date taken from an image genisoimage wrote; Joliet levels;
  identifiers; SUSP areas good and bad; SL link text; NM continuation; a
  short PX; malformed records and dates; block counts.

The proofs use bytes' interface laws (`octets_to_of`, `octets_of_to`,
`octets_append_list`, `octets_of_list_idempotent`) where a byte string's
contents are unknown, and split a `U32` into its bits where both-endian
halves are compared.

## Tests

* `check.bend`: an image built with the package's own writers (a primary and
  a Joliet hierarchy, SP, ER, PX, NM and SL entries, a two-block file):
  descriptors, the three namings, ranges, a stream, lookups, a both-endian
  mismatch refused and trusted, a blank device, a 512-byte device, dates,
  records and SUSP areas. Its last line is a large input, a volume made up
  as it is read: a directory of 7,200 entries (240 KB) walked and searched
  for a name it lacks, and a file of 2,400 extents read whole (about 1.3 s
  of the run).
* `ref/run.sh` (48 cases on 34 images, seed 2026): `ref/gen.py` builds
  images with an independent ISO 9660 / Joliet / Rock Ridge builder written
  from the specifications (long names in several NM entries, symbolic links
  with split components, CE continuation areas, a multi-sector directory, a
  multi-extent file), and with **genisoimage** (plain, `-J`, `-R`, `-r -J`,
  a deep tree it relocates, an El Torito image) and **xorriso** (`-as mkisofs
  -R -J`) from random trees. Its independent reader is checked against the
  source trees (names, kinds, link targets, contents) and against
  `isoinfo -l` (plain, `-J`, `-R`); `isoinfo -d -l` reads the builder's own
  images. Then the package reads every image a block at a time (`File.read_at`
  into a `MemDev`), walks it, streams every file (CRC-32), reads byte ranges
  (across extents and past the end) and the boot catalog, and must print
  what the reader prints. Fourteen corruptions (bad standard identifier,
  version, both-endian halves, block size, no primary; record and identifier
  lengths, a record's extent halves, a directory extent past the volume;
  SUSP lengths, a short PX, a CE past its block,
  an odd Joliet name) must be refused with the named error, and a mismatch
  read with a trusted half must succeed. The reader shares an author with the
  package, which is why the third-party tools check it.
  Without genisoimage, xorriso or isoinfo the independent part still runs and
  must match, and the run reports a skip (exit 77). CI needs the apt packages
  `genisoimage` (which provides isoinfo) and `xorriso`.

## Speed and size limits

Measured on native builds (Bend 2.0.37, `bend file.bend -o prog`, WSL2;
times are whole runs, including loading the test device). Byte strings are
`Octets` (bytes' `OctByte` storage, about 80 bytes of memory per byte held
natively). The differential test (34 images of up to 480 KB, 48 cases,
every file streamed and CRC'd) runs in 2.0 s and 50 MB once built (the
build takes 21 s and 500 MB; about 12 s on the JavaScript lane, `bend
file.bend`); `check.bend` in 0.9 s (about 2.6 s on the JavaScript lane); the
proofs check in about 1.5 s, with `--verdict` in about 4.3 s.

Large images, read a 2048-byte block at a time from a sparse device (a
`MemDev` holding the image's metadata blocks, every file's data zero, so the
streamed and read bytes' CRC-32s are checked against Python's `zlib`; the
counts against `ref/gen.py`'s reader). The JavaScript-lane figures are the
earlier ones, on images built the same way:

| Image | Operation | Time, peak memory, native | JavaScript lane, before |
|---|---|---|---|
| plain, `ref/gen.py`'s builder, a directory of 30,000 entries (1.28 MB) | open only | 0.25 s, 127 MB | |
| | `Iso.list` | 1.1 s, 178 MB | 4.1 s, 874 MB (940 KB directory) |
| | `Iso.walk` (30,000 items); `Iso.find` of the last | 1.2 s, 179 MB; 1.2 s, 178 MB | 7.8 s, 896 MB; 7.1 s |
| plain, a 40 MB file of 20,481 extents of 2 KB | `Iso.find` | 0.77 s, 110 MB | 3.1 s, 548 MB |
| | stream it (20,481 pieces) | 10.4 s, 110 MB | 91 s, 683 MB |
| | read 1 MB across 512 extents; 100 KB; its last 5,000 bytes | 1.1 s, 193 MB; 0.79 s, 110 MB; 1.5 s, 110 MB | 6.3 s, 1.9 GB; 3.0 s, 605 MB; 3.1 s |
| Rock Ridge and Joliet, the builder, a 12 MB file of 3,073 extents | `Iso.find` | 0.32 s, 87 MB | 2.8 s, 690 MB |
| | stream it; read 1 MB across 256 extents | 3.2 s, 87 MB; 0.65 s, 166 MB | 14 s, 690 MB; 7.1 s, 1.9 GB |
| `genisoimage -R -J`, 22 MB, a directory of 4,000 Rock Ridge names | open only | 0.30 s, 134 MB | |
| | `Iso.list` of it; `Iso.walk` | 0.96 s, 204 MB; 0.98 s, 205 MB | 11 s, 1.2 GB; 8.8 s, 1.2 GB |
| | stream a 20 MB file (10,241 pieces) | 4.5 s, 135 MB | 24 s, 704 MB |
| | `Iso.read_path` of 1 MB; of 100 KB | 0.60 s, 233 MB; 0.32 s, 144 MB | 11.7 s, 1.5 GB; 1.0 s, 480 MB |

Before this round a directory listing, a walk, a lookup and a file's extents
recursed once per record (or per extent, with a quadratic list of pending
extents), and a directory walk once per sector: on the JavaScript lane a
30,000-entry directory overflowed the stack and a 20,481-extent file ran out
of memory, while 12,000 entries and 3,073 extents still worked. They are loops now (the walk of
sectors keeps its structural form as the reference the proofs use), and a
byte range is read from the device in pieces of at most 64 blocks, so no
single read is long. Nothing recurses over a file's size, a directory's
records or a file's extents; walking a tree recurses once per directory level
(at most `max_depth`). What is left:

* a range read answers one `Octets`, so its length is bounded by memory:
  1 MB adds about 80 to 100 MB natively (1.5 to 2 GB on the JavaScript
  lane). Stream large files (`Iso.file_start` /
  `Iso.file_next`), which hold one block at a time;
* a directory is read whole: every record is held, its identifier and
  system use area as `Octets` (natively about 1.7 KB a record with plain
  names and about 17 KB with genisoimage's Rock Ridge entries, beyond the
  device; about 30 KB and 250 KB on the JavaScript lane), so listing a
  directory of 30,000 plain entries takes about 180 MB in all and one of
  4,000 Rock Ridge entries about 200 MB (about 900 MB and 1.2 GB on the
  JavaScript lane);
* offsets and lengths are `Nat`s.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (its last line a 7,200-entry directory and a
2,400-extent file), `ref/run.sh` 48 cases on 34 images match (with
genisoimage, xorriso and isoinfo), `scripts/deps.sh` passes; all re-run
unchanged on blockdev's tree-backed `MemDev`. Large inputs:
measured to 30,000-entry directories and 40 MB files of 20,481 extents (see
Speed and size limits).
