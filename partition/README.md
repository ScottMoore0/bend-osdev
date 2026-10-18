# bend-osdev-partition

Partition tables: the classic Master Boot Record (with the protective MBR of
a GPT disk) and the GUID Partition Table. Parsing, validating and building
both, with the CRCs GPT requires.

Specifications: the UEFI Specification (version 2.10), chapter 5, "GUID
Partition Table (GPT) Disk Layout": section 5.2.1 for the legacy MBR layout,
5.2.3 for the protective MBR, 5.3.2 for the GPT header and 5.3.3 for the
partition entry array. GUIDs use bend-osdev-uuid (RFC 9562; the GUID layout
of the UEFI Specification's appendix A), and the CRCs are CRC-32/ISO-HDLC
from bend-osdev-crc.

## Files

| File | Holds |
|---|---|
| `partition.bend` | the entry concern: telling a disk's scheme from its first two blocks |
| `mbr.bend` | the MBR: records, CHS addresses, parsing and building a sector, the protective MBR |
| `gpt.bend` | the GPT: header blocks, their CRC, entries, entry arrays, laying out a new disk |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/genlaws.py`, `gen/sectors.txt` | write `LAWS.bend`; its vectors are the sectors in `sectors.txt`, dumped from images sgdisk and sfdisk made |
| `gen/genproof.py`, `gen/parts.py` | write `PROOF.bend` (`parts.py` holds the property proofs, whose bit-split patterns are long). Run `python3 partition/gen/genlaws.py`, then `python3 partition/gen/genproof.py` |
| `check.bend` | a runnable check on sectors written by sgdisk and sfdisk |
| `ref/gen.py`, `ref/run.sh` | the differential test against sgdisk and sfdisk (`gen.py` writes `ref/cases.bend` and `ref/expected.txt`, which `ref/.gitignore` lists) |

Bend imports do not re-export: import `mbr.bend` or `gpt.bend` directly for
their defs.

## API

Byte strings are `Octets` (bend-osdev-bytes), 64-bit values `W64`
(bend-osdev-word64), GUIDs `Uuid` (bend-osdev-uuid). The records below are
open: their fields are part of the interface.

### partition.bend

| Def | Meaning |
|---|---|
| `Partition.detect(lba0, lba1)` | `PartitionNone{}` (no MBR signature), `PartitionMbr{mbr}`, `PartitionGpt{mbr, header}` (a protective MBR, OS type 0xEE, and a valid GPT header), or `PartitionBadGpt{mbr, error}` (a protective MBR whose primary header is refused: look for the backup) |
| `PartitionScheme.show` | its name |

### mbr.bend

| Def | Meaning |
|---|---|
| `Mbr{disk_signature, p0, p1, p2, p3}` | a table: the disk signature and four records |
| `MbrEntry{status, first, os_type, last, lba, sectors}` | a record: boot indicator (0x80 bootable), first and last CHS, OS type, first LBA, size |
| `MbrChs{head, sector, cylinder}` | a CHS address |
| `Mbr.parse(o)` | the table of a 512-byte sector: `Fail{MbrTooShort{}}`, `Fail{MbrBadSignature{}}` (no 0x55 0xAA at 510) |
| `Mbr.build(boot, m)` | the sector: the boot code cut or padded to 440 bytes, then the table |
| `Mbr.boot_code(o)` | the 440 bytes of boot code |
| `Mbr.norm`, `MbrEntry.norm`, `MbrChs.norm` | a value as the sector stores it (8-bit status and type; 8-, 6- and 10-bit CHS fields) |
| `MbrEntry.empty()`, `MbrEntry.is_used`, `MbrEntry.is_bootable` | records |
| `MbrChs.of_lba(g, lba)`, `MbrGeometry{heads, sectors}`, `MbrGeometry.standard()` | the CHS address of a block (255 heads and 63 sectors by default; 1023/255/63, stored 0xFFFFFF, past cylinder 1023) |
| `Mbr.protective(last_lba)`, `Mbr.protective_with(g, last_lba)`, `Mbr.is_protective` | the protective MBR of a GPT disk whose last block is `last_lba` |
| `MbrError`, `MbrError.show` | why a sector was refused |

### gpt.bend

| Def | Meaning |
|---|---|
| `GptHeader{revision, header_size, header_crc, my_lba, alternate_lba, first_usable, last_usable, disk_guid, entries_lba, entry_count, entry_size, entries_crc}` | a header |
| `Gpt.parse_header(o)` | the fields of a header block (`GptTooShort`, `GptBadSignature`); no CRC check |
| `Gpt.validate_header(o)` | the same, checked: signature, header size from 92 bytes to the block's size (`GptBadHeaderSize`), header CRC (`GptBadHeaderCrc`) |
| `Gpt.header_crc(o)`, `Gpt.header_crc_ok(o)` | the header CRC a block should carry (CRC-32 of its first header-size bytes, the CRC field read as zero), and whether it does |
| `Gpt.build_header(h)`, `Gpt.build_header_with(layout, h)` | the header block of `h`, its header CRC computed (`h.header_crc` is ignored), one block long |
| `GptHeader.seal(h)` | `h` with the header CRC `build_header` writes |
| `GptEntry{type_guid, unique_guid, first_lba, last_lba, attributes, name}` | an entry; `name` is its UTF-16 code units |
| `GptEntry.decode(o)`, `GptEntry.encode(e)` | an entry's 128 bytes |
| `GptEntry.norm(e)` | the entry as stored: the name cut or padded to 36 code units of 16 bits |
| `GptEntry.unused()`, `GptEntry.is_used(e)` | an all-zero entry; whether the type GUID is not nil |
| `GptEntry.name_text(e)`, `Gpt.name_units(s)` | the name as text (up to its first NUL, surrogate pairs combined), and the code units of a text |
| `Gpt.entries(h, o)` | the entries of an entry array, as many as `h` says (fewer if the array ends); `GptBadEntrySize` below 128 |
| `Gpt.entries_encode(es)`, `Gpt.entries_crc_ok(h, o)` | an entry array, and whether `h.entries_crc` is the CRC-32 of its first count × size bytes |
| `Gpt.build(h, es)` | the header block of `h` for the entries `es`: both CRCs computed |
| `GptLayout{block_size, entry_count}`, `GptLayout.standard()`, `GptHeader.standard(layout, disk_blocks, guid)`, `GptHeader.backup(h)`, `Gpt.entry_blocks(layout)` | laying out a new disk: the primary header (entries from LBA 2, usable blocks between the arrays) and its backup (in the last block, its entries just after the last usable LBA) |
| `GptHeader.entries_crc`, `GptHeader.entry_count`, `GptHeader.entry_size` | accessors |
| `GptError`, `GptError.show` | why a header or array was refused |

## Extension points

* **Geometry and layout are parameters.** `MbrGeometry` sets the heads and
  sectors CHS addresses are computed with (`MbrGeometry.standard()` is the
  usual 255/63); `GptLayout` sets the logical block size and the number of
  entries (`GptLayout.standard()`: 512-byte blocks, 128 entries). 4096-byte
  blocks: `Gpt.build_header_with(GptLayout{4096, 128}, h)` and
  `GptHeader.standard(GptLayout{4096, 128}, …)`.
* **Bytes, words and GUIDs are other packages' opaque types**, used only
  through their interfaces; the proofs see a `W64` through word64's law
  `parts_of` and a `Uuid` through uuid's law `make_bytes`.
* **Not covered yet:** extended and logical MBR partitions (an extended
  partition's records are returned as they are, not followed), hybrid MBRs,
  and finding the backup header when the primary is damaged (read the last
  block and pass it to `Gpt.validate_header`).

## Laws

`LAWS.bend`:

* **for every input:**
  * `Mbr.parse(Mbr.build(boot, m)) == Done{Mbr.norm(m)}`, for every boot code
    and table;
  * `Gpt.header_crc_ok(Gpt.build_header(h)) == True`: a built header block
    validates;
  * `Gpt.parse_header(Gpt.build_header(h)) == Done{GptHeader.seal(h)}`;
  * `GptEntry.decode(GptEntry.encode(e)) == Done{GptEntry.norm(e)}`;
  * the entries CRC that `Gpt.build(h, es)` stores is the CRC-32 of
    `Gpt.entries_encode(es)`;
* **vectors:** a header block, an entry, the protective MBR and an MBR
  written by sgdisk and sfdisk: their parsed fields, the header CRC, building
  them back byte for byte, the standard layout of that disk, a header with one
  changed byte refused for its CRC, CHS addresses, UTF-16 names with a
  surrogate pair, telling the schemes apart, and malformed sectors with the
  failure each gives.

The proofs split only `U32`s into bits. Each `W64` field is first rewritten
as `from_parts(hi, lo)` (word64's `parts_of`) and each GUID as
`Uuid.make` of its bytes (uuid's `make_bytes`), so no other package's type is
opened. Converting a list to `Octets` and back goes through bytes' interface
law `octets_to_of`, and the parsers read fields on the list layer
(`B.le32_at`, `Uuid.from_guid_list`), so no proof depends on how `Octets`
stores its bytes.

## Tests

`check.bend` also builds sgdisk's header block from scratch
(`GptHeader.standard`, the two entries, 126 unused ones) and gets sgdisk's
bytes, entries CRC included.

`ref/run.sh` makes 18 small disk images (sparse files of 2 to 6 MiB) and
compares 116 facts with the tools that wrote them:

* 12 GPT images by `sgdisk` (random disk and partition GUIDs, one to four
  partitions of random types, sizes, attributes and names, ASCII and not),
  checked against `sgdisk -p` (disk GUID, usable LBAs, table location and
  size), `sgdisk -i` (each partition) and `sfdisk -J` (cross-checked), with
  `sgdisk -v` reporting no problems: the primary and backup headers, both
  entry CRCs, every partition, and the header blocks and protective MBR
  rebuilt byte for byte from the parsed values;
* two of them with one byte changed after sgdisk wrote them (a header's
  reserved field; an unused entry): the package refuses that header, or that
  array's CRC, as Python's zlib confirms;
* 6 MBR images by `sfdisk` (random disk identifier, one to four partitions of
  random types, sizes and boot flags), checked against `sfdisk -J`; the CHS
  fields against the raw bytes decoded in `gen.py`; the sector rebuilt byte
  for byte.

sgdisk does not print names outside the Basic Multilingual Plane correctly,
so surrogate pairs are covered by the vectors only.

## Speed

Byte strings are lists and the fields are read by bit slicing, so a table is
read one sector at a time: read the blocks you need (`File.read_at`), not
the disk.

## Sizes

Measured on native builds (Bend 2.0.37, `bend file.bend -o prog`, WSL2):

| Run | Time, native | Peak RAM, native | JavaScript lane, before |
|---|---|---|---|
| an 8 MiB image sgdisk wrote with 128 partitions: the protective MBR parsed, the header validated, the 16 KB entry array's CRC checked, every entry read (128 used, the names sgdisk wrote) | 0.02 s | 6 MB | 0.65 s, 190 MB |
| a 1,024-entry table built (`Gpt.entries_encode`, `Gpt.build`), validated and read back | 0.31 s | 30 MB | 2.2 s, 670 MB |
| the same with 4,096 entries (a 512 KB array) | 1.3 s | 114 MB | 6.9 s, 2.2 GB |

`Gpt.entries` reads the array with a tail call, and decodes each entry from
its first 128 bytes. Before this it converted the whole rest of the array to
a list for every entry: on the JavaScript lane 128 entries took 1.4 s, 1,024
took 69 s, and 4,096 ran out of memory. Building an array
(`Gpt.entries_encode`) recurses once per entry, which is fine for the thousands of entries a table can have; the
MBR and the header are fixed-size. `check.bend` builds, validates and reads
a 384-entry table (a 48 KB array) as a regression test.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 116 facts from 18 images match.
