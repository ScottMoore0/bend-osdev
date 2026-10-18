# bend-osdev-fat

A read-only FAT12, FAT16 and FAT32 file system over bend-osdev-blockdev's
device interface: mounting a volume (its boot sector checked, a named error
for each failure), listing directories with their long (VFAT) names, finding
a path case-insensitively, and reading a file's bytes as a range or a sector
at a time. Writers for single on-disk records (a boot sector, a FAT entry, a
directory entry, a long name's entries) are included, for building images and
for the round-trip laws; a writing file system is not (see Extension points).

Specification: Microsoft Corporation, "Microsoft Extensible Firmware
Initiative FAT32 File System Specification: FAT: General Overview of
On-Disk Format", version 1.03, December 6, 2000: section 3 (the boot sector
and BPB, and 3.5, FAT type determination), section 4 (the FAT), section 5
(FSInfo), section 6 (directory entries) and section 7 (long directory
entries, the VFAT long-name format, and the short-name checksum). No GPL
source was read (no Linux `fs/fat`, no dosfstools or mtools source); the
reference test runs dosfstools and mtools as programs only.

The FAT type is fixed by the count of clusters alone, as section 3.5 says
(fewer than 4085: FAT12; fewer than 65525: FAT16; otherwise FAT32), never by
the `BS_FilSysType` label.

## Files

| File | Holds |
|---|---|
| `fat.bend` | the entry concern: mounting a volume, and the operations by path (`Fat.stat`, `Fat.list`, `Fat.read`, `Fat.open` / `Fat.next`) |
| `error.bend` | `FatError`, one constructor per failure, and `FatError.show` |
| `bpb.bend` | the boot sector and BPB, the BS_ fields, the checks and the volume geometry they give, the FAT type, FSInfo, the options; building a boot sector |
| `table.bend` | the FAT: FAT12 and FAT32 packing, entry values, reading an entry from the device, reading and writing entries of a FAT in memory, following a cluster chain with a bound; reading the device (`FatIo.read`) |
| `dirent.bend` | directory entries: the 32-byte short entry (encode, decode, fields, times and dates), 8.3 names, long-name entries (encode, decode, build, the checksum), UCS-2 names |
| `dir.bend` | directories: the scan (streaming, an entry at a time), long names assembled and checked, listing, finding a name, resolving a path |
| `file.bend` | reading files: a cursor a sector at a time, and ranges |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`PROOF.bend` is written by `gen/genproof.py`: `python3 fat/gen/genproof.py`) |
| `check.bend` | a runnable check on a FAT12 image built with the package's own writers |
| `ref/gen.py`, `ref/run.sh`, `ref/harness.bend` | the differential test (`gen.py` writes `ref/cases.bend` and `ref/expected.txt`, which `ref/.gitignore` lists) |

Bend imports do not re-export: import the file whose defs you use.

## The device interface

Every operation that reads takes blockdev's template arguments `~Dv: Data`,
`~block_size: Dv -> Nat`, `~read_block: Dv -> Nat -> Result<&2, &2,
DevError, Octets>` and a device `d`, and reads through `Dev.read_bytes`: only
the blocks it needs (the boot sector, the directories on a path, the FAT
entries of the chains it follows, the sectors of the bytes asked for). The
device's block size need not be the volume's sector size. A device error is
`FatDev{e}`. In the examples below `T` stands for the three template
arguments, e.g. `~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block`.

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

The records below are open (their fields are part of the interface) except
`FatVolume`, `FatScan` and `FatCursor`, which are read through their defs.

### fat.bend

| Def | Meaning |
|---|---|
| `Fat.mount(T, d, opts)` | `FatFs{opts, bpb, vol}`: the boot sector read and checked |
| `FatFs.options`, `FatFs.bpb`, `FatFs.volume`, `FatFs.kind` | its parts |
| `Fat.stat(T, d, fs, path)` | what a path names: `FatPathRoot{}` or `FatPathNode{node}` (`FatNotFound`; `FatNotADirectory` when a component before the last is a file) |
| `Fat.list(T, d, fs, path)` | the entries of a directory, in order |
| `Fat.read(T, d, fs, path, off, len)` | at most `len` bytes of a file from `off`, never past its size (`FatIsADirectory`) |
| `Fat.open(T, d, fs, path)`, `Fat.next(T, d, fs, cur)` | streaming: a cursor at a file's start, then `FatChunk{data, rest}` a sector at a time (`rest` is `None` at the end) |
| `Fat.boot_ext(T, d, fs)`, `Fat.fs_info(T, d, fs)` | the BS_ fields (volume ID, label); the FAT32 FSInfo hints |

### error.bend

`FatError`: `FatDev{e}`, `FatTooShort`, the boot sector's `FatBadJump`,
`FatBadSignature`, `FatBadBytesPerSector{value}`,
`FatBadSectorsPerCluster{value}`, `FatClusterTooLarge{bytes}`,
`FatBadReservedSectors`, `FatBadFatCount`, `FatBadRootEntries`,
`FatBadTotalSectors`, `FatBadMedia{value}`, `FatBadFatSize`, `FatBadVersion`,
`FatBadRootCluster{cluster}`, `FatTooSmall`, `FatBadFsInfo`; chains'
`FatBadCluster{cluster}` (out of range), `FatFreeInChain{cluster}`,
`FatBadInChain{cluster}`, `FatChainLoop`, `FatChainShort` (ends before the
file's size); directories' `FatNotLongEntry`, `FatLfnBadChecksum`,
`FatLfnBadSequence`, `FatDirTooLong` (over 65536 entries); paths'
`FatNotFound`, `FatNotADirectory`, `FatIsADirectory`.
`FatError.show(e)` names it.

### bpb.bend

| Def | Meaning |
|---|---|
| `FatType`: `Fat12{}`, `Fat16{}`, `Fat32{}`; `FatType.of_clusters(n)`, `FatType.show` | the type a count of clusters gives |
| `FatBpb{jump, oem, bytes_per_sector, sectors_per_cluster, reserved_sectors, num_fats, root_entries, total16, media, fat_size16, sectors_per_track, heads, hidden, total32, fat_size32, ext_flags, fs_version, root_cluster, fs_info, backup_boot, signature}` | the BPB as stored (the FAT32 fields read at their offsets whatever the type, as section 3.5 reads `BPB_FATSz32`) |
| `FatBpb.decode(o)` | the fields of a boot sector, unchecked (`FatTooShort` under 512 bytes) |
| `FatBootExt{drive, boot_sig, volume_id, label, fs_type}`, `FatBootExt.decode(t, o)` | the BS_ fields, at 36 (FAT12/16) or 64 (FAT32) |
| `FatOptions{max_cluster_bytes, strict_names}`, `FatOptions.default()`, `FatOptions.lenient()` | the reader's choices (see Extension points) |
| `FatVolume.of_bpb(opts, b)`, `FatVolume.parse(opts, o)` | the checked geometry, or the first check that fails, in this order: signature 0x55AA at 510, jump (0xEB ?? 0x90 or 0xE9), bytes per sector (512 to 4096), sectors per cluster (a power of 2 to 128), cluster size, reserved sectors, FAT count, media (0xF0, 0xF8 to 0xFF), total sectors, FAT size, the metadata smaller than the volume and at least one cluster, the FAT large enough for every cluster, the active FAT, then FAT32's (no fixed root, FATSz16 and TotSec16 zero, version 0, root cluster in range) or FAT12/16's (a fixed root) |
| `FatVolume.kind`, `sector`, `cluster_bytes`, `fat_start`, `fat_bytes`, `fats`, `root`, `data_start`, `clusters`, `cluster_offset(v, n)`, `valid_cluster(v, n)` | the geometry, in bytes from the device's start; valid clusters are 2 to `clusters + 1`; the FAT read is the active one (FAT32 `BPB_ExtFlags`) |
| `FatRoot`: `FatRootFixed{start, entries}`, `FatRootChain{cluster}` | where the root directory is |
| `FatFsInfo{free_count, next_free}`, `FatFsInfo.parse(o)`, `FatFsInfo.build(f)` | FSInfo (its three signatures checked) |
| `FatBpb.build(t, b, x)` | a boot sector (writer) |

### table.bend

| Def | Meaning |
|---|---|
| `Fat12Window{first, second}`, `Fat12.get(odd, w)`, `Fat12.set(odd, w, v)` | FAT12 packing: the two bytes at `n + n / 2` and the even (`odd = False`) or odd entry in them |
| `Fat32.get(v)`, `Fat32.set(old, v)` | FAT32 packing: the low 28 bits; the high 4 kept |
| `FatEntry`: `FatFree{}`, `FatNext{cluster}`, `FatBad{}`, `FatEnd{}`; `FatEntry.of(t, v)`, `FatEntry.value(t, e)`, `FatEntry.bad(t)`, `FatEntry.end_value(t)` | what an entry value means, and back |
| `FatTable.get(T, d, vol, n)` | the entry of cluster `n`, read from the device (two or four bytes, across a sector boundary if need be) |
| `FatTable.get_in(t, fat, n)`, `FatTable.set_in(t, fat, n, v)` | the same on a FAT held in memory, and writing an entry there (writer) |
| `FatLink`: `FatLinkEnd{}`, `FatLinkNext{cluster}`; `FatChain.next(T, d, vol, c)` | where a chain goes after `c` (`FatFreeInChain`, `FatBadInChain`, `FatBadCluster`) |
| `FatChain.walk(T, d, vol, start)` | the clusters of a chain (none from cluster 0); more than the volume's count of clusters is `FatChainLoop` |
| `FatIo.read(T, d, off, len)` | bytes from the device, its error wrapped |

### dirent.bend

| Def | Meaning |
|---|---|
| `FatDirent{name, attr, nt_res, crt_tenth, crt_time, crt_date, acc_date, clus_hi, wrt_time, wrt_date, clus_lo, size}` | a short entry as stored (`name`: the 11 bytes) |
| `FatDirent.decode(o)`, `FatDirent.encode(d)`, `FatDirent.norm(d)`, `FatDirent.fit_name(name)` | its 32 bytes, and the entry as they store it |
| `FatDirent.name`, `attr`, `size`, `cluster`, `is_dir`, `is_volume_label`, `has_attr(d, a)`, `short_text` | fields (`cluster` joins the high and low words); the name as text with Windows NT's lower-case flags |
| `FatDirent.write_time`, `write_date`, `create_time`, `create_date`, `access_date`; `FatTime{hour, minute, second}`, `FatDate{year, month, day}`, `FatTime.of`, `FatTime.encode`, `FatDate.of`, `FatDate.encode` | times and dates |
| `FatAttr.read_only()` … `FatAttr.archive()`, `FatAttr.long_name()` | attribute bits |
| `FatName.text(name)`, `FatName.short_of(s)`, `FatName.units(s)`, `FatName.text_of(us)`, `FatName.same(a, b)`, `FatName.upper` | 8.3 names as text; the 8.3 form of a path component (upper-cased; `None` if it cannot be one); text to UCS-2 units and back (surrogate pairs); comparing ignoring ASCII case |
| `FatLfn{ord, units, chksum}`, `FatLfn.decode(o)`, `FatLfn.encode(e)`, `FatLfn.is_long(o)` | a long-name entry (13 units) |
| `FatLfn.checksum(short)`, `FatLfn.build(short, name)`, `FatLfn.carries(es, c)`, `FatLfn.cut(us)`, `FatLfn.count(n)` | the short name's checksum; a name's entries in stored order (writer); whether entries carry a checksum; a name's units before its 0x0000 |

### dir.bend

| Def | Meaning |
|---|---|
| `FatNode{long, entry}`, `FatNode.name`, `short_name`, `is_dir`, `size`, `cluster`, `long`, `entry` | an entry as listed: its long name (no units if none) and its short entry |
| `FatDir`: `FatDirRoot{}`, `FatDirAt{cluster}`; `FatDir.of_node(n)` | a directory |
| `FatDir.list(T, d, opts, vol, dir)`, `FatDir.find(T, d, opts, vol, dir, name)`, `FatDir.scan(T, d, opts, vol, dir, want)` | listing; the entry a name names (the scan stops there) |
| `FatWant`: `FatWantAll{}`, `FatWantName{units, short}`, `FatWant.name(s)` | what a scan looks for |
| `FatScan.start(opts, want)`, `FatScan.feed(s, o)`, `FatScan.step(s, o)`, `FatScan.found(s)`, `FatScan.ended(s)` | streaming: directory data in pieces of whole entries, from any source |
| `FatPath`: `FatPathRoot{}`, `FatPathNode{node}`; `FatPath.resolve(T, d, opts, vol, path)`, `FatPath.parts(s)`, `FatPath.dir(p)` | paths |

### file.bend

| Def | Meaning |
|---|---|
| `FatFile.open(vol, node)`, `FatFile.next(T, d, vol, cur)`, `FatChunk{data, rest}`, `FatChunk.data`, `FatChunk.rest` | streaming, a sector at a time |
| `FatFile.read(T, d, vol, node, off, len)` | a range |

## Extension points

* **Options** (`FatOptions`, defaults `FatOptions.default()`):
  `max_cluster_bytes` (32768: the specification's limit; `lenient()` takes
  65536, which some systems write) and `strict_names` (`True`: a long name out
  of sequence, or whose checksum does not match, makes the directory an error;
  `False`, as `lenient()`: such entries are ignored as orphans and the short
  name is used, the specification's own handling).
* **Any device**, through blockdev's template interface; a partition is a
  device that wraps another with an offset (a natural blockdev extension).
* **Streaming sources**: `FatScan` takes directory data from anywhere, so a
  cache, or a directory already in memory, can feed it.
* **Writing** is the next step. The writers for single records are here
  (`FatBpb.build`, `FatFsInfo.build`, `FatTable.set_in`, `FatDirent.encode`,
  `FatLfn.build` / `encode`); a writing file system needs a write operation
  in the device interface (blockdev names it as an extension), cluster
  allocation (FSInfo's hints), short-name generation (`~n` tails), directory
  entry insertion, and mirroring the FATs.
* **Not covered yet**: the backup boot sector (`backup_boot`) is parsed but
  not used as a fallback; long names compare ignoring ASCII case only (not the
  full Unicode upper-case table Windows uses); OEM code pages for short names
  (bytes above 127 are shown as the code points of the same value); a file
  read follows its chain only as far as its size, so a loop within that
  length is not noticed there (`FatChain.walk` finds every loop);
  `DIR_FstClusHI` is joined into the first cluster on FAT12/16 too (the
  specification says it is 0 there).
* `DIR_NTRes` bits 3 and 4 (Windows NT's lower-case base and extension) are
  applied when showing a short name; the specification reserves the field.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every input:**
  * `FatDirent.decode(FatDirent.encode(d)) == Done{FatDirent.norm(d)}` for
    every short entry `d` (the name cut or padded with spaces to 11 bytes,
    the 8- and 16-bit fields masked);
  * `FatLfn.carries(FatLfn.build(short, name), FatLfn.checksum(short)) ==
    True` for every short name and long name: a built long name carries its
    short name's checksum, the check the directory reader makes;
  * FAT12: `Fat12.get(odd, Fat12.set(odd, w, v)) == v & 0xFFF`, and setting
    the even entry leaves the odd entry that shares its second byte (and the
    odd entry, the even one that shares its first byte) unchanged, for every
    value and bytes;
  * FAT32: `Fat32.get(Fat32.set(old, v)) == v & 0x0FFFFFFF`, and the high 4
    bits of `old` are kept;
  * an entry value read back: the end-of-chain, bad and free values on every
    FAT type, and a next-cluster value under its three hypotheses (not 0, not
    the bad value, not above it), with witnesses that the hypotheses hold
    (cluster 2 on every type);
  * `FatChain.walk` returns at most the volume's count of clusters, for every
    in-memory device (`MemDev`), volume and start cluster. The walk runs as
    a loop (`FatChain.go`); the bound is proved on the structural reference
    (`FatChain.go.ref`) and carried over by a lemma that the two are equal
    for every device, fuel, cluster and link (`chain_eq` in `PROOF.bend`);
* **vectors:** the FAT type at 4084, 4085, 65524 and 65525 clusters; the
  checksum of `BOOTX64 EFI`; a hand-built entry's cluster, size, date, time
  and a short read refused; a long name's two entries and an entry's round
  trip; 8.3 forms of path components; FAT12 packing on known bytes; a short
  name with the NT lower-case flags.

The proofs use bytes' interface laws (`octets_to_of`, `octets_of_to`), never
the inside of `Octets`, and split only `U32`s into bits. The law about the
chain walk is stated for `MemDev`; its proof does not depend on the device
(each answer is a case), but a law cannot quantify over template arguments.

## Tests

`check.bend` builds a FAT12 volume with the package's writers (`FatBpb.build`,
`FatTable.set_in`, `FatDirent.encode`, `FatLfn.build`; a fragmented file, a
nested directory, a long name) and checks 23 results: mounting, listings,
case-insensitive paths through long and short names, ranges across a cluster
boundary, the pieces of a streamed file, a chain walk, lookups that fail, a
loop, a free cluster and an early end in a chain, an out-of-range cluster,
and a bad BPB. A 24th is a large input: a FAT16 volume of 50,000 clusters
made up as it is read (a device of 2-byte blocks computing the FAT), whose
25.6 MB file's chain of 50,000 clusters is walked, and 100 KB of it read
near its end (about 0.8 s and under 300 MB; the structural walk overflowed
the stack on it).

`ref/run.sh` compares 956 results on 39 images with `ref/gen.py`'s reader:

* 8 images from `gen.py`'s builder (written from the specification by the
  same author as the package, so not independent of its reading of the
  specification): FAT12, FAT16 and FAT32 at 512 to 4096 bytes per sector and
  1 to 4 sectors per cluster, at the type boundaries (4084, 4085 and 65525
  clusters), random trees with short names, long names (Unicode, a surrogate
  pair, exactly 13 and 26 units, names needing `~n` short names), lower-case
  8.3 names, empty files, files of whole clusters, fragmented chains, a
  directory spanning clusters, a volume label; each checked by `fsck.fat -n`
  (dosfstools) and against the builder's record of the tree;
* 26 corrupted copies: 15 boot sectors (each check: jump, signature, bytes and
  sectors per cluster, cluster size, reserved sectors, FATs, media, root
  entries, FAT size, total sectors, FAT32 version, root cluster, a fixed root
  on FAT32 that makes the count of clusters FAT16's), 6 chains (a loop to the
  start, a cluster pointing at itself, out of range, free, bad, ended early),
  a directory whose chain loops, and 4 long names (a checksum on every entry,
  on one entry, an ordinal, an orphan), each listed strictly (refused) and
  leniently;
* 5 images made by `mkfs.fat` (FAT12, FAT16, FAT32) and filled by `mmd` and
  `mcopy` (mtools) from random trees with long names and nested directories,
  checked against their source trees and `mdir`'s listing.

On every image: mounting, the label, FSInfo (FAT32), every directory listed,
every file read whole, streamed and in random ranges, chain walks, lookups
with the case of each name changed and through each component's short name,
and lookups that fail. FAT32 needs at least 65525 clusters (about 34 MB at
512 bytes per cluster), so the images go to Bend as sparse devices (the
non-zero 512-byte blocks) and are read a block at a time. CI needs the apt
packages `dosfstools mtools` (run.sh exits 77 without them).

## Speed and size limits

**Lanes.** The figures in this section were measured on bend's JavaScript lane
(`bend file.bend`, which runs `main` inside the bend process). That lane's
stack overflows at some tens of thousands of nested non-tail calls, and it
uses several times the memory of a native build (`bend file.bend -o prog`),
which has a 2 GB stack; see AGENTS.md, "Runtime and checker limits". They
will be re-measured natively once W64-heavy code builds natively
(bendlang/bend#1069).

Measured with Bend 2.0.37 under bun in WSL2 (not a native build; times are
whole runs, including loading the test device). Every operation reads
through `Octets`, which cost about 940 bytes of memory per byte
(when measured; bytes' compact `OctByte` storage, merged since, holds an
`Octets` in about a third of that, about 150 bytes per byte, and these
figures have not been re-measured).

`check.bend` runs in about 1.3 s. The reference test's generated program
(1.8 MB, 956 operations on 39 images) checks in 0.5 s and runs in about 17 s
with about 2 GB of memory: about 18 ms an operation, each of which mounts the
volume again.

Large images, read a 512-byte block at a time from a sparse device (its
non-zero metadata blocks, and file data computed from the block number):

| Image | Operation | Time, peak memory |
|---|---|---|
| FAT16, 32 MB, `mkfs.fat` + `mcopy`, 512-byte clusters | walk of a 20 MB file's chain (40,962 clusters) | 9.6 s, 395 MB (before: stack overflow) |
| | stream the 20 MB file (`Fat.open` / `Fat.next`, 40,962 pieces) | 28 s, 480 MB |
| | `Fat.read` of a whole 1 MB file | 6 s, 1.8 GB |
| | `Fat.read` of 100 KB; of the last 5,000 bytes of the 20 MB file | 0.9 s, 340 MB; 9.7 s, 370 MB |
| | list a directory of 3,000 long names (12,001 entries) | 1.7 s, 310 MB |
| FAT32, 40 MB, `mkfs.fat` + `mcopy`, 512-byte clusters | walk of a 30 MB file's chain (61,442 clusters) | 22 s, 456 MB |
| | stream the 30 MB file | 56 s, 494 MB |
| | list the root: 2,000 long names | 1.7 s, 316 MB |
| FAT12, 16 MB, 8 KB clusters | stream a 12 MB file; walk its 1,537 clusters | 24 s, 345 MB; 1.3 s |
| FAT16, 30 MB, `ref/gen.py`'s builder, fragmented chains | list a directory of 42,000 entries (40,000 8.3 and 2,000 long names, 1.4 MB) | 9.4 s, 748 MB |
| | find its last entry; walk a fragmented 40,962-cluster chain | 3.7 s; 12 s, 547 MB |

Before this round only the chain walk failed (the stack overflowed between
about 10,000 and 40,000 clusters); directory scans, streams, range reads and
cluster skips were already loops. Nothing in the package now recurses over a
file's size, a directory's entries or a chain's length; what is left:

* a range read (`Fat.read`) answers one `Octets`, so its length is bounded by
  memory: 1 MB takes about 1.8 GB. Stream large files with `Fat.open` /
  `Fat.next`, which hold one sector at a time;
* a listing (`Fat.list`) holds every entry it returns, about 15 KB each (the
  11-byte name is an `Octets`): the specification's largest directory, 65,536
  entries, would take about 1 GB. A path lookup (`Fat.stat`) stops at the
  entry it finds;
* every FAT entry is a block read (there is no cache), so a walk, a stream or
  a skip to an offset costs a read per cluster. A cache of FAT sectors would
  be the first speed-up.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (24 results, one a 50,000-cluster volume),
`ref/run.sh` 956 cases on 39 images match, `scripts/deps.sh` passes; all
re-run unchanged on blockdev's tree-backed `MemDev` (the reference test's
program still runs on the JavaScript lane: its native build is killed for
memory). Large
inputs: measured to 61,442-cluster chains, 30 MB files and 42,000-entry
directories (see Speed and size limits).
