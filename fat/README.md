# bend-osdev-fat

A FAT12, FAT16 and FAT32 file system that reads and writes, over
bend-osdev-blockdev's device interfaces.

* **Reading** (on blockdev's pure interface): mounting a volume (its boot
  sector checked, a named error for each failure), listing directories with
  their long (VFAT) names, finding a path case-insensitively, and reading a
  file's bytes as a range or a sector at a time.
* **Writing** (on blockdev's owned interface, where every operation hands
  the device back, so a device may be a single-owner `Array<U32>` image,
  `ImgDev`): formatting a volume (mkfs); creating files and directories
  with short names, long names and `~n` aliases; writing at any offset,
  appending and truncating, allocating clusters first fit from the FSInfo
  hint and keeping every FAT copy equal; deleting files and empty
  directories; renaming within and across directories; setting times and
  attributes; keeping FSInfo's free count and hint. Reading and listing work
  on the same device.

Writers for single on-disk records (a boot sector, a FAT entry, a directory
entry, a long name's entries) are also public, for building images and for
the round-trip laws.

## Specification

Microsoft Corporation, "Microsoft Extensible Firmware Initiative FAT32 File
System Specification: FAT: General Overview of On-Disk Format", version
1.03, December 6, 2000: section 3 (the boot sector and BPB; 3.5, FAT type
determination and the FATSz computation), section 4 (the FAT, its reserved
entries 0 and 1, mirroring and `BPB_ExtFlags`), section 5 (FSInfo), section
6 (directory entries, free entries, "." and "..", the volume label) and
section 7 (long directory entries, the characters of long names, the
short-name checksum, and the basis-name and numeric-tail generation
algorithms). No GPL source was read (no Linux `fs/fat`, no dosfstools or
mtools source); the reference test runs dosfstools and mtools as programs
only.

The FAT type is fixed by the count of clusters alone, as section 3.5 says
(fewer than 4085: FAT12; fewer than 65525: FAT16; otherwise FAT32), never by
the `BS_FilSysType` label.

Where the specification leaves a choice open, the package makes this one
(each is what `ref/wgen.py`'s model does too, and fsck.fat and mtools accept
the result):

* **Where a new name's entries go:** the first run of free entries long
  enough (an `0xE5` entry, or any entry from the first `0x00` one on) in
  directory order; a cluster-chain directory grows by zeroed clusters when
  no run fits; the FAT12/16 root cannot grow (`FatRootFull`); a directory
  holds at most 65536 entries (`FatDirFull`).
* **The numeric tail** is the smallest `n` from 1 whose short name no entry
  of the directory has (the specification only asks that it not collide;
  Windows switches to hashed tails after a few, which the package does not).
* **Names:** leading and trailing spaces and trailing periods are removed
  (section 7: "ignored"), in names being created and in paths. A name that
  is a valid 8.3 name in upper case gets a short entry only; one that is
  valid but has lower-case letters gets its 8.3 form plus a long name (the
  specification reserves `DIR_NTRes`), or, with `FatWOptions.nt_case`, a
  short entry alone with Windows NT's lower-case flags when its base and
  extension are each in one case. Characters outside ASCII become `_` in
  short names (no OEM code page is assumed).
* **Allocation** is first fit from the hint: the search starts at the hint
  and wraps from the last cluster to cluster 2. After an allocation the hint
  is the cluster after the last one taken (wrapped to 2 past the end of the
  volume); freeing leaves it. FSInfo's free count and hint are written
  after every operation that changed the FAT (FAT32, when FSInfo was valid
  when the volume was opened). A volume with FATs mirrored (always on
  FAT12/16; FAT32 with `BPB_ExtFlags` bit 7 clear) has every changed FAT
  sector written to every copy; otherwise only the active FAT is written.
* **Data:** writing past a file's end fills the gap with zeros, as does
  growing a file with `truncate`; shrinking frees the clusters after the
  new end and marks the last kept one the end of the chain. Writing sets
  the archive attribute and the write time and access date from the
  writer's clock (`FatW.set_clock`; the package has no clock of its own).
  Deleting writes `0xE5` into each of the name's entries; directories are
  never shrunk.
* **Renaming** onto a name that exists is refused (`FatExists`), unless it
  is the entry itself (a change of case); a directory moved to another
  directory has its ".." entry relinked (0 for the root, on FAT32 too). A
  directory cannot be moved into itself (`FatMoveIntoSelf`).
* **Read-only files** (`ATTR_READ_ONLY`) refuse writing, truncating and
  deleting (`FatReadOnly`), unless `FatWOptions.read_only` is false.
* **Format:** each FAT's size is the specification's FATSz computation
  (section 3.5) generalised to every entry width and sector size, with room
  for the two reserved entries:
  `FATSz = ceil((D + 2C) * b / (8 * S * C + b * N))` for data sectors `D`,
  `b` bits an entry, `S` bytes a sector, `C` sectors a cluster and `N`
  FATs; for FAT16 and FAT32 at 512 bytes a sector this is what mkfs.fat
  writes (checked on its images). The cluster size by default is the
  smallest power of 2 (a cluster at most 32 KB) that gives a count of
  clusters of the type asked for (Microsoft's tables choose larger clusters
  for large FAT32 volumes; pass `sectors_per_cluster` for that). Reserved
  sectors: 1 on FAT12/16, 32 on FAT32; root entries rounded up to whole
  sectors; FAT32's FSInfo at sector 1 (next free 3), its backup boot sector
  at 6 and the backup FSInfo at 7 (the places mkfs.fat uses, observed on
  its images); entry 0 holds the media byte, entry 1 and FAT32's root
  cluster the end-of-chain value; the reserved area, every FAT and the root
  directory are zeroed; a volume label entry is written unless the label is
  `NO NAME`. Boot code is zeros, the OEM name `MSWIN4.1`, the volume ID 0
  unless given. Cluster counts within 16 of a type boundary (which the
  specification suggests avoiding) are not avoided.
* **Crash safety** is out of scope: an operation's device writes (data,
  directory entries, then the FAT and FSInfo) are not ordered for
  consistency after a crash part way.

## Files

| File | Holds |
|---|---|
| `fat.bend` | the reader's entry concern: mounting a volume, and the operations by path (`Fat.stat`, `Fat.list`, `Fat.read`, `Fat.open` / `Fat.next`) |
| `error.bend` | `FatError`, one constructor per failure, and `FatError.show` |
| `bpb.bend` | the boot sector and BPB, the BS_ fields, the checks and the volume geometry they give, the FAT type, FSInfo, the reader's options; building a boot sector |
| `table.bend` | the FAT on the device: FAT12 and FAT32 packing, entry values, reading an entry, reading and writing entries of a FAT in memory, following a cluster chain with a bound; reading the device (`FatIo.read`) |
| `dirent.bend` | directory entries: the 32-byte short entry, 8.3 names, long-name entries (encode, decode, build, the checksum), UCS-2 names |
| `dir.bend` | directories: the scan (streaming, an entry at a time, with where each node's entries are), long names assembled and checked, listing, finding a name, resolving a path |
| `file.bend` | reading files: a cursor a sector at a time, and ranges |
| `io.bend` | the owned interface: `FatRun` (steps that thread the device), reading and writing any byte range |
| `map.bend` | the allocation table in memory: `FatMap`, first-fit allocation, extending, freeing and cutting chains, following a chain |
| `alias.bend` | names for new entries: checking a long name, the basis name, the numeric tail, what is stored (`FatAlias`) |
| `format.bend` | making a volume: the layout for a size and type, and writing it |
| `wdir.bend` | directories for writing: reading one with where its entries are and which are free, finding, placing a run of new entries, writing and erasing entries |
| `write.bend` | the writer: `FatW`, opening a volume for writing, the operations by path, and the flush of FAT sectors and FSInfo |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`PROOF.bend` is written by `gen/genproof.py`: `python3 fat/gen/genproof.py`) |
| `check.bend` | a runnable check: reading a FAT12 image built with the record writers, and a volume formatted, written and read back |
| `ref/gen.py`, `ref/harness.bend` | the reader's differential test (`gen.py` writes `ref/cases-NN.bend` and `ref/expected.txt`) |
| `ref/wgen.py`, `ref/wharness.bend` | the writer's differential test (`wgen.py` writes `ref/wcases.bend` and `ref/wexpected.txt`, and checks the images afterwards) |
| `ref/run.sh` | runs both; `ref/.gitignore` lists the generated files |

Bend imports do not re-export: import the file whose defs you use.

## The device interfaces

**Reading** takes blockdev's pure template arguments `~Dv: Data`,
`~block_size: Dv -> Nat`, `~read_block: Dv -> Nat -> Result<&2, &2,
DevError, Octets>` and a device `d`, and reads through `Dev.read_bytes`:
only the blocks it needs. The device's block size need not be the volume's
sector size. A device error is `FatDev{e}`. In the reader's tables below `T`
stands for the three template arguments, e.g. `~D.MemDev,
~D.MemDev.block_size, ~D.MemDev.read_block`. Its laws are statements about
a pure read's `Result`, so the reader stays on the pure interface,
unchanged.

**Writing** takes blockdev's owned template arguments `~Dv: Type`,
`~block_size: Dv -> Dv & Nat`, `~read_block: Dv -> Nat -> Dv & Result<&2,
&2, DevError, Octets>`, `~write_block: Dv -> Nat -> Octets -> Dv &
Result<&2, &2, DevError, Unit>` (`T4` below; `T3` without `write_block`)
and a device `d`; every operation answers the device and a result, `d &
Done{...}` or `d & Fail{why}`. blockdev's `ImgDev` (an `Array<U32>` image)
is such a device; a pure device such as `MemDev` is one through blockdev's
adapters (`MemDev.own_block_size`, `MemDev.own_read_block`,
`MemDev.own_write_block`). A byte range a block covers only in part is read,
changed and written back.

## API

The records below are open (their fields are part of the interface) except
`FatVolume`, `FatScan`, `FatCursor`, `FatMap`, `FatDirView` and `FatW`,
which are read through their defs.

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

### write.bend

| Def | Meaning |
|---|---|
| `FatWOptions{nt_case, from_hint, read_only}`, `FatWOptions.default()` | the writer's choices (see Extension points) |
| `FatClock{date, time, tenth}`, `FatClock.epoch()` | a moment as entries store it (`R.FatDate`, `R.FatTime`, tenths 0 to 199); 1980-01-01 00:00:00 |
| `FatTimes{create, write, access}` | an entry's times (`access` a date) |
| `FatW.open(T3, d, opts, wopts)` | a volume opened for writing: the boot sector checked as `Fat.mount` does, the active FAT read into a map, FSInfo's hint |
| `FatW.create(T4, d, w, path)`, `FatW.mkdir(T4, d, w, path)` | a new empty file, or a new directory (with "." and ".."); `FatExists`, `FatBadName`, `FatRootFull`, `FatDirFull`, `FatDiskFull`, `FatNoAlias` |
| `FatW.write(T4, d, w, path, off, data)`, `FatW.append(T4, d, w, path, data)` | data written at byte `off` (a gap past the end zeroed), or at the end; `FatIsADirectory`, `FatReadOnly`, `FatFileTooLarge` (past 4 GiB - 1), `FatDiskFull` |
| `FatW.truncate(T4, d, w, path, size)` | the file cut to `size` bytes (its clusters after freed), or grown with zeros |
| `FatW.unlink(T4, d, w, path)`, `FatW.rmdir(T4, d, w, path)` | a file deleted; an empty directory deleted (`FatNotEmpty`, `FatNotADirectory`, `FatIsRoot`) |
| `FatW.rename(T4, d, w, from, to)` | a file or directory moved and renamed (`FatExists`, `FatMoveIntoSelf`, `FatIsRoot`) |
| `FatW.set_times(T4, d, w, path, t)`, `FatW.set_attr(T4, d, w, path, a)` | an entry's times; its read-only, hidden, system and archive bits (the directory bit kept) |
| `FatW.stat(T3, d, w, path)`, `FatW.list(T3, d, w, path)`, `FatW.read(T3, d, w, path, off, len)` | as `Fat.stat`, `Fat.list` and `Fat.read`, on the same device |
| `FatW.fs`, `FatW.volume`, `FatW.kind`, `FatW.map`, `FatW.free_clusters`, `FatW.hint`, `FatW.clock`, `FatW.set_clock`, `FatW.wopts` | the state |
| `FatW.make`, `FatW.write.steps`, ... , `FatW.flush(T4, w)` | the same operations as `FatRun` steps, to compose sequences on one device; the flush (every changed FAT sector to each FAT copy, then FSInfo) |

Each operation answers the state after it; a failed operation (other than
a device error) has written nothing, and the caller keeps the state it had.

### format.bend

| Def | Meaning |
|---|---|
| `FatFormatOptions{bytes_per_sector, sectors_per_cluster, reserved, fats, root_entries, media, sectors_per_track, heads, hidden, drive, volume_id, label, oem, fs_info, backup_boot}`, `FatFormatOptions.default()` | the choices (512, 0 = smallest that fits, 0 = 1 or 32, 2, 512, 0xF8, 63, 255, 0, 0x80, 0, `NO NAME`, `MSWIN4.1`, 1, 6) |
| `FatLayout{kind, bpb, ext, clusters}` and its accessors | a volume's BPB, BS_ fields and count of clusters |
| `FatFormat.layout(t, tot, o)` | the layout of a volume of `tot` sectors of type `t`, checked with the reader's own checks (`FatFormatBadParam`; `FatFormatBadType{clusters}` when no allowed cluster size gives the type) |
| `FatFormat.format(T4, d, t, tot, o)`, `FatFormat.steps(T4, t, tot, o)` | the layout written to a device |

### map.bend

| Def | Meaning |
|---|---|
| `FatMap.of_list(t, xs)`, `FatMap.kind`, `FatMap.count`, `FatMap.entries` | the allocation table of type `t` with entries `xs` (from entry 0), each masked |
| `FatMap.get(m, n)`, `FatMap.set(m, n, v)`, `FatMap.mask(t, v)`, `FatMap.end(m)` | an entry (0 past the map); an entry set (masked to 12, 16 or 28 bits); the end-of-chain value |
| `FatMap.is_free(m, n)`, `FatMap.free_count(m)`, `FatMap.find(m, hint)`, `FatMap.wrap(m, c)` | a free cluster of the map (2 to count - 1, entry 0); the count of them; the first one from a hint, wrapping |
| `FatAlloc{map, clusters}`, `FatMap.alloc(m, hint, k)`, `FatMap.extend(m, last, hint, k)` | `k` clusters first fit from `hint`, as a new chain or linked after `last` (`FatDiskFull`) |
| `FatMap.free(cs, m)`, `FatMap.cut(m, c)` | clusters freed; a chain ended at `c` |
| `FatMap.chain(m, start)`, `FatMap.link_of(m, c)` | a chain's clusters (none from 0), with the reader's checks (`FatFreeInChain`, `FatBadInChain`, `FatBadCluster`, `FatChainLoop`) |
| `FatMap.member`, `FatMap.distinct`, `FatMap.all_free`, `FatMap.links` | what the laws state: a cluster in a list; no cluster twice; every cluster free; each cluster's entry the next, the last's the end of a chain |

### alias.bend

| Def | Meaning |
|---|---|
| `FatAlias.check(s)` | a path component as the name stored for it (trimmed), or `FatBadName` (empty, a character a long name cannot hold, more than 255 UCS-2 units) |
| `FatAlias{short, nt, long}`, `FatAlias.make(nt_case, name, taken)` | what is stored for a new name among entries whose short names are `taken`: the short name, the `DIR_NTRes` case flags, the long name's units (none when the short name shows it) |
| `FatBasis{base, ext, lossy}`, `FatAlias.basis(xs)`, `FatAlias.with_tail(base, ext, n)`, `FatAlias.taken(s, xs)` | the basis name of a name's code points; a short name with tail `~n`; whether a short name is taken |
| `FatAlias.trim`, `FatAlias.codes`, `FatAlias.text`, `FatAlias.long_char` | names as code points |

### wdir.bend

| Def | Meaning |
|---|---|
| `FatDirView.load(T3, opts, vol, map, dir)` | a directory read through `FatScan`, a sector at a time, with its sectors, its free entries and its end |
| `FatDirView.dir`, `fixed`, `clusters`, `sectors`, `slots`, `holes`, `end`, `nodes`, `spans` | its parts |
| `FatHit{node, span}`, `FatDirView.find(v, name)`, `FatDirView.taken(v)` | the node a name names and where its entries are; the short names in use |
| `FatDirView.place(v, k)`, `FatDirView.slot(ss, per, i)` | where a run of `k` new entries starts; the byte offset of entry `i` |
| `FatDirView.put(T4, es, ss, per, i)`, `FatDirView.erase(T4, n, ss, per, i)` | entries written from entry `i`; `n` entries erased |

### io.bend

| Def | Meaning |
|---|---|
| `FatRun<Dv, A>`, `FatRun.exec`, `FatRun.pure`, `FatRun.fail`, `FatRun.lift`, `FatRun.bind` | steps on an owned device (`do FatRun<Dv, A>:` blocks); running them on a device |
| `FatOIo.block_size`, `FatOIo.read_block`, `FatOIo.write_block` | the device's operations as steps |
| `FatOIo.read(T3, off, len)`, `FatOIo.write(T4, off, data)`, `FatOIo.zero(T4, off, len)`, `FatOIo.write_src(T4, off, src)` | a byte range read; written (partly covered blocks read, changed and written back); zeroed |
| `FatSrc`: `FatSrcBytes{data}`, `FatSrcZeros{len}`; `FatSrc.len`, `take`, `head`, `drop` | what a write puts down |

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
`FatNotFound`, `FatNotADirectory`, `FatIsADirectory`; writing's
`FatDiskFull`, `FatExists` (the name exists), `FatNotEmpty` (a directory
not empty), `FatBadName`, `FatRootFull` (the FAT12/16 root has no room),
`FatDirFull` (65536 entries), `FatNoAlias` (no numeric tail left),
`FatIsRoot`, `FatMoveIntoSelf`, `FatFileTooLarge`, `FatReadOnly`;
formatting's `FatFormatBadType{clusters}` and `FatFormatBadParam`.
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
| `FatTable.get_in(t, fat, n)`, `FatTable.set_in(t, fat, n, v)`, `FatTable.offset(t, n)`, `FatTable.width(t)` | the same on a FAT held in memory, and writing an entry there; where an entry is |
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
| `FatName.text(name)`, `FatName.short_of(s)`, `FatName.units(s)`, `FatName.text_of(us)`, `FatName.same(a, b)`, `FatName.upper`, `FatName.short_char` | 8.3 names as text; the 8.3 form of a path component (upper-cased; `None` if it cannot be one); text to UCS-2 units and back (surrogate pairs); comparing ignoring ASCII case; a character a short name may hold |
| `FatLfn{ord, units, chksum}`, `FatLfn.decode(o)`, `FatLfn.encode(e)`, `FatLfn.is_long(o)` | a long-name entry (13 units) |
| `FatLfn.checksum(short)`, `FatLfn.build(short, name)`, `FatLfn.carries(es, c)`, `FatLfn.cut(us)`, `FatLfn.count(n)` | the short name's checksum; a name's entries in stored order (writer); whether entries carry a checksum; a name's units before its 0x0000 |

### dir.bend

| Def | Meaning |
|---|---|
| `FatNode{long, entry}`, `FatNode.name`, `short_name`, `is_dir`, `size`, `cluster`, `long`, `entry` | an entry as listed: its long name (no units if none) and its short entry |
| `FatDir`: `FatDirRoot{}`, `FatDirAt{cluster}`; `FatDir.of_node(n)` | a directory |
| `FatDir.list(T, d, opts, vol, dir)`, `FatDir.find(T, d, opts, vol, dir, name)`, `FatDir.scan(T, d, opts, vol, dir, want)` | listing; the entry a name names (the scan stops there) |
| `FatWant`: `FatWantAll{}`, `FatWantName{units, short}`, `FatWant.name(s)`, `FatWant.matches(w, n)` | what a scan looks for |
| `FatScan.start(opts, want)`, `FatScan.feed(s, o)`, `FatScan.step(s, o)`, `FatScan.found(s)`, `FatScan.spans(s)`, `FatScan.ended(s)` | streaming: directory data in pieces of whole entries, from any source; the nodes found and where each one's entries are (`FatSpan{first, last}`: the index of its first entry and of its short entry) |
| `FatPath`: `FatPathRoot{}`, `FatPathNode{node}`; `FatPath.resolve(T, d, opts, vol, path)`, `FatPath.parts(s)`, `FatPath.dir(p)` | paths |

### file.bend

| Def | Meaning |
|---|---|
| `FatFile.open(vol, node)`, `FatFile.next(T, d, vol, cur)`, `FatChunk{data, rest}`, `FatChunk.data`, `FatChunk.rest` | streaming, a sector at a time |
| `FatFile.read(T, d, vol, node, off, len)` | a range |

## Extension points

* **Reader options** (`FatOptions`, defaults `FatOptions.default()`):
  `max_cluster_bytes` (32768: the specification's limit; `lenient()` takes
  65536, which some systems write) and `strict_names` (`True`: a long name
  out of sequence, or whose checksum does not match, makes the directory an
  error; `False`, as `lenient()`: such entries are ignored as orphans and
  the short name is used, the specification's own handling). The writer
  mounts with these too.
* **Writer options** (`FatWOptions`, defaults `FatWOptions.default()`):
  `nt_case` (`False`: names with lower case get long-name entries;
  `True`: Windows NT's `DIR_NTRes` flags where they suffice),
  `from_hint` (`True`: allocate first fit from FSInfo's hint, as
  section 5 suggests; `False`: from cluster 2) and `read_only` (`True`:
  read-only files refuse changes).
* **Format options** (`FatFormatOptions.default()`): every BPB choice, the
  cluster size (0: the smallest that fits), the label and volume ID, and
  FAT32's FSInfo and backup sectors.
* **The clock**: entries are stamped from `FatW.set_clock`, so a caller
  supplies the time from wherever it has one.
* **Any device**, through blockdev's pure interface (reading) or owned
  interface (writing); a partition is a device that wraps another with an
  offset (a natural blockdev extension). A file-backed device needs an `IO`
  twin of the owned interface (see blockdev's README); `FatRun` would take
  it unchanged in shape.
* **Streaming**: `FatScan` takes directory data from anywhere; a file is
  read a sector at a time (`Fat.open` / `Fat.next`) and written a piece at a
  time (`FatW.append`, or `FatW.write` at successive offsets), so no
  operation needs a whole file in memory.
* **The allocation table** (`FatMap`) is pure data with laws; a different
  policy (next fit, best fit) can be written over `FatMap.get` /
  `FatMap.set` and given the same laws.
* **Not covered yet**: the backup boot sector (`backup_boot`) is parsed but
  not used as a fallback, and is not rewritten after format; long names
  compare ignoring ASCII case only (not the full Unicode upper-case table
  Windows uses); OEM code pages for short names (bytes above 127 shown as
  the code points of the same value; characters outside ASCII become `_`
  in new short names); a file read follows its chain only as far as its
  size, so a loop within that length is not noticed there
  (`FatChain.walk` finds every loop); `DIR_FstClusHI` is joined into the
  first cluster on FAT12/16 too (the specification says it is 0 there; the
  writer writes 0); the writer does not update the parent directory's
  times; hashed numeric tails (Windows NT's after `~4`) are not used.
* `DIR_NTRes` bits 3 and 4 (Windows NT's lower-case base and extension) are
  applied when showing a short name; the specification reserves the field.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer), 78 laws.

**For every input** (31):

* reading's records: `FatDirent.decode(FatDirent.encode(d)) ==
  Done{FatDirent.norm(d)}` for every short entry (`dirent_round_trip`);
  `FatLfn.build`'s entries carry the short name's checksum, the check the
  directory reader makes (`lfn_carries_checksum`); FAT12 packing
  (`fat12_set_get`, and setting one entry leaves its neighbour sharing a
  byte, `fat12_even_keeps_odd`, `fat12_odd_keeps_even`); FAT32 packing
  (`fat32_set_get`, `fat32_keeps_reserved`); entry values read back
  (`entry_end`, `entry_bad`, `entry_free`, and `entry_next` under three
  hypotheses); `FatChain.walk` returns at most the volume's count of
  clusters, for every in-memory device, volume and start (`chain_bound`,
  proved on the structural reference walk and carried over by a lemma that
  it equals the loop for every device, fuel, cluster and link);
* **the allocation table** (map.bend), for every map, cluster, value, hint
  and count:
  * `map_get_set`, `map_get_set_other`: a read after a write gives the
    value masked to the type; a write changes no other entry;
  * `alloc_fresh`: every cluster an allocation takes was free;
    `alloc_distinct`: none twice; `alloc_count`: as many as asked;
  * `alloc_links`: they form a chain in the new map (each entry the next
    cluster, the last's the end of a chain): **allocated clusters are
    marked**;
  * `alloc_frame`: every other entry is unchanged; `alloc_keeps_used`:
    every cluster in use (entry not 0) keeps its entry, so with
    `alloc_fresh`, **no cluster belongs to two chains**: a chain already on
    the volume loses and gains nothing;
  * `extend_fresh`, `extend_distinct`, `extend_count`, `extend_links` (the
    chain's old last cluster and the new ones form a chain, when the old
    last is in use and at least one cluster is added), `extend_frame` and
    `extend_keeps_used` (every entry but those and the old last's);
  * `free_frees`: **every freed cluster is free**; `free_frame`: no other
    entry changes; `cut_ends`: a cut makes its cluster a chain's end;
* `alias_fresh`: the short name `FatAlias.make` stores for a new entry is
  never one of the directory's (for every name, list of names and option);
* `format_mounts`: every layout `FatFormat.layout` answers passes the
  reader's own checks (`FatVolume.of_bpb`) as a volume of the type asked
  for, with the count of clusters the layout gives (**format gives a volume
  that mounts**, at the level of its BPB).

These last two hold by construction: `FatAlias.make` checks a candidate
against the directory's names before it answers it, and `FatFormat.layout`
runs the reader's checks on its BPB before it answers it; the laws say that
no path through the code skips the check. That the tail chosen is the
smallest free one (`FatAlias.first_tail` starts the search there) is not a
law: the differential test holds it to the model's search from 1.

The allocation laws are proved through two phases that are the code's own:
the first takes each cluster as it finds it and marks it the end of a chain
at once (so a later search cannot find it again; the proof follows the map
as an overlay of end marks over the original, by an invariant on the
clusters taken), the second links them; the tree's read-after-write laws
are proved for every tree (a write to a place the tree lacks adds a node).

**Witnesses and vectors** (47): every law with a hypothesis has a witness
(`entry_next_witness_*`; `w_ne`, `w_alloc_miss`, `w_used`,
`w_extend_used`, `w_extend_pos`, `w_extend_miss`, `w_extend_other`,
`w_free_hit`, `w_free_miss`), and the laws that hold vacuously when an
operation fails have vectors where it succeeds (`v_alloc`, `v_alloc_map`,
`v_alloc_hint`, `v_extend_map`, `v_free`, `v_alias_*`, `v_format12`: a
64-sector FAT12 layout of 61 clusters); `v_alloc_full` is a disk-full
refusal. The reader's vectors: the FAT type at 4084, 4085, 65524 and 65525
clusters; the checksum of `BOOTX64 EFI`; a hand-built entry's cluster,
size, date, time and a short read refused; a long name's two entries and an
entry's round trip; 8.3 forms of path components; FAT12 packing on known
bytes; a short name with the NT lower-case flags. New short names: a tail,
the next tail when the first is taken, an 8.3 name stored alone, a lower
case one with its long name, the NT flags, and a lossy name (`a+b=c` is
`A_B_C~1`).

The proofs use bytes' interface laws (`octets_to_of`, `octets_of_to`),
never the inside of `Octets`, and split only `U32`s into bits.

**Covered by tests, not laws**: that a file reads back what was written,
that creating or deleting one file leaves every other file and the listing
otherwise unchanged, that the FAT copies stay equal on the device, and that
a formatted device mounts (the device-level statements, through directory
scans and the device's reads and writes). The reference test checks each on
every operation of its random sequences (see Tests): every image the
package writes is byte for byte the model's, fsck.fat compares the FAT
copies and the chains, and mtools lists and reads back every file. The law
`chain_bound` is stated for `MemDev`; its proof does not depend on the
device, but a law cannot quantify over template arguments.

## Tests

`check.bend` (68 results): 24 on reading (a FAT12 volume built with the
record writers: mounting, listings, case-insensitive paths through long and
short names, ranges across a cluster boundary, the pieces of a streamed
file, a chain walk, lookups that fail, a loop, a free cluster and an early
end in a chain, an out-of-range cluster, a bad BPB; and a FAT16 volume of
50,000 clusters made up as it is read, whose 25.6 MB file's chain is walked
and 100 KB of it read near its end), and 44 on writing: a 720-sector FAT12
volume formatted on an `ImgDev`, then directories, files with long names,
writes past a gap, appends, a duplicate name, a bad name, a write to a
directory, renames across directories and into itself, a truncation, a
read-only file refused, a non-empty directory refused, deletions, a file
grown until the disk is full; the image then read by the reader (through
`ImgDev.freeze`); a FAT32 format the size cannot hold; and FAT16 formatted
and written on a `MemDev` through blockdev's adapters, read back by the
reader.

`ref/run.sh` runs two differential tests (CI needs the apt packages
`dosfstools mtools`; run.sh exits 77 without them):

**Reading**, 956 results on 39 images (`ref/gen.py`, unchanged from before
but for its output: each image is written to a file, which the case files
load a non-zero block at a time, and its operations go in `cases-NN.bend`
files of at most 120 operations, in helper defs of at most 40, so every
file builds natively; 8 files):

* 8 images from `gen.py`'s builder (written from the specification by the
  same author as the package, so not independent of its reading of the
  specification): FAT12, FAT16 and FAT32 at 512 to 4096 bytes per sector and
  1 to 4 sectors per cluster, at the type boundaries (4084, 4085 and 65525
  clusters), random trees with short names, long names (Unicode, a surrogate
  pair, exactly 13 and 26 units, names needing `~n` short names), lower-case
  8.3 names, empty files, files of whole clusters, fragmented chains, a
  directory spanning clusters, a volume label; each checked by `fsck.fat -n`
  (dosfstools) and against the builder's record of the tree;
* 26 corrupted copies: 15 boot sectors, 6 chains, a directory whose chain
  loops, and 4 long names, each listed strictly (refused) and leniently;
* 5 images made by `mkfs.fat` and filled by `mmd` and `mcopy` (mtools),
  checked against their source trees and `mdir`'s listing.

**Writing**, 1537 results in 11 cases (`ref/wgen.py`; one program,
`wcases.bend`, since building the writer natively takes about half a minute
of the C compiler, every def in it holding at most 40 operations), each a
random sequence of operations run through the package on an `ImgDev` and on
an independent model, `wgen.py`'s `Model`, a FAT writer written here from
the specification on a bytearray (by the package's author, so not
independent of its reading of the specification):

* volumes formatted by the package: FAT12 (a 1.44 MB floppy; 800 sectors
  with a 16-entry root, filled until it is full, with the NT case flags; 4096
  bytes a sector), FAT16 (20,000 sectors; 2048 bytes a sector with one FAT;
  a fragmented directory of 30 files, every other one deleted, then a
  40 KB file across the holes), FAT32 (70,000 sectors, 20 KB writes), a
  small FAT12 volume written until the disk is full, and formats that
  cannot be made;
* volumes made by `mkfs.fat` and filled by `mmd` and `mcopy` (FAT12,
  FAT16 with 4 sectors a cluster and allocation from cluster 2, FAT32),
  updated by the package;
* operations: creating files and directories (short names, long names,
  names needing tails and colliding, lower case, Unicode, names with
  characters short names cannot hold, invalid names), writing at random
  offsets (gaps past the end), appending, truncating both ways, deleting,
  removing empty and non-empty directories, renaming within and across
  directories and into itself, setting times and attributes (read-only
  files then refused), listings (name, size, short name, attributes, first
  cluster), reads (length and hash), lookups through flipped case and
  short names, and operations on the root; 14 kinds of error come up.

Every line must match the model's. Then `wgen.py check` puts the blocks
the package wrote back into each image and checks (173 checks): the image
is **byte for byte the model's** (11 images); `fsck.fat -n` accepts it
(10); `mdir` lists exactly the model's tree (10); `mtype` reads back every
file the model has, with its length and hash (132); `gen.py`'s reader reads
the model's tree from it (10).

## Speed and size limits

Measured natively (Bend 2.0.37, WSL2, `bend file.bend -o prog`), not in
CI.

| Run | Time, peak memory |
|---|---|
| `FatFormat.format`: FAT32, 70,000 sectors (35 MB) on an `ImgDev` | 0.12 s, 68 MB (the image itself is 35 MB) |
| format, `FatW.open` (a 68,892-entry FAT32 map), 160 appends of 512 bytes | 0.39 s, 74 MB |
| a 10 MB file written in 160 appends of 64 KB (FAT32, 512-byte clusters: 20,480 clusters) | 3.0 s, 76 MB |
| the same 10 MB in one `FatW.write` | 3.9 s, 404 MB (most of it the 10 MB `Octets`) |
| the 10 MB file read back in 160 `FatW.read` ranges of 64 KB | 2.1 s, 79 MB |
| 300 files whose names share one basis (`File number N.txt`: `FILENU~1` to `FILENU~300`) created in one directory | 7.5 s, 26 MB (25 ms each by the end) |
| 2,000 8.3 files created in one directory (which grows to 64 KB) | 92 s, 28 MB (46 ms each by the end) |
| `check.bend` (68 results) | 0.83 s, 49 MB (its native build about 40 s) |
| `ref/run.sh` (both differential tests, builds included) | 120 s, 1.2 GB (most of it building the 8 reading programs, about 8 s each, and the writing program, about 40 s, whose C compile peaks at 1.2 GB) |

An operation on a directory reads that directory (about 23 µs an entry,
most of it the bit-sliced field readers of `dirent.bend`), so operations in
a directory of thousands of entries take tens of milliseconds each. The
first `~n` tail tried is the smallest no taken name has (one pass over the
directory's short names), so names sharing a basis cost no more than
others. Each write or append follows the file's chain in the map from its
start (no cursor is kept between operations), a few microseconds a cluster.

The writer holds the FAT in memory as a balanced tree, read once by
`FatW.open` (with it, a 35 MB FAT32 image of 68,890 clusters peaks at 74 MB
in all); an operation reads only the directories on its path and the
clusters it writes, and writes back only the FAT sectors it changed (to
each copy) and FSInfo. A directory being changed is read whole into a
`FatDirView` (its nodes held as `FatNode`s, as a listing holds them).
Generating a `~n` tail costs a pass over the directory's short names for
each name, to find the first tail free (Windows' hashed tails, which
change the short names chosen, are not implemented).

The reader's figures, measured earlier on bend's JavaScript lane (which
uses several times the memory of a native build):

| Image | Operation | Time, peak memory |
|---|---|---|
| FAT16, 32 MB, `mkfs.fat` + `mcopy`, 512-byte clusters | walk of a 20 MB file's chain (40,962 clusters) | 9.6 s, 395 MB |
| | stream the 20 MB file (`Fat.open` / `Fat.next`, 40,962 pieces) | 28 s, 480 MB |
| | `Fat.read` of a whole 1 MB file | 6 s, 1.8 GB |
| | list a directory of 3,000 long names (12,001 entries) | 1.7 s, 310 MB |
| FAT32, 40 MB, `mkfs.fat` + `mcopy`, 512-byte clusters | walk of a 30 MB file's chain (61,442 clusters) | 22 s, 456 MB |
| | stream the 30 MB file | 56 s, 494 MB |
| FAT16, 30 MB, `ref/gen.py`'s builder | list a directory of 42,000 entries | 9.4 s, 748 MB |

Nothing in the package recurses over a file's size, a directory's entries
or a chain's length. A range read (`Fat.read`, `FatW.read`) answers one
`Octets` (about 150 bytes of memory a byte held): read large files a piece
at a time. A listing holds every entry it returns. Every FAT entry the
reader follows is a block read (there is no cache); the writer follows
chains in its map.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (78 laws: 31 for every input,
47 witnesses and vectors), `--verdict` ALL PROOFS CHECK, `check.bend`
passes (68 results), `ref/run.sh` matches (reading: 956 cases on 39 images
in 8 case files, each built natively; writing: 1537 results in 11 cases
against the model, and 173 image checks: every image byte for byte the
model's, accepted by `fsck.fat -n`, listed by `mdir` and read back by
`mtype`), `scripts/deps.sh fat` ok; `VERDICT=1` package check (native)
passes with no JavaScript-lane program. Large inputs: measured to 10 MB
files on a 35 MB FAT32 volume and 2,000-entry directories (see Speed and
size limits).
