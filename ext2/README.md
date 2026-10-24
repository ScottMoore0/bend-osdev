# bend-osdev-ext2

A reader and writer of ext2, ext3 and ext4 filesystems over blockdev's device
interface. Reading: the superblock and its checks, block group descriptors,
inodes, file data through the classic block map and through extent trees,
directories, path lookup and symbolic links, and the metadata checksums of
ext4. Writing: mkfs (revision 1, an ext2 and an ext4 profile), allocation
through the bitmaps with the descriptors' and superblock's free counts kept
in step, files, directories, fast and slow symbolic links, hard links,
unlink, rmdir, rename, writes, appends and truncation through the block map
or extents, directory entries split and merged, the metadata checksums
updated; every operation checked before it answers (a whole-filesystem
check, `Ext2Fsck.full`, is there too).

Specifications:

* "The Second Extended File System: Internal Layout", Dave Poirier
  (nongnu.org; GNU FDL documentation): the superblock, block groups, inodes,
  the block map, directories;
* the ext4 disk-layout documentation (kernel.org,
  Documentation/filesystems/ext4): 64-bit fields and descriptors, the feature
  flags, meta_bg, flex_bg, extent trees, checksums (crc32c seeds, the
  directory and extent block tails), htree directories.

Both are documentation; the package was written from them only. No Linux
kernel code and no e2fsprogs source was read. The e2fsprogs tools (mke2fs,
debugfs, e2fsck, dumpe2fs, tune2fs) are used as black boxes by the
differential tests.

## What it reads

| | |
|---|---|
| Revisions | 0 (original) and 1 (dynamic) |
| Block sizes | 1 KiB to 64 KiB |
| Incompat features read | filetype, meta_bg, extent, 64bit, mmp, flex_bg, ea_inode, metadata_csum_seed, large_dir |
| Refused, named | compression, journal_dev, dirdata, inline_data, encrypt, casefold, and any unknown bit (`Ext2Unsupported{"inline_data"}`, ...); needs_recovery (`Ext2NeedsRecovery`) unless the options allow it |
| ro_compat features | ignored, as a read-only reader may, except the two checksum ones |
| Checksums verified | metadata_csum: superblock, group descriptors, inodes, extent tree blocks, directory leaf blocks; gdt_csum (crc16): group descriptors |
| File data | twelve direct, singly, doubly and triply indirect blocks; extent trees to the depth bound; holes and unwritten extents read as zeros |
| Directories | linear entries, validated; htree directories read linearly |
| Symbolic links | fast (in i_block) and slow; reported, or followed up to a bound |

Not read: inline data, extended attributes, the journal (no replay), the
bitmaps (a reader never needs them, so their checksums are not verified),
and the checksums of htree index blocks (their entries are read linearly; the
leaf blocks' checksums are verified). The writer below reads and writes
the bitmaps and their checksums.

Block numbers and sizes are `Nat`, at most 48 bits (ext4's own limit, and the
largest immediate `Nat` of Bend 2.0.37); a 64-bit field's high half beyond
that is ignored rather than overflow. Sizes in records are `W64`.

## What it writes

| | |
|---|---|
| Operations | create (regular files), mkdir (`.`, `..`, the parent's link), symlink (fast up to 59 bytes, slow beyond), link (hard links to files), unlink (the inode and its blocks freed with the last link), rmdir (empty directories only), rename (files and directories, over an existing file or empty directory; a directory never into itself), write at an offset (holes left as holes, a block written only where data goes), append, truncate (shorter: blocks freed; longer: a hole) |
| Features written | filetype, meta_bg, extent, 64bit, flex_bg, metadata_csum_seed, large_dir (incompat); sparse_super, large_file, huge_file, gdt_csum, dir_nlink, extra_isize, metadata_csum (ro_compat); the compat ones (a journal is left as it is). Anything else is refused before anything is written: `Ext2CannotWrite{why}` names it |
| Checksums | metadata_csum: superblock, descriptors, both bitmaps, inodes, extent blocks, directory leaf blocks (their tails); gdt_csum's crc16; or, with `Ext2CsumRefuse`, a filesystem that has them is refused |
| File data | the block map (direct, singly, doubly, triply indirect blocks, allocated as needed, freed when empty) on any filesystem; extents (depth 0, or depth 1 with up to four leaves: 336 extents with 1 KiB blocks, 1360 with 4 KiB) where the filesystem has them and the options ask (`extents`, default on) |
| mkfs | revision 1; ext2 profile: sparse_super, filetype, large_file (1 KiB blocks, 256-byte inodes); ext4 profile: also extent, 64bit, metadata_csum, dir_nlink, extra_isize (4 KiB blocks); any block size from 1 to 32 KiB, inode size, inode ratio, blocks per group, reserved percentage, UUID, label and time as options; the root (`/`, links 3) and `lost+found` |
| Refused, named | htree (indexed) directories (`Ext2HtreeDir`: entries go into a linear directory only; the index would go stale), an inode with an extended attribute block on release (`Ext2Xattr`), extent trees deeper than 1 or past four leaves (`Ext2ExtentFull`), a write into an unwritten extent (`Ext2Unwritten`), a block past the triply indirect block (`Ext2FileTooBig`), a file of 2 GiB or more without large_file, a 65,000th link (`Ext2TooManyLinks`), names with "/" or NUL or over 255 bytes (`Ext2BadName`), 64 KiB blocks (rec_len cannot hold them), a filesystem marked as having errors |

Not written: the journal (a filesystem with one is written around it: its
inode and blocks are left alone; bend-osdev-ext4's `jext2.bend` runs this
writer, unchanged, through the journal, logging, committing and
checkpointing each operation's writes as a jbd2 transaction), htree indexes,
extended attributes, inline data, flex_bg's packing at mkfs (an opened
filesystem with flex_bg is written correctly, its bitmaps and tables
wherever they are), resize_inode, uninit_bg's lazy groups at mkfs (all
groups are initialised; uninit groups of an opened filesystem are
initialised as they are first used), quota, orphan lists.

Every operation is all or nothing: it answers the device after it, or why
it was refused (`Ext2Error`), and a refused operation hands back no device,
so the caller's is as it was. Times, owner and the allocation policy come
from the options; a write takes the time it is given (no clock is read).

## Files

| File | Holds |
|---|---|
| `ext2.bend` | the entry: opening a filesystem; paths: lookup, listing, reading, symbolic links |
| `super.bend` | the superblock: its fields, feature bits, validation; `Ext2Fs`, the mounted filesystem and its geometry |
| `group.bend` | block group descriptors (32 and 64 bytes), where they are (meta_bg too), superblock backups |
| `inode.bend` | inode numbers and locations, the inode record, file types, reading an inode |
| `blockmap.bend` | the ext2/ext3 block map (direct and indirect blocks) |
| `extent.bend` | ext4 extent trees |
| `file.bend` | file data: by block, streamed, by byte range; symbolic link targets |
| `dir.bend` | directory entries (codec and checks), directory blocks, name lookup |
| `csum.bend` | the checksums (crc32c and crc16 from bend-osdev-crc) |
| `options.bend` | `Ext2Options` and its default |
| `error.bend` | `Ext2Error` |
| `field.bend` | internal: little-endian field reads of records of known length |
| `wopts.bend` | writing: `Ext2WriteOptions` (allocation policy, checksums, the check after each operation, extents, time, owner) and their defaults |
| `run.bend` | writing, the entry: `Ext2Op.run`, an operation checked before it answers (`Ext2Guard`: what each operation promises) |
| `ops.bend` | writing: the operations on paths (`Ext2W.create`, `mkdir`, `symlink`, `link`, `unlink`, `rmdir`, `rename`, `write`, `append`, `truncate`), `Ext2Op`, which filesystems may be written |
| `mkfs.bend` | writing: making a filesystem (`Ext2Mkfs.make`), its options and geometry |
| `fsck.bend` | writing: the checks, `Ext2Fsck.counts` (bitmaps against free counts) and `Ext2Fsck.full` (ownership, bitmaps, the tree, link counts) |
| `meta.bend` | writing: device writes, the superblock, descriptors and bitmaps written with their checksums and counts, `Ext2Out` |
| `alloc.bend` | writing: inode and block allocation and freeing through the bitmaps, by the options' policy |
| `bitmap.bend`, `patch.bend` | writing: bit operations on bitmaps; little-endian field patches of records |
| `inodew.bend` | writing: inode records (fields, a fresh inode, the checksum) |
| `mapw.bend`, `extentw.bend`, `filew.bend` | writing: the block map (set, truncate), extent lists and trees (insert, cut, store), file data (write, truncate) |
| `dirw.bend` | writing: directory blocks as slots (insert splitting a record, remove merging one), entries added, removed, retargeted |
| `sample.bend` | test fixture (not interface): the small image `check.bend` reads, written by `ref/sample.py` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | a runnable check: the sample image read, volumes made by mkfs written |
| `ref/` | the differential tests against e2fsprogs: reading (`gen.py`) and writing (`wgen.py`) |

Bend imports do not re-export: import the file that holds what you use.

## API

Every reading function takes the device as blockdev's template arguments
`~D`, `~block_size`, `~read_block` and the device `d`, then the filesystem
`fs`, and answers `Result<&2, &2, Ext2Error, A>`. Below, `(dev)` stands for
those four arguments. Only the blocks an operation needs are read: a lookup
reads the descriptors, inodes and directory blocks on its path.

```
import ../blockdev/blockdev.bend as D
import ./options.bend as O
import ./ext2.bend as X

X.Ext2.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dev, O.Ext2Options.default())
X.Ext2.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dev, fs, B.Octets.of_string("/etc/passwd"))
```

### ext2.bend

| Def | Meaning |
|---|---|
| `Ext2.open(dev, opts)` | the filesystem: the superblock read and checked |
| `Ext2.lookup(dev, fs, path)` | the inode a path (an `Octets`, "/"-separated) names; symbolic links followed as the options allow (none by default: a link inside a path is `Ext2SymlinkInPath`, a link at the end is answered itself); `Ext2NotFound`, `Ext2NotDir`, `Ext2SymlinkLoop` |
| `Ext2.lookup_link(dev, fs, path)` | the same, a final link never followed (lstat) |
| `Ext2.list(dev, fs, path)` | the used entries of a directory |
| `Ext2.read(dev, fs, path)` | a whole (small) file |
| `Ext2.readlink(dev, fs, path)` | a symbolic link's target |
| `Ext2.root(dev, fs)`, `Ext2.root_ino()` | the root directory (inode 2) |
| `Ext2Path.components(o)` | a path's components |

### super.bend

| Def | Meaning |
|---|---|
| `Ext2Super{...}` | the superblock's fields (open record): counts (`blocks_count`, `r_blocks_count`, `free_blocks_count` as `W64`), geometry, magic, state, revision, features, `uuid` (bend-osdev-uuid's `Uuid`), volume name, descriptor size, first meta group, checksum type, seed and value, ... |
| `Ext2Super.parse(o)` | the fields of 1024 bytes, unchecked |
| `Ext2Super.read(dev)` | the 1024 bytes at byte 1024 of a device |
| `Ext2Super.block_size`, `block_count`, `inode_size`, `first_ino`, `desc_size`, `group_count`, `label`, `seed`, `csum_kind`, `has_compat`, `has_incompat`, `has_ro_compat`, the accessors | derived values (revision 0 defaults; the 64bit feature's halves) |
| `Ext2Super.incompat_*`, `ro_compat_*`, `compat_*`, `incompat_name(bit)` | feature bits and their e2fsprogs names |
| `Ext2Fs.mount(opts, raw)` | the filesystem a superblock describes, checked: `Ext2BadMagic`, `Ext2BadRevision`, `Ext2BadBlockSize`, `Ext2Unsupported{name}`, `Ext2NeedsRecovery`, `Ext2BadChecksumType`, `Ext2BadSuperCsum`, `Ext2BadInodeSize`, `Ext2BadDescSize`, `Ext2BadGeometry{why}` |
| `Ext2Fs.open(dev, opts)` | read and mount |
| `Ext2Fs` (opaque), `Ext2Fs.sb`, `opts`, `block_size`, `blocks`, `groups`, `desc_size`, `inode_size`, `inodes_per_group`, `inodes_count`, `seed`, `csum`, `verify_meta` | the mounted filesystem |
| `Ext2Fs.read_block(dev, fs, n)` | filesystem block `n` |
| `Ext2Fs.with_symlink_hops(fs, h)` | the same filesystem, following up to `h` links |
| `Ext2CsumKind` | `Ext2CsumNone`, `Ext2CsumGdt`, `Ext2CsumMeta` |

### group.bend

| Def | Meaning |
|---|---|
| `Ext2Group{block_bitmap, inode_bitmap, inode_table, free_blocks, free_inodes, used_dirs, flags, itable_unused, checksum}` | a descriptor (open record) |
| `Ext2Group.parse(wide, o)` | its fields (`wide`: 64-byte descriptors) |
| `Ext2Group.read(dev, fs, g)` | descriptor `g`, checksum verified; `Ext2BadGroup`, `Ext2BadGroupCsum` |
| `Ext2Group.desc_loc(fs, g)`, `Ext2DescLoc{block, offset}` | where descriptor `g` is (meta_bg too) |
| `Ext2Group.has_super(fs, g)`, `Ext2Group.first_block(fs, g)` | superblock backups (sparse_super, sparse_super2), a group's first block |

### inode.bend

| Def | Meaning |
|---|---|
| `Ext2Inode.locate(ipg, n)`, `Ext2Inode.number(ipg, loc)`, `Ext2InodeLoc{group, index}` | inode numbers and (group, index) pairs |
| `Ext2Inode{number, mode, uid, gid, size, atime, ctime, mtime, dtime, links, blocks, flags, generation, file_acl, block, extra_isize, checksum}` | an inode (open record; `size`, `blocks`, `file_acl` are `W64`, `block` the 60 bytes of i_block) |
| accessors (`Ext2Inode.number_of`, `mode`, `size`, `size_nat`, `flags`, `block`, ...), `has_flag`, `flag_extents`, `flag_index`, `flag_inline_data`, `flag_huge_file` | |
| `Ext2Kind` (`Ext2Regular`, `Ext2Directory`, `Ext2Symlink`, `Ext2CharDev`, `Ext2BlockDev`, `Ext2Fifo`, `Ext2Socket`, `Ext2Unknown{mode}`), `Ext2Inode.kind`, `Ext2Kind.show`, `is_dir`, `is_symlink` | file types |
| `Ext2Inode.parse(n, isz, raw)` | an inode record's fields |
| `Ext2Inode.read(dev, fs, n)` | inode `n`, checksum verified; `Ext2BadInodeNumber`, `Ext2BadInodeCsum` |

### file.bend

| Def | Meaning |
|---|---|
| `Ext2File.map(dev, fs, i, l)` | the block holding logical block `l`: `Some{block}`, or `None` for a hole; `Ext2PastEnd` past the size; `Ext2InlineData` |
| `Ext2File.blocks_needed(fs, i)` | the blocks the size needs |
| `Ext2File.read_block(dev, fs, i, l)` | the bytes of logical block `l` (the last cut at the size; holes as zeros) |
| `Ext2File.start(i)`, `Ext2File.next(dev, fs, r)`, `Ext2Reader{inode, next}`, `Ext2Chunk` (`Ext2Piece{data, rest}`, `Ext2Eof`) | streaming, a block at a time |
| `Ext2File.read_range(dev, fs, i, off, len)` | bytes from `off`, never past the size; reads only the blocks the range covers |
| `Ext2File.read_all(dev, fs, i)` | the whole file (an `Octets` holds about 100 bytes of memory per byte natively: stream anything over a few megabytes; see Speed and size) |
| `Ext2File.readlink(dev, fs, i)`, `Ext2File.is_fast_symlink(fs, i)` | link targets; `Ext2NotSymlink` |

### blockmap.bend and extent.bend

| Def | Meaning |
|---|---|
| `Ext2Map.map(dev, fs, ino, iblock, l)` | logical block `l` through the block map; `Ext2BadBlockRef` for a pointer outside the filesystem |
| `Ext2Map.path(l, per)`, `Ext2MapPath{slot, levels, index}` | where `l` is: the i_block slot, the indirect levels, the index |
| `Ext2Map.check`, `check_some`, `final`, `inside` | the bounds checks every answer passes |
| `Ext2Extent.map(dev, fs, ino, gen, iblock, l)` | logical block `l` through an extent tree; `Ext2BadExtentMagic`, `Ext2BadExtentHeader`, `Ext2ExtentTooDeep`, `Ext2BadExtentDepth`, `Ext2BadExtentCsum`, `Ext2BadBlockRef` |
| `Ext2Extent.root_depth`, `Ext2ExtentHeader`, `Ext2Extent{block, len, start, written}`, `Ext2ExtentIndex{block, leaf}` and their `parse` | the tree's records |

### dir.bend

| Def | Meaning |
|---|---|
| `Ext2Dirent{inode, rec_len, name_len, file_type, name}` | an entry (open record) |
| `Ext2Dirent.encode(e)`, `Ext2Dirent.decode(filetype, o)` | the codec (`filetype`: the filetype feature's layout, else a 16-bit name_len) |
| `Ext2Dirent.norm(e)`, `Ext2Dirent.min_rec_len(n)` | an entry as stored; the shortest rec_len for a name of `n` bytes |
| `Ext2Dirent.check(e, avail, inodes)` | why an entry is malformed, if it is: rec_len a multiple of 4, long enough, within the block; the inode number in range; a used entry has a name |
| `Ext2Dir.block(dev, fs, i, k)` | the used entries of directory block `k` (a directory a block at a time), its checksum tail verified; `Ext2BadDirent{ino, offset, why}`, `Ext2BadDirCsum`, `Ext2NoDirTail` |
| `Ext2Dir.entries(dev, fs, i)`, `Ext2Dir.find(dev, fs, i, name)` | all entries; one by name (reads blocks up to the one that holds it) |

### csum.bend, options.bend, error.bend

| Def | Meaning |
|---|---|
| `Ext2Csum.crc32c(c, o)`, `Ext2Csum.crc16(c, o)` | the raw registers ext4 chains |
| `Ext2Csum.seed(uuid)`, `inode_seed(seed, ino, gen)`, `super(sb)`, `group(seed, g, desc, size)`, `group16(uuid, g, desc, size)`, `inode(iseed, raw, size, hi_fits)`, `extent_block(iseed, blk, max)`, `dir_block(iseed, blk, bs)` | each structure's checksum |
| `Ext2Options{incompat, verify, allow_recovery, symlink_hops, max_depth}`, `Ext2Options.default()`, `with_verify`, `with_incompat`, `with_recovery`, `with_symlink_hops`, `with_max_depth`, accessors | the options (default: every feature above, checksums verified, no recovery, links not followed, depth 5) |
| `Ext2Options.all_incompat()`, `Ext2Options.ext2_incompat()` | feature sets: everything this package reads; plain ext2 (filetype only) |
| `Ext2Error`, `Ext2Error.show`, `Ext2Error.kind` | one constructor per failure; a message; the constructor's name |

### Writing

Every writing function takes the device as blockdev's pure interface plus a
pure write, `~D`, `~block_size`, `~read_block`, `~write_block` (`D -> Nat ->
Octets -> Result<&2, &2, DevError, D>`), and the device `d`; below, `(wdev)`
stands for those five. On a `MemDev` the write is `Ext2Dev.mem_write`
(meta.bend), `MemDev.write_block` with plain parameters. The filesystem
`fs` is the one `Ext2.open` answered, and stays valid across writes: the
writer reads the superblock's counts, the descriptors and the bitmaps from
the device each time.

```
import ../blockdev/blockdev.bend as D
import ./meta.bend as T
import ./mkfs.bend as MK
import ./ops.bend as P
import ./run.bend as RN
import ./wopts.bend as WO

MK.Ext2Mkfs.make(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, D.MemDev.blank(4096n, 2048n), MK.Ext2MkfsOptions.ext4(2048n, uuid))
RN.Ext2Op.run(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~T.Ext2Dev.mem_write, P.Ext2OpWrite{B.Octets.of_string("/f"), 0n, data}, dev, fs, WO.Ext2WriteOptions.default())
```

| Def | Meaning |
|---|---|
| `Ext2Op` (`Ext2OpCreate{path, mode}`, `Ext2OpMkdir{path, mode}`, `Ext2OpSymlink{path, target}`, `Ext2OpLink{target, path}`, `Ext2OpUnlink{path}`, `Ext2OpRmdir{path}`, `Ext2OpRename{from, to}`, `Ext2OpWrite{path, off, data}`, `Ext2OpAppend{path, data}`, `Ext2OpTruncate{path, size}`) (ops.bend) | the operations; `mode` is the permission bits |
| `Ext2Op.run(wdev, op, d, fs, wo)` (run.bend) | the operation done and then checked as the options ask (`Ext2CheckLocal` by default: the counts and the operation's promise; `Ext2CheckFull`: also `Ext2Fsck.full`); the device after it, or why not (`Ext2CheckFailed{what}` if the check fails; the caller's device is as it was) |
| `Ext2Op.apply(wdev, op, d, fs, wo)`; `Ext2W.create`, `mkdir`, `symlink`, `link`, `unlink`, `rmdir`, `rename`, `write`, `append`, `truncate` (wdev, d, fs, wo, ...) (ops.bend) | the same, unchecked |
| `Ext2W.writable(fs, wo)` | whether this writer may write the filesystem (the features above, checksums, error state, block size): `Ext2CannotWrite{why}` |
| `Ext2Guard.promise(op, d, d2, fs)`, `post(level, op, d, d2, fs)` (run.bend) | what each operation promises (the data read back, the entry there or gone, the other entries kept, a size), and the check a level runs |
| `Ext2WriteOptions{alloc, csum, check, extents, time, uid, gid}`, `.default()`, `with_alloc`, `with_csum`, `with_check`, `with_extents`, `with_time`, `with_owner`, accessors (wopts.bend) | the options (default: the default policy, checksums updated, the local check, extents where the filesystem has them, time 0, owner 0:0) |
| `Ext2AllocPolicy{files, dirs, blocks}`, `.default()` (files near the parent's group, directories spread to the emptiest group, blocks near the goal), `.first_fit()`; `Ext2GroupPick` (`Ext2PickFirst`, `Ext2PickNear`, `Ext2PickSpread`), `Ext2BlockPick` (`Ext2BlockFirst`, `Ext2BlockNear`) | the allocation policy |
| `Ext2CsumMode` (`Ext2CsumUpdate`, `Ext2CsumRefuse`), `Ext2CheckLevel` (`Ext2CheckNone`, `Ext2CheckLocal`, `Ext2CheckFull`) | |
| `Ext2Mkfs.make(wdev, d, o)` (mkfs.bend) | a new filesystem on `d`, checked (`Ext2Mkfs.check`: it opens and passes `Ext2Fsck.full`) before it answers; `Ext2BadMkfs{why}` for options that cannot make one (too few blocks, a bad inode size, ...) |
| `Ext2Mkfs.build(wdev, d, o)`, `Ext2Mkfs.check(dev)`, `Ext2Mkfs.checked(dev, r)` | the same, unchecked; the check; the check applied to a result |
| `Ext2MkfsOptions{blocks, log_block, inode_size, inode_ratio, blocks_per_group, reserved_percent, features, uuid, label, time, zero}`, `.ext2(blocks, uuid)`, `.ext4(blocks, uuid)`, `with_block(o, log)`, `with_inodes(o, size, ratio)`, `with_group`, `with_features`, `with_label`, `with_time`, `with_zero`, `with_reserved`, accessors | mkfs's options (`blocks_per_group` 0: 8 per bit of a block; `zero`: write the inode tables' zeros, which a blank device does not need) |
| `Ext2MkfsFeatures{sparse_super, filetype, large_file, extents, wide, metadata_csum, dir_nlink, extra_isize}`, `.ext2()`, `.ext4()` | the features mkfs writes |
| `Ext2Fsck.counts(dev, fs)`, `Ext2Fsck.full(dev, fs)` (fsck.bend) | the bitmaps against the descriptors' and superblock's free counts; the whole check: metadata and every inode's blocks owned once, `i_blocks`, every group's bitmaps exactly what is used (padding set), the tree walked from the root (`.` and `..`, file types, every used inode reached), every link count the number of entries naming the inode; `Ext2CheckFailed{what}` |

The parts the operations are built from, for a writer of more of ext4 (a
journal, htree directories) to reuse:

| Def | Meaning |
|---|---|
| `Ext2Out{dev, value}` (meta.bend) | a device and a value (a result's pair) |
| `Ext2Fs.write_block(wdev, fs, n, data)`, `Ext2Dev.write_bytes(wdev, off, data)` (meta.bend) | a filesystem block; bytes anywhere (read, patched, written back) |
| `Ext2Meta.write_super(wdev, raw)`, `adjust_super(wdev, bplus, bminus, iplus, iminus)`, `desc_read(dev, fs, g)` (the raw descriptor), `desc(fs, raw)`, `desc_write(wdev, fs, g, raw)`, `block_bitmap`, `inode_bitmap`, `put_block_bitmap`, `put_inode_bitmap`, `bitmap_csum` | the superblock and descriptors written with their checksums; the free counts moved; bitmaps read (an uninit group's computed) and written with their checksums |
| `Ext2Alloc.inode(wdev, fs, wo, parent, dir)`, `blocks(wdev, fs, wo, goal, count)`, `free_blocks(wdev, fs, xs)`, `free_inode(wdev, fs, ino, dir)` (alloc.bend) | allocation and freeing, the bitmaps, descriptors and superblock kept in step |
| `Ext2Bitmap.test`, `set`, `clear`, `update`, `find`, `count_clear`, `make`, `range`, `same` (bitmap.bend); `Ext2Patch.u8`, `u16`, `u32`, `lo32`, `hi32`, `split`, `bytes` (patch.bend) | bitmaps; field patches |
| `Ext2InodeW.read_raw`, `write_raw` (checksum set), `fresh`, `csum`; `Ext2IRaw` field getters and setters (inodew.bend) | inode records |
| `Ext2MapW.set`, `Ext2MapW.truncate` (mapw.bend); `Ext2ExtW.load`, `lookup`, `insert`, `cut`, `store` (extentw.bend); `Ext2FileW.write`, `Ext2FileW.truncate` (filew.bend) | the block map, extents, file data |
| `Ext2Slot{inode, rec_len, file_type, name}`, `Ext2Slots.parse`, `encode`, `insert`, `remove`, `retarget`, `lookup`, `names`, `total`; `Ext2DirW.add`, `remove`, `retarget`, `is_empty`, `first_block` (dirw.bend) | directory blocks and entries |

## Extension points

* **Any device:** the reader is a set of templates over blockdev's interface;
  a file, a partition or a cached device works unchanged. Device errors come
  back as `Ext2Dev{e}`.
  The reader takes blockdev's pure interface. blockdev now also has an owned
  interface (every operation hands the device back, so a device may be a
  single-owner value: an `Array` image, later a file); the reader stays on
  the pure one, unchanged, because it only reads and each of its laws that
  mentions a device is a statement about a pure read's `Result`, which on
  the owned interface would become a pair. The pure interface is the owned
  one's special case for `Data` devices (blockdev's adapters, with laws), and
  an owned device such as blockdev's `ImgDev` is read here through
  `ImgDev.freeze` (a copy into a `MemDev`). `MemDev` now finds a block in
  O(log n) instead of walking a list.
* **Which features to accept:** `Ext2Options.incompat` is the set of
  incompat bits the reader agrees to read (`ext2_incompat()` turns it into a
  plain ext2 reader that refuses extents); checksum verification, journal
  recovery, symbolic link hops and the extent depth bound are options too.
* **Writing on any device:** the writer takes blockdev's pure interface and
  a pure write (`write_block: D -> Nat -> Octets -> Result<.., D>`) as a
  fourth template argument; a device whose write hands back a new value
  (a `MemDev`, a copy-on-write image) works unchanged. A refused operation
  hands back no device, which is what makes every operation all or nothing.
  An owned device (blockdev's `ImgDev`) would take an adapter whose write
  copies, or a writer on the owned interface; the laws would then be about
  pairs.
* **Allocation policy:** `Ext2AllocPolicy` picks the group for files, for
  directories and for blocks (first, near the parent or goal, spread to the
  emptiest); a new policy is a new constructor and a branch in alloc.bend.
* **How much to check:** `Ext2CheckLevel` runs no check, the local one (the
  counts, and what the operation promised), or the whole-filesystem one
  after every operation; a caller can also run `Ext2Fsck.full` itself.
* **More of ext4 (the ext4 package builds on these):** a journal (every write goes
  through the `write_block` argument, so a device that collects an
  operation's blocks can log them before they reach their places: ext4's
  `Ext4Ov` is that device, and its `jext2.bend` journals this writer's
  operations), htree
  directories (refused now as `Ext2HtreeDir`; `Ext2Slots` handles the leaf
  blocks), deeper extent trees (`Ext2ExtentFull` marks the limit), writes
  into unwritten extents, extended attribute blocks, flex_bg packing at
  mkfs.
* **More of ext4 (reading):** inline data (`Ext2InlineData` marks where it would go),
  htree lookups by hash (linear reading is correct, only slower), extended
  attributes, bitmap checksums, casefolded names.
* **Faster reading:** `Ext2File.next` walks the block map or extent tree for
  every block; a reader that kept the last indirect block or extent in its
  cursor would read far fewer blocks, and could be tied to `Ext2File.map` by a
  differential test or a law.

## Laws

`LAWS.bend`:

* **for every input:**
  * `inode_locate_number`, `inode_locate_index`, `inode_number_locate`: inode
    number `n` and its (group, index) convert both ways, for every number of
    inodes per group from 1, and the index is below it (proved from Base's
    `Nat.divmod`);
  * `dirent_round_trip`: `decode(encode(e)) == Some{norm(e)}` for every entry
    whose name has `name_len` bytes (proved from bytes' interface laws:
    lengths, take and drop at a join, the field round trips);
  * `map_past_end`: on every in-memory device, filesystem and inode, a block
    the size does not reach is `Ext2PastEnd`, so the map never answers more
    blocks than the file needs;
  * `map_inside`: every block the map answers is below the filesystem's block
    count. The walks check every block number they read; the law is proved
    from the last check (`Ext2Map.final`) that every answer passes, which
    makes it hold whichever walk answered;
  * `extent_depth_bound`: a root deeper than the options' bound is refused
    before anything is read (the walk recurses on the depth, a child's being
    its parent's less one);
  * `next_at_end`: a reader at or past the blocks a file needs answers the end;
* **witnesses** that each hypothesis can hold (`*_witness`);
* **vectors:** superblocks accepted and refused (bad magic, inline_data and
  extents named, needs_recovery), the checksums mke2fs wrote (the seed, a
  group descriptor's, an inode's), inode locations, directory entries with and
  without the filetype layout and their checks, block-map paths.

The writer's laws:

* **for every input:**
  * `slots_insert_total`, `slots_remove_total`: inserting an entry into a
    directory block's slots, or removing one, keeps the total of the
    records: the block stays exactly covered (a record is split or merged,
    never lost);
  * `slots_insert_names`: an entry whose name the block does not hold,
    inserted, leaves every other entry as it was and in order, the new one
    among them; `slots_remove_names`: removing one leaves exactly the
    others (proved by induction on the slots);
  * `run_counts`: every device `Ext2Op.run` answers, for every operation,
    device, filesystem and options whose check level checks anything, has
    bitmaps that agree with the descriptors' and superblock's free counts;
  * `run_promise`: and is what the operation promised (`Ext2Guard.promise`);
    in particular `write_reads_back` (after a write, the file read from
    `off` for the data's length is the data), `create_keeps_others` and
    `unlink_keeps_others` (creating or removing an entry leaves every other
    entry of its directory as it was, and the entry is there, or gone);
  * `run_full`: with the full check, every device answered passes
    `Ext2Fsck.full`: no block owned twice, every bitmap exactly what is
    used, every link count the number of entries naming the inode;
  * `mkfs_opens`, `mkfs_consistent`: every device `Ext2Mkfs.make` answers,
    for every device and options, opens with the reader's default options
    and passes `Ext2Fsck.full`;
* **witnesses:** the slot laws' hypotheses together (`slots_*_witness`), and
  the default options do check (`run_check_witness`, `run_full_witness`);
* **vectors:** a record split and merged, the first entry of a block
  removed, a full block refused; bitmaps made, searched and counted; a field
  patch; extent lists joined, kept apart and cut.

These say what every answer satisfies, not that an operation succeeds: each
operation and mkfs check their result before answering it (the check is
part of the operation: a result that fails it is refused,
`Ext2CheckFailed`), and the laws follow from that, whatever the operation
did. That the operations do succeed, and do what ext2 means, is what the
tests show: the kernel that checks the laws counts in unary, so running an
operation on an image is beyond what a law can evaluate. The "bitmaps agree
with the counts" and "no block in two inodes" and "links_count = entries"
laws hold with the check level that checks them (`Ext2CheckFull` for the
last two; the default, `Ext2CheckLocal`, checks the counts and the
promise); `Ext2CheckNone` gives none of them.

The checker counts in unary, so the vectors keep their numbers small; the
reading and writing of real images is covered by `check.bend` and the
differential tests.

## Tests

* `check.bend`: the sample image (ext4 with metadata_csum, written by mke2fs;
  `ref/sample.py` regenerates it): listings, contents streamed, holes, ranges,
  fast and slow links, lookups with and without following links; six
  corruptions refused (bad magic, superblock, inode and directory checksums,
  an unsupported feature, a bad rec_len), one accepted again with
  verification off, and a plain-ext2 reader refusing extents. Then mkfs on
  blank devices (the ext2 profile with 1 KiB blocks, the ext4 one with
  4 KiB blocks, extents and metadata_csum), each passing `Ext2Fsck.full`,
  and a script of 24 operations on each (directories, files written,
  appended, linked, renamed, truncated, a sparse file, fast and slow links;
  six refused: a non-empty rmdir, an existing name, rmdir of a file, a
  directory renamed into itself, a missing parent), read back and checked
  whole.
* `ref/run.sh`: `ref/gen.py` builds 16 images with mke2fs (ext2 with 1 KiB and
  4 KiB blocks, several groups, revision 0, htree directories after
  `e2fsck -D`; ext3; ext2 with gdt_csum; ext4 with and without metadata_csum,
  without 64bit, with meta_bg over 20 groups, with several groups, with
  metadata_csum_seed after a UUID change, with htree directories and an
  unwritten extent, and with larger inputs: a directory of 3000 entries and
  a file of 100 to 160 KB read whole by range), each from a random tree
  (nested directories, empty, small and large files, sparse files including
  one reaching the triply indirect block, fast and slow symbolic links,
  absolute links, chains and loops, a long name, a directory of many
  entries), and 27 more runs over corrupted copies (or with a narrower
  reader or other options). It
  compares the listings, inode numbers, sizes, modes and link counts with
  the tree and with `debugfs -R "ls -l"` and `stat`; contents (streamed,
  CRC-32) and byte ranges with the files (checked against `debugfs -R cat`);
  block numbers with `debugfs -R bmap`; link targets with `os.readlink`;
  lookups that follow links with a model of path resolution in `gen.py`
  (written here, so it shares an author with the package); and requires each
  corruption to be refused with the error it calls for. 43 images, 2949
  queries (7130 lines of output) with the default seed 2026; seed 7 passes
  too. The images live in a
  temporary directory and are read a block at a time (`ref/image.bend` holds
  their non-zero blocks, each read from the file on its own and kept as a
  list of bytes until it is read); each image runs in its own process.
* `ref/run.sh`, writing: `ref/wgen.py` builds 12 images with mke2fs, each
  populated from a random tree with `mke2fs -d` (ext2 with 1 KiB and 4 KiB
  blocks, revision 0, with uninit_bg over several groups; ext3 with its
  journal; ext4 with 1 KiB and 4 KiB blocks, without metadata_csum, without
  64bit, over several groups, with meta_bg, with an htree directory), and
  lists 6 filesystems for the package's mkfs to make (both profiles, 1, 2
  and 4 KiB blocks, 128- and 256-byte inodes, several groups); on each it
  draws a random sequence of operations (about a third meant to be
  refused: missing parents, existing names, bad names (too long, ".",
  ".."), non-empty directories, a directory renamed into itself, hard links
  to directories, a directory written as a file, entries added to an htree
  directory, ...). Further cases run the same images with the full check after
  every operation, with first-fit allocation, without extents (block maps
  on ext4), with checksums refused, with two files grown in turn into a
  depth-1 extent tree, with writes into an unwritten extent (refused), and
  on three images corrupted after the fact (a bitmap bit, a link count, a
  free count), where `Ext2Fsck.full` must find the corruption. The
  operations run through a model written in `wgen.py` from POSIX's and
  ext2's documented behaviour (so it shares an author with the package, but
  not its code), and the run compares, for every case: each operation's
  outcome (done, or refused with the error kind the model expects); the
  tree the package reads back (kinds, sizes, link counts, CRC-32 of the
  contents, link targets) with the model's; and the image itself, rebuilt
  from the program's output, with `e2fsck -fn` (which must accept every
  image written) and `debugfs` (`ls -p`: names, kinds, sizes and which names
  share an inode; `rdump`: contents and link targets). 27 cases, 993
  operations with the default seed 2026. `ref/wmain.bend` is one program
  that reads the case list from a file and runs every case, so it builds
  once.
* Both need python3 and e2fsprogs (exit 77 without them).

## Speed and size

Measured natively (Bend 2.0.37, WSL2, `bend file.bend -o prog`).
`check.bend` runs in about 1 s; the reading test's 43 case files are each
built natively, which is most of the 17 minutes `scripts/check.sh ext2`
takes. Field reads go through bytes' bit-sliced readers; checksums use
crc's bitwise reference engine.

Large inputs, on images of 4 to 256 MB written by mke2fs and read a block
at a time (throwaway size tests, not kept in the repository, run on the
same workloads as the JavaScript-lane figures beside them). Each program
loads the image's blocks from its file into a `MemDev`, except the files'
data blocks (each holding one byte pattern) and a grown directory's empty
blocks, which a test device answers from one shared block; the memory is
the whole process's, the device's blocks included, and the time includes
the load (0.02 to 0.3 s):

| Operation | Input | Time, peak memory | JavaScript lane, before |
|---|---|---|---|
| streaming (`Ext2File.start`, `next`) | 8 MB file, 1 KiB blocks, block map into the doubly indirect block | 2.2 s, 18 MB | 25 s, 0.4 GB |
| streaming | 48 MB file, 4 KiB blocks, extents | 5.2 s, 9 MB | 93 s, 0.4 GB |
| streaming | 6000-block sparse file of 3000 one-block extents (a tree of depth 2: one index block, 37 leaves) | 14.5 s, 22 MB | 28 s, 0.7 GB |
| streaming | 70 MB sparse file, 4300 data blocks under 36 indirect, 2 doubly and 1 triply indirect blocks | 8.5 s, 16 MB | 96 s, 0.7 GB |
| `read_all` | 1 MB (block map and extents, 1 and 4 KiB blocks) | 0.33 to 0.49 s, 107 to 120 MB | 4 to 10 s, 1.3 to 1.9 GB |
| `read_all` | 100 KB | 0.04 to 0.07 s, 18 to 32 MB | 1.1 s, 0.3 GB |
| `Ext2File.map` | the last block of each file above | 0.01 to 0.03 s, 9 to 22 MB | about 1 s, 0.2 to 0.5 GB |
| `Ext2.list` | 20,000 entries (1 KiB blocks, linear and htree; 4 KiB; 64 KiB) | 1.0 to 1.6 s, 0.56 to 0.62 GB | 2.3 to 2.8 s, 1.0 to 1.3 GB |
| `Ext2.list` | a directory of 10,000 blocks, 8 entries left | 2.4 s, 29 MB | 13 s, 0.44 GB |
| `Ext2.list` | a directory of 30,000 blocks, 8 entries left | 7.3 s, 45 MB | 38 s, 0.48 GB |
| `Ext2.lookup` | the last of 20,000 entries; a missing name in 10,000 and in 30,000 blocks | 1.4 s; 2.4 s and 7.2 s | 2 s; 12 s and 29 s |
| `Ext2.lookup`, `Ext2.read` | a file whose inode is in the last of 256 groups (ext2; ext4 with meta_bg) | 0.27 s, 141 MB; 0.10 s, 52 MB | 1 s, 0.35 GB |

The 20,000-entry rows' memory is mostly the test device's directory blocks
(1,400 to 5,800 of them, held as `Octets`); the lookup of the last of them
peaks at 0.54 GB, the missing names at 29 and 46 MB (0.9, 0.45 and 0.48 GB
before). The large directories are grown by debugfs's `expand_dir` (empty
blocks after the first, which holds the 8 entries), where the JavaScript
lane's had 30,000 and 90,000 entries removed; either way every block is
read. The 1 MB rows are `read_all` (`read_range` over the whole file).

No operation recurses once per block, entry or group. Reading a range and
listing a directory are tail calls a block at a time (the blocks or entries
are collected last first and joined once at the end), and so are the walk
along a block's entries, the search of a block for a name, the scan of an
extent node and the search of a directory; the block map and the extent
tree are walked by recursion on their depth (at most three indirect levels,
at most the options' `max_depth` nodes), and a group's descriptor and an
inode are found by arithmetic, whatever the number of groups. (Before,
reading a range and listing a directory recursed once per block: listing
the 10,000-block directory took 2.5 GB and 16 s, and either would have
overflowed the JavaScript lane's stack somewhere between 10,000 and 40,000 blocks.)
A block read through blockdev's `Dev.read_bytes` recurses once per device
block it spans: at most 128 (a 64 KiB block on a 512-byte device).

What limits one call is memory: an `Octets` holds about 100 bytes of
memory a byte natively, so `read_all` of a 1 MB file peaks at about 0.1 GB (1.3 to
1.9 GB before, on the JavaScript lane): read files of more than a few
megabytes by streaming or in ranges. A listing holds every entry's name.
Streaming reads the block map or extent tree again for every block (about
0.1 ms a block for a hole, 0.3 to 0.4 ms for a block of data through the
block map or a shallow extent tree, 2.4 ms through the depth-2 tree above,
which reads its index block and a leaf of 84 extents for each); the differential test reads the 70 MB
sparse file's far blocks by range and by map instead.

### Writing (native)

Measured natively (`bend file.bend -o`, clang 22) on in-memory devices
(throwaway size tests, not kept in the repository; each figure is the whole
program: mkfs on a blank device, the operations, then reading the result
back and `Ext2Fsck.full`; the 1 MB of data is generated in the program):

| Operation | Input | Time | Memory |
|---|---|---|---|
| `Ext2Mkfs.make` and `Ext2Fsck.full` | 64 MB, ext2 profile (1 KiB blocks, 8 groups, 16,384 inodes) | 1.1 s | 0.4 GB |
| `Ext2Mkfs.make` and `Ext2Fsck.full` | 64 MB, ext4 profile (4 KiB blocks, 1 group, 4096 inodes) | 0.3 s | 0.1 GB |
| create and write 1 MB in one write | ext4 profile (extents) | 3.6 s (3.0 s unchecked) | 0.4 GB |
| create and write 1 MB in one write | ext2 profile (block map into the doubly indirect block) | 11 to 12 s (10 s unchecked) | 0.7 GB |
| 64 appends of 16 KB | ext4 profile | 3.0 s | 0.3 GB |
| 300 files created in one directory | ext2 profile (1 KiB blocks, 8 groups) | 8.9 s (4.1 s unchecked; 65 s with the full check after each) | 0.4 GB |
| 300 files created in one directory | ext4 profile (4 KiB blocks, metadata_csum) | 18 to 20 s (11 s unchecked) | 0.1 GB |
| write 1 MB, truncate to 0, unlink | ext4 profile | 3.3 s | 0.4 GB |

"Unchecked" is `Ext2CheckNone`; the default, `Ext2CheckLocal`, reads every
group's bitmaps and descriptor after each operation (the counts) and what
the operation promised (a written range read back, the directory listed
again), which costs about as much as the operation again. A create walks
the directory's blocks for the name and for room, so creating n entries in
one directory is quadratic (htree directories, which would make it
logarithmic, are refused, not written); with metadata_csum every block
written is checksummed with crc's bitwise crc32c, which is what makes the
ext4 creates slower. Writes hold their data as an `Octets` (about 150 bytes
of memory a byte), so write large files in pieces of a megabyte or so.
Some of the writer's walks recurse once per element (a block's slots,
the list of blocks one write allocates, merging sorted block lists); on
the native lane's 2 GB stack the largest above (1,024 blocks allocated and
mapped in one write) runs within it, but on the JavaScript lane a write of
several thousand blocks at once could overflow it. `check.bend` builds in
56 s (1.8 GB) and runs in 1.1 s;
`ref/wmain.bend` builds in 58 s (1.7 GB) and runs the 27 writing cases in
46 s (52 MB).

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and `Nat` division (`LAWS_div.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` passes (reading: 7130 lines, 2949
queries, 43 images match; writing: 27 cases, 993 operations match, every
image accepted by `e2fsck -fn` and read back by debugfs), `scripts/deps.sh`
passes; the whole `scripts/check.sh ext2` (with `VERDICT=1`) takes about 17
minutes natively, most of it building the reading test's 43 case files.
Every program, `check.bend`, `ref/wmain.bend` and all 43 reading case
files, builds and runs natively (`ref/gen.py` builds each image's query
list from helper defs of at most 40 queries, so no def passes the C
backend's 247 live values, bendlang/bend#1069).
