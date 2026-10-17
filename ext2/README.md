# bend-osdev-ext2

A read-only reader of ext2, ext3 and ext4 filesystems over blockdev's device
interface: the superblock and its checks, block group descriptors, inodes,
file data through the classic block map and through extent trees, directories,
path lookup and symbolic links, and the metadata checksums of ext4.

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
differential test.

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
leaf blocks' checksums are verified). Writing is out of scope.

Block numbers and sizes are `Nat`, at most 48 bits (ext4's own limit, and the
largest immediate `Nat` of Bend 2.0.37); a 64-bit field's high half beyond
that is ignored rather than overflow. Sizes in records are `W64`.

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
| `sample.bend` | test fixture (not interface): the small image `check.bend` reads, written by `ref/sample.py` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | a runnable check on the sample image |
| `ref/` | the differential test against mke2fs and debugfs |

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
| `Ext2File.read_all(dev, fs, i)` | the whole file (small files: an `Octets` is a list today) |
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

## Extension points

* **Any device:** the reader is a set of templates over blockdev's interface;
  a file, a partition or a cached device works unchanged. Device errors come
  back as `Ext2Dev{e}`.
* **Which features to accept:** `Ext2Options.incompat` is the set of
  incompat bits the reader agrees to read (`ext2_incompat()` turns it into a
  plain ext2 reader that refuses extents); checksum verification, journal
  recovery, symbolic link hops and the extent depth bound are options too.
* **Writing** is the obvious extension: the records' parsers have field
  offsets a writer would mirror (`Ext2Dirent.encode` is the first writer),
  and blockdev would need a write operation in its interface.
* **More of ext4:** inline data (`Ext2InlineData` marks where it would go),
  htree lookups by hash (linear reading is correct, only slower), extended
  attributes, bitmap checksums, casefolded names.
* **Faster reading:** `Ext2File.next` walks the block map or extent tree for
  every block; a reader that kept the last indirect block or extent in its
  cursor would read far fewer blocks, and could be tied to `Ext2File.map` by a
  differential test or a law.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

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

The checker counts in unary, so the vectors keep their numbers small; the
reading of real images is covered by `check.bend` and the differential test.

## Tests

* `check.bend`: the sample image (ext4 with metadata_csum, written by mke2fs;
  `ref/sample.py` regenerates it): listings, contents streamed, holes, ranges,
  fast and slow links, lookups with and without following links; six
  corruptions refused (bad magic, superblock, inode and directory checksums,
  an unsupported feature, a bad rec_len), one accepted again with
  verification off, and a plain-ext2 reader refusing extents.
* `ref/run.sh`: `ref/gen.py` builds 15 images with mke2fs (ext2 with 1 KiB and
  4 KiB blocks, several groups, revision 0, htree directories after
  `e2fsck -D`; ext3; ext2 with gdt_csum; ext4 with and without metadata_csum,
  without 64bit, with meta_bg over 20 groups, with several groups, with
  metadata_csum_seed after a UUID change, with htree directories and an
  unwritten extent), each from a random tree (nested directories, empty, small
  and large files, sparse files including one reaching the triply indirect
  block, fast and slow symbolic links, absolute links, chains and loops, a
  long name, a directory of many entries), and 27 more runs over corrupted
  copies (or with a narrower reader or other options). It
  compares the listings, inode numbers, sizes, modes and link counts with
  the tree and with `debugfs -R "ls -l"` and `stat`; contents (streamed,
  CRC-32) and byte ranges with the files (checked against `debugfs -R cat`);
  block numbers with `debugfs -R bmap`; link targets with `os.readlink`;
  lookups that follow links with a model of path resolution in `gen.py`
  (written here, so it shares an author with the package); and requires each
  corruption to be refused with the error it calls for. 42 images, 2819
  queries (3958 lines of output) with the default seed 2026; seed 7 passes
  too. The images live in a
  temporary directory and are read a block at a time (`ref/image.bend` holds
  their non-zero blocks, each read from the file on its own); each image runs
  in its own process. It needs python3 and e2fsprogs (exit 77 without them).

## Speed and size

Measured with Bend 2.0.37's JavaScript runtime (bun; no clang on the test
machine): `check.bend` runs in about 1 s; the differential test takes about
30 s to build its images and 70 s to read them (1 to 10 s an image, 0.5 to
0.8 GB of memory each: Bend 2.0.37 does not give memory back between
images, so each runs in a process of its own). Field reads go through
bytes' bit-sliced readers; checksums use crc's bitwise reference engine.
Streaming reads the block map or extent tree again for every block, so a
70 MB sparse file (all holes) takes about half a minute to stream; the test
reads that file's far blocks by range and by map instead.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 3958 lines (2819 queries, 42 images) match,
`scripts/deps.sh` passes.
