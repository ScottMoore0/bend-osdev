# bend-osdev-ext4

What ext4 has beyond what bend-osdev-ext2 reads (ext2 already reads ext2,
ext3 and ext4: extents, metadata checksums, 64-bit descriptors, meta_bg,
flex_bg): hashed (htree) directory lookups through the index, and a writer
of hashed directories; inline data (files and directories kept in the
inode); extended attributes (in the inode body, in an attribute block, and
in EA inodes); and the jbd2 journal: its superblock, descriptor, revoke and
commit blocks with their checksums, the three-pass recovery applied to a
device, writing a transaction (a list of block writes) into the journal,
and journalled updates (any writer's block writes, committed and replayed).
Everything takes blockdev's device interface, and builds on ext2's public
reader: this package adds no second superblock, inode or extent reader.

## Specification

* the ext4 disk-layout documentation (kernel.org,
  Documentation/filesystems/ext4): "Hash Tree Directories", "Inline Data",
  "Extended Attributes", "Directory Entries", "The Super Block" (the hash
  seed, default hash version, s_flags, journal fields), "Checksums";
* the same documentation's "Journal (jbd2)": the superblock (v1, v2), block
  header, descriptor block and tags, data blocks and escaping, revocation
  block, commit block, the checksum features, and recovery;
* RFC 1320 (MD4) for the round functions and constants of half MD4, and
  Wheeler and Needham, "TEA, a Tiny Encryption Algorithm" (1994), for TEA.

The package was written from these documents only; no Linux kernel code and
no e2fsprogs source was read. The e2fsprogs tools (mke2fs, e2fsck, debugfs,
tune2fs, dumpe2fs) were run as black boxes: they settle what the
documentation leaves open, and the differential test compares with them.

Where the documentation is incomplete, and how the package settles it:

* **The directory hashes.** The documentation names the hash versions (0
  legacy, 1 half MD4, 2 TEA, 3 to 5 the same over unsigned chars) and the
  seed but does not define the functions. The definitions in `hash.bend`
  apply RFC 1320's MD4 round functions and constants to 8 words at a time
  (three rounds of 8 steps), TEA's 16 cycles as a compression function on 4
  words, and a multiplicative hash for legacy; names are packed into words
  big end first from a padding word made of the remaining length; the major
  hash has bit 0 cleared and avoids 0xFFFFFFFE. They were fixed by
  experiment: they agree with debugfs's `dx_hash` on 397 of 400 random
  names (all six versions, bytes above 127, random seeds; the 3 others
  begin with "-", which debugfs reads as an option) and with the hashes e2fsck
  writes into the indexes it builds (`e2fsck -D`), and `LAWS.bend` holds 12
  of debugfs's values as vectors. The author knew these algorithms' general
  shape before writing them; they are pinned down here by the experiments,
  not by any implementation.
* **The htree checksum** (dx_tail): crc32c from the inode's seed over the
  block up to the end of the count entries, then dt_reserved, then four
  zero bytes; found by matching the checksums e2fsck writes.
* **Extended attribute hashes**: an entry's hash folds the name's bytes in
  (hash << 5 ^ hash >> 27 ^ byte), then the value's little-endian words
  (hash << 16 ^ hash >> 16 ^ word); an EA inode's value contributes one
  word, crc32c(seed, value), which the EA inode keeps in i_atime; the block
  hash folds the entries' hashes the second way. A stored hash of 0 is not
  checked (e2fsprogs writes 0 for entries in the inode body, and for some
  block hashes); names hash as unsigned bytes, or signed ones, either is
  accepted. All found by matching what e2fsprogs and debugfs store.
* **jbd2 tags with csum_v2** are 2 bytes longer than the documented fields
  (10 bytes, 14 with 64bit); seen in the journals debugfs writes.
* **jbd2 checksums**: the superblock's covers its 1024 bytes; a descriptor's
  and a revoke block's tail covers the block with the tail zeroed; a commit
  block's covers the whole block with h_chksum[0] zeroed; a tag's covers
  the transaction ID (be32) and the data block as the log stores it
  (escaped). Matched against debugfs's journals.
* **Recovery's corner cases**, settled against debugfs's `journal_run` and
  e2fsck's own replay: a commit block whose checksum fails ends the log
  before its transaction; a descriptor or revoke block whose checksum fails
  makes the whole log unusable: nothing is replayed and the recovery fails
  (`Ext4BadLogCsum`; e2fsprogs refuses too); a journalled block whose tag
  checksum fails is skipped and counted (or fails the recovery, as the
  options choose); a revoke record in transaction T covers T and earlier
  transactions. After recovery the next transaction ID is one past the ID
  after the last replayed transaction, as e2fsprogs leaves it; one
  difference, kept on purpose: after skipping a block for its checksum
  e2fsprogs leaves s_sequence unchanged, while this package moves it on as
  after any recovery, so that stale log blocks can never pass for the next
  transaction's.
* **Inline directories** keep entries in the system.data value too (the
  kernel writes them; e2fsprogs never does, it moves a full inline
  directory to a block); the test writes such directories by hand. "." and
  ".." are given the directory file type.

## What it reads and writes

| | |
|---|---|
| Hashed directories | the index walked from dx_root through dx_nodes (2 levels, 3 with large_dir) to one leaf, its checksums (dx_tail) verified; collisions followed into the next leaf; hash versions 0 to 5, the seed, s_flags' signedness |
| The htree writer | a directory's blocks from its entries: sorted by hash, leaves filled, the index built to the levels allowed, checksums, padding to a block count |
| Inline data | files of up to an inode's size (i_block, then system.data); directories, entries in i_block and system.data |
| Extended attributes | the inode body and the attribute block (header, checksum, entry hashes, block hash), EA inode values (hash checked); full names with their prefixes |
| The journal | internal journals (s_journal_inum); superblock v1 and v2; features revoke, 64bit, async_commit, csum_v2, csum_v3 (fast_commit refused); recovery in three passes on a device; writing a transaction; journalled updates |
| Not done | external journals, fast commits, the old compat checksum (read, not checked), casefolded and encrypted directories (hash version 6) |

## Files

| File | Holds |
|---|---|
| `ext4.bend` | the entry: opening a filesystem; paths (lookup, listing, reading, symbolic links, attributes) through every kind of directory and file |
| `super.bend` | the superblock fields ext2's reader does not keep; `Ext4Fs` (ext2's filesystem, those fields, the options) |
| `options.bend` | `Ext4Options` and `Jbd2Options`, with defaults |
| `error.bend` | `Ext4Error` |
| `hash.bend` | the directory hashes |
| `dx.bend` | dx_root and dx_node: codec and checksum |
| `htree.bend` | the htree model (pick, find, lookup, scan, the ordered class) and the lookup on a device |
| `htwrite.bend` | the htree writer |
| `dir.bend` | directories of every kind: inline, hashed, linear |
| `inode.bend` | an inode's raw record (the extra fields, the attribute area, i_atime) |
| `inline.bend` | inline data: files and directories |
| `xattr.bend` | extended attributes |
| `jsuper.bend` | the journal superblock and the log's geometry |
| `jblock.bend` | descriptor, revoke and commit blocks, tags, data escaping, checksums |
| `jlog.bend` | the log as records; the three passes (scan, revoke table, replay plan) |
| `jscan.bend` | reading log blocks as records, one block at a time |
| `jwrite.bend` | a transaction's log blocks from block writes and revokes |
| `journal.bend` | the journal on a device: open, recover, commit, transact |
| `overlay.bend` | `Ext4Ov`: a device that keeps writes aside, for journalled updates |
| `devwrite.bend` | writing filesystem blocks and the superblock through blockdev's pure write |
| `sample.bend` | test fixture (not interface): the image `check.bend` reads, written by `ref/sample.py` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | a runnable check on the sample image |
| `ref/` | the differential test |

Bend imports do not re-export: import the file that holds what you use.

## API

Device functions take blockdev's pure interface as template arguments
`~Dv`, `~block_size`, `~read_block` and the device `d` (written `(dev)`
below), and the writing ones also a pure write `~write_block: Dv -> Nat ->
Octets -> Result<&2, &2, DevError, Dv>` (written `(wdev)`); `Ext4Dev.mem_write`
is that write for blockdev's `MemDev`. Fallible functions answer
`Result<&2, &2, Ext4Error, A>`.

```
import ../blockdev/blockdev.bend as D
import ./options.bend as O
import ./ext4.bend as X4
import ./journal.bend as JR
import ./devwrite.bend as DW

X4.Ext4.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, O.Ext4Options.default())
X4.Ext4.lookup(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, B.Octets.of_string("/big/name"))
JR.Ext4Journal.recover(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, O.Jbd2Options.default())
```

### ext4.bend, dir.bend, super.bend, options.bend

| Def | Meaning |
|---|---|
| `Ext4.open(dev, opts)`, `Ext4Fs.open`, `Ext4Fs.mount(opts, raw)` | the filesystem (ext2's reader underneath, with inline_data accepted) |
| `Ext4.lookup(dev, fs, path)` | the inode a path names; a symbolic link before the end is `Ext4SymlinkInPath`, a final one is answered itself; `Ext4NotFound`, `Ext4NotDir` |
| `Ext4.list(dev, fs, path)`, `Ext4Dir.entries(dev, fs, i)` | a directory's used entries ("." and ".." first) |
| `Ext4Dir.find(dev, fs, i, name)` | one entry: inline directories searched in the inode, hashed ones through the index, others by ext2's linear search |
| `Ext4.read(dev, fs, path)`, `Ext4.read_inode(dev, fs, i)` | a whole file, inline or in blocks (stream large files with ext2's `Ext2File.start`, `next`) |
| `Ext4.readlink(dev, fs, path)` | a symbolic link's target (inline ones too) |
| `Ext4.xattrs(dev, fs, path)`, `Ext4.xattr(dev, fs, path, name)` | extended attributes, and one value by its full name |
| `Ext4.inode(dev, fs, n)` | inode n (ext2's reader) |
| `Ext4Fs` (`ext2`, `super`, `opts`, `block_size`, `seed`, `hash_signed`, `has_compat`, `has_incompat`, `verify`, `verify_meta`), `Ext4Super{hash_seed, def_hash_version, flags, journal_inum, journal_dev, journal_uuid}` and its accessors and feature bits | the mounted filesystem |
| `Ext4Options{ext2, verify, signed_default, max_levels}`, `.default()`, `with_*`, accessors, `Ext4Options.incompat()` | reading options |
| `Jbd2Options{verify, skip_bad_data, commit_sec, commit_nsec}`, `.default()`, `with_*`, accessors | journal options |

### hash.bend, dx.bend, htree.bend, htwrite.bend

| Def | Meaning |
|---|---|
| `Ext4Hash.name(v, seed, name)` | a name's `Ext4DxHash{major, minor}` under hash version v (0 to 5); `Ext4BadHashVersion` |
| `Ext4Hash.version(root, signed)` | the version a lookup uses: the root's, or its unsigned twin |
| `Ext4Hash.legacy`, `md4`, `tea`, `pack`, `md4_of`, `tea_of`, `finish` | the pieces |
| `Ext4DxRoot{dot, dotdot, version, levels, limit, entries}`, `Ext4DxNode{limit, entries}`, `Ext4DxEntry{hash, block}`, `.parse`, `.encode`, `Ext4Dx.csum`, `Ext4Dx.limit` | the index blocks |
| `Ext4Htree.lookup_dev(dev, fs, i, name)` | the entry by the index: reads the root, the nodes on the path and the leaf (and the next leaf only for a continued hash) |
| `Ext4HtEnt{hash, entry}`, `Ext4HtLeaf{lo, ents}`, `Ext4Htree.pick`, `continues`, `find`, `lookup`, `scan`, `ordered`, `consistent` | the model the laws are about; `pick`, `continues` and `find` are the device lookup's own |
| `Ext4HtreeParams{block_size, version, signed, seed, csum, filetype, ino, parent, levels, pad_to}`, `.default(bs, ino, parent)`, `.of_fs(fs, ino, gen, parent)`, `with_pad`, `with_version` | what the writer needs |
| `Ext4Htree.build(params, entries)` | a hashed directory's blocks (root, leaves, nodes); `Ext4HtreeTooBig` |
| `Ext4Htree.plan(ents, cap)`, `sort`, `insert`, `hashed` | the writer's leaves, as the model |

### inline.bend, xattr.bend, inode.bend

| Def | Meaning |
|---|---|
| `Ext4Inline.data(dev, fs, i)`, `entries(dev, fs, i)`, `is_inline`, `system_data` | inline files and directories; `Ext4NotInline`, `Ext4BadInline` |
| `Ext4Xattr{index, name, value, inum, size, hash}`, `full_name`, `prefix` | an attribute |
| `Ext4Xattr.list(dev, fs, i)`, `get(dev, fs, i, name)`, `ibody(raw, ino, check)`, `block_of(fs, n, blk, ino)`, `entries`, `entry_hash`, `inode_hash`, `block_hash`, `block_csum` | reading and checking them; `Ext4BadXattr`, `Ext4BadXattrBlock`, `Ext4BadXattrCsum`, `Ext4BadXattrHash`, `Ext4NoXattr` |
| `Ext4Inode.raw(dev, fs, n)`, `ea_offset`, `atime`, `flag_index`, `flag_inline_data`, `flag_ea_inode` | the raw inode record |

### The journal: jsuper.bend, jblock.bend, jlog.bend, jscan.bend, jwrite.bend, journal.bend

| Def | Meaning |
|---|---|
| `Jbd2Super{...}`, `.parse`, `.check(o, bs, blocks, opts)`, `.csum`, `.geom`, `.seed`, `.with_log(o, start, seq)`, feature bits | the superblock; `Ext4BadJournalMagic`, `Ext4BadJournalType`, `Ext4BadJournal`, `Ext4JournalUnsupported`, `Ext4BadJournalCsum` |
| `Jbd2Geom{bs, wide, csum, seed, first, maxlen}`, `tag_size`, `tail`, `next` | the log's geometry |
| `Jbd2Tag{block, flags, csum}`, `Jbd2Desc.decode`, `encode`, `capacity`, `Jbd2Revoke.decode`, `encode`, `capacity`, `Jbd2Commit.ok`, `encode`, `Jbd2Block.kind`, `Jbd2.escape`, `unescape`, `needs_escape`, `data_csum`, `data_ok`, `tag_csum` | the blocks |
| `Jbd2Put{block, src, flags, csum}`, `Jbd2Rec` (`Jbd2RDesc`, `Jbd2RRevoke`, `Jbd2RCommit`), `Jbd2Tx`, `Jbd2Rv`, `Jbd2Do` | records |
| `Jbd2Log.scan(s, rs)`, `table(txs)`, `revoked`, `plan(txs)`, `recover(s, rs)` | the three passes; `revoked_in`, `none_revoked`, `no_commit`, `member`, `unrevoked` state the laws |
| `Jbd2Scan.start(pos, seq)`, `feed(check, g, st, blk)`, `pos`, `seq`, `live`, `bad`, `records`, `Jbd2Scan.list(check, g, blocks, s)` | the streaming parser of log blocks |
| `Jbd2Write{block, data}`, `Jbd2Write.blocks(g, uuid, seq, rv, ws, sec, nsec)` | a transaction's log blocks |
| `Ext4Journal.open(dev, fs, opts)`, `read`, `home`, `records` | the journal on a device |
| `Ext4Journal.recover(wdev, fs, opts)` | `Ext4Recovered{dev, report}`: every committed transaction replayed, the journal marked empty, needs_recovery cleared; `Jbd2Report{transactions, replayed, skipped, next}`; `Ext4BadLogCsum`, `Ext4ReplayCsum` |
| `Ext4Journal.commit(wdev, fs, opts, rv, ws)` | `Ext4Committed{dev, seq, blocks}`: a transaction written into the (empty) journal, which then needs recovery; `Ext4JournalNotEmpty`, `Ext4JournalFull`, `Ext4BadJournalWrite` |
| `Ext4Journal.transact(wdev, fs, opts, op)` | a journalled update: `op` writes through an `Ext4Ov`, its writes are committed as one transaction, then recovered |

### overlay.bend, devwrite.bend

| Def | Meaning |
|---|---|
| `Ext4Ov{base, writes}`, `start`, `block_size`, `read_block`, `write_block`, `writes`, `base` | a device keeping writes aside |
| `Ext4Dev.write(wdev, bs, n, data)`, `write_all(ws, r, bs)`, `set_incompat(wdev, fs, set, clear)`, `super_with`, `mem_write`, `fits`, `read_mem` | writing |

## Extension points

* **Any device**, through blockdev's pure interface and a pure write
  (blockdev's `Dev.own_write_block` adapts one to its owned interface; a
  device whose blocks divide the filesystem's is written a piece at a
  time).
* **Journalled updates of any writer:** `Ext4Journal.transact` takes any
  operation written over a pure device interface and a pure write, runs it
  on an `Ext4Ov` and journals its writes. ext2's writer (being written in
  `ext2/`, not yet in its public interface) is such an operation: in a
  scratch test, `Ext2W.mkdir` through `transact` gave a transaction that
  e2fsck replays to a clean filesystem with the new directory. Once ext2's
  writing API is published, journalled metadata updates are `transact` over
  its operations (and a test of them belongs in `ref/`).
* **Options:** which features ext2's reader accepts, checksum verification
  (ours and ext2's), the hash signedness default, index depth; the
  journal's verification, skipping bad blocks, the commit time stamped.
* **The htree writer's parameters** (`Ext4HtreeParams`: hash version, seed,
  checksums, file types, index levels, padding) come from a filesystem
  (`of_fs`) or are chosen freely.
* **Faster paths:** the writer's sort is an insertion sort (quadratic: see
  below), the reference the laws are about; a merge sort can be added
  beside it, tied to it by a law or a differential test. The revoke table
  is a list; a tree would make large revoke sets cheaper. The streaming
  scan reads only header blocks; replay reads each journalled block once.
* **More of the format:** external journals, fast commits, writing inline
  data and attributes, casefolded directories.

## Laws

`LAWS.bend`:

* **for every input:**
  * `htree_lookup_scan`: on every ordered model (each leaf's index hash at
    most the next's, every entry below the next leaf's index hash, every
    entry of a later leaf at least its own) and every name whose entries
    all have the hash given, the index lookup finds what a linear scan of
    all leaves finds;
  * `htree_plan_ordered`: the writer's plan of every list of entries, for
    every leaf size, is ordered (proved through the insertion sort's
    sortedness and the filling's boundaries);
  * `htree_writer_lookup`: so on every directory the writer plans, the
    lookup finds what the scan finds;
  * `scan_incomplete`: records after the last commit change nothing the
    scan answers when they hold no commit: an incomplete final transaction
    is never replayed;
  * `plan_revoked`: no block the plan replays is revoked, in the log it is
    made from, by its own transaction or a later one;
  * `commit_replays`: a committed transaction (revoke block, descriptor,
    commit) replays exactly its blocks that it does not revoke;
  * `replay_idempotent`: on blockdev's `MemDev`, writing a list of good
    writes (`Ext4Dev.write_all`, what the replay does with each block it
    replays) a second time changes no block (proved from blockdev's laws
    `read_after_update`, `update_other`, `update_keeps_size`,
    `update_keeps_count` and `own_write_ok`);
  * `escape_round_trip`: every data block comes back from the log as it was
    journalled (escaping a block that starts with the magic number is
    undone; proved through bytes' laws and the soundness of bytes'
    `list_eq`, itself proved from Base's `Word.cmp`);
* **witnesses** that every hypothesis can hold;
* **vectors:** 12 directory hashes debugfs computes (every version, signed
  and unsigned names, long names, a seed), a hash version's unsigned twin,
  a bad version refused, two attribute hashes e2fsprogs stored, model
  lookups, a transaction with a revoke.

What the laws do not cover, and what stands in for it: the device lookup
(`Ext4Htree.lookup_dev`) uses the model's `pick`, `continues` and `find`,
but its walk over blocks is tied to the model by the differential test, not
a law; the byte layout of the journal's blocks (the codec under the
records, so the end-to-end claim that replaying a written transaction gives
the device the writes give) is tested, not proved: the writer's blocks are
byte-identical to an independent model's, and debugfs and e2fsck replay
them to exactly the writes (see Tests). Proving the codec needs bytes' field
readers at offsets inside appended strings, which bytes' interface laws do
not cover yet.

## Tests

* `check.bend`: the sample image (ext4, 1 KiB blocks, dir_index,
  has_journal, inline_data, ea_inode, metadata_csum; `ref/sample.py`
  regenerates it): lookups through a hashed directory (and misses, "..",
  through a file), an inline directory, inline files (one with system.data),
  attributes in the body, the block and an EA inode; recovery of three
  debugfs transactions (one revoking an earlier block, one escaped block);
  a commit replayed and compared with writing directly; a journalled update
  through the overlay; corruptions refused or handled (index checksum, a
  checksum ignored when verification is off, leaf and attribute block
  checksums, a bad commit, a bad descriptor, a bad data block skipped or
  refused, a bad journal superblock); the htree writer.
* `ref/run.sh` (`ref/gen.py`, `ref/model.py`, `ref/run.bend`): images made
  by mke2fs 1.47.0 with `-O dir_index,has_journal,inline_data,ea_inode,
  metadata_csum` from random trees (`mke2fs -d`: a directory of 3000 long
  names with a 2-level index, others with tea and unsigned hashes and with
  legacy, inline files and directories, nested directories), indexed by
  `e2fsck -fD`, given attributes by debugfs (`ea_set`, values in the body,
  the block and EA inodes) and inline directory entries in system.data by
  `gen.py`. Lookups are compared with `debugfs stat`, listings with
  `debugfs ls -p`, contents with the trees (and debugfs `cat`), attributes
  with `debugfs ea_list` and the values set, 60 hashes an image with
  model.py (and 15 with `debugfs dx_hash`). Journals: four made by
  debugfs's journal commands (debugfs 1.47.0 has `logdump`, `journal_open`,
  `journal_write`, `journal_close` and `journal_run`; used with no
  checksums, csum_v2, csum_v3, 32- and 64-bit tags, 1 and 4 KiB blocks),
  and nine logs written by model.py's writer (random transactions of
  writes, revokes and re-writes, starting near the journal's end so they
  wrap, sequence numbers that wrap at 2^32, and endings: complete,
  incomplete, a bad commit, a bad descriptor, a bad data block, the strict
  option): each recovery is compared block by block with model.py's, which
  is checked against debugfs's `journal_run`; then (phase 2) the package's
  recovered image must pass `e2fsck -fn` and match `journal_run` and
  e2fsck's own replay on a copy. Five commits (none, v2, v3; 32- and
  64-bit; up to 300 blocks, escaped blocks, revokes) must be byte-identical
  to model.py's writer, and replayed by debugfs and by e2fsck they must give
  exactly the writes (and `e2fsck -fn` clean). Four htree builds (up to
  3500 names, a 2-level index, half MD4, TEA unsigned, legacy) must be
  byte-identical to model.py's writer; written into an image they must pass
  `e2fsck -fn` and `debugfs htree_dump`, and the package's lookups of every
  name (a sample) in them must find the right inode. 25 images, about 3400
  answers in phase 1 and 2000 in phase 2, 20 tool checks, with the default
  seed 2026; seed 7 passes too. model.py is written here from the same
  documents as the package, so it shares an author with it; it is checked
  against debugfs and e2fsck wherever they answer. It needs python3 and
  e2fsprogs (exit 77 without them); `run.bend` is built once and runs both
  query files.

## Speed and size

Measured natively (Bend 2.0.37, WSL2), on throwaway images (not in CI):

| Operation | Input | Time | Memory |
|---|---|---|---|
| `Ext4.lookup` | 1000 names in a directory of 50,000 (4 KiB blocks, 2-level index) | 13 s (13 ms a name) | 0.24 GB |
| `Ext4.list` (linear, ext2's) | the same directory | 1.6 s | 0.43 GB |
| `Ext4Journal.recover` | 100 transactions, 7582 blocks replayed (1 KiB, csum_v3) | 3.3 s | 0.26 GB beyond the 0.84 GB device |
| `Ext4Journal.commit` | 2000 blocks of 4 KiB | about 1 s | 0.8 GB (the blocks as Octets) |
| `Ext4Htree.build` | 10,000 entries; 40,000 entries | 2.5 s; 45 s | 0.08 GB; 0.29 GB |
| `check.bend` | | 0.1 s | |
| `ref/run.sh` | (a native build of `run.bend`, about 40 s, included) | about 70 s | 1 GB peak |

A lookup in a hashed directory reads the directory's root, its index nodes
and one leaf, whatever the directory's size; a linear search reads blocks
up to the name's. Recovery reads the log's header blocks in a first pass,
then each replayed block once, and writes it at once (a block at a time,
never the log as a whole). The htree writer sorts by insertion, so its time
grows with the square of the entries. Every loop over a block's entries, a
directory's leaves, the log's blocks, the plan and the writes is a tail
call; the index walk recurses on its depth (at most 3), and the model's
lookup and the laws' specifications recurse on the leaves. An `Octets`
holds about 150 bytes of memory a byte (bytes' storage), which dominates
the memory figures.

## Dependencies

`bytes`, `word64` (the commit block's 64-bit time, an attribute block's
number in its checksum), `blockdev` (devices), `ext2` (the reader this
package extends: superblock, descriptors, inodes, block maps and extents,
linear directories, ext2's checksums), and `crc` (only `check.bend`'s
CRC-32 of contents; the package's crc32c comes through ext2's `Ext2Csum`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes (natively), `ref/run.sh` 3422 answers on 25 images,
20 tool checks and 1981 answers on 4 built directories match (seed 7 too),
`scripts/deps.sh ext4` passes.
