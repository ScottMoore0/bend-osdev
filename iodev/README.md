# bend-osdev-iodev

Block devices whose operations are in `IO`: the interface, helpers that read
and write byte ranges across blocks or stream every block of a range,
adapters that run any of blockdev's devices (pure or owned) through it, a
disk image file read on demand (`FileDev`), a write overlay that makes
any IO device writable (`IOOverlay`), and a disk image file read and
written in place, of any size (`FileRW`, on file effects passed in as
template arguments: bend-osdev-fileio's, or Base's own once it has them).
A large image is never held in memory: a 64 MB image is read, or rewritten
in place, block by block in under 3 MB (below).

## Base's file API (Bend 2.0.37)

What a file-backed device can use, from Base (`base.bend` and its effects,
`effs/file_*.c` and `.js`):

| Def | What it does |
|---|---|
| `File.open(path, mode)` | `"r"` (read only), `"w"` (write; created, truncated), `"a"` (write; created, appended). No read-write mode. |
| `File.read_at(f, offset: U32, max: U32)` | a positioned read (`pread`): up to `max` bytes at `offset`, as `List<&2, U32>`; the file's position does not move; empty at or past the end |
| `File.read_bytes(f, max)`, `File.read(f, max)` | a sequential read from the position (bytes, or text) |
| `File.size(f)` | the size, as `U32` (fails with `EOVERFLOW` past 4 GiB) |
| `File.write_bytes(f, bytes)`, `File.write(f, text)` | a sequential write at the position (or the end, in `"a"`) |
| `File.close(f)` | |

Every operation on a handle hands the handle back beside its result, also on
failure, as blockdev's owned interface does. There is **no seek and no
positioned write**, and no mode that both reads and writes without
truncating. So:

* **reading at an offset: yes.** `FileDev.read_block` is one `File.read_at`
  (repeated if the system answers short), so a block is read when it is asked
  for;
* **writing a block in place: no.** `FileDev.write_block` fails with
  `DevFailed{30}` (`EROFS`). Writes go to an `IOOverlay` on the `FileDev`,
  and `FileDev.save` streams the whole device, writes included, to a new
  file, a block at a time;
* **sizes:** offsets and sizes are `U32`, so an image is at most 4 GiB - 1
  bytes.

### Filling the gaps: library effects, passed in

The Bend team keeps Base's effects to thin system-call wrappers and leaves
the rest to libraries (bendlang/bend#1430; a library effect reuses Base's
`File` handle, WONTFIX.txt #825, as bendlang/bend#1573 does).
**bend-osdev-fileio** is such a library: `FileIO.open_rw` (`O_RDWR`, no
truncation), `FileIO.write_at` (a `pwrite` loop), `FileIO.read_at` and
`FileIO.size` with 64-bit offsets and sizes (`W64`), and `FileIO.sync`
(`fsync`), each with a C side and a JavaScript side, on Base's `File`.

iodev does not import it. `FileRW` (filerw.bend) takes its five file
operations as template arguments, of exactly fileio's types, so this
package holds no foreign code and its proofs never meet an effect (a file
that imports a foreign def gets "relies on foreign code" from
`--check-only`). With fileio's effects passed in, `FileRW.write_block` is
one `pwrite` of the block, in place, and images past 4 GiB work; with the
Base-only defaults (`FileRW.base_*`), `FileRW` behaves as `FileDev`. If Base
gains the same effects (a draft proposal: `"r+"`, `File.write_at`, 64-bit
offsets and sizes), they are passed in place of fileio's and nothing here
changes.

`FileDev`, `FileOv` and `IOOverlay` are unchanged: the overlay is still
the way to write without touching the file.

## The IO interface

A device is a single-owner value `d` of a `Type` `D` (a file handle, or a
record holding one); every operation hands it back, whatever happens:

| Operation | Type |
|---|---|
| `block_size` | `D -> IO(D & Nat)` |
| `block_count` | `D -> IO(D & Nat)` (for whole-device helpers: `FileDev.save`, `IOOverlay.over`) |
| `read_block` | `D -> Nat -> IO(D & Result<&2, &2, DevError, Octets>)` |
| `write_block` | `D -> Nat -> Octets -> IO(D & Result<&2, &2, DevError, Unit>)` |

These are blockdev's owned interface with the answer in `IO`, and its
`DevError`. Helpers take the operations as template arguments, as blockdev's
do, so a helper is specialised to its device at compile time (a template's
type may be an `IO` function type; blockdev's README expected that it could
not). A template argument can itself be a template def applied to its
template arguments: `~IOOverlay.read_block(~FileDev, ~FileDev.read_block)`.

**Adapters.** Every pure device and every owned device is an IO device that
performs no effect: `IODev.of_pure_*` and `IODev.of_own_*` lift their
operations, and `IOMem.*` (MemDev) and `IOImg.*` (ImgDev) are those lifts,
named. The laws prove that the IO helpers on a lifted pure device answer
what blockdev's pure helpers answer, for every device and range.

## Files and API

| File | Holds |
|---|---|
| `span.bend` | `IOSpan`: block arithmetic (no device) |
| `iodev.bend` | the IO helpers and the adapters (`IODev.*`) |
| `mem.bend` | `IOMem.*` and `IOImg.*`: MemDev and ImgDev on the IO interface |
| `overlay.bend` | `IOOverlay`: a write overlay on any IO device |
| `filedev.bend` | `FileDev`: an image file read on demand; `FileDev.save` |
| `fileov.bend` | `FileOv.*`: an `IOOverlay` on a `FileDev`, its operations named |
| `filerw.bend` | `FileRW`: an image file read and written in place, of any size, on file effects passed as template arguments; the Base-only defaults `FileRW.base_*` |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`IOP.` lemmas) |
| `LAWS_write.bend`, `PROOF_write.bend` | the laws of `fold_blocks`, and of the reads and writes on `IOMem` (`IWP.` lemmas), checked in a process of their own |
| `check.bend` | a runnable check of every file (it writes two files in `/tmp`) |
| `ref/` | the differential tests (`gen.py`, `run.sh`, `cases.bend`, and `big.bend` over 4 GiB) and the size measurement (`measure.sh`, `measure.bend`, `measure_rw.bend`); they import bend-osdev-fileio for `FileRW`'s effects |

### span.bend

| Def | Meaning |
|---|---|
| `IOSpan{first, skip, count, slack}` | the blocks `first` to `first + count - 1` hold the range, which starts `skip` bytes into the first and ends `slack` bytes before the end of the last (the type is open) |
| `IOSpan.of(bs, off, len)` | the span of `len` bytes from byte offset `off`, on `bs`-byte blocks |
| `IOSpan.first`, `.skip`, `.count`, `.slack` | its fields |
| `IOSpan.offset(bs, n)` | the byte offset of block `n` |
| `IOSpan.blocks(bs, size)` | how many blocks hold `size` bytes (a final partial block counts) |

### iodev.bend

| Def | Meaning |
|---|---|
| `IODev.read_blocks(~D, ~read_block, count, d, first)` | `count` blocks from block `first`, joined; the first failure stops it |
| `IODev.read_bytes(~D, ~block_size, ~read_block, d, off, len)` | `len` bytes from byte offset `off`, reading only the blocks they span; zero bytes always succeed |
| `IODev.fold_blocks(~A, ~D, ~read_block, ~step, count, d, first, acc)` | streaming: `step(acc, block)` over `count` blocks, in order, one block held at a time (`A` a `Data` type) |
| `IODev.write_blocks(~D, ~write_block, count, d, bs, n, data)` | `count` blocks cut from `data`, written from block `n` |
| `IODev.write_bytes(~D, ~block_size, ~read_block, ~write_block, d, off, data)` | `data` written at byte offset `off`: the first and last blocks of its span are read (for the bytes around it), then every block of the span is written; a range past the end fails before anything is written; zero bytes always succeed |
| `IODev.of_own_size`, `IODev.of_own_read`, `IODev.of_own_write` | an owned device's operations on the IO interface |
| `IODev.of_pure_size`, `IODev.of_pure_read`, `IODev.of_pure_write` | a pure device's operations on the IO interface (through blockdev's `Dev.own_*`) |

### mem.bend

| Def | Meaning |
|---|---|
| `IOMem.block_size`, `IOMem.block_count`, `IOMem.read_block`, `IOMem.write_block` | a `MemDev` on the IO interface (the write is `MemDev.own_write_block`) |
| `IOImg.block_size`, `IOImg.block_count`, `IOImg.read_block`, `IOImg.write_block` | an `ImgDev` on the IO interface |

### overlay.bend

`IOOverlay<D>` is a device `D` with the blocks written since it was wrapped,
kept in an `XArray<Octets>` (bend-osdev-xarray) by block number; its fields
are internal.

| Def | Meaning |
|---|---|
| `IOOverlay.of(~D, d, bs, count)` | `d`, with nothing written, as a device of `count` blocks of `bs` bytes |
| `IOOverlay.over(~D, ~block_size, ~block_count, d)` | the same, with `d`'s own size and count (in `IO`) |
| `IOOverlay.base(~D, o)` | the device below; the written blocks are dropped |
| `IOOverlay.block_size(~D, o)`, `IOOverlay.block_count(~D, o)` | the IO interface |
| `IOOverlay.read_block(~D, ~read_block, o, n)` | the block last written at `n`, else block `n` of the device below |
| `IOOverlay.write_block(~D, o, n, data)` | `put`, in `IO` |
| `IOOverlay.put(~D, o, n, data)` | block `n` replaced in the overlay (no effect): exactly one block, and `n` below the count, else `DevBadLength` or `DevOutOfRange` and the overlay unchanged |

Block numbers are kept as `U32`: a device of 2^32 blocks or more would see
blocks 2^32 apart share an entry (no `FileDev` is that large).

### filedev.bend

| Def | Meaning |
|---|---|
| `FileDev` | an open image file (internal fields: the handle, block size, count) |
| `FileDevError` | `FileDevOpenFailed{code}`, `FileDevSizeFailed{code}` (the system's error number), `FileDevBadBlockSize{size}` |
| `FileDev.open(path, bs)` | the file, read only, as a device of `bs`-byte blocks (`bs` from 1 to `FileDev.max_block()`, 1 GiB): `IO(Result<&1, &1, FileDevError, FileDev>)` (`&1`, as the device is a `Type`) |
| `FileDev.close(d)` | |
| `FileDev.block_size`, `FileDev.block_count`, `FileDev.read_block` | the IO interface; a final partial block reads padded with zeros; a failed system read is `DevFailed{errno}` |
| `FileDev.write_block` | always `DevFailed{30}` (`EROFS`): Base has no positioned write |
| `FileDev.save(~D, ~block_count, ~read_block, d, path)` | every block of any IO device written, in order, to the file at `path` (created or truncated: not the file being read); one block in memory at a time; the device is handed back |
| `FileDev.max_block()` | 1 GiB |

The size is read when the file is opened; a file that grows or shrinks
while open is not noticed (a read past its new end reads zeros).

### filerw.bend

`FileRW` is an open image file (internal fields: the handle, block size,
count). Its file operations are template arguments, each of the type of
fileio's def named beside it (`W64` is bend-osdev-word64's):

| Template | Type | fileio | Base-only default |
|---|---|---|---|
| `~open` | `String -> IO(Result<&1, &1, U32 & String, File>)` | `FileIO.open_rw` | `FileRW.base_open`: `File.open(path, "r")` |
| `~size` | `File -> IO(File & Result<&1, &1, U32 & String, W64>)` | `FileIO.size` | `FileRW.base_size`: `File.size` (fails past 4 GiB) |
| `~read_at` | `File -> W64 -> U32 -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>)` | `FileIO.read_at` | `FileRW.base_read_at`: `File.read_at` below 4 GiB, else `EOVERFLOW` |
| `~write_at` | `File -> W64 -> List<&2, U32> -> IO(File & Result<&1, &1, U32 & String, Unit>)` | `FileIO.write_at` | `FileRW.base_write_at`: always `EROFS` (30) |
| `~sync` | `File -> IO(File & Result<&1, &1, U32 & String, Unit>)` | `FileIO.sync` | `FileRW.base_sync`: nothing to do |

| Def | Meaning |
|---|---|
| `FileRW.open(~open, ~size, path, bs)` | the file at `path`, opened with `~open`, as a device of `bs`-byte blocks (1 to `FileDev.max_block()`); `IO(Result<&1, &1, FileDevError, FileRW>)`; a bad block size fails before the file is opened |
| `FileRW.of(~size, f, bs)` | a file already open (any way) as such a device; on a failure the file is closed |
| `FileRW.close(d)` | |
| `FileRW.block_size`, `FileRW.block_count` | the IO interface |
| `FileRW.read_block(~read_at, d, n)` | block `n`, read from the file now; a final partial block reads padded with zeros; a failed system read is `DevFailed{errno}` |
| `FileRW.write_block(~write_at, d, n, data)` | block `n` written to the file now, in place: exactly one block and `n` below the count (else `DevBadLength`, `DevOutOfRange`, nothing written, as `IOOverlay.put`); the whole block is written, so a final partial block grows the file to a whole number of blocks; a failed system write is `DevFailed{errno}` |
| `FileRW.sync(~sync, d)` | the blocks written so far reach the device |

`FileRW.read_block` and `write_block`, applied to their effect, are the
template arguments the IO helpers take. On fileio:

```python
import bend-osdev-blockdev@0.1.0.0/blockdev.bend as D
import bend-osdev-fileio@0.1.0.0/fileio.bend as FIO
import bend-osdev-iodev@0.1.0.0/iodev.bend as V
import bend-osdev-iodev@0.1.0.0/filedev.bend as F
import bend-osdev-iodev@0.1.0.0/filerw.bend as R
...
  d : Result<&1, &1, F.FileDevError, R.FileRW> <- R.FileRW.open(~FIO.FileIO.open_rw, ~FIO.FileIO.size, "disk.img", 4096n)
  ...
  w : R.FileRW & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~R.FileRW, ~R.FileRW.block_size, ~R.FileRW.read_block(~FIO.FileIO.read_at), ~R.FileRW.write_block(~FIO.FileIO.write_at), d, off, data)
```

`FileDev.save` and every IO helper work on a `FileRW` as on any device.
Block offsets are computed as a `Nat` (`IOSpan.offset`) and passed as a
`W64`, so the image may be as large as the file system allows, up to
2^48 − 1 bytes natively (the largest `Nat` a native build holds) and
2^63 − 1 bytes on the JavaScript lane (`off_t`). The size is read when
the device is made.

### fileov.bend

| Def | Meaning |
|---|---|
| `FileOv.open(path, bs)` | `FileDev.open` under an empty `IOOverlay` |
| `FileOv.block_size`, `FileOv.block_count`, `FileOv.read_block`, `FileOv.write_block` | its IO interface, with plain parameters for template arguments |
| `FileOv.save(o, path)` | the device, writes included, as a new file |
| `FileOv.close(o)` | the file closed, the writes dropped |

## Extension points

* **Any IO device:** a partition of another device, a cache, a device that
  counts reads, a network block device: provide the operations for its type
  and pass them as template arguments. Every pure or owned device already is
  one, through `IODev.of_pure_*` / `of_own_*`.
* **The file effects under `FileRW`** are template arguments: fileio's
  (in place, any size), the Base-only defaults (`FileRW.base_*`), Base's own
  once it has a positioned write and 64-bit offsets, or any def of the same
  type (one that counts or fails writes, for a test; one over a network
  block device). `FileRW.of` takes a file opened any way.
* **Writing a file in place:** `FileRW` with fileio's effects. `FileDev`
  stays read-only, for callers that must not change the file, and the
  overlay over it keeps writes in memory until `FileDev.save`.
* **The overlay** works on any IO device; its store (an `XArray`) is
  internal and can change behind the same laws. A flush that writes the
  overlay's blocks to a device that can be written is a short addition.
* **Block arithmetic** (`span.bend`) has no device in it, so pure and owned
  helpers can share it.
* **Read strategy:** `read_bytes` reads exactly the blocks a range spans and
  `write_bytes` reads at most two; a caching or read-ahead device can be
  wrapped around a `FileDev` without changing either.

## Laws

`LAWS.bend` and `LAWS_write.bend` (each proof file checked in its own
process). A law about an IO action states what the action gives a
continuation `k`, for every `R` and `k`: the action run as `m(R, k)`.
Effects themselves (`FileDev`, and `FileRW` on any effects) are tested,
not proved.

**Block arithmetic, for every block size `1 + bp`, offset and length:**
`span_start` (`first * bs + skip == off`), `span_skip` (`skip < bs`),
`span_cover` (`count * bs == skip + len + slack`), `span_slack`
(`slack < bs`), `span_in_block` (an offset `n * bs + i`, `i < bs`, is in
block `n`, `i` bytes in), `blocks_cover` (`blocks(bs, size) * bs` is `size`
plus less than a block), `span_within` (a range inside the first `n` blocks,
`off + len <= n * bs`, has its span inside them: `first + count <= n`) and
`span_past` (a range that passes their end has a span that does too).
Proved from Base's definitions of `Nat.divmod` (the division lemmas are
ext2's).

**The adapters, for every pure device (`~D: Data` and its operations),
continuation, device and range:** `io_read_blocks` and `io_read_bytes`: the
IO helpers on the lifted device perform no effect, hand back the device
unchanged and answer what blockdev's `Dev.read_blocks` and `Dev.read_bytes`
answer; `io_mem_write_ok`: a good write through `IOMem` is
`MemDev.update` (from blockdev's `own_write_ok`). With blockdev's own laws,
the owned helpers answer the same, and blockdev's `LAWS_range.bend` says
what `Dev.read_blocks` and `Dev.read_bytes` compute (`read_bytes_image`, and
on a valid `MemDev` `read_blocks_mem` and `read_bytes_mem`). These two
proofs follow those public defs' definitions (they name no internal
helper); a change to how blockdev computes them, even one that keeps their
answers, would need the proofs redone (`io_mem_write_ok` uses blockdev's
law only).

**The overlay:** `ov_read_put`, for every device below (any `Type`, any
read): reading block `n` after a write of `n` that succeeded answers what was
written, without reading the device below; `ov_put_other`, for every pure
device below: a write of block `n` leaves the answer of every read of a
block `m` (with `n` and `m` distinct as `U32`) unchanged; `ov_read_fresh`:
an overlay with nothing written reads the device below. Proved through
xarray's laws (`load_store`, `load_store_other`, `load_empty`).

**Vectors:** a span; `IOSpan.blocks`; `read_bytes` across blocks and past
the end on `IOMem` and across blocks on `IOImg`; `write_bytes` then a read
back on `IOMem`; the same on an `IOOverlay` over a `MemDev`, and the device
below unchanged.

**Streaming and writing (`LAWS_write.bend`):**

* `io_fold_blocks`, for every pure device, step, accumulator,
  continuation and range: `IODev.fold_blocks` performs no effect, hands the
  device back, and answers the step folded, in order, over the blocks
  blockdev's `Dev.read_list` reads (`fold_list`, defined in the law file),
  or the first failed read;
* `io_mem_read_blocks`, `io_mem_read_bytes`: the same as `io_read_blocks`
  and `io_read_bytes` for `IOMem`'s own operations (`IOMem.read_block`,
  `IOMem.block_size`), which the kernel cannot identify with the lifted
  pure ones (no eta rule), so that the laws below compose with them;
* on `IOMem`, for every valid `MemDev` and continuation (`outcome`,
  `shape` and `failed`, defined in the law file, are what the laws look at:
  a write's answer and the device's image; whether the device is valid,
  its block size and count; the device and whether the answer failed):
  * `io_mem_write_blocks`, `io_mem_write_blocks_shape`: `count` blocks of
    data (`len(data) == count * bs`) written from block `first`, inside the
    device, succeed, leave the image patched at `first * bs` (blockdev's
    `Dev.patch`) and the device valid with its block size and count;
    `io_mem_write_blocks_read`: then reading the same blocks back gives
    the data;
  * `io_mem_write_bytes`, `io_mem_write_bytes_shape`: `data` written at
    `off`, inside the device, succeeds and leaves the image patched at
    `off`, the device valid with its block size and count, for every length
    (zero included) and every alignment; `io_mem_write_read`: reading
    `[off, off + len(data))` back gives `data`; `io_mem_write_before`,
    `io_mem_write_after`: every range wholly before, or wholly after and
    inside the device, reads as before the write;
  * `io_mem_write_past_end`: a nonempty write that passes the end, on
    blocks of `1 + bp` bytes, fails and hands the device back unchanged
    (the first block's read fails, or the last block's does, before any
    write).
  The proofs follow the read-modify-write over the span: the first and
  last blocks of the span read as slices of the image (blockdev's
  `read_block_mem`), the bytes kept around the data are the image's own
  (`take` of the first, `drop` of the last), the span's blocks are written
  one `MemDev.update` at a time (`to_octets_update`, `patch_patch`), and
  patching with the kept bytes is patching the data alone (`patch_keep`);
  the arithmetic is the span laws above.

**Vectors** (`LAWS_write.bend`): a fold that sums the block lengths, and a
`write_blocks` read back.

What is not proved: `write_bytes`, `write_blocks` and `fold_blocks` on the
other devices (`IOImg`, `IOOverlay`, `FileDev`, `FileRW`) are covered by
vectors and the differential test; the laws above are for `IOMem`
(`fold_blocks`: every pure device). The same proofs would carry over to a
device with laws like blockdev's `read_block_mem`, `to_octets_update` and
`own_write_ok`; `ImgDev` has read-after-write laws (`img_read_write`,
`img_write_other`) but no image function, so it would need its own.

**A note for the proof kernel.** `--verdict`'s kernel has no eta rule, so
the code writes each IO continuation it builds out in full
(`d2 => R => k => f(d2)(R, x => k(x))`) and the proofs do the same; a
lemma's statement that mentions a lambda returning IO is given as a def
(`IOP.tail`) so that it elaborates as the code does.

## Tests

* `check.bend`: every device and helper, including a `FileDev` on a file it
  writes, the overlay, `FileDev.save`, the open errors, and a `FileRW` on
  the Base-only defaults (reads, refused writes, bad lengths and blocks,
  the open errors).
* `ref/run.sh`: 40 random image files (sizes 0 to 6000 bytes, block sizes
  1 to 4096), each opened three ways, a `FileDev` under an overlay (read
  from the file on demand), a `MemDev` and, for block sizes that are
  multiples of 4, an `ImgDev`; then a random sequence of reads, writes
  across blocks (in range and past the end) and saves is run on each through
  the same IO helpers (518 operations at the default seed). A copy of each
  file is opened as a fourth device, a `FileRW` on bend-osdev-fileio's
  effects, and the same operations write it in place. Every answer is
  compared with a model in Python that reads the generated file back itself
  (`seek`, `read`), and every saved file with the model's image byte for
  byte; each copy written in place is compared byte for byte with Python's
  own copy, to which Python does every write that succeeds itself (`seek`,
  `write`; a write that reaches a final partial block pads it to a whole
  block, as `FileRW` writes whole blocks).
* `ref/run.sh`, over 4 GiB (`big.bend`): a sparse image of 5 GiB + 1234
  bytes (Python's `truncate`, in a fresh directory under `$TMPDIR`, default
  `/tmp`, removed afterwards), in 1000-byte blocks so that one block holds
  the 4 GiB mark, opened as a `FileRW` on fileio; its block count, then 29
  reads and writes before, across and past the mark and into the final
  partial block (which grows the file), against the same model on
  Python's own sparse copy, and the two files compared byte for byte over
  their data extents. Left out where the file system keeps no sparse
  files.
* Both parts pass natively and on the JavaScript lane (`BEND_LANE=js`), so
  fileio's C and JavaScript sides are both exercised; seeds 1 to 5 pass
  too.

## Sizes and speed

Measured natively (`ref/measure.sh`; Bend 2.0.37, WSL2, the image in the
Linux file system), not in CI: every block of a 64 MB file of random bytes
read through `FileDev` with `IODev.fold_blocks`, timed with
`/usr/bin/time -f "%es %MKB"`:

| Run | Time | Peak RAM |
|---|---|---|
| 16384 blocks of 4 KB, counted | 1.32 s | 2.8 MB |
| 16384 blocks of 4 KB, every byte summed and hashed (matches Python) | 6.05 s | 2.8 MB |
| 131072 blocks of 512 bytes, counted | 6.85 s | 3.3 MB |
| 131072 blocks of 512 bytes, summed and hashed | 12.7 s | 3.3 MB |
| 16384 blocks of 4 KB rewritten in place through `FileRW` on fileio (checked by Python) | 5.62 s | 2.7 MB |
| 131072 blocks of 512 bytes rewritten in place | 13.9 s | 2.4 MB |

Memory is one block and the runtime's 2 to 3 MB, whatever the image's size
(blockdev's `ImgDev` holds a 64 MB image in about 67 MB). A block read costs
one `pread` (on a helper thread) and the conversion of its bytes to
`Octets`, about 50 µs, and a block write one `pwrite` and the conversion
back (the rewrite also builds each block's bytes); small blocks are
dominated by that.

Image sizes: `FileDev` and `FileOv` are capped by Base at 4 GiB - 1 bytes;
`FileRW` on fileio has no cap of its own (tested at 5 to 8 GiB, above), up
to 2^48 - 1 bytes natively (the largest `Nat` a native build holds) and
2^63 - 1 on the JavaScript lane.

## Dependencies

`bytes` (Octets); `blockdev` (`DevError`, the pure and owned interfaces and
their helpers, `MemDev`, `ImgDev`, and its laws in the proofs); `xarray`
(the overlay's store, and its laws in the proofs); `word64` (`W64`, the
64-bit offsets and sizes in `FileRW`'s template types, so that fileio's
effects fit them). No other: fileio is imported only by the tests in
`ref/`, not by the package.

## Status

Bend 2.0.37: `PROOF.bend` and `PROOF_write.bend` ALL PROOFS CHECK,
`--verdict` ALL PROOFS CHECK (each in its own process),
`check.bend` passes, `ref/run.sh` 518 operations on 40 image files (43
saves, 40 files written in place) match and 29 operations on a 5 GiB
sparse image match, natively and on the JavaScript lane;
`scripts/deps.sh iodev` ok. `FileRW` adds no laws. The 64 MB measurements above were run
separately, natively.
