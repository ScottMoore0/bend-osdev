# bend-osdev-iodev

Block devices whose operations are in `IO`: the interface, helpers that read
and write byte ranges across blocks or stream every block of a range,
adapters that run any of blockdev's devices (pure or owned) through it, a
disk image file read on demand (`FileDev`), and a write overlay that makes
any IO device writable (`IOOverlay`). A large image is never held in
memory: a 64 MB image is read block by block in under 3 MB (below).

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

### What Base would need (a draft note, not posted)

> A block device over an image file needs to rewrite blocks in place. Base
> 2.0.37 can read at an offset (`File.read_at`) but cannot write at one:
> `File.open` has no read-write mode that keeps the file (`"w"` truncates,
> `"a"` only appends) and there is no `File.seek`. Two additions would
> cover it: a mode `"r+"` (`O_RDWR`, no create, no truncate), and
> `File.write_at(file, offset: U32, data: List<&2, U32>) -> IO(File &
> Result<&1, &1, U32 & String, Unit>)`, a `pwrite` loop shaped like
> `File.write_bytes`, the position unchanged as with `read_at`. A
> `File.sync(file)` (`fsync`) would let a writer order its writes
> (a journal before its commit block). For images past 4 GiB, `read_at` and
> `write_at` would need a 64-bit offset (`Nat`, or two `U32`s) and
> `File.size` a 64-bit answer.

With those, `FileDev.write_block` becomes one `write_at`, and the overlay is
needed only for writes that must not reach the file.

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
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`IOP.` lemmas) |
| `check.bend` | a runnable check of every file (it writes two files in `/tmp`) |
| `ref/` | the differential test (`gen.py`, `run.sh`, `cases.bend`) and the size measurement (`measure.sh`, `measure.bend`) |

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
* **Writing a file in place:** when Base gains a positioned write, only
  `FileDev.write_block` changes (and `FileDev.open` opens read-write); the
  interface, helpers and laws stay.
* **The overlay** works on any IO device; its store (an `XArray`) is
  internal and can change behind the same laws. A flush that writes the
  overlay's blocks to a device that can be written is a short addition.
* **Block arithmetic** (`span.bend`) has no device in it, so pure and owned
  helpers can share it.
* **Read strategy:** `read_bytes` reads exactly the blocks a range spans and
  `write_bytes` reads at most two; a caching or read-ahead device can be
  wrapped around a `FileDev` without changing either.

## Laws

`LAWS.bend` (draft, not yet reviewed by the maintainer). A law about an IO
action states what the action gives a continuation `k`, for every `R` and
`k`: the action run as `m(R, k)`. Effects themselves (`FileDev`) are
tested, not proved.

**Block arithmetic, for every block size `1 + bp`, offset and length:**
`span_start` (`first * bs + skip == off`), `span_skip` (`skip < bs`),
`span_cover` (`count * bs == skip + len + slack`), `span_slack`
(`slack < bs`), `span_in_block` (an offset `n * bs + i`, `i < bs`, is in
block `n`, `i` bytes in), `blocks_cover` (`blocks(bs, size) * bs` is `size`
plus less than a block). Proved from Base's definitions of `Nat.divmod` (the
division lemmas are ext2's).

**The adapters, for every pure device (`~D: Data` and its operations),
continuation, device and range:** `io_read_blocks` and `io_read_bytes`: the
IO helpers on the lifted device perform no effect, hand back the device
unchanged and answer what blockdev's `Dev.read_blocks` and `Dev.read_bytes`
answer; `io_mem_write_ok`: a good write through `IOMem` is
`MemDev.update` (from blockdev's `own_write_ok`). With blockdev's own laws,
the owned helpers answer the same. blockdev has no law that says what
`Dev.read_blocks` and `Dev.read_bytes` compute for every input, so these two
proofs follow those public defs' definitions (they name no internal helper);
a change to how blockdev computes them, even one that keeps their answers,
would need the proofs redone (`io_mem_write_ok` uses blockdev's law only).

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

`write_bytes`, `fold_blocks` and `write_blocks` are covered by vectors and
the differential test, not by laws for every input.

**A note for the proof kernel.** `--verdict`'s kernel has no eta rule, so
the code writes each IO continuation it builds out in full
(`d2 => R => k => f(d2)(R, x => k(x))`) and the proofs do the same; a
lemma's statement that mentions a lambda returning IO is given as a def
(`IOP.tail`) so that it elaborates as the code does.

## Tests

* `check.bend`: every device and helper, including a `FileDev` on a file it
  writes, the overlay, `FileDev.save`, and the open errors.
* `ref/run.sh`: 40 random image files (sizes 0 to 6000 bytes, block sizes
  1 to 4096), each opened three ways, a `FileDev` under an overlay (read
  from the file on demand), a `MemDev` and, for block sizes that are
  multiples of 4, an `ImgDev`; then a random sequence of reads, writes
  across blocks (in range and past the end) and saves is run on each through
  the same IO helpers (518 operations at the default seed). Every answer is
  compared with a model in Python that reads the generated file back itself
  (`seek`, `read`), and every saved file with the model's image byte for
  byte. Seeds 1 to 5 pass too.

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

Memory is one block and the runtime's 2 to 3 MB, whatever the image's size
(blockdev's `ImgDev` holds a 64 MB image in about 67 MB). A block read costs
one `pread` (on a helper thread) and the conversion of its bytes to
`Octets`, about 50 µs; small blocks are dominated by that.

## Dependencies

`bytes` (Octets); `blockdev` (`DevError`, the pure and owned interfaces and
their helpers, `MemDev`, `ImgDev`, and its laws in the proofs); `xarray`
(the overlay's store, and its laws in the proofs). No other.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 518 operations on 40 image files (43
saves) match, `scripts/deps.sh iodev` ok. Laws: a draft, not yet reviewed
by the maintainer. The 64 MB measurement above was run separately,
natively.
