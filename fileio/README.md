# bend-osdev-fileio

Library effects on Base's `File` handle, for what Base 2.0.37 cannot do with
a file: open it for reading and writing without truncating it, write at an
offset, read at and size a file past 4 GiB, and flush it to the device.
With these, iodev's `FileRW` rewrites the blocks of a disk image in place,
on images of any size.

## Why a library

Base's file effects (2.0.37, and `main` at `e5527d5`) are `File.open` with
modes `"r"`, `"w"` (truncates) and `"a"` (appends), `File.read_at` with a
`U32` offset, `File.size` answering a `U32` (failing with `EOVERFLOW` past
4 GiB), and sequential reads and writes. There is no read-write mode that
keeps the file, no positioned write and no 64-bit offset.

The Bend team closed bendlang/bend#1430 (a `File.read_into`) on the grounds
that Base's effects are thin system-call wrappers over `U32`, `String`,
`List`, handles and `Result`, and that anything else belongs in libraries;
WONTFIX.txt (#825) adds that a custom effect reuses a Base handle type such
as `File`, and bendlang/bend#1573 reports a library effect shipped that way.
This package does the same: every effect is a foreign def (a def whose body
is `import "./fileio.c"` and `import "./fileio.js"`), shaped exactly as
Base's own `File.*` effects are (`bend2/base.bend` and `bend2/effs/file_*.c`,
`.js`): the handle first and handed back beside a `Result`, `Fail` carrying
the system's error number and message, the system call on a helper thread
in C. A handle from `FileIO.open` works with `File.read_bytes`,
`File.write_bytes` and `File.close`, and a handle from `File.open` works
here. The same proposals for Base itself are drafted separately, with this
package as working evidence.

## Specification

The system calls are POSIX's, as The Open Group Base Specifications
Issue 7 (IEEE Std 1003.1-2017) defines them: `open` (`O_RDWR`, `O_CREAT`),
`pread`, `pwrite`, `fstat` and `fsync`; on the JavaScript lane, Node's `fs`
module (`openSync`, `readSync` and `writeSync` with a `bigint` position,
`fstatSync` with `bigint: true`, `fsyncSync`), as Bun provides it. The
shape of each effect (how arguments arrive, how the handle and the
`Result` are built, the helper thread) follows Base's own file effects
(`bend2/effs/file_*.c`, `.js`, Apache-2.0), which were read as the model;
no Base source is copied. The C side uses only the runtime helpers Base's
effects use (`io_work`, `io_res`, `io_tup`, `io_hand`, `io_cbuf`,
`io_list`).

## Offsets and sizes: W64 outside, two U32 halves across

The public defs take a 64-bit offset and answer a 64-bit size as a `W64`
(bend-osdev-word64), as every bend-osdev package does for 64-bit values
(CONVENTIONS.md): callers compute offsets with `W64.add` and `W64.mul`, and
when Base gains a native `U64` only word64 changes.

At the effect boundary itself (`FileIO.eff.*`) an offset is two `U32`s, high
then low, and a size comes back as such a pair, because:

* **a `U32` is what Base's effects already pass.** It crosses to C as an
  unboxed machine word (`(u64)hi << 32 | lo`) and to JavaScript as a number
  (`BigInt(hi) << 32n | BigInt(lo)`, exact past 2^53), so nothing new is
  marshalled on either lane;
* **`W64` is opaque.** Its fields are word64's internals; C or JavaScript
  that took one apart would depend on them, and break when word64 changes.
  The halves come from `W64.hi`/`W64.lo` and go back through
  `W64.from_parts`, word64's public defs;
* **not a `Nat`.** A `Nat` has no fixed width (a native build holds one
  only up to 2^48 − 1), so the C side could not read it as a word.

`off.bend` holds the two conversions, and its laws prove that no offset is
changed on the way to an effect and no size on the way back.

## Files and API

| File | Holds |
|---|---|
| `fileio.bend` | the effects (`FileIO.eff.*`) and the interface on them (`FileIO.*`) |
| `fileio.c`, `fileio.js` | the effects' C side (native builds, `bend f.bend -o prog`) and JavaScript side (`bend f.bend`) |
| `off.bend` | `FileIO.off.*`: offsets and sizes between `W64` and the halves (pure) |
| `LAWS.bend`, `PROOF.bend` | the laws about `off.bend` and their proofs |
| `check.bend` | a runnable check of every effect (it writes two files in `/tmp`, and empties them) |
| `ref/` | the differential test against Python (`gen.py`, `run.sh`, `cases.bend`) |

### fileio.bend

Every effect answers `Fail{(errno, message)}` on failure, as Base's do.

| Def | Meaning |
|---|---|
| `FileIO.open(path: String, create: Bool) -> IO(Result<&1, &1, U32 & String, File>)` | `open(2)` with `O_RDWR`, never `O_TRUNC`: the file read and written from its start; a missing file is created (empty, mode 0644) when `create` is `True`, and fails with `ENOENT` when it is `False` |
| `FileIO.open_rw(path)` | the usual choice, `FileIO.open(path, False{})`: an existing file, in place (C's `"r+"`) |
| `FileIO.read_at(file: File, off: W64, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>)` | `pread(2)`: up to `max` bytes (at most 2^31 − 1) at `off`, fewer at the end, none past it; the position of the file does not move. As `File.read_at`, with a 64-bit offset |
| `FileIO.write_at(file: File, off: W64, data: List<&2, U32>) -> IO(File & Result<&1, &1, U32 & String, Unit>)` | `pwrite(2)`, repeated on short writes until every byte is written; a write that makes no progress fails with `EIO`, as Base's `File.write` does since #1445; a value past 255 fails with `EINVAL` before any byte is written; the file grows to hold the bytes (a gap reads as zeros); the position does not move |
| `FileIO.size(file: File) -> IO(File & Result<&1, &1, U32 & String, W64>)` | `fstat(2)`: the size, any size |
| `FileIO.sync(file: File) -> IO(File & Result<&1, &1, U32 & String, Unit>)` | `fsync(2)`: what has been written reaches the device |
| `FileIO.eff.open(path, create: U32)` | the effect under `FileIO.open` (`create` not 0: `O_CREAT`) |
| `FileIO.eff.read_at(file, hi: U32, lo: U32, max: U32)` | the effect under `FileIO.read_at`, the offset `hi * 2^32 + lo` |
| `FileIO.eff.write_at(file, hi: U32, lo: U32, data)` | the effect under `FileIO.write_at` |
| `FileIO.eff.size(file) -> IO(File & Result<&1, &1, U32 & String, U32 & U32>)` | the effect under `FileIO.size`: (high, low) |
| `FileIO.eff.sync(file)` | the effect under `FileIO.sync` |

An offset of 2^63 or more is past what `off_t` holds: reads fail with
`EINVAL`, and so do writes of at least one byte, on both lanes.

Bytes are `List<&2, U32>` here, not `Octets`, because these are Base's own
I/O shapes (`File.read_bytes`, `File.read_at`, `File.write_bytes`): a caller
of Base's defs can switch to these without converting, a device written
against these types (iodev's `FileRW`) takes Base's own defs once they
exist, and the package needs no `bytes`. Errors are Base's `U32 & String`
for the same reason: they are the system's error numbers, not failures to
parse input. There is no streaming interface beyond the effects
themselves: positioned reads and writes already take a file a piece at a
time, at any offset.

### off.bend

| Def | Meaning |
|---|---|
| `FileIO.off.halves(v: W64) -> U32 & U32` | (high 32 bits, low 32 bits), as an effect takes an offset |
| `FileIO.off.join(p: U32 & U32) -> W64` | the word with those halves, as an effect answers a size |
| `FileIO.off.of_u32(o: U32) -> W64` | a 32-bit offset (as Base's `File.read_at` takes) as a 64-bit one |
| `FileIO.off.fits32(v: W64) -> Bool` | whether the word is below 2^32, so Base's 32-bit defs could take it |

## Using it

```python
import Base
import bend-osdev-word64@0.1.0.0/word64.bend as W
import bend-osdev-fileio@0.1.0.0/fileio.bend as F

def done(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, x) = r
  File.close(f)

# three bytes written at 4 GiB + 512, in place
def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, F.FileIO.open_rw("disk.img"))
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.from_parts(1, 512), [1, 2, 3])
    done(w)
```

A file that imports `fileio.bend` gets the verdict "N defs rely on unsafe or
foreign code" from `--check-only`, as with any foreign effect: the checker
reads an effect's type, never its code, and treats it as a promise, as it
does `@unsafe`. So proofs should not import `fileio.bend`: this package's
`PROOF.bend` imports only `off.bend`, and iodev's `FileRW` takes these
effects as template arguments, so iodev's proofs never see them.

## Extension points

* **Other effects on the same handle** (`ftruncate`, `fallocate`,
  `posix_fadvise`, `O_DIRECT`) follow the same pattern: a `FileIO.eff.*` def
  importing `fileio.c` and `fileio.js`, a `#ifdef CID(...)` block in the C
  side (so an unused effect is not compiled) and a function in the
  JavaScript side, with a `W64` def above it if it takes an offset.
* **Replacing an effect:** a caller that takes these defs as template
  arguments (as iodev's `FileRW` does) can pass any def of the same type:
  Base's own, once Base has them, or a test double that records calls or
  injects failures.
* **The offset representation** is `off.bend`'s alone; the laws pin down
  what it must do.

## Laws

`LAWS.bend` (draft, not yet reviewed by the maintainer), for `off.bend`
only; the effects themselves are tested, not proved (below), as nuxyel's
library effect is.

**Properties, for every input:** `off_join_halves` (a word's halves joined
are the word), `off_halves_join` (a joined pair splits back into it),
`off_of_u32` (a 32-bit offset's halves are 0 and itself),
`off_fits32_of_u32`. Proved from word64's interface laws (`parts_of`,
`hi_from_parts`, `lo_from_parts`), never from the inside of `W64`.

**Vectors:** `off_halves_carry` ((2^32 − 1) + 6 has halves 1 and 5),
`off_halves_max`, `off_fits32_past`.

## Tests

* `check.bend`: every effect, natively and on the JavaScript lane, on a
  file in `/tmp`: a read-write open that keeps the file, writes and reads at
  offsets, a write at 4 GiB + 5 (the file becomes sparse, 4 GiB + 7 bytes)
  and a read across the 4 GiB mark, `File.read_bytes` on a `FileIO` handle,
  a value past 255, an offset past 2^63, `sync`, a missing file with and
  without `create`, and an open with `create` that keeps an existing file.
* `ref/run.sh`: 31 files in a fresh directory under `$TMPDIR` (default
  `/tmp`), removed afterwards: 30 small ones (0 to 5000 bytes, some missing
  and created by the open, some missing and failing) and one sparse file of
  5 GiB + 1234 bytes (made with Python's `truncate`), each opened with
  `FileIO.open` and given random positioned reads, writes (in place, past
  the end, over holes), sizes and syncs; the big one also reads and writes
  across the 4 GiB mark, past it and past its end, growing it to over
  8 GiB. Python does the same operations to its own copy of each file
  (`seek`, `read`, `write`), and every answer is compared, then every file
  with Python's copy, byte for byte (sparse files over the union of their
  data extents, from `SEEK_DATA`/`SEEK_HOLE`; outside them both are
  zeros). If the file system does not keep the big file sparse, it is left
  out and the count says so. 543 operations at the default seed; seeds 1
  to 3 pass too, natively and on the JavaScript lane.

## Dependencies

`word64` (`W64`, and its laws in the proofs). No other.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes natively and on the JavaScript lane, `ref/run.sh` 543
operations on 31 files, the 5 GiB sparse file included, match on both
lanes, every file byte for byte; `scripts/deps.sh fileio` ok. Laws: a draft,
not yet reviewed by the maintainer. Linux (WSL2) only so far; the C and
JavaScript sides use only POSIX calls and Node's `fs`, as Base's do, but
macOS is untested.
