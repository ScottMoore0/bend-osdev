# bend-osdev-iodev: a disk image file as a block device that is written in
# place, of any size (past 4 GiB too). A block is read from the file when
# it is asked for and written back to the file when it is written, so the
# image is never held in memory and no overlay is needed.
#
# Base 2.0.37 cannot do this alone (see filedev.bend): it has no read-write
# open, no positioned write and only 32-bit offsets. So FileRW takes its
# file operations as template arguments, with 64-bit offsets and sizes as
# W64 (bend-osdev-word64):
#
#   ~open:     String -> IO(Result<&1, &1, U32 & String, File>)
#   ~size:     File -> IO(File & Result<&1, &1, U32 & String, W64>)
#   ~read_at:  File -> W64 -> U32 -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>)
#   ~write_at: File -> W64 -> List<&2, U32> -> IO(File & Result<&1, &1, U32 & String, Unit>)
#   ~sync:     File -> IO(File & Result<&1, &1, U32 & String, Unit>)
#
# bend-osdev-fileio's FileIO.open_rw, FileIO.size, FileIO.read_at,
# FileIO.write_at and FileIO.sync have exactly these types, and so would
# Base's own if it gained them; this file holds no foreign code. The
# FileRW.base_* defaults use only Base 2.0.37: the file opened read-only,
# offsets and sizes below 4 GiB, writes refused (EROFS), as FileDev.
#
# A final partial block reads padded with zeros, as FileDev's does; a write
# of it writes the whole block, so the file grows to a whole number of
# blocks. The size is read when the device is made.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../word64/word64.bend as W
import ./span.bend as S
import ./filedev.bend as F

type FileRW is Type:
  FileRW{file: File, block_size: Nat, count: Nat}

# The defaults, from Base 2.0.37 alone

# Base's File.open, read-only (Base has no read-write mode that keeps the
# file)
def FileRW.base_open(path: String) -> IO(Result<&1, &1, U32 & String, File>):
  File.open(path, "r")

def FileRW.base_size.got(r: File & Result<&1, &1, U32 & String, U32>) -> IO(File & Result<&1, &1, U32 & String, W.W64>):
  (f, res) = r
  match res:
    case Done{n}:
      IO.pure(File & Result<&1, &1, U32 & String, W.W64>, (f, Done{W.W64.from_u32(n)}))
    case Fail{e}:
      IO.pure(File & Result<&1, &1, U32 & String, W.W64>, (f, Fail{e}))

# Base's File.size, which fails (EOVERFLOW) past 4 GiB
def FileRW.base_size(f: File) -> IO(File & Result<&1, &1, U32 & String, W.W64>):
  IO.bind(File & Result<&1, &1, U32 & String, U32>, File & Result<&1, &1, U32 & String, W.W64>, File.size(f), FileRW.base_size.got)

def FileRW.base_read_at.pick(low: Bool, f: File, lo: U32, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  match low:
    case True{}:
      File.read_at(f, lo, max)
    case False{}:
      IO.pure(File & Result<&1, &1, U32 & String, List<&2, U32>>, (f, Fail{(75, "an offset past 4 GiB")}))

def FileRW.base_read_at.go(f: File, +off: W.W64, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  FileRW.base_read_at.pick(U32.is_eq(W.W64.hi(off), 0), f, W.W64.lo(off), max)

# Base's File.read_at, for offsets below 4 GiB; past it EOVERFLOW (plain
# parameters, so it fits the template type)
def FileRW.base_read_at(f: File, off: W.W64, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  FileRW.base_read_at.go(f, off, max)

# always EROFS: Base has no positioned write
def FileRW.base_write_at(f: File, off: W.W64, data: List<&2, U32>) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  IO.pure(File & Result<&1, &1, U32 & String, Unit>, (f, Fail{(30, "Base has no positioned write")}))

# nothing to flush: the defaults never write
def FileRW.base_sync(f: File) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  IO.pure(File & Result<&1, &1, U32 & String, Unit>, (f, Done{Unit{}}))

# Making a device

def FileRW.of.sized(+bs: Nat, r: File & Result<&1, &1, U32 & String, W.W64>) -> IO(Result<&1, &1, F.FileDevError, FileRW>):
  (f, res) = r
  match res:
    case Done{size}:
      IO.pure(Result<&1, &1, F.FileDevError, FileRW>, Done{FileRW{f, bs, S.IOSpan.blocks(bs, W.W64.to_nat(size))}})
    case Fail{(code, msg)}:
      IO.bind(Unit, Result<&1, &1, F.FileDevError, FileRW>, File.close(f), u => IO.pure(Result<&1, &1, F.FileDevError, FileRW>, Fail{F.FileDevSizeFailed{code}}))

def FileRW.bs_ok(+bs: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, bs), Nat.is_le(bs, F.FileDev.max_block()))

def FileRW.of.check(~size: File -> IO(File & Result<&1, &1, U32 & String, W.W64>), ok: Bool, f: File, +bs: Nat) -> IO(Result<&1, &1, F.FileDevError, FileRW>):
  match ok:
    case True{}:
      IO.bind(File & Result<&1, &1, U32 & String, W.W64>, Result<&1, &1, F.FileDevError, FileRW>, size(f), FileRW.of.sized(bs))
    case False{}:
      IO.bind(Unit, Result<&1, &1, F.FileDevError, FileRW>, File.close(f), u => IO.pure(Result<&1, &1, F.FileDevError, FileRW>, Fail{F.FileDevBadBlockSize{bs}}))

# an open file as a device of bs-byte blocks (bs from 1 to
# FileDev.max_block()), its size taken now; on a failure the file is closed
def FileRW.of(~size: File -> IO(File & Result<&1, &1, U32 & String, W.W64>), f: File, +bs: Nat) -> IO(Result<&1, &1, F.FileDevError, FileRW>):
  FileRW.of.check(~size, FileRW.bs_ok(bs), f, bs)

def FileRW.open.got(~size: File -> IO(File & Result<&1, &1, U32 & String, W.W64>), +bs: Nat, r: Result<&1, &1, U32 & String, File>) -> IO(Result<&1, &1, F.FileDevError, FileRW>):
  match r:
    case Done{f}:
      FileRW.of(~size, f, bs)
    case Fail{(code, msg)}:
      IO.pure(Result<&1, &1, F.FileDevError, FileRW>, Fail{F.FileDevOpenFailed{code}})

def FileRW.open.check(~open: String -> IO(Result<&1, &1, U32 & String, File>), ~size: File -> IO(File & Result<&1, &1, U32 & String, W.W64>), ok: Bool, path: String, +bs: Nat) -> IO(Result<&1, &1, F.FileDevError, FileRW>):
  match ok:
    case True{}:
      IO.bind(Result<&1, &1, U32 & String, File>, Result<&1, &1, F.FileDevError, FileRW>, open(path), FileRW.open.got(~size, bs))
    case False{}:
      IO.pure(Result<&1, &1, F.FileDevError, FileRW>, Fail{F.FileDevBadBlockSize{bs}})

# the file at path, opened with ~open, as a device of bs-byte blocks; a bad
# block size fails before the file is opened
def FileRW.open(~open: String -> IO(Result<&1, &1, U32 & String, File>), ~size: File -> IO(File & Result<&1, &1, U32 & String, W.W64>), path: String, +bs: Nat) -> IO(Result<&1, &1, F.FileDevError, FileRW>):
  FileRW.open.check(~open, ~size, FileRW.bs_ok(bs), path, bs)

def FileRW.close(d: FileRW) -> IO(Unit):
  match d:
    case FileRW{f, bs, c}:
      File.close(f)

# The IO interface

def FileRW.block_size(d: FileRW) -> IO(FileRW & Nat):
  match d:
    case FileRW{f, +bs, c}:
      IO.pure(FileRW & Nat, (FileRW{f, bs, c}, bs))

def FileRW.block_count(d: FileRW) -> IO(FileRW & Nat):
  match d:
    case FileRW{f, bs, +c}:
      IO.pure(FileRW & Nat, (FileRW{f, bs, c}, c))

# want bytes from offset off onto acc: positioned reads until they are all
# read, or the end of the file (the rest then zeros); a read that does not
# end the loop gives at least one byte, so want is enough fuel. Each answer
# is taken by FileDev's own step (FileDev.read.got).
def FileRW.read.more(~read_at: File -> W.W64 -> U32 -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>), fuel: Nat, f: File, +off: Nat, +want: Nat, acc: B.Octets) -> IO(File & Result<&2, &2, D.DevError, B.Octets>):
  match fuel:
    case 0n:
      IO.pure(File & Result<&2, &2, D.DevError, B.Octets>, (f, Done{B.Octets.append(acc, B.Octets.zeros(want))}))
    case 1n+g:
      IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>, File & Result<&2, &2, D.DevError, B.Octets>, read_at(f, W.W64.from_nat(off), U32.from_nat(want)), r => F.FileDev.read.got(want, acc, r, f2 => +n => acc2 => FileRW.read.more(~read_at, g, f2, Nat.add(off, n), Nat.sub(want, n), acc2)))

def FileRW.read.fin(+bs: Nat, +c: Nat, r: File & Result<&2, &2, D.DevError, B.Octets>) -> IO(FileRW & Result<&2, &2, D.DevError, B.Octets>):
  (f, res) = r
  IO.pure(FileRW & Result<&2, &2, D.DevError, B.Octets>, (FileRW{f, bs, c}, res))

def FileRW.read.check(~read_at: File -> W.W64 -> U32 -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>), ok: Bool, f: File, +bs: Nat, +c: Nat, +n: Nat) -> IO(FileRW & Result<&2, &2, D.DevError, B.Octets>):
  match ok:
    case True{}:
      IO.bind(File & Result<&2, &2, D.DevError, B.Octets>, FileRW & Result<&2, &2, D.DevError, B.Octets>, FileRW.read.more(~read_at, bs, f, S.IOSpan.offset(bs, n), bs, B.Octets.empty()), FileRW.read.fin(bs, c))
    case False{}:
      IO.pure(FileRW & Result<&2, &2, D.DevError, B.Octets>, (FileRW{f, bs, c}, Fail{D.DevOutOfRange{n}}))

def FileRW.read_block.go(~read_at: File -> W.W64 -> U32 -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>), d: FileRW, +n: Nat) -> IO(FileRW & Result<&2, &2, D.DevError, B.Octets>):
  match d:
    case FileRW{f, +bs, +c}:
      FileRW.read.check(~read_at, Nat.is_lt(n, c), f, bs, c, n)

# block n, read from the file now
def FileRW.read_block(~read_at: File -> W.W64 -> U32 -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>), d: FileRW, n: Nat) -> IO(FileRW & Result<&2, &2, D.DevError, B.Octets>):
  FileRW.read_block.go(~read_at, d, n)

def FileRW.wrote(+bs: Nat, +c: Nat, r: File & Result<&1, &1, U32 & String, Unit>) -> IO(FileRW & Result<&2, &2, D.DevError, Unit>):
  (f, res) = r
  match res:
    case Done{u}:
      IO.pure(FileRW & Result<&2, &2, D.DevError, Unit>, (FileRW{f, bs, c}, Done{Unit{}}))
    case Fail{(code, msg)}:
      IO.pure(FileRW & Result<&2, &2, D.DevError, Unit>, (FileRW{f, bs, c}, Fail{D.DevFailed{code}}))

def FileRW.write.check(~write_at: File -> W.W64 -> List<&2, U32> -> IO(File & Result<&1, &1, U32 & String, Unit>), okl: Bool, okn: Bool, f: File, +bs: Nat, +c: Nat, +n: Nat, +data: B.Octets) -> IO(FileRW & Result<&2, &2, D.DevError, Unit>):
  match okl okn:
    case True{} True{}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>, FileRW & Result<&2, &2, D.DevError, Unit>, write_at(f, W.W64.from_nat(S.IOSpan.offset(bs, n)), B.Octets.to_list(data)), FileRW.wrote(bs, c))
    case False{} _:
      IO.pure(FileRW & Result<&2, &2, D.DevError, Unit>, (FileRW{f, bs, c}, Fail{D.DevBadLength{bs, B.Octets.len(data)}}))
    case True{} False{}:
      IO.pure(FileRW & Result<&2, &2, D.DevError, Unit>, (FileRW{f, bs, c}, Fail{D.DevOutOfRange{n}}))

def FileRW.write_block.go(~write_at: File -> W.W64 -> List<&2, U32> -> IO(File & Result<&1, &1, U32 & String, Unit>), d: FileRW, +n: Nat, +data: B.Octets) -> IO(FileRW & Result<&2, &2, D.DevError, Unit>):
  match d:
    case FileRW{f, +bs, +c}:
      FileRW.write.check(~write_at, Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c), f, bs, c, n, data)

# block n written to the file now, in place: data must be exactly one
# block and block n must exist (as IOOverlay.put), else nothing is written;
# a failed system write is DevFailed{errno}
def FileRW.write_block(~write_at: File -> W.W64 -> List<&2, U32> -> IO(File & Result<&1, &1, U32 & String, Unit>), d: FileRW, n: Nat, data: B.Octets) -> IO(FileRW & Result<&2, &2, D.DevError, Unit>):
  FileRW.write_block.go(~write_at, d, n, data)

# the blocks written so far reach the device (~sync; fileio's is fsync)
def FileRW.sync(~sync: File -> IO(File & Result<&1, &1, U32 & String, Unit>), d: FileRW) -> IO(FileRW & Result<&2, &2, D.DevError, Unit>):
  match d:
    case FileRW{f, +bs, +c}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>, FileRW & Result<&2, &2, D.DevError, Unit>, sync(f), FileRW.wrote(bs, c))
