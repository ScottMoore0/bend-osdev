# bend-osdev-iodev: a disk image file as a block device on the IO
# interface, read on demand: a block is read from the file when it is asked
# for (Base's File.read_at, a positioned read), so the image is never held
# in memory. The file's size is taken when it is opened; a final partial
# block reads padded with zeros, as MemDev.of_octets pads.
#
# Writing: Base 2.0.37 opens a file for reading ("r"), or for writing from
# the start ("w", which truncates) or the end ("a"), and has no positioned
# write, so a block cannot be written back in place. FileDev.write_block
# therefore fails (DevFailed{30}, EROFS); write through an IOOverlay and
# stream the result to a new file with FileDev.save.
#
# Limits: Base's offsets and sizes are U32, so an image is at most
# 4 GiB - 1 bytes; a block is at most 1 GiB.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./span.bend as S

type FileDevError is Data:
  FileDevOpenFailed{code: U32}
  FileDevSizeFailed{code: U32}
  FileDevBadBlockSize{size: Nat}

type FileDev is Type:
  FileDev{file: File, block_size: Nat, count: Nat}

# the largest block size open accepts (1 GiB)
def FileDev.max_block() -> Nat:
  1073741824n

# Opening and closing

def FileDev.open.sized(+bs: Nat, r: File & Result<&1, &1, U32 & String, U32>) -> IO(Result<&1, &1, FileDevError, FileDev>):
  (f, res) = r
  match res:
    case Done{size}:
      IO.pure(Result<&1, &1, FileDevError, FileDev>, Done{FileDev{f, bs, S.IOSpan.blocks(bs, U32.to_nat(size))}})
    case Fail{(code, msg)}:
      IO.bind(Unit, Result<&1, &1, FileDevError, FileDev>, File.close(f), u => IO.pure(Result<&1, &1, FileDevError, FileDev>, Fail{FileDevSizeFailed{code}}))

def FileDev.open.got(+bs: Nat, r: Result<&1, &1, U32 & String, File>) -> IO(Result<&1, &1, FileDevError, FileDev>):
  match r:
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, U32>, Result<&1, &1, FileDevError, FileDev>, File.size(f), FileDev.open.sized(bs))
    case Fail{(code, msg)}:
      IO.pure(Result<&1, &1, FileDevError, FileDev>, Fail{FileDevOpenFailed{code}})

def FileDev.open.check(ok: Bool, path: String, +bs: Nat) -> IO(Result<&1, &1, FileDevError, FileDev>):
  match ok:
    case True{}:
      IO.bind(Result<&1, &1, U32 & String, File>, Result<&1, &1, FileDevError, FileDev>, File.open(path, "r"), FileDev.open.got(bs))
    case False{}:
      IO.pure(Result<&1, &1, FileDevError, FileDev>, Fail{FileDevBadBlockSize{bs}})

# the file at path, read-only, as a device of bs-byte blocks (bs from 1 to
# FileDev.max_block())
def FileDev.open(path: String, +bs: Nat) -> IO(Result<&1, &1, FileDevError, FileDev>):
  FileDev.open.check(Bool.and(Nat.is_lt(0n, bs), Nat.is_le(bs, FileDev.max_block())), path, bs)

def FileDev.close(d: FileDev) -> IO(Unit):
  match d:
    case FileDev{f, bs, c}:
      File.close(f)

# The IO interface

def FileDev.block_size(d: FileDev) -> IO(FileDev & Nat):
  match d:
    case FileDev{f, +bs, c}:
      IO.pure(FileDev & Nat, (FileDev{f, bs, c}, bs))

def FileDev.block_count(d: FileDev) -> IO(FileDev & Nat):
  match d:
    case FileDev{f, bs, +c}:
      IO.pure(FileDev & Nat, (FileDev{f, bs, c}, c))

def FileDev.read.pick(eof: Bool, short: Bool, f: File, +want: Nat, acc: B.Octets, +n: Nat, xs: List<&2, U32>, k: File -> Nat -> B.Octets -> IO(File & Result<&2, &2, D.DevError, B.Octets>)) -> IO(File & Result<&2, &2, D.DevError, B.Octets>):
  match eof short:
    case True{} _:
      IO.pure(File & Result<&2, &2, D.DevError, B.Octets>, (f, Done{B.Octets.append(acc, B.Octets.zeros(want))}))
    case False{} False{}:
      IO.pure(File & Result<&2, &2, D.DevError, B.Octets>, (f, Done{B.Octets.append(acc, B.Octets.of_list(xs))}))
    case False{} True{}:
      k(f, n, B.Octets.append(acc, B.Octets.of_list(xs)))

def FileDev.read.got(+want: Nat, acc: B.Octets, r: File & Result<&1, &1, U32 & String, List<&2, U32>>, k: File -> Nat -> B.Octets -> IO(File & Result<&2, &2, D.DevError, B.Octets>)) -> IO(File & Result<&2, &2, D.DevError, B.Octets>):
  (f, res) = r
  match res:
    case Done{+xs}:
      +n = B.len.fast(xs)
      FileDev.read.pick(Nat.is_eq(n, 0n), Nat.is_lt(n, want), f, want, acc, n, xs, k)
    case Fail{(code, msg)}:
      IO.pure(File & Result<&2, &2, D.DevError, B.Octets>, (f, Fail{D.DevFailed{code}}))

# want bytes from offset off onto acc: positioned reads until they are all
# read, or the end of the file (the rest then zeros); a read that does not
# end the loop gives at least one byte, so want is enough fuel
def FileDev.read.more(fuel: Nat, f: File, +off: Nat, +want: Nat, acc: B.Octets) -> IO(File & Result<&2, &2, D.DevError, B.Octets>):
  match fuel:
    case 0n:
      IO.pure(File & Result<&2, &2, D.DevError, B.Octets>, (f, Done{B.Octets.append(acc, B.Octets.zeros(want))}))
    case 1n+g:
      IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>, File & Result<&2, &2, D.DevError, B.Octets>, File.read_at(f, U32.from_nat(off), U32.from_nat(want)), r => FileDev.read.got(want, acc, r, f2 => +n => acc2 => FileDev.read.more(g, f2, Nat.add(off, n), Nat.sub(want, n), acc2)))

def FileDev.read.fin(+bs: Nat, +c: Nat, r: File & Result<&2, &2, D.DevError, B.Octets>) -> IO(FileDev & Result<&2, &2, D.DevError, B.Octets>):
  (f, res) = r
  IO.pure(FileDev & Result<&2, &2, D.DevError, B.Octets>, (FileDev{f, bs, c}, res))

def FileDev.read.check(ok: Bool, f: File, +bs: Nat, +c: Nat, +n: Nat) -> IO(FileDev & Result<&2, &2, D.DevError, B.Octets>):
  match ok:
    case True{}:
      IO.bind(File & Result<&2, &2, D.DevError, B.Octets>, FileDev & Result<&2, &2, D.DevError, B.Octets>, FileDev.read.more(bs, f, S.IOSpan.offset(bs, n), bs, B.Octets.empty()), FileDev.read.fin(bs, c))
    case False{}:
      IO.pure(FileDev & Result<&2, &2, D.DevError, B.Octets>, (FileDev{f, bs, c}, Fail{D.DevOutOfRange{n}}))

def FileDev.read_block.go(d: FileDev, +n: Nat) -> IO(FileDev & Result<&2, &2, D.DevError, B.Octets>):
  match d:
    case FileDev{f, +bs, +c}:
      FileDev.read.check(Nat.is_lt(n, c), f, bs, c, n)

# block n, read from the file now (plain parameters, so it fits the IO
# interface's template type)
def FileDev.read_block(d: FileDev, n: Nat) -> IO(FileDev & Result<&2, &2, D.DevError, B.Octets>):
  FileDev.read_block.go(d, n)

# always fails: DevFailed{30} (EROFS), as Base has no positioned write
def FileDev.write_block(d: FileDev, n: Nat, data: B.Octets) -> IO(FileDev & Result<&2, &2, D.DevError, Unit>):
  IO.pure(FileDev & Result<&2, &2, D.DevError, Unit>, (d, Fail{D.DevFailed{30}}))

# Saving: every block of any IO device written in order to a new file, a
# block at a time (so memory stays one block). The file at path is created
# or truncated first, so it must not be the file the device reads.

def FileDev.save.wrote(~D: Type, d: D, w: File & Result<&1, &1, U32 & String, Unit>, k: D -> File -> IO((D & File) & Result<&2, &2, D.DevError, Unit>)) -> IO((D & File) & Result<&2, &2, D.DevError, Unit>):
  (out, res) = w
  match res:
    case Done{u}:
      k(d, out)
    case Fail{(code, msg)}:
      IO.pure((D & File) & Result<&2, &2, D.DevError, Unit>, ((d, out), Fail{D.DevFailed{code}}))

def FileDev.save.block(~D: Type, r: D & Result<&2, &2, D.DevError, B.Octets>, out: File, k: D -> File -> IO((D & File) & Result<&2, &2, D.DevError, Unit>)) -> IO((D & File) & Result<&2, &2, D.DevError, Unit>):
  (d, res) = r
  match res:
    case Done{blk}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>, (D & File) & Result<&2, &2, D.DevError, Unit>, File.write_bytes(out, B.Octets.to_list(blk)), w => FileDev.save.wrote(~D, d, w, k))
    case Fail{e}:
      IO.pure((D & File) & Result<&2, &2, D.DevError, Unit>, ((d, out), Fail{e}))

def FileDev.save.go(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), count: Nat, d: D, out: File, +n: Nat) -> IO((D & File) & Result<&2, &2, D.DevError, Unit>):
  match count:
    case 0n:
      IO.pure((D & File) & Result<&2, &2, D.DevError, Unit>, ((d, out), Done{Unit{}}))
    case 1n+p:
      IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, (D & File) & Result<&2, &2, D.DevError, Unit>, read_block(d, n), r => FileDev.save.block(~D, r, out, d2 => o2 => FileDev.save.go(~D, ~read_block, p, d2, o2, Nat.add(n, 1n))))

def FileDev.save.close(~D: Type, r: (D & File) & Result<&2, &2, D.DevError, Unit>) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  (p, res) = r
  (d, out) = p
  IO.bind(Unit, D & Result<&2, &2, D.DevError, Unit>, File.close(out), u => IO.pure(D & Result<&2, &2, D.DevError, Unit>, (d, res)))

def FileDev.save.opened(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), d: D, c: Nat, r: Result<&1, &1, U32 & String, File>) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  match r:
    case Done{out}:
      IO.bind((D & File) & Result<&2, &2, D.DevError, Unit>, D & Result<&2, &2, D.DevError, Unit>, FileDev.save.go(~D, ~read_block, c, d, out, 0n), FileDev.save.close(~D))
    case Fail{(code, msg)}:
      IO.pure(D & Result<&2, &2, D.DevError, Unit>, (d, Fail{D.DevFailed{code}}))

def FileDev.save.counted(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), path: String, r: D & Nat) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  (d, c) = r
  IO.bind(Result<&1, &1, U32 & String, File>, D & Result<&2, &2, D.DevError, Unit>, File.open(path, "w"), FileDev.save.opened(~D, ~read_block, d, c))

# the device's blocks, all of them, as the file at path; the device is
# handed back however the save ends
def FileDev.save(~D: Type, ~block_count: D -> IO(D & Nat), ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), d: D, path: String) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  IO.bind(D & Nat, D & Result<&2, &2, D.DevError, Unit>, block_count(d), FileDev.save.counted(~D, ~read_block, path))
