# bend-osdev-fileio: library effects on Base's File handle, for what Base
# 2.0.37 cannot do with a file: open it for reading and writing without
# truncating it, write at an offset, read at and size past 4 GiB, and
# flush it to the device.
#
# Each effect is a foreign def, as Base's own are (base.bend's File.*): a
# def whose body imports its C side (fileio.c) and its JavaScript side
# (fileio.js), so it runs natively (bend -o) and on the JavaScript lane
# (bend file.bend). Each takes and hands back Base's File, so a handle from
# FileIO.open works with File.read_bytes, File.write_bytes and File.close,
# and one from File.open works here.
#
# The FileIO.eff.* defs are the effects themselves, with a 64-bit offset as
# two U32 halves (high, low); the FileIO.* defs above them take and answer
# a W64 (bend-osdev-word64), converted by off.bend. Effects are tested
# against Python (ref/), not proved; off.bend's conversions have laws.
import Base
import ../word64/word64.bend as W
import ./off.bend as O

# The effects

# open(2) with O_RDWR, never O_TRUNC; with O_CREAT (mode 0644) when create
# is not 0
def FileIO.eff.open(path: String, create: U32) -> IO(Result<&1, &1, U32 & String, File>):
  import "./fileio.c"
  import "./fileio.js"

# pread(2): up to max bytes (at most 2^31 - 1) at the offset hi * 2^32 +
# lo; fewer at the end of the file, none past it
def FileIO.eff.read_at(file: File, hi: U32, lo: U32, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  import "./fileio.c"
  import "./fileio.js"

# pwrite(2), repeated until every byte is written: the bytes at the offset
# hi * 2^32 + lo (a file grows to hold them; a gap reads as zeros)
def FileIO.eff.write_at(file: File, hi: U32, lo: U32, data: List<&2, U32>) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  import "./fileio.c"
  import "./fileio.js"

# fstat(2): the size, as (high, low)
def FileIO.eff.size(file: File) -> IO(File & Result<&1, &1, U32 & String, U32 & U32>):
  import "./fileio.c"
  import "./fileio.js"

# fsync(2)
def FileIO.eff.sync(file: File) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  import "./fileio.c"
  import "./fileio.js"

# The interface, with 64-bit offsets and sizes as W64

def FileIO.create_flag(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# the file at path, for reading and writing, from its start; it is never
# truncated; if it does not exist it is created (empty) when create is
# True, and the open fails (ENOENT) when it is False
def FileIO.open(path: String, create: Bool) -> IO(Result<&1, &1, U32 & String, File>):
  FileIO.eff.open(path, FileIO.create_flag(create))

# the usual choice: an existing file, read and written in place (fopen's
# "r+")
def FileIO.open_rw(path: String) -> IO(Result<&1, &1, U32 & String, File>):
  FileIO.open(path, False{})

def FileIO.read_at.go(file: File, p: U32 & U32, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  (h, l) = p
  FileIO.eff.read_at(file, h, l, max)

# up to max bytes at offset off, as File.read_at gives them (the position
# of the file does not move)
def FileIO.read_at(file: File, off: W.W64, max: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
  FileIO.read_at.go(file, O.FileIO.off.halves(off), max)

def FileIO.write_at.go(file: File, p: U32 & U32, data: List<&2, U32>) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  (h, l) = p
  FileIO.eff.write_at(file, h, l, data)

# every byte of data at offset off (the position of the file does not
# move); a value past 255 fails (EINVAL) before any byte is written
def FileIO.write_at(file: File, off: W.W64, data: List<&2, U32>) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  FileIO.write_at.go(file, O.FileIO.off.halves(off), data)

def FileIO.size.got(r: File & Result<&1, &1, U32 & String, U32 & U32>) -> IO(File & Result<&1, &1, U32 & String, W.W64>):
  (f, res) = r
  match res:
    case Done{p}:
      IO.pure(File & Result<&1, &1, U32 & String, W.W64>, (f, Done{O.FileIO.off.join(p)}))
    case Fail{e}:
      IO.pure(File & Result<&1, &1, U32 & String, W.W64>, (f, Fail{e}))

# the size of the file in bytes (any size, past 4 GiB too)
def FileIO.size(file: File) -> IO(File & Result<&1, &1, U32 & String, W.W64>):
  IO.bind(File & Result<&1, &1, U32 & String, U32 & U32>, File & Result<&1, &1, U32 & String, W.W64>, FileIO.eff.size(file), FileIO.size.got)

# the data and metadata written so far reach the device (fsync)
def FileIO.sync(file: File) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  FileIO.eff.sync(file)
