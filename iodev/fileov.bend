# bend-osdev-iodev: a disk image file that can be written: an IOOverlay
# on a FileDev, with its operations named so they can be passed to the IO
# helpers as template arguments. Reads come from the file (or from the
# overlay, for a block written since it was opened); writes stay in the
# overlay until FileOv.save streams the whole device to a new file.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./overlay.bend as O
import ./filedev.bend as F

def FileOv.opened(r: Result<&1, &1, F.FileDevError, F.FileDev>) -> IO(Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>):
  match r:
    case Done{d}:
      IO.bind(O.IOOverlay<F.FileDev>, Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>, O.IOOverlay.over(~F.FileDev, ~F.FileDev.block_size, ~F.FileDev.block_count, d), o => IO.pure(Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>, Done{o}))
    case Fail{e}:
      IO.pure(Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>, Fail{e})

# the file at path as a writable device of bs-byte blocks (the file itself
# is only read)
def FileOv.open(path: String, +bs: Nat) -> IO(Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>):
  IO.bind(Result<&1, &1, F.FileDevError, F.FileDev>, Result<&1, &1, F.FileDevError, O.IOOverlay<F.FileDev>>, F.FileDev.open(path, bs), FileOv.opened)

# the file closed; the blocks written are dropped
def FileOv.close(o: O.IOOverlay<F.FileDev>) -> IO(Unit):
  F.FileDev.close(O.IOOverlay.base(~F.FileDev, o))

def FileOv.block_size(o: O.IOOverlay<F.FileDev>) -> IO(O.IOOverlay<F.FileDev> & Nat):
  O.IOOverlay.block_size(~F.FileDev, o)

def FileOv.block_count(o: O.IOOverlay<F.FileDev>) -> IO(O.IOOverlay<F.FileDev> & Nat):
  O.IOOverlay.block_count(~F.FileDev, o)

def FileOv.read_block(o: O.IOOverlay<F.FileDev>, n: Nat) -> IO(O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, B.Octets>):
  O.IOOverlay.read_block(~F.FileDev, ~F.FileDev.read_block, o, n)

def FileOv.write_block(o: O.IOOverlay<F.FileDev>, n: Nat, data: B.Octets) -> IO(O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit>):
  O.IOOverlay.write_block(~F.FileDev, o, n, data)

# every block, with the writes, as the file at path (which must not be the
# file the device reads)
def FileOv.save(o: O.IOOverlay<F.FileDev>, path: String) -> IO(O.IOOverlay<F.FileDev> & Result<&2, &2, D.DevError, Unit>):
  F.FileDev.save(~O.IOOverlay<F.FileDev>, ~FileOv.block_count, ~FileOv.read_block, o, path)
