# bend-osdev-iodev: a write overlay on any IO device. Writes are kept in
# memory, in an XArray of blocks; a read answers the written block if
# there is one, else reads the device below. So a device that cannot be
# written (a FileDev, since Base cannot write a file at an offset) can be
# written through an overlay, and the result streamed out with
# FileDev.save. Memory: the blocks written, and nothing else.
#
# The overlay checks a write against the block size and count it was given
# (IOOverlay.over takes them from the device); the device below is never
# written.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../xarray/xarray.bend as X

type IOOverlay<-D: Type> is Type:
  IOOverlay{base: D, block_size: Nat, count: Nat, blocks: X.XArray<B.Octets>}

# an overlay with nothing written on base, of count blocks of bs bytes
def IOOverlay.of(~D: Type, base: D, bs: Nat, count: Nat) -> IOOverlay<D>:
  IOOverlay{base, bs, count, X.XArray.empty(B.Octets)}

def IOOverlay.over.fin(~D: Type, +bs: Nat, r: D & Nat) -> IO(IOOverlay<D>):
  (d, c) = r
  IO.pure(IOOverlay<D>, IOOverlay.of(~D, d, bs, c))

def IOOverlay.over.size(~D: Type, ~block_count: D -> IO(D & Nat), r: D & Nat) -> IO(IOOverlay<D>):
  (d, +bs) = r
  IO.bind(D & Nat, IOOverlay<D>, block_count(d), IOOverlay.over.fin(~D, bs))

# an overlay with nothing written on an IO device, with the device's block
# size and count
def IOOverlay.over(~D: Type, ~block_size: D -> IO(D & Nat), ~block_count: D -> IO(D & Nat), d: D) -> IO(IOOverlay<D>):
  IO.bind(D & Nat, IOOverlay<D>, block_size(d), IOOverlay.over.size(~D, ~block_count))

# the device below, with the written blocks dropped
def IOOverlay.base(~D: Type, o: IOOverlay<D>) -> D:
  match o:
    case IOOverlay{b, bs, c, x}:
      b

# The IO interface

def IOOverlay.block_size(~D: Type, o: IOOverlay<D>) -> IO(IOOverlay<D> & Nat):
  match o:
    case IOOverlay{b, +bs, c, x}:
      IO.pure(IOOverlay<D> & Nat, (IOOverlay{b, bs, c, x}, bs))

def IOOverlay.block_count(~D: Type, o: IOOverlay<D>) -> IO(IOOverlay<D> & Nat):
  match o:
    case IOOverlay{b, bs, +c, x}:
      IO.pure(IOOverlay<D> & Nat, (IOOverlay{b, bs, c, x}, c))

def IOOverlay.read.base(~D: Type, +bs: Nat, +c: Nat, x: X.XArray<B.Octets>, r: D & Result<&2, &2, D.DevError, B.Octets>) -> IO(IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>):
  (b, res) = r
  IO.pure(IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>, (IOOverlay{b, bs, c, x}, res))

def IOOverlay.read.got(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), m: Maybe<&2, B.Octets>, b: D, +bs: Nat, +c: Nat, x: X.XArray<B.Octets>, n: Nat) -> IO(IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>):
  match m:
    case Some{blk}:
      IO.pure(IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>, (IOOverlay{b, bs, c, x}, Done{blk}))
    case None{}:
      IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>, read_block(b, n), IOOverlay.read.base(~D, bs, c, x))

def IOOverlay.read_block.go(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), o: IOOverlay<D>, +n: Nat) -> IO(IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>):
  match o:
    case IOOverlay{b, bs, c, +x}:
      IOOverlay.read.got(~D, ~read_block, X.XArray.load(B.Octets, x, U32.from_nat(n)), b, bs, c, x, n)

# block n: the block last written there, else the device's block n
def IOOverlay.read_block(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), o: IOOverlay<D>, n: Nat) -> IO(IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>):
  IOOverlay.read_block.go(~D, ~read_block, o, n)

def IOOverlay.put.check(~D: Type, okl: Bool, okn: Bool, b: D, +bs: Nat, c: Nat, x: X.XArray<B.Octets>, +n: Nat, +data: B.Octets) -> IOOverlay<D> & Result<&2, &2, D.DevError, Unit>:
  match okl okn:
    case True{} True{}:
      (IOOverlay{b, bs, c, X.XArray.store(B.Octets, x, U32.from_nat(n), data)}, Done{Unit{}})
    case False{} _:
      (IOOverlay{b, bs, c, x}, Fail{D.DevBadLength{bs, B.Octets.len(data)}})
    case True{} False{}:
      (IOOverlay{b, bs, c, x}, Fail{D.DevOutOfRange{n}})

def IOOverlay.put.go(~D: Type, o: IOOverlay<D>, +n: Nat, +data: B.Octets) -> IOOverlay<D> & Result<&2, &2, D.DevError, Unit>:
  match o:
    case IOOverlay{b, +bs, +c, x}:
      IOOverlay.put.check(~D, Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c), b, bs, c, x, n, data)

# block n replaced by data in the overlay (the owned interface's write, with
# no effect): data must be exactly one block and block n must exist, else
# the overlay is handed back unchanged with why not
def IOOverlay.put(~D: Type, o: IOOverlay<D>, n: Nat, data: B.Octets) -> IOOverlay<D> & Result<&2, &2, D.DevError, Unit>:
  IOOverlay.put.go(~D, o, n, data)

# put, on the IO interface
def IOOverlay.write_block(~D: Type, o: IOOverlay<D>, n: Nat, data: B.Octets) -> IO(IOOverlay<D> & Result<&2, &2, D.DevError, Unit>):
  IO.pure(IOOverlay<D> & Result<&2, &2, D.DevError, Unit>, IOOverlay.put(~D, o, n, data))
