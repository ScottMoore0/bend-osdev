# bend-osdev-fat, io.bend: reading and writing a device on blockdev's owned
# interface, for the writing file system (write.bend).
#
# On the owned interface every device operation hands the device back, so a
# device may be a single-owner value (blockdev's ImgDev, an Array<U32>
# image). FatRun<Dv, A> threads the device through a sequence of steps:
# a step is a function from the device to the device and a result (A, or a
# FatError), and do-blocks over FatRun read like ordinary code:
#
#   do FatRun<Dv, Unit>:
#     o : B.Octets <- FatOIo.read(~Dv, ~block_size, ~read_block, 0n, 512n)
#     FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, 512n, o)
#
# A step that fails ends the sequence; the device is handed back as the
# failed step left it. FatOIo.write writes any byte range: whole blocks are
# written as they are, a block it covers only in part is read, changed and
# written back.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E

type FatRun<-Dv: Type, -A: Data> is Type:
  FatRun{run: Dv -> Dv & Result<&2, &2, E.FatError, A>}

# run the steps on a device: the device after them, and their result
def FatRun.exec(-Dv: Type, -A: Data, m: FatRun<Dv, A>, d: Dv) -> Dv & Result<&2, &2, E.FatError, A>:
  match m:
    case FatRun{f}:
      f(d)

def FatRun.pure(-Dv: Type, -A: Data, x: A) -> FatRun<Dv, A>:
  FatRun{d => (d, Done{x})}

def FatRun.fail(-Dv: Type, -A: Data, e: E.FatError) -> FatRun<Dv, A>:
  FatRun{d => (d, Fail{e})}

# a pure result as a step (the device untouched)
def FatRun.lift(-Dv: Type, -A: Data, r: Result<&2, &2, E.FatError, A>) -> FatRun<Dv, A>:
  FatRun{d => (d, r)}

def FatRun.go(-Dv: Type, -A: Data, -B: Data, r: Dv & Result<&2, &2, E.FatError, A>, k: A -> FatRun<Dv, B>) -> Dv & Result<&2, &2, E.FatError, B>:
  (d, res) = r
  match res:
    case Done{a}:
      FatRun.exec(Dv, B, k(a), d)
    case Fail{e}:
      (d, Fail{e})

def FatRun.bind(-Dv: Type, -A: Data, -B: Data, m: FatRun<Dv, A>, k: A -> FatRun<Dv, B>) -> FatRun<Dv, B>:
  match m:
    case FatRun{f}:
      FatRun{d => FatRun.go(Dv, A, B, f(d), k)}

# a device's own result, its error wrapped as FatDev
def FatRun.dev(-Dv: Type, -A: Data, r: Dv & Result<&2, &2, D.DevError, A>) -> Dv & Result<&2, &2, E.FatError, A>:
  (d, res) = r
  match res:
    case Done{x}:
      (d, Done{x})
    case Fail{e}:
      (d, Fail{E.FatDev{e}})

def FatRun.size(-Dv: Type, r: Dv & Nat) -> Dv & Result<&2, &2, E.FatError, Nat>:
  (d, n) = r
  (d, Done{n})

# The device's operations as steps

def FatOIo.block_size(~Dv: Type, ~block_size: Dv -> Dv & Nat) -> FatRun<Dv, Nat>:
  FatRun{d => FatRun.size(Dv, block_size(d))}

def FatOIo.read_block(~Dv: Type, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, n: Nat) -> FatRun<Dv, B.Octets>:
  FatRun{d => FatRun.dev(Dv, B.Octets, read_block(d, n))}

def FatOIo.write_block(~Dv: Type, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, n: Nat, data: B.Octets) -> FatRun<Dv, Unit>:
  FatRun{d => FatRun.dev(Dv, Unit, write_block(d, n, data))}

# len bytes from byte offset off (blockdev's owned ODev.read_bytes)
def FatOIo.read(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, off: Nat, len: Nat) -> FatRun<Dv, B.Octets>:
  FatRun{d => FatRun.dev(Dv, B.Octets, D.ODev.read_bytes(~Dv, ~block_size, ~read_block, d, off, len))}

# What a write puts on the device: bytes, or a run of zeros

type FatSrc is Data:
  FatSrcBytes{data: B.Octets}
  FatSrcZeros{len: Nat}

def FatSrc.len(s: FatSrc) -> Nat:
  match s:
    case FatSrcBytes{o}:
      B.Octets.len(o)
    case FatSrcZeros{n}:
      n

def FatSrc.take(+k: Nat, s: FatSrc) -> B.Octets:
  match s:
    case FatSrcBytes{o}:
      B.Octets.take(k, o)
    case FatSrcZeros{n}:
      B.Octets.zeros(Nat.min(k, n))

# the first k bytes of a source, as a source
def FatSrc.head(+k: Nat, s: FatSrc) -> FatSrc:
  match s:
    case FatSrcBytes{o}:
      FatSrcBytes{B.Octets.take(k, o)}
    case FatSrcZeros{n}:
      FatSrcZeros{Nat.min(k, n)}

def FatSrc.drop(+k: Nat, s: FatSrc) -> FatSrc:
  match s:
    case FatSrcBytes{o}:
      FatSrcBytes{B.Octets.drop(k, o)}
    case FatSrcZeros{n}:
      FatSrcZeros{Nat.sub(n, k)}

def FatOIo.splice(+skip: Nat, +piece: B.Octets, old: B.Octets) -> B.Octets:
  +o = old
  B.Octets.append(B.Octets.take(skip, o), B.Octets.append(piece, B.Octets.drop(Nat.add(skip, B.Octets.len(piece)), o)))

def FatOIo.put(~Dv: Type, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, whole: Bool, +blk: Nat, +skip: Nat, piece: B.Octets) -> FatRun<Dv, Unit>:
  match whole:
    case True{}:
      FatOIo.write_block(~Dv, ~write_block, blk, piece)
    case False{}:
      do FatRun<Dv, Unit>:
        old : B.Octets <- FatOIo.read_block(~Dv, ~read_block, blk)
        FatOIo.write_block(~Dv, ~write_block, blk, FatOIo.splice(skip, piece, old))

# n blocks from block blk, the first from byte skip of it (left: the bytes
# of src still to write, so its length is not counted again)
def FatOIo.write.go(~Dv: Type, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, n: Nat, +bs: Nat, +blk: Nat, +skip: Nat, +left: Nat, +src: FatSrc) -> FatRun<Dv, Unit>:
  match n:
    case 0n:
      FatRun.pure(Dv, Unit, Unit{})
    case 1n+p:
      +k = Nat.min(Nat.sub(bs, skip), left)
      do FatRun<Dv, Unit>:
        FatOIo.put(~Dv, ~read_block, ~write_block, Bool.and(Nat.is_eq(skip, 0n), Nat.is_eq(k, bs)), blk, skip, FatSrc.take(k, src))
        FatOIo.write.go(~Dv, ~read_block, ~write_block, p, bs, Nat.add(blk, 1n), 0n, Nat.sub(left, k), FatSrc.drop(k, src))

# the blocks a write of len bytes from byte skip of a block spans (none for
# an empty write)
def FatOIo.span(empty: Bool, +bs: Nat, +skip: Nat, +len: Nat) -> Nat:
  match empty:
    case True{}:
      0n
    case False{}:
      Nat.div(Nat.add(Nat.add(skip, len), Nat.sub(bs, 1n)), bs)

def FatOIo.write.src(~Dv: Type, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +bs: Nat, +off: Nat, +src: FatSrc) -> FatRun<Dv, Unit>:
  +skip = Nat.mod(off, bs)
  +len = FatSrc.len(src)
  FatOIo.write.go(~Dv, ~read_block, ~write_block, FatOIo.span(Nat.is_eq(len, 0n), bs, skip, len), bs, Nat.div(off, bs), skip, len, src)

def FatOIo.write_src(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +off: Nat, +src: FatSrc) -> FatRun<Dv, Unit>:
  do FatRun<Dv, Unit>:
    bs : Nat <- FatOIo.block_size(~Dv, ~block_size)
    FatOIo.write.src(~Dv, ~read_block, ~write_block, bs, off, src)

# data written at byte offset off, whichever blocks it spans
def FatOIo.write(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +off: Nat, data: B.Octets) -> FatRun<Dv, Unit>:
  FatOIo.write_src(~Dv, ~block_size, ~read_block, ~write_block, off, FatSrcBytes{data})

# len zero bytes written at byte offset off
def FatOIo.zero(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +off: Nat, len: Nat) -> FatRun<Dv, Unit>:
  FatOIo.write_src(~Dv, ~block_size, ~read_block, ~write_block, off, FatSrcZeros{len})
