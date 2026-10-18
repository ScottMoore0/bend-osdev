# bend-osdev-iodev: the IO block-device interface, helpers built on it, and
# adapters that run any pure or owned device (blockdev's) through it.
#
# The IO interface is blockdev's owned interface with every operation in
# IO: the device is a single-owner value (a Type: a file handle, or a
# record holding one), handed back by every operation, whatever happens:
#
#   block_size(d)            -> IO(D & Nat)
#   block_count(d)           -> IO(D & Nat)   (for whole-device helpers)
#   read_block(d, n)         -> IO(D & Result<&2, &2, DevError, Octets>)
#   write_block(d, n, data)  -> IO(D & Result<&2, &2, DevError, Unit>)
#
# The operations are passed as template arguments, as blockdev's are, so a
# helper is specialised to its device at compile time.
#
# (A continuation that runs an IO helper is written out, R => k => ...(R,
# x => k(x)), so that the laws' statements and the code elaborate alike
# for the proof kernel.)
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./span.bend as S

# Reading blocks

def IODev.cons(~D: Type, blk: B.Octets, r: D & Result<&2, &2, D.DevError, B.Octets>) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  (d, res) = r
  match res:
    case Done{rest}:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Done{B.Octets.append(blk, rest)}))
    case Fail{e}:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Fail{e}))

def IODev.then(~D: Type, r: D & Result<&2, &2, D.DevError, B.Octets>, k: D -> IO(D & Result<&2, &2, D.DevError, B.Octets>)) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  (d, res) = r
  match res:
    case Done{blk}:
      IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, D & Result<&2, &2, D.DevError, B.Octets>, k(d), x => IODev.cons(~D, blk, x))
    case Fail{e}:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Fail{e}))

# count blocks from block first, joined; the device is handed back however
# the reads end (count comes first: it shrinks in the recursion)
def IODev.read_blocks(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), count: Nat, d: D, +first: Nat) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  match count:
    case 0n:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Done{B.Octets.empty()}))
    case 1n+p:
      IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, D & Result<&2, &2, D.DevError, B.Octets>, read_block(d, first), r => IODev.then(~D, r, d2 => R => k => IODev.read_blocks(~D, ~read_block, p, d2, Nat.add(first, 1n))(R, x => k(x))))

def IODev.slice(~D: Type, +skip: Nat, +len: Nat, r: D & Result<&2, &2, D.DevError, B.Octets>) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  (d, res) = r
  match res:
    case Done{blocks}:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Done{B.Octets.slice(skip, len, blocks)}))
    case Fail{e}:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Fail{e}))

def IODev.read_bytes.go(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), +off: Nat, +len: Nat, r: D & Nat) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  (d, +bs) = r
  +s = S.IOSpan.of(bs, off, len)
  IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, D & Result<&2, &2, D.DevError, B.Octets>, IODev.read_blocks(~D, ~read_block, S.IOSpan.count(s), d, S.IOSpan.first(s)), x => R => k => IODev.slice(~D, S.IOSpan.skip(s), len, x)(R, y => k(y)))

def IODev.read_bytes.some(~D: Type, ~block_size: D -> IO(D & Nat), ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), empty: Bool, d: D, +off: Nat, +len: Nat) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  match empty:
    case True{}:
      IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, (d, Done{B.Octets.empty()}))
    case False{}:
      IO.bind(D & Nat, D & Result<&2, &2, D.DevError, B.Octets>, block_size(d), x => R => k => IODev.read_bytes.go(~D, ~read_block, off, len, x)(R, y => k(y)))

# len bytes from byte offset off, whichever blocks they span (only those
# blocks are read); reading zero bytes always succeeds and reads no block
def IODev.read_bytes(~D: Type, ~block_size: D -> IO(D & Nat), ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), d: D, +off: Nat, +len: Nat) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  IODev.read_bytes.some(~D, ~block_size, ~read_block, Nat.is_eq(len, 0n), d, off, len)

# Streaming: every block of a range passed to a step function as it is
# read, so only one block is held at a time

def IODev.fold.then(~A: Data, ~D: Type, r: D & Result<&2, &2, D.DevError, B.Octets>, acc: A, k: D -> A -> B.Octets -> IO(D & Result<&2, &2, D.DevError, A>)) -> IO(D & Result<&2, &2, D.DevError, A>):
  (d, res) = r
  match res:
    case Done{blk}:
      k(d, acc, blk)
    case Fail{e}:
      IO.pure(D & Result<&2, &2, D.DevError, A>, (d, Fail{e}))

# step(acc, block) over count blocks from block first, in order; the final
# acc, or the first read's failure
def IODev.fold_blocks(~A: Data, ~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), ~step: A -> B.Octets -> A, count: Nat, d: D, +first: Nat, acc: A) -> IO(D & Result<&2, &2, D.DevError, A>):
  match count:
    case 0n:
      IO.pure(D & Result<&2, &2, D.DevError, A>, (d, Done{acc}))
    case 1n+p:
      IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, D & Result<&2, &2, D.DevError, A>, read_block(d, first), r => IODev.fold.then(~A, ~D, r, acc, d2 => a => blk => R => k => IODev.fold_blocks(~A, ~D, ~read_block, ~step, p, d2, Nat.add(first, 1n), step(a, blk))(R, x => k(x))))

# Writing blocks

def IODev.unit_then(~D: Type, r: D & Result<&2, &2, D.DevError, Unit>, k: D -> IO(D & Result<&2, &2, D.DevError, Unit>)) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  (d, res) = r
  match res:
    case Done{u}:
      k(d)
    case Fail{e}:
      IO.pure(D & Result<&2, &2, D.DevError, Unit>, (d, Fail{e}))

# count blocks of bs bytes, cut in order from data, written from block n;
# the first failed write stops the run
def IODev.write_blocks(~D: Type, ~write_block: D -> Nat -> B.Octets -> IO(D & Result<&2, &2, D.DevError, Unit>), count: Nat, d: D, +bs: Nat, +n: Nat, +data: B.Octets) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  match count:
    case 0n:
      IO.pure(D & Result<&2, &2, D.DevError, Unit>, (d, Done{Unit{}}))
    case 1n+p:
      IO.bind(D & Result<&2, &2, D.DevError, Unit>, D & Result<&2, &2, D.DevError, Unit>, write_block(d, n, B.Octets.take(bs, data)), r => IODev.unit_then(~D, r, d2 => R => k => IODev.write_blocks(~D, ~write_block, p, d2, bs, Nat.add(n, 1n), B.Octets.drop(bs, data))(R, x => k(x))))

def IODev.write_bytes.edge(~D: Type, r: D & Result<&2, &2, D.DevError, B.Octets>, k: D -> B.Octets -> IO(D & Result<&2, &2, D.DevError, Unit>)) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  (d, res) = r
  match res:
    case Done{blk}:
      k(d, blk)
    case Fail{e}:
      IO.pure(D & Result<&2, &2, D.DevError, Unit>, (d, Fail{e}))

def IODev.write_bytes.go(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), ~write_block: D -> Nat -> B.Octets -> IO(D & Result<&2, &2, D.DevError, Unit>), +off: Nat, +data: B.Octets, r: D & Nat) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  (d, +bs) = r
  +s = S.IOSpan.of(bs, off, B.Octets.len(data))
  +first = S.IOSpan.first(s)
  +count = S.IOSpan.count(s)
  IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, D & Result<&2, &2, D.DevError, Unit>, read_block(d, first), r1 => IODev.write_bytes.edge(~D, r1, d1 => head => IO.bind(D & Result<&2, &2, D.DevError, B.Octets>, D & Result<&2, &2, D.DevError, Unit>, read_block(d1, Nat.add(first, Nat.sub(count, 1n))), r2 => IODev.write_bytes.edge(~D, r2, d2 => tail => IODev.write_blocks(~D, ~write_block, count, d2, bs, first, B.Octets.concat([B.Octets.take(S.IOSpan.skip(s), head), data, B.Octets.drop(Nat.sub(bs, S.IOSpan.slack(s)), tail)]))))))

def IODev.write_bytes.some(~D: Type, ~block_size: D -> IO(D & Nat), ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), ~write_block: D -> Nat -> B.Octets -> IO(D & Result<&2, &2, D.DevError, Unit>), empty: Bool, d: D, +off: Nat, +data: B.Octets) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  match empty:
    case True{}:
      IO.pure(D & Result<&2, &2, D.DevError, Unit>, (d, Done{Unit{}}))
    case False{}:
      IO.bind(D & Nat, D & Result<&2, &2, D.DevError, Unit>, block_size(d), IODev.write_bytes.go(~D, ~read_block, ~write_block, off, data))

# data written at byte offset off, whichever blocks it spans: the first and
# last of them are read (for the bytes around data), then every one is
# written; writing zero bytes always succeeds and touches no block. A
# failure part way leaves the blocks before it written.
def IODev.write_bytes(~D: Type, ~block_size: D -> IO(D & Nat), ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), ~write_block: D -> Nat -> B.Octets -> IO(D & Result<&2, &2, D.DevError, Unit>), d: D, +off: Nat, +data: B.Octets) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  IODev.write_bytes.some(~D, ~block_size, ~read_block, ~write_block, Nat.is_eq(B.Octets.len(data), 0n), d, off, data)

# The adapters: an owned device's operations (blockdev's owned interface)
# on the IO interface; they perform no effect

def IODev.of_own_size(~D: Type, ~block_size: D -> D & Nat, d: D) -> IO(D & Nat):
  IO.pure(D & Nat, block_size(d))

def IODev.of_own_read(~D: Type, ~read_block: D -> Nat -> D & Result<&2, &2, D.DevError, B.Octets>, d: D, n: Nat) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, read_block(d, n))

def IODev.of_own_write(~D: Type, ~write_block: D -> Nat -> B.Octets -> D & Result<&2, &2, D.DevError, Unit>, d: D, n: Nat, data: B.Octets) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  IO.pure(D & Result<&2, &2, D.DevError, Unit>, write_block(d, n, data))

# a pure device's operations on the IO interface (through blockdev's
# adapters to the owned interface)

def IODev.of_pure_size(~D: Data, ~block_size: D -> Nat, d: D) -> IO(D & Nat):
  IO.pure(D & Nat, D.Dev.own_block_size(~D, ~block_size, d))

def IODev.of_pure_read(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, d: D, n: Nat) -> IO(D & Result<&2, &2, D.DevError, B.Octets>):
  IO.pure(D & Result<&2, &2, D.DevError, B.Octets>, D.Dev.own_read_block(~D, ~read_block, d, n))

def IODev.of_pure_write(~D: Data, ~write_block: D -> Nat -> B.Octets -> Result<&2, &2, D.DevError, D>, d: D, n: Nat, data: B.Octets) -> IO(D & Result<&2, &2, D.DevError, Unit>):
  IO.pure(D & Result<&2, &2, D.DevError, Unit>, D.Dev.own_write_block(~D, ~write_block, d, n, data))
