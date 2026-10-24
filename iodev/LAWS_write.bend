# What the IO helpers compute: streaming, and read-modify-write over spans.
#
# On every pure device (any Data type and read), for every step,
# continuation and range: IODev.fold_blocks performs no effect, hands the
# device back and answers the step folded over the blocks Dev.read_list
# reads (the first failed read, if one fails).
#
# On IOMem, for every MemDev and continuation: IODev.read_blocks and
# IODev.read_bytes perform no effect, hand the device back and answer what
# blockdev's Dev.read_blocks and Dev.read_bytes answer (blockdev's
# LAWS_range.bend says what that is on a valid MemDev).
#
# On IOMem, for every valid MemDev, continuation and range inside the
# device: IODev.write_blocks and IODev.write_bytes succeed, keep the device
# valid with its block size and count, and leave its image patched with
# the data (Dev.patch); what was written reads back as the data, every
# byte outside it reads as before, and a nonempty write that passes the
# end fails and leaves the device as it was.
#
# A law about an IO action states what it gives a continuation k: the
# action run as m(R, k); outcome, shape and failed below are what the laws
# look at of the device and answer a write leaves.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./iodev.bend as V
import ./mem.bend as M

# step folded over a list of blocks, in order
def fold_list(~A: Data, ~step: A -> B.Octets -> A, xs: List<&2, B.Octets>, acc: A) -> A:
  match xs:
    case Nil{}:
      acc
    case Con{b, t}:
      fold_list(~A, ~step, t, step(acc, b))

# what a write leaves: its answer, and the device's image
def outcome(x: D.MemDev & Result<&2, &2, D.DevError, Unit>) -> Result<&2, &2, D.DevError, Unit> & B.Octets:
  (d, r) = x
  (r, D.MemDev.to_octets(d))

# a device's shape: whether it is valid, its block size and its count
def shape(+d: D.MemDev) -> Bool & (Nat & Nat):
  (D.MemDev.valid(d), (D.MemDev.block_size(d), D.MemDev.block_count(d)))

# the device a write leaves, and whether its answer is a failure
def failed(x: D.MemDev & Result<&2, &2, D.DevError, Unit>) -> D.MemDev & Bool:
  (d, r) = x
  (d, Result.is_fail(&2, &2, D.DevError, Unit, r))

# Every pure device

law io_fold_blocks:
  for ~A: Data
  for ~D: Data
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for ~step: A -> B.Octets -> A
  for -R: Type
  for -k: (D & Result<&2, &2, D.DevError, A>) -> IO.OP<R>
  for +d: D
  for count: Nat
  for +first: Nat
  for +acc: A
  {V.IODev.fold_blocks(~A, ~D, ~V.IODev.of_pure_read(~D, ~read_block), ~step, count, d, first, acc)(R, k) == k((d, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => fold_list(~A, ~step, xs, acc), D.Dev.read_list(~D, ~read_block, d, count, first)))) : IO.OP<R>}

# IOMem: reads

law io_mem_read_blocks:
  for -R: Type
  for -k: (D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>
  for +d: D.MemDev
  for +count: Nat
  for +first: Nat
  {V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, d, first)(R, k) == k((d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first))) : IO.OP<R>}

law io_mem_read_bytes:
  for -R: Type
  for -k: (D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>
  for +d: D.MemDev
  for +off: Nat
  for +len: Nat
  {V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, off, len)(R, k) == k((d, D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, off, len))) : IO.OP<R>}

# IOMem: write_blocks, count blocks of data from block first

law io_mem_write_blocks:
  for -R: Type
  for -k: (Result<&2, &2, D.DevError, Unit> & B.Octets) -> IO.OP<R>
  for +d: D.MemDev
  for +count: Nat
  for +first: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}
  for hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}
  {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, D.MemDev.block_size(d), first, data)(R, x => k(outcome(x))) == k((Done{Unit{}}, D.Dev.patch(Nat.mul(first, D.MemDev.block_size(d)), data, D.MemDev.to_octets(d)))) : IO.OP<R>}

law io_mem_write_blocks_shape:
  for -R: Type
  for -k: (Bool & (Nat & Nat)) -> IO.OP<R>
  for +d: D.MemDev
  for +count: Nat
  for +first: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}
  for hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}
  {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, D.MemDev.block_size(d), first, data)(R, x => k(shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))) == k(shape(d)) : IO.OP<R>}

law io_mem_write_blocks_read:
  for -R: Type
  for -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>
  for +d: D.MemDev
  for +count: Nat
  for +first: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}
  for hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}
  {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, D.MemDev.block_size(d), first, data)(R, x => V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), first)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == k(Done{data}) : IO.OP<R>}

# IOMem: write_bytes, data at byte offset off

law io_mem_write_bytes:
  for -R: Type
  for -k: (Result<&2, &2, D.DevError, Unit> & B.Octets) -> IO.OP<R>
  for +d: D.MemDev
  for +off: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(outcome(x))) == k((Done{Unit{}}, D.Dev.patch(off, data, D.MemDev.to_octets(d)))) : IO.OP<R>}

law io_mem_write_bytes_shape:
  for -R: Type
  for -k: (Bool & (Nat & Nat)) -> IO.OP<R>
  for +d: D.MemDev
  for +off: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))) == k(shape(d)) : IO.OP<R>}

law io_mem_write_read:
  for -R: Type
  for -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>
  for +d: D.MemDev
  for +off: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), off, B.Octets.len(data))(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == k(Done{data}) : IO.OP<R>}

law io_mem_write_before:
  for -R: Type
  for -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>
  for +d: D.MemDev
  for +off: Nat
  for +data: B.Octets
  for +i: Nat
  for +n: Nat
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  for h: {Nat.is_le(Nat.add(i, n), off) == True{} : Bool}
  {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))) : IO.OP<R>}

law io_mem_write_after:
  for -R: Type
  for -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>
  for +d: D.MemDev
  for +off: Nat
  for +data: B.Octets
  for +i: Nat
  for +n: Nat
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  for h: {Nat.is_le(Nat.add(off, B.Octets.len(data)), i) == True{} : Bool}
  for hi: {Nat.is_le(Nat.add(i, n), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))) : IO.OP<R>}

law io_mem_write_past_end:
  for -R: Type
  for -k: (D.MemDev & Bool) -> IO.OP<R>
  for +d: D.MemDev
  for +bp: Nat
  for +off: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for hbs: {D.MemDev.block_size(d) == 1n+bp : Nat}
  for nz: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}
  for past: {Nat.is_lt(Nat.mul(D.MemDev.block_count(d), 1n+bp), Nat.add(off, B.Octets.len(data))) == True{} : Bool}
  {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(failed(x))) == k((d, True{})) : IO.OP<R>}

# Vectors: a 3-block device of 4-byte blocks holding "abcdefghij" (padded)

def dev() -> D.MemDev:
  D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij"))

def add_len(n: Nat, b: B.Octets) -> Nat:
  Nat.add(n, B.Octets.len(b))

def run_fold(m: IO(D.MemDev & Result<&2, &2, D.DevError, Nat>)) -> IO.OP<Nat>:
  m(Nat, x => Emit{Result.default(&2, &2, D.DevError, Nat, Pair.snd(D.MemDev, Result<&2, &2, D.DevError, Nat>, x), 0n)})

def run_write(m: IO(D.MemDev & Result<&2, &2, D.DevError, Unit>)) -> IO.OP<String>:
  m(String, x => Emit{B.Octets.to_string(B.Octets.take(10n, D.MemDev.to_octets(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x))))})

law vector_fold:
  {run_fold(V.IODev.fold_blocks(~Nat, ~D.MemDev, ~M.IOMem.read_block, ~add_len, 3n, dev(), 0n, 0n)) == Emit{12n} : IO.OP<Nat>}

law vector_write_blocks:
  {run_write(V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, 1n, dev(), 4n, 1n, B.Octets.of_string("WXYZ"))) == Emit{"abcdWXYZij"} : IO.OP<String>}
