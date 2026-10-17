# bend-osdev-blockdev: the block-device interface that filesystems read
# through, generic helpers over it, and an in-memory device.
#
# A device is a value d of some Data type D, with two operations:
#   block_size(d) -> Nat                                   bytes per block
#   read_block(d, n) -> Result<&2, &2, DevError, Octets>   block n
# A filesystem takes the type and the operations as template arguments
# (~D, ~block_size, ~read_block), so it is specialised to its device at compile
# time: the interface costs nothing at run time, and any device works (an
# in-memory image here; a file, a partition or a driver elsewhere).
import Base
import ../bytes/bytes.bend as B

type DevError is Data:
  DevOutOfRange{block: Nat}
  DevBadLength{expected: Nat, got: Nat}
  DevFailed{code: U32}

# Generic helpers: built only from the two operations, so they work on every
# device

# count blocks from block first, joined
def Dev.read_blocks(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, +d: D, count: Nat, +first: Nat) -> Result<&2, &2, DevError, B.Octets>:
  match count:
    case 0n:
      Done{B.Octets.empty()}
    case 1n+p:
      do Result<&2, &2, DevError, B.Octets>:
        blk : B.Octets <- read_block(d, first)
        rest : B.Octets <- Dev.read_blocks(~D, ~read_block, d, p, Nat.add(first, 1n))
        return B.Octets.append(blk, rest)

def Dev.read_bytes.go(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, +d: D, +bs: Nat, +off: Nat, +len: Nat) -> Result<&2, &2, DevError, B.Octets>:
  +skip = Nat.mod(off, bs)
  do Result<&2, &2, DevError, B.Octets>:
    blocks : B.Octets <- Dev.read_blocks(~D, ~read_block, d, Nat.div(Nat.add(Nat.add(skip, len), Nat.sub(bs, 1n)), bs), Nat.div(off, bs))
    return B.Octets.slice(skip, len, blocks)

def Dev.read_bytes.some(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, empty: Bool, +d: D, off: Nat, len: Nat) -> Result<&2, &2, DevError, B.Octets>:
  match empty:
    case True{}:
      Done{B.Octets.empty()}
    case False{}:
      Dev.read_bytes.go(~D, ~read_block, d, block_size(d), off, len)

# len bytes from byte offset off, whichever blocks they span; reading zero
# bytes always succeeds and reads no block
def Dev.read_bytes(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, +d: D, off: Nat, +len: Nat) -> Result<&2, &2, DevError, B.Octets>:
  Dev.read_bytes.some(~D, ~block_size, ~read_block, Nat.is_eq(len, 0n), d, off, len)

# MemDev: a device held in memory, as its list of blocks (every block
# block_size bytes). Its representation is internal.

type MemDev is Data:
  MemDev{block_size: Nat, blocks: List<&2, B.Octets>}

# Block lists are walked by tail calls (an image may have far more blocks
# than Bend's stack has room for nested calls)

def MemDev.blocks.rev_onto(xs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      MemDev.blocks.rev_onto(t, Con{h, acc})

# n blocks of bs bytes cut from o, reversed onto acc
def MemDev.split.go(n: Nat, +bs: Nat, o: B.Octets, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +rest = o
      +blk = B.Octets.take(bs, rest)
      MemDev.split.go(p, bs, B.Octets.drop(bs, rest), Con{B.Octets.append(blk, B.Octets.zeros(Nat.sub(bs, B.Octets.len(blk)))), acc})

def MemDev.split(n: Nat, +bs: Nat, o: B.Octets) -> List<&2, B.Octets>:
  MemDev.blocks.rev_onto(MemDev.split.go(n, bs, o, Nil{}), Nil{})

# an image as a device; a final partial block is padded with zeros
def MemDev.of_octets(+bs: Nat, +o: B.Octets) -> MemDev:
  MemDev{bs, MemDev.split(Nat.div(Nat.add(B.Octets.len(o), Nat.sub(bs, 1n)), bs), bs, o)}

# count zero blocks
def MemDev.blank.go(n: Nat, +bs: Nat, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match n:
    case 0n:
      acc
    case 1n+p:
      MemDev.blank.go(p, bs, Con{B.Octets.zeros(bs), acc})

def MemDev.blank(+bs: Nat, count: Nat) -> MemDev:
  MemDev{bs, MemDev.blank.go(count, bs, Nil{})}

def MemDev.block_size(d: MemDev) -> Nat:
  match d:
    case MemDev{bs, blocks}:
      bs

def MemDev.count.go(blocks: List<&2, B.Octets>, n: Nat) -> Nat:
  match blocks:
    case Nil{}:
      n
    case Con{h, t}:
      MemDev.count.go(t, 1n+n)

def MemDev.block_count(d: MemDev) -> Nat:
  match d:
    case MemDev{bs, blocks}:
      MemDev.count.go(blocks, 0n)

def MemDev.nth(i: Nat, blocks: List<&2, B.Octets>, +n: Nat) -> Result<&2, &2, DevError, B.Octets>:
  match i blocks:
    case 0n Con{h, t}:
      Done{h}
    case 1n+p Con{h, t}:
      MemDev.nth(p, t, n)
    case _ Nil{}:
      Fail{DevOutOfRange{n}}

def MemDev.read_block.go(d: MemDev, +n: Nat) -> Result<&2, &2, DevError, B.Octets>:
  match d:
    case MemDev{bs, blocks}:
      MemDev.nth(n, blocks, n)

# block n (the device interface's read_block, with plain parameters so it
# fits the template type every filesystem expects)
def MemDev.read_block(d: MemDev, n: Nat) -> Result<&2, &2, DevError, B.Octets>:
  MemDev.read_block.go(d, n)

# the blocks with block i replaced by v (unchanged if there is no block i):
# the structural form the proofs reason about
def MemDev.set.ref(i: Nat, blocks: List<&2, B.Octets>, v: B.Octets) -> List<&2, B.Octets>:
  match i blocks:
    case 0n Con{h, t}:
      Con{v, t}
    case 1n+p Con{h, t}:
      Con{h, MemDev.set.ref(p, t, v)}
    case _ Nil{}:
      Nil{}

# the same by tail calls: the blocks passed are kept, reversed, in acc
def MemDev.set.go(i: Nat, blocks: List<&2, B.Octets>, v: B.Octets, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match i blocks:
    case 0n Con{h, t}:
      MemDev.blocks.rev_onto(acc, Con{v, t})
    case 1n+p Con{h, t}:
      MemDev.set.go(p, t, v, Con{h, acc})
    case _ Nil{}:
      MemDev.blocks.rev_onto(acc, Nil{})

def MemDev.set(i: Nat, blocks: List<&2, B.Octets>, v: B.Octets) -> List<&2, B.Octets>:
  MemDev.set.go(i, blocks, v, Nil{})

def MemDev.update.check(ok: Bool, +bs: Nat, blocks: List<&2, B.Octets>, +n: Nat, data: B.Octets) -> MemDev:
  match ok:
    case True{}:
      MemDev{bs, MemDev.set(n, blocks, data)}
    case False{}:
      MemDev{bs, blocks}

# block n replaced by data when data is exactly one block and block n
# exists; otherwise the device unchanged (write_block reports why)
def MemDev.update(d: MemDev, +n: Nat, +data: B.Octets) -> MemDev:
  match d:
    case MemDev{+bs, blocks}:
      MemDev.update.check(Nat.is_eq(B.Octets.len(data), bs), bs, blocks, n, data)

def MemDev.write.check(okl: Bool, okn: Bool, +d: MemDev, +n: Nat, +data: B.Octets) -> Result<&2, &2, DevError, MemDev>:
  match okl okn:
    case True{} True{}:
      Done{MemDev.update(d, n, data)}
    case False{} _:
      Fail{DevBadLength{MemDev.block_size(d), B.Octets.len(data)}}
    case True{} False{}:
      Fail{DevOutOfRange{n}}

# block n replaced by data, or why not
def MemDev.write_block(+d: MemDev, +n: Nat, +data: B.Octets) -> Result<&2, &2, DevError, MemDev>:
  MemDev.write.check(Nat.is_eq(B.Octets.len(data), MemDev.block_size(d)), Nat.is_lt(n, MemDev.block_count(d)), d, n, data)

# the device as a whole image
def MemDev.to_octets(d: MemDev) -> B.Octets:
  match d:
    case MemDev{bs, blocks}:
      B.Octets.concat(blocks)
