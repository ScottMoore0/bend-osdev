# bend-osdev-blockdev: the block-device interfaces that filesystems read
# (and later write) through, generic helpers over them, and an in-memory
# device.
#
# Two interfaces, both passed to a filesystem as template arguments, so a
# filesystem is specialised to its device at compile time:
#
# * the pure interface: a device is a value d of a Data type D, read as
#   often as one likes:
#     block_size(d) -> Nat
#     read_block(d, n) -> Result<&2, &2, DevError, Octets>
# * the owned interface: a device may be a single-owner value (a Type: an
#   Array, a file handle), so every operation hands the device back:
#     block_size(d) -> D & Nat
#     read_block(d, n) -> D & Result<&2, &2, DevError, Octets>
#     write_block(d, n, data) -> D & Result<&2, &2, DevError, Unit>
#
# Every pure device is an owned device through the adapters Dev.own_*
# below, and the laws tie the owned helpers on an adapted device to the pure
# ones. MemDev (here) is a pure device; ImgDev (imgdev.bend) is an owned
# device held in an Array<U32>.
import Base
import ../bytes/bytes.bend as B

type DevError is Data:
  DevOutOfRange{block: Nat}
  DevBadLength{expected: Nat, got: Nat}
  DevFailed{code: U32}

# The pure interface's helpers: built only from its two operations, so they
# work on every pure device

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

# count blocks from block first, as a list, in order (read_blocks joins
# them: LAWS_range.bend, read_blocks_list)
def Dev.read_list(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, +d: D, count: Nat, +first: Nat) -> Result<&2, &2, DevError, List<&2, B.Octets>>:
  match count:
    case 0n:
      Done{Nil{}}
    case 1n+p:
      do Result<&2, &2, DevError, List<&2, B.Octets>>:
        blk : B.Octets <- read_block(d, first)
        rest : List<&2, B.Octets> <- Dev.read_list(~D, ~read_block, d, p, Nat.add(first, 1n))
        return Con{blk, rest}

# Specifications for the laws (they run, too)

def Dev.uniform.ok(r: Result<&2, &2, DevError, B.Octets>, +bs: Nat) -> Bool:
  match r:
    case Done{b}:
      Nat.is_eq(B.Octets.len(b), bs)
    case Fail{e}:
      False{}

# whether count blocks from block first each read as exactly bs bytes
def Dev.uniform.go(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, count: Nat, +d: D, +bs: Nat, +first: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Dev.uniform.ok(read_block(d, first), bs), Dev.uniform.go(~D, ~read_block, p, d, bs, Nat.add(first, 1n)))

# whether blocks 0 to n - 1 of d each read as exactly block_size(d) bytes:
# then the blocks joined are the device's first n * block_size(d) bytes, and
# Dev.read_bytes reads inside them (LAWS_range.bend, read_bytes_image)
def Dev.uniform(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, +d: D, n: Nat) -> Bool:
  Dev.uniform.go(~D, ~read_block, n, d, block_size(d), 0n)

# o with the bytes from offset off on replaced by data: the bytes before off,
# then data, then the bytes of o after off + len(data) (what a write of data
# at off does to a device's image)
def Dev.patch(+off: Nat, +data: B.Octets, +o: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.take(off, o), B.Octets.append(data, B.Octets.drop(Nat.add(off, B.Octets.len(data)), o)))

# The adapters: a pure device as an owned one (the device handed back is
# the device itself)

def Dev.own_block_size(~D: Data, ~block_size: D -> Nat, +d: D) -> D & Nat:
  (d, block_size(d))

def Dev.own_read_block(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, DevError, B.Octets>, +d: D, n: Nat) -> D & Result<&2, &2, DevError, B.Octets>:
  (d, read_block(d, n))

def Dev.own_write.fin(~D: Data, +d: D, r: Result<&2, &2, DevError, D>) -> D & Result<&2, &2, DevError, Unit>:
  match r:
    case Done{d2}:
      (d2, Done{Unit{}})
    case Fail{e}:
      (d, Fail{e})

# a pure write (the new device, or why not) as an owned one: on a failed
# write the device is handed back unchanged
def Dev.own_write_block(~D: Data, ~write_block: D -> Nat -> B.Octets -> Result<&2, &2, DevError, D>, +d: D, n: Nat, data: B.Octets) -> D & Result<&2, &2, DevError, Unit>:
  Dev.own_write.fin(~D, d, write_block(d, n, data))

# The owned interface's helpers: each read hands the device on to the next

def ODev.join(~D: Type, blk: B.Octets, r: D & Result<&2, &2, DevError, B.Octets>) -> D & Result<&2, &2, DevError, B.Octets>:
  (d, res) = r
  match res:
    case Done{rest}:
      (d, Done{B.Octets.append(blk, rest)})
    case Fail{e}:
      (d, Fail{e})

def ODev.then(~D: Type, r: D & Result<&2, &2, DevError, B.Octets>, k: D -> D & Result<&2, &2, DevError, B.Octets>) -> D & Result<&2, &2, DevError, B.Octets>:
  (d, res) = r
  match res:
    case Done{blk}:
      ODev.join(~D, blk, k(d))
    case Fail{e}:
      (d, Fail{e})

# count blocks from block first, joined; the device is handed back however
# the reads end (count comes first: it shrinks in the recursion)
def ODev.read_blocks(~D: Type, ~read_block: D -> Nat -> D & Result<&2, &2, DevError, B.Octets>, count: Nat, d: D, +first: Nat) -> D & Result<&2, &2, DevError, B.Octets>:
  match count:
    case 0n:
      (d, Done{B.Octets.empty()})
    case 1n+p:
      ODev.then(~D, read_block(d, first), d2 => ODev.read_blocks(~D, ~read_block, p, d2, Nat.add(first, 1n)))

def ODev.slice(~D: Type, +skip: Nat, +len: Nat, r: D & Result<&2, &2, DevError, B.Octets>) -> D & Result<&2, &2, DevError, B.Octets>:
  (d, res) = r
  match res:
    case Done{blocks}:
      (d, Done{B.Octets.slice(skip, len, blocks)})
    case Fail{e}:
      (d, Fail{e})

def ODev.read_bytes.go(~D: Type, ~read_block: D -> Nat -> D & Result<&2, &2, DevError, B.Octets>, r: D & Nat, +off: Nat, +len: Nat) -> D & Result<&2, &2, DevError, B.Octets>:
  (d, +bs) = r
  +skip = Nat.mod(off, bs)
  ODev.slice(~D, skip, len, ODev.read_blocks(~D, ~read_block, Nat.div(Nat.add(Nat.add(skip, len), Nat.sub(bs, 1n)), bs), d, Nat.div(off, bs)))

def ODev.read_bytes.some(~D: Type, ~block_size: D -> D & Nat, ~read_block: D -> Nat -> D & Result<&2, &2, DevError, B.Octets>, empty: Bool, d: D, off: Nat, len: Nat) -> D & Result<&2, &2, DevError, B.Octets>:
  match empty:
    case True{}:
      (d, Done{B.Octets.empty()})
    case False{}:
      ODev.read_bytes.go(~D, ~read_block, block_size(d), off, len)

# len bytes from byte offset off; reading zero bytes always succeeds and
# reads no block
def ODev.read_bytes(~D: Type, ~block_size: D -> D & Nat, ~read_block: D -> Nat -> D & Result<&2, &2, DevError, B.Octets>, d: D, off: Nat, +len: Nat) -> D & Result<&2, &2, DevError, B.Octets>:
  ODev.read_bytes.some(~D, ~block_size, ~read_block, Nat.is_eq(len, 0n), d, off, len)

# MemDev: a pure device held in memory. Its blocks are kept in a tree
# split by block number (a node holds the count of block numbers on its
# left), so a read or a write walks one path: O(log n) on the trees the
# defs build. A block never written reads as zeros. The representation is
# internal.

type MemTree is Data:
  MemTEmpty{}
  MemTLeaf{block: B.Octets}
  MemTNode{left_count: Nat, left: MemTree, right: MemTree}

def MemTree.left_count(t: MemTree) -> Nat:
  match t:
    case MemTNode{k, l, r}:
      k
    case MemTLeaf{b}:
      0n
    case MemTEmpty{}:
      0n

def MemTree.get.leaf(z: Bool, b: B.Octets) -> Maybe<&2, B.Octets>:
  match z:
    case True{}:
      Some{b}
    case False{}:
      None{}

# block n of t (z: whether n is left of t's split, computed by the caller
# from t's left count, so that the walk is one structural descent)
def MemTree.get.at(t: MemTree, +n: Nat, z: Bool) -> Maybe<&2, B.Octets>:
  match t z:
    case MemTEmpty{} _:
      None{}
    case MemTLeaf{b} _:
      MemTree.get.leaf(Nat.is_eq(n, 0n), b)
    case MemTNode{k, +l, r} True{}:
      MemTree.get.at(l, n, Nat.is_lt(n, MemTree.left_count(l)))
    case MemTNode{+k, l, +r} False{}:
      +m = Nat.sub(n, k)
      MemTree.get.at(r, m, Nat.is_lt(m, MemTree.left_count(r)))

def MemTree.get(+t: MemTree, +n: Nat) -> Maybe<&2, B.Octets>:
  MemTree.get.at(t, n, Nat.is_lt(n, MemTree.left_count(t)))

def MemTree.set.leaf(+n: Nat, b: B.Octets, v: B.Octets) -> MemTree:
  match n:
    case 0n:
      MemTLeaf{v}
    case 1n+p:
      MemTNode{n, MemTLeaf{b}, MemTLeaf{v}}

# t with block n set to v (a block number t has no place for is added)
def MemTree.set.at(t: MemTree, +n: Nat, v: B.Octets, z: Bool) -> MemTree:
  match t z:
    case MemTEmpty{} _:
      MemTNode{n, MemTEmpty{}, MemTLeaf{v}}
    case MemTLeaf{b} _:
      MemTree.set.leaf(n, b, v)
    case MemTNode{k, +l, r} True{}:
      MemTNode{k, MemTree.set.at(l, n, v, Nat.is_lt(n, MemTree.left_count(l))), r}
    case MemTNode{+k, l, +r} False{}:
      +m = Nat.sub(n, k)
      MemTNode{k, l, MemTree.set.at(r, m, v, Nat.is_lt(m, MemTree.left_count(r)))}

def MemTree.set(+t: MemTree, +n: Nat, v: B.Octets) -> MemTree:
  MemTree.set.at(t, n, v, Nat.is_lt(n, MemTree.left_count(t)))

# Building a balanced tree from a list of blocks, in order

type MemTBuilt is Data:
  MemTBuilt{tree: MemTree, rest: List<&2, B.Octets>}

def MemTree.build.fin(+h: Nat, l: MemTree, b: MemTBuilt) -> MemTBuilt:
  match b:
    case MemTBuilt{r, rest}:
      MemTBuilt{MemTNode{h, l, r}, rest}

def MemTree.build.node(+h: Nat, b: MemTBuilt, k: List<&2, B.Octets> -> MemTBuilt) -> MemTBuilt:
  match b:
    case MemTBuilt{l, rest}:
      MemTree.build.fin(h, l, k(rest))

def MemTree.build.one(xs: List<&2, B.Octets>) -> MemTBuilt:
  match xs:
    case Con{b, t}:
      MemTBuilt{MemTLeaf{b}, t}
    case Nil{}:
      MemTBuilt{MemTEmpty{}, Nil{}}

# the first n blocks of xs as a tree (fuel: at least its depth), and the rest
def MemTree.build(+fuel: Nat, +n: Nat, xs: List<&2, B.Octets>) -> MemTBuilt:
  match fuel:
    case 0n:
      MemTBuilt{MemTEmpty{}, xs}
    case 1n+f:
      match n:
        case 0n:
          MemTBuilt{MemTEmpty{}, xs}
        case 1n+p:
          match p:
            case 0n:
              MemTree.build.one(xs)
            case 1n+q:
              +h = Nat.div(n, 2n)
              MemTree.build.node(h, MemTree.build(f, h, xs), ys => MemTree.build(f, Nat.sub(n, h), ys))

def MemTree.of_list.fin(b: MemTBuilt) -> MemTree:
  match b:
    case MemTBuilt{t, rest}:
      t

def MemTree.of_list(+n: Nat, xs: List<&2, B.Octets>) -> MemTree:
  MemTree.of_list.fin(MemTree.build(n, n, xs))

# The device: its block size, its count of blocks, and the tree of its
# blocks

type MemDev is Data:
  MemDev{block_size: Nat, count: Nat, tree: MemTree}

# n blocks of bs bytes cut from o, reversed onto acc
def MemDev.split.go(n: Nat, +bs: Nat, o: B.Octets, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +rest = o
      +blk = B.Octets.take(bs, rest)
      MemDev.split.go(p, bs, B.Octets.drop(bs, rest), Con{B.Octets.append(blk, B.Octets.zeros(Nat.sub(bs, B.Octets.len(blk)))), acc})

def MemDev.blocks.rev_onto(xs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      MemDev.blocks.rev_onto(t, Con{h, acc})

def MemDev.of_octets.go(+bs: Nat, +n: Nat, o: B.Octets) -> MemDev:
  MemDev{bs, n, MemTree.of_list(n, MemDev.blocks.rev_onto(MemDev.split.go(n, bs, o, Nil{}), Nil{}))}

# an image as a device; a final partial block is padded with zeros
def MemDev.of_octets(+bs: Nat, +o: B.Octets) -> MemDev:
  MemDev.of_octets.go(bs, Nat.div(Nat.add(B.Octets.len(o), Nat.sub(bs, 1n)), bs), o)

# count zero blocks
def MemDev.blank(bs: Nat, count: Nat) -> MemDev:
  MemDev{bs, count, MemTEmpty{}}

def MemDev.block_size(d: MemDev) -> Nat:
  match d:
    case MemDev{bs, c, t}:
      bs

def MemDev.block_count(d: MemDev) -> Nat:
  match d:
    case MemDev{bs, c, t}:
      c

def MemDev.read.got(+bs: Nat, m: Maybe<&2, B.Octets>) -> B.Octets:
  match m:
    case Some{b}:
      b
    case None{}:
      B.Octets.zeros(bs)

def MemDev.read.check(ok: Bool, +bs: Nat, +t: MemTree, +n: Nat) -> Result<&2, &2, DevError, B.Octets>:
  match ok:
    case True{}:
      Done{MemDev.read.got(bs, MemTree.get(t, n))}
    case False{}:
      Fail{DevOutOfRange{n}}

def MemDev.read_block.go(d: MemDev, +n: Nat) -> Result<&2, &2, DevError, B.Octets>:
  match d:
    case MemDev{bs, +c, t}:
      MemDev.read.check(Nat.is_lt(n, c), bs, t, n)

# block n (the pure interface's read_block, with plain parameters so it
# fits the template type every filesystem expects)
def MemDev.read_block(d: MemDev, n: Nat) -> Result<&2, &2, DevError, B.Octets>:
  MemDev.read_block.go(d, n)

def MemDev.update.check(ok: Bool, +bs: Nat, +c: Nat, t: MemTree, +n: Nat, data: B.Octets) -> MemDev:
  match ok:
    case True{}:
      MemDev{bs, c, MemTree.set(t, n, data)}
    case False{}:
      MemDev{bs, c, t}

# block n replaced by data when data is exactly one block and block n
# exists; otherwise the device unchanged (write_block reports why)
def MemDev.update(d: MemDev, +n: Nat, +data: B.Octets) -> MemDev:
  match d:
    case MemDev{+bs, +c, t}:
      MemDev.update.check(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)), bs, c, t, n, data)

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

# the blocks 0 to n - 1, in order, onto acc
def MemDev.blocks.go(n: Nat, +bs: Nat, +t: MemTree, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match n:
    case 0n:
      acc
    case 1n+ +p:
      MemDev.blocks.go(p, bs, t, Con{MemDev.read.got(bs, MemTree.get(t, p)), acc})

# the device as a whole image
def MemDev.to_octets(d: MemDev) -> B.Octets:
  match d:
    case MemDev{+bs, c, +t}:
      B.Octets.concat(MemDev.blocks.go(c, bs, t, Nil{}))

# MemDev on the owned interface (through the adapters; plain parameters, so
# they fit the owned interface's template types)

def MemDev.own_block_size(d: MemDev) -> MemDev & Nat:
  Dev.own_block_size(~MemDev, ~MemDev.block_size, d)

def MemDev.own_read_block(d: MemDev, n: Nat) -> MemDev & Result<&2, &2, DevError, B.Octets>:
  Dev.own_read_block(~MemDev, ~MemDev.read_block, d, n)

def MemDev.own_write_block.go(+d: MemDev, n: Nat, data: B.Octets) -> MemDev & Result<&2, &2, DevError, Unit>:
  Dev.own_write.fin(~MemDev, d, MemDev.write_block(d, n, data))

def MemDev.own_write_block(d: MemDev, n: Nat, data: B.Octets) -> MemDev & Result<&2, &2, DevError, Unit>:
  MemDev.own_write_block.go(d, n, data)

# whether every block of d reads as exactly block_size(d) bytes (true of
# every device of_octets, blank and update build: LAWS_range.bend)
def MemDev.valid(+d: MemDev) -> Bool:
  Dev.uniform(~MemDev, ~MemDev.block_size, ~MemDev.read_block, d, MemDev.block_count(d))
