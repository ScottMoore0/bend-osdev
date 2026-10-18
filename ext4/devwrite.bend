# bend-osdev-ext4: writing filesystem blocks, and the superblock, through
# blockdev's pure write (the shape of MemDev.write_block and of what
# blockdev's Dev.own_write_block adapts: D -> Nat -> Octets ->
# Result<&2, &2, DevError, D>, the device after the write).
#
# A filesystem block of bs bytes is one device block when the device's
# blocks are as large, or bs / dbs device blocks when the device's blocks
# (dbs bytes) divide it.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ../ext2/csum.bend as K
import ./error.bend as E
import ./jwrite.bend as JW

def Ext4Dev.lift(-Dv: Data, r: Result<&2, &2, D.DevError, Dv>) -> Result<&2, &2, E.Ext4Error, Dv>:
  match r:
    case Done{d}:
      Done{d}
    case Fail{e}:
      Fail{E.Ext4DevWrite{e}}

def Ext4Dev.mem_write.fin(r: D.MemDev & Result<&2, &2, D.DevError, Unit>) -> Result<&2, &2, D.DevError, D.MemDev>:
  (d, x) = r
  match x:
    case Done{u}:
      Done{d}
    case Fail{e}:
      Fail{e}

# MemDev's write as the pure write template expects it (from blockdev's
# owned write, MemDev.own_write_block, whose law own_write_ok says what a
# good write does)
def Ext4Dev.mem_write(d: D.MemDev, n: Nat, data: B.Octets) -> Result<&2, &2, D.DevError, D.MemDev>:
  Ext4Dev.mem_write.fin(D.MemDev.own_write_block(d, n, data))

# the pieces of data, dbs bytes each, written to device blocks from first
# on, a tail call each
def Ext4Dev.pieces(~Dv: Data, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, k: Nat, r: Result<&2, &2, D.DevError, Dv>, +dbs: Nat, +first: Nat, +data: B.Octets) -> Result<&2, &2, D.DevError, Dv>:
  match k r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{d}:
      Done{d}
    case 1n+p Done{d}:
      Ext4Dev.pieces(~Dv, ~write_block, p, write_block(d, first, B.Octets.take(dbs, data)), dbs, Nat.add(first, 1n), B.Octets.drop(dbs, data))

def Ext4Dev.write.go(~Dv: Data, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, same: Bool, divides: Bool, d: Dv, +dbs: Nat, +bs: Nat, +n: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext4Error, Dv>:
  match same divides:
    case True{} _:
      Ext4Dev.lift(Dv, write_block(d, n, data))
    case False{} True{}:
      +k = Nat.div(bs, dbs)
      Ext4Dev.lift(Dv, Ext4Dev.pieces(~Dv, ~write_block, k, Done{d}, dbs, Nat.mul(n, k), data))
    case False{} False{}:
      Fail{E.Ext4BadDevBlock{bs, dbs}}

# the device after filesystem block n (bs bytes) becomes data
def Ext4Dev.write(~Dv: Data, ~block_size: Dv -> Nat, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +bs: Nat, +n: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext4Error, Dv>:
  +dbs = block_size(d)
  Ext4Dev.write.go(~Dv, ~write_block, Nat.is_eq(dbs, bs), Bool.and(Nat.is_lt(0n, dbs), Nat.is_eq(Nat.mod(bs, dbs), 0n)), d, dbs, bs, n, data)

# The superblock: 1024 bytes at byte 1024, in block 1 of a 1 KiB-block
# filesystem and at offset 1024 of block 0 otherwise

# the superblock's 1024 bytes with s_feature_incompat (byte 96) ORed with
# set and ANDed with the complement of clear, and its checksum (bytes
# 1020-1023, metadata_csum) recomputed
def Ext4Dev.super_with.seal(meta: Bool, +sb: B.Octets) -> B.Octets:
  match meta:
    case True{}:
      B.Octets.append(B.Octets.take(1020n, sb), B.Octets.le32(K.Ext2Csum.super(sb)))
    case False{}:
      sb

def Ext4Dev.super_with(+sb: B.Octets, set: U32, clear: U32) -> B.Octets:
  +old = Maybe.default(&2, U32, B.Octets.le32_at(sb, 96n), 0)
  +new = U32.and(U32.or(old, set), U32.not(clear))
  +x = B.Octets.append(B.Octets.take(96n, sb), B.Octets.append(B.Octets.le32(new), B.Octets.drop(100n, sb)))
  Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x)

def Ext4Dev.super_block(one_k: Bool) -> Nat:
  match one_k:
    case True{}:
      1n
    case False{}:
      0n

def Ext4Dev.super_off(one_k: Bool) -> Nat:
  match one_k:
    case True{}:
      0n
    case False{}:
      1024n

# the device after its superblock's incompat features change (set some
# bits, clear others), its checksum kept right; fs: the filesystem as
# mounted (its block size)
def Ext4Dev.set_incompat(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: XS.Ext2Fs, set: U32, clear: U32) -> Result<&2, &2, E.Ext4Error, Dv>:
  +bs = XS.Ext2Fs.block_size(fs)
  +one = Nat.is_eq(bs, 1024n)
  +n = Ext4Dev.super_block(one)
  +off = Ext4Dev.super_off(one)
  do Result<&2, &2, E.Ext4Error, Dv>:
    o : B.Octets <- E.Ext4Error.lift(B.Octets, XS.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, n))
    +blk : B.Octets = o
    +sb : B.Octets = Ext4Dev.super_with(B.Octets.slice(off, 1024n, blk), set, clear)
    Ext4Dev.write(~Dv, ~block_size, ~write_block, d, bs, n, B.Octets.append(B.Octets.take(off, blk), B.Octets.append(sb, B.Octets.drop(Nat.add(off, 1024n), blk))))

# Many writes: each filesystem block written in order (a replay's writes,
# or the writes a transaction journals, applied directly); r is the device
# so far, and the first failure is the answer

def Ext4Dev.write_all(~Dv: Data, ~block_size: Dv -> Nat, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, ws: List<&2, JW.Jbd2Write>, r: Result<&2, &2, E.Ext4Error, Dv>, +bs: Nat) -> Result<&2, &2, E.Ext4Error, Dv>:
  match ws r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{d}:
      Done{d}
    case Con{JW.Jbd2Write{n, data}, t} Done{d}:
      Ext4Dev.write_all(~Dv, ~block_size, ~write_block, t, Ext4Dev.write(~Dv, ~block_size, ~write_block, d, bs, n, data), bs)

# whether every write is one block of bs bytes to a block below count
def Ext4Dev.fits(+bs: Nat, +count: Nat, ws: List<&2, JW.Jbd2Write>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{JW.Jbd2Write{n, data}, t}:
      Bool.and(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, count)), Ext4Dev.fits(bs, count, t))

def Ext4Dev.dev_read(r: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match r:
    case Done{o}:
      Done{o}
    case Fail{e}:
      Fail{E.Ext4DevRead{e}}

# block m of a MemDev that writing gave (or why the writing failed)
def Ext4Dev.read_mem(r: Result<&2, &2, E.Ext4Error, D.MemDev>, m: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match r:
    case Done{d}:
      Ext4Dev.dev_read(D.MemDev.read_block(d, m))
    case Fail{e}:
      Fail{e}
