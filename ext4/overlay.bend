# bend-osdev-ext4: a device that keeps writes aside: reads see them, the
# device underneath is not touched. It is the journalling layer's device:
# a writer runs on it unchanged, and its writes become one transaction
# (jtx.bend, jext2.bend), or are written straight through (Ext4Ov.flush). A writer (ext2's, or any code over
# blockdev's pure interface and a pure write) runs on it, and its writes
# become one journal transaction (Ext4Journal.transact).
#
# The overlay is itself a device: Ext4Ov.block_size, read_block and
# write_block are the pure interface and the pure write, given the
# underlying device's operations as template arguments.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./jwrite.bend as JW
import ./devwrite.bend as DW

type Ext4Ov<-Dv: Data> is Data:
  Ext4Ov{base: Dv, writes: List<&2, JW.Jbd2Write>}

# an overlay on d with nothing written
def Ext4Ov.start(-Dv: Data, d: Dv) -> Ext4Ov<Dv>:
  Ext4Ov{d, Nil{}}

def Ext4Ov.block_size(~Dv: Data, ~block_size: Dv -> Nat, o: Ext4Ov<Dv>) -> Nat:
  match o:
    case Ext4Ov{d, ws}:
      block_size(d)

def Ext4Ov.find.pick(hit: Bool, data: B.Octets) -> Maybe<&2, B.Octets>:
  match hit:
    case True{}:
      Some{data}
    case False{}:
      None{}

# the last write to block n (writes are kept last first)
def Ext4Ov.find(ws: List<&2, JW.Jbd2Write>, +n: Nat, found: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match ws found:
    case _ Some{x}:
      Some{x}
    case Nil{} None{}:
      None{}
    case Con{JW.Jbd2Write{+b, data}, t} None{}:
      Ext4Ov.find(t, n, Ext4Ov.find.pick(Nat.is_eq(b, n), data))

def Ext4Ov.read.got(~Dv: Data, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, m: Maybe<&2, B.Octets>, d: Dv, n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      read_block(d, n)

# block n: as last written, else the underlying device's
def Ext4Ov.read_block(~Dv: Data, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, o: Ext4Ov<Dv>, n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  match o:
    case Ext4Ov{d, ws}:
      +k = n
      Ext4Ov.read.got(~Dv, ~read_block, Ext4Ov.find(ws, k, None{}), d, k)

def Ext4Ov.write.check(-Dv: Data, ok: Bool, +d: Dv, ws: List<&2, JW.Jbd2Write>, +n: Nat, +data: B.Octets, +bs: Nat) -> Result<&2, &2, D.DevError, Ext4Ov<Dv>>:
  match ok:
    case True{}:
      Done{Ext4Ov{d, Con{JW.Jbd2Write{n, data}, ws}}}
    case False{}:
      Fail{D.DevBadLength{bs, B.Octets.len(data)}}

# block n written (kept aside): data must be one block of the device
def Ext4Ov.write_block(~Dv: Data, ~block_size: Dv -> Nat, o: Ext4Ov<Dv>, n: Nat, data: B.Octets) -> Result<&2, &2, D.DevError, Ext4Ov<Dv>>:
  match o:
    case Ext4Ov{+d, ws}:
      +bs = block_size(d)
      +x = data
      Ext4Ov.write.check(Dv, Nat.is_eq(B.Octets.len(x), bs), d, ws, n, x, bs)

def Ext4Ov.seen(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(Nat.is_eq(x, n), Ext4Ov.seen(t, n))

def Ext4Ov.keep(dup: Bool, +w: JW.Jbd2Write, +b: Nat, seen: List<&2, Nat>, acc: List<&2, JW.Jbd2Write>) -> List<&2, Nat> & List<&2, JW.Jbd2Write>:
  match dup:
    case True{}:
      (seen, acc)
    case False{}:
      (Con{b, seen}, Con{w, acc})

def Ext4Ov.dedup(ws: List<&2, JW.Jbd2Write>, st: List<&2, Nat> & List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match ws:
    case Nil{}:
      (seen, acc) = st
      acc
    case Con{+w, t}:
      (+seen, acc) = st
      +b = JW.Jbd2Write.block(w)
      Ext4Ov.dedup(t, Ext4Ov.keep(Ext4Ov.seen(seen, b), w, b, seen, acc))

# the blocks written, each once with its last contents, in the order of
# those last writes
def Ext4Ov.writes(-Dv: Data, o: Ext4Ov<Dv>) -> List<&2, JW.Jbd2Write>:
  match o:
    case Ext4Ov{d, ws}:
      Ext4Ov.dedup(ws, (Nil{}, Nil{}))

# the device underneath, untouched
def Ext4Ov.base(-Dv: Data, o: Ext4Ov<Dv>) -> Dv:
  match o:
    case Ext4Ov{d, ws}:
      d

# The device underneath with the writes written on it (no journal): what a
# writer run on the overlay would have done on the device directly
# (LAWS.bend: ov_flush); a failed writer's failure is the answer
def Ext4Ov.flush(~Dv: Data, ~block_size: Dv -> Nat, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, r: Result<&2, &2, E.Ext4Error, Ext4Ov<Dv>>) -> Result<&2, &2, E.Ext4Error, Dv>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Ext4Ov{+d, ws}}:
      DW.Ext4Dev.write_all(~Dv, ~block_size, ~write_block, Ext4Ov.dedup(ws, (Nil{}, Nil{})), Done{d}, block_size(d))

# The overlay of a MemDev, with plain parameters (to pass as template
# arguments: ~Ext4Ov<MemDev>, ~Ext4Ov.mem_block_size, ~Ext4Ov.mem_read,
# ~Ext4Ov.mem_write)

def Ext4Ov.mem_block_size(o: Ext4Ov<D.MemDev>) -> Nat:
  Ext4Ov.block_size(~D.MemDev, ~D.MemDev.block_size, o)

def Ext4Ov.mem_read(o: Ext4Ov<D.MemDev>, n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  Ext4Ov.read_block(~D.MemDev, ~D.MemDev.read_block, o, n)

def Ext4Ov.mem_write(o: Ext4Ov<D.MemDev>, n: Nat, data: B.Octets) -> Result<&2, &2, D.DevError, Ext4Ov<D.MemDev>>:
  Ext4Ov.write_block(~D.MemDev, ~D.MemDev.block_size, o, n, data)

# block m of the overlay a writing gave (or why the writing failed)
def Ext4Ov.read_mem(r: Result<&2, &2, E.Ext4Error, Ext4Ov<D.MemDev>>, m: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match r:
    case Done{o}:
      DW.Ext4Dev.dev_read(Ext4Ov.mem_read(o, m))
    case Fail{e}:
      Fail{e}
