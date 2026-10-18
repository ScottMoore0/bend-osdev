# bend-osdev-ext4: ext2's writer (bend-osdev-ext2: mkdir, create, write,
# link, rename, truncate, ...) journalled: its operations run, unchanged,
# on an overlay of the device (overlay.bend: the journalling device, which
# keeps every write aside), and the writes they made become one jbd2
# transaction (jtx.bend), logged, committed and checkpointed as the
# kernel's jbd2 does, in data=journal or data=ordered mode.
#
# The writer's own check (ext2's Ext2Op.run: the counts, and what each
# operation promises) runs on the overlay before anything reaches the
# device, so a refused operation writes nothing. In data=ordered mode the
# blocks the transaction allocates (those free in the old image's block
# bitmaps) are written in place before the commit; every other block is
# logged.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ../ext2/meta.bend as XT
import ../ext2/bitmap.bend as XM
import ../ext2/ops.bend as XP
import ../ext2/run.bend as XR
import ../ext2/wopts.bend as XW
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./jwrite.bend as JW
import ./overlay.bend as OV
import ./jtx.bend as JT

# ext2's operations, in order, on the overlay r (each checked as the write
# options say); the first refusal is the answer
def Ext4JExt2.ops(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ops: List<&2, XP.Ext2Op>, r: Result<&2, &2, E.Ext4Error, OV.Ext4Ov<Dv>>, +fs: XS.Ext2Fs, +wo: XW.Ext2WriteOptions) -> Result<&2, &2, E.Ext4Error, OV.Ext4Ov<Dv>>:
  match ops r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{o}:
      Done{o}
    case Con{op, t} Done{o}:
      Ext4JExt2.ops(~Dv, ~block_size, ~read_block, t, E.Ext4Error.lift(OV.Ext4Ov<Dv>, XR.Ext2Op.run(~OV.Ext4Ov<Dv>, ~(x => OV.Ext4Ov.block_size(~Dv, ~block_size, x)), ~(x => n => OV.Ext4Ov.read_block(~Dv, ~read_block, x, n)), ~(x => n => v => OV.Ext4Ov.write_block(~Dv, ~block_size, x, n, v)), op, o, fs, wo)), fs, wo)

def Ext4JExt2.kept(-Dv: Data, r: Result<&2, &2, E.Ext4Error, OV.Ext4Ov<Dv>>) -> Result<&2, &2, E.Ext4Error, List<&2, JW.Jbd2Write>>:
  match r:
    case Done{o}:
      Done{OV.Ext4Ov.writes(Dv, o)}
    case Fail{e}:
      Fail{e}

# the writes ext2's operations make on d, each block once with its last
# contents, nothing written to d; the device's blocks must be the
# filesystem's
def Ext4JExt2.writes(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ops: List<&2, XP.Ext2Op>, +d: Dv, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions) -> Result<&2, &2, E.Ext4Error, List<&2, JW.Jbd2Write>>:
  +bs = S.Ext4Fs.block_size(fs)
  do Result<&2, &2, E.Ext4Error, List<&2, JW.Jbd2Write>>:
    E.Ext4.require(Nat.is_eq(block_size(d), bs), E.Ext4BadDevBlock{bs, block_size(d)})
    Ext4JExt2.kept(Dv, Ext4JExt2.ops(~Dv, ~block_size, ~read_block, ops, Done{OV.Ext4Ov.start(Dv, d)}, S.Ext4Fs.ext2(fs), wo))

# Blocks free before the transaction (read from the old image's block
# bitmaps; an uninit group's is computed by ext2)

type Ext4JBitmap is Data:
  Ext4JBitmap{group: Nat, bits: B.Octets}

def Ext4JExt2.bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: XS.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext4Error, Ext4JBitmap>:
  do Result<&2, &2, E.Ext4Error, Ext4JBitmap>:
    raw : B.Octets <- E.Ext4Error.lift(B.Octets, XT.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g))
    bm : B.Octets <- E.Ext4Error.lift(B.Octets, XT.Ext2Meta.block_bitmap(~Dv, ~block_size, ~read_block, d, fs, g, XT.Ext2Meta.desc(fs, raw)))
    return Ext4JBitmap{g, bm}

# the search so far: the last bitmap read, and the free blocks found (last
# first)
type Ext4JFresh is Data:
  Ext4JFresh{cache: Maybe<&2, Ext4JBitmap>, found: List<&2, Nat>}

def Ext4JExt2.cached(c: Maybe<&2, Ext4JBitmap>, +g: Nat) -> Bool:
  match c:
    case Some{Ext4JBitmap{h, bm}}:
      Nat.is_eq(h, g)
    case None{}:
      False{}

def Ext4JExt2.pick(hit: Bool, +b: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      Con{b, acc}
    case False{}:
      acc

def Ext4JExt2.test(r: Result<&2, &2, E.Ext4Error, Ext4JBitmap>, +b: Nat, +k: Nat, acc: List<&2, Nat>) -> Result<&2, &2, E.Ext4Error, Ext4JFresh>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Ext4JBitmap{g, +bm}}:
      Done{Ext4JFresh{Some{Ext4JBitmap{g, bm}}, Ext4JExt2.pick(Bool.not(XM.Ext2Bitmap.test(bm, k)), b, acc)}}

def Ext4JExt2.again(c: Maybe<&2, Ext4JBitmap>) -> Result<&2, &2, E.Ext4Error, Ext4JBitmap>:
  match c:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{E.Ext4BadJournal{"no block bitmap"}}

def Ext4JExt2.look(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, hit: Bool, c: Maybe<&2, Ext4JBitmap>, +d: Dv, +fs: XS.Ext2Fs, +g: Nat, +b: Nat, +k: Nat, acc: List<&2, Nat>) -> Result<&2, &2, E.Ext4Error, Ext4JFresh>:
  match hit:
    case True{}:
      Ext4JExt2.test(Ext4JExt2.again(c), b, k, acc)
    case False{}:
      Ext4JExt2.test(Ext4JExt2.bitmap(~Dv, ~block_size, ~read_block, d, fs, g), b, k, acc)

def Ext4JExt2.one(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inside: Bool, c: Maybe<&2, Ext4JBitmap>, +d: Dv, +fs: XS.Ext2Fs, +b: Nat, acc: List<&2, Nat>) -> Result<&2, &2, E.Ext4Error, Ext4JFresh>:
  match inside:
    case False{}:
      Done{Ext4JFresh{c, acc}}
    case True{}:
      +sb = XS.Ext2Fs.sb(fs)
      +i = Nat.sub(b, U32.to_nat(XS.Ext2Super.first_data_block(sb)))
      +bpg = U32.to_nat(XS.Ext2Super.blocks_per_group(sb))
      +g = Nat.div(i, bpg)
      +cc = c
      Ext4JExt2.look(~Dv, ~block_size, ~read_block, Ext4JExt2.cached(cc, g), cc, d, fs, g, b, Nat.mod(i, bpg), acc)

def Ext4JExt2.fresh.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ws: List<&2, JW.Jbd2Write>, r: Result<&2, &2, E.Ext4Error, Ext4JFresh>, +d: Dv, +fs: XS.Ext2Fs) -> Result<&2, &2, E.Ext4Error, List<&2, Nat>>:
  match ws r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{Ext4JFresh{c, acc}}:
      Done{List.reverse(&2, Nat, acc)}
    case Con{JW.Jbd2Write{+b, o}, t} Done{Ext4JFresh{c, acc}}:
      +sb = XS.Ext2Fs.sb(fs)
      +inside = Bool.and(Nat.is_le(U32.to_nat(XS.Ext2Super.first_data_block(sb)), b), Nat.is_lt(b, XS.Ext2Fs.blocks(fs)))
      Ext4JExt2.fresh.go(~Dv, ~block_size, ~read_block, t, Ext4JExt2.one(~Dv, ~block_size, ~read_block, inside, c, d, fs, b, acc), d, fs)

# the blocks of ws that are free in d's block bitmaps
def Ext4JExt2.fresh(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, List<&2, Nat>>:
  Ext4JExt2.fresh.go(~Dv, ~block_size, ~read_block, ws, Done{Ext4JFresh{None{}, Nil{}}}, d, S.Ext4Fs.ext2(fs))

def Ext4JExt2.fresh_for(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, m: JT.Jbd2Mode, +d: Dv, +fs: S.Ext4Fs, ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, List<&2, Nat>>:
  match m:
    case JT.Jbd2DataJournal{}:
      Done{Nil{}}
    case JT.Jbd2DataOrdered{}:
      Ext4JExt2.fresh(~Dv, ~block_size, ~read_block, d, fs, ws)

# the plan of ext2's operations ops on d as one transaction in mode m
# (nothing written; JT.Ext4JTx.apply writes it, or a prefix of it)
def Ext4JExt2.plan(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ops: List<&2, XP.Ext2Op>, +d: Dv, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions, +jo: O.Jbd2Options, +m: JT.Jbd2Mode) -> Result<&2, &2, E.Ext4Error, JT.Ext4JPlan>:
  do Result<&2, &2, E.Ext4Error, JT.Ext4JPlan>:
    +ws : List<&2, JW.Jbd2Write> <- Ext4JExt2.writes(~Dv, ~block_size, ~read_block, ops, d, fs, wo)
    fr : List<&2, Nat> <- Ext4JExt2.fresh_for(~Dv, ~block_size, ~read_block, m, d, fs, ws)
    JT.Ext4JTx.plan(~Dv, ~block_size, ~read_block, d, fs, jo, m, fr, ws)

# the device after ext2's operations ops, journalled as one transaction in
# mode m: logged, committed and checkpointed; or why not (the device as it
# was)
def Ext4JExt2.run(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, ops: List<&2, XP.Ext2Op>, +d: Dv, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions, +jo: O.Jbd2Options, +m: JT.Jbd2Mode) -> Result<&2, &2, E.Ext4Error, Dv>:
  do Result<&2, &2, E.Ext4Error, Dv>:
    +p : JT.Ext4JPlan <- Ext4JExt2.plan(~Dv, ~block_size, ~read_block, ops, d, fs, wo, jo, m)
    JT.Ext4JTx.apply(~Dv, ~block_size, ~read_block, ~write_block, d, fs, p, JT.Ext4JPlan.length(p))

# one operation, its own transaction
def Ext4JExt2.op(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, op: XP.Ext2Op, +d: Dv, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions, +jo: O.Jbd2Options, +m: JT.Jbd2Mode) -> Result<&2, &2, E.Ext4Error, Dv>:
  Ext4JExt2.run(~Dv, ~block_size, ~read_block, ~write_block, [op], d, fs, wo, jo, m)
