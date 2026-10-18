# Test support for the journalled-writes test (ref/jgen.py, ref/jmain.bend):
# a case is an image (an ext3 or ext4 file with a journal) and a list of
# transactions, each a list of ext2's operations. Each transaction is run
# twice: journalled (jext2.bend, in the case's data mode) and directly
# (ext2's writer on the device, no journal). Printed, for jgen.py:
#
#   case NAME
#   tx K ok STEPS COMMIT_AT LOG_BLOCKS IN_PLACE | tx K err KIND
#   direct K ok | direct K err KIND
#   cut N COMMIT_AT          a crash after the last transaction's first N
#   blk B HEX ...            steps: the crashed image's blocks that differ
#   rec N ok T R | rec N err KIND   from the original, then this package's
#   blk B HEX ...            recovery of it (T transactions, R blocks)
#   differ B1 B2 ...         blocks where the journalled and direct images
#                            differ
#   final
#   blk B HEX ...            the journalled image's blocks that differ from
#   done                     the original
#
# Only blocks a plan touches can differ (its homes, its journal blocks, the
# superblock), so only those are compared and printed.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../../ext2/ops.bend as XP
import ../../ext2/run.bend as XR
import ../../ext2/wopts.bend as XW
import ./image.bend as I
import ../error.bend as E
import ../options.bend as O
import ../super.bend as S
import ../jwrite.bend as JW
import ../jlog.bend as JL
import ../devwrite.bend as DW
import ../journal.bend as JR
import ../jtx.bend as JT
import ../jext2.bend as JX
import ../ext4.bend as X4

type Ext4JCase is Data:
  Ext4JCase{name: String, path: String, bs: Nat, count: Nat, nonzero: List<&2, Nat>, mode: JT.Jbd2Mode, crash: Bool, time: U32, txs: List<&2, List<&2, XP.Ext2Op>>}

def Ext4JDrv.err(+e: E.Ext4Error) -> String:
  E.Ext4Error.kind(e)

# Printing blocks

def Ext4JDrv.blk.go(same: Bool, +n: Nat, o: B.Octets) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print("blk " ++ Nat.show(n) ++ " " ++ B.Octets.hex(o))

def Ext4JDrv.blk(+n: Nat, a: Result<&2, &2, D.DevError, B.Octets>, b: Result<&2, &2, D.DevError, B.Octets>) -> IO(Unit):
  match a b:
    case Done{+x} Done{y}:
      Ext4JDrv.blk.go(B.Octets.is_eq(x, y), n, x)
    case _ _:
      IO.print("blk " ++ Nat.show(n) ++ " error")

# the blocks ns of d that differ from base
def Ext4JDrv.dump(ns: List<&2, Nat>, +d: D.MemDev, +base: D.MemDev) -> IO(Unit):
  match ns:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+n, t}:
      do IO<Unit>:
        Ext4JDrv.blk(n, D.MemDev.read_block(d, n), D.MemDev.read_block(base, n))
        Ext4JDrv.dump(t, d, base)

def Ext4JDrv.same(a: Result<&2, &2, D.DevError, B.Octets>, b: Result<&2, &2, D.DevError, B.Octets>) -> Bool:
  match a b:
    case Done{x} Done{y}:
      B.Octets.is_eq(x, y)
    case _ _:
      False{}

def Ext4JDrv.differ.add(same: Bool, +n: Nat, acc: String) -> String:
  match same:
    case True{}:
      acc
    case False{}:
      acc ++ " " ++ Nat.show(n)

# The blocks a plan touches


# the blocks ns where a and b differ, as text
def Ext4JDrv.differ(ns: List<&2, Nat>, +a: D.MemDev, +b: D.MemDev, acc: String) -> String:
  match ns:
    case Nil{}:
      acc
    case Con{+n, t}:
      Ext4JDrv.differ(t, a, b, Ext4JDrv.differ.add(Ext4JDrv.same(D.MemDev.read_block(a, n), D.MemDev.read_block(b, n)), n, acc))

def Ext4JDrv.add(+n: Nat, +us: List<&2, Nat>) -> List<&2, Nat>:
  JX.Ext4JExt2.pick(Bool.not(JL.Jbd2Log.member(us, n)), n, us)

def Ext4JDrv.add_home(r: Result<&2, &2, E.Ext4Error, Nat>, us: List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case Done{n}:
      Ext4JDrv.add(n, us)
    case Fail{e}:
      us

def Ext4JDrv.touched(xs: List<&2, JT.Ext4JStep>, +d: D.MemDev, +fs: S.Ext4Fs, +j: JR.Ext4Journal, us: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      us
    case Con{JT.Ext4JHome{JW.Jbd2Write{b, o}}, t}:
      Ext4JDrv.touched(t, d, fs, j, Ext4JDrv.add(b, us))
    case Con{JT.Ext4JLog{p, o}, t}:
      Ext4JDrv.touched(t, d, fs, j, Ext4JDrv.add_home(JR.Ext4Journal.home(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, j, p), us))
    case Con{JT.Ext4JDesc{p, o, ps}, t}:
      Ext4JDrv.touched(t, d, fs, j, Ext4JDrv.add_home(JR.Ext4Journal.home(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, j, p), us))
    case Con{JT.Ext4JData{p, u, o}, t}:
      Ext4JDrv.touched(t, d, fs, j, Ext4JDrv.add_home(JR.Ext4Journal.home(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, j, p), us))
    case Con{JT.Ext4JCommit{p, o}, t}:
      Ext4JDrv.touched(t, d, fs, j, Ext4JDrv.add_home(JR.Ext4Journal.home(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, j, p), us))
    case Con{JT.Ext4JFlag{a, b}, t}:
      Ext4JDrv.touched(t, d, fs, j, us)

def Ext4JDrv.touch(+p: JT.Ext4JPlan, +d: D.MemDev, +fs: S.Ext4Fs, us: List<&2, Nat>) -> List<&2, Nat>:
  Ext4JDrv.touched(JT.Ext4JTx.steps(JT.Ext4JPlan.tx(p)), d, fs, JT.Ext4JPlan.journal(p), Ext4JDrv.add(JT.Ext4JTx.super_block(S.Ext4Fs.block_size(fs)), us))

# Crashes

def Ext4JDrv.recovered(+n: Nat, r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>, +us: List<&2, Nat>, +d0: D.MemDev) -> IO(Unit):
  match r:
    case Done{JR.Ext4Recovered{+d, +rep}}:
      do IO<Unit>:
        IO.print("rec " ++ Nat.show(n) ++ " ok " ++ Nat.show(JR.Jbd2Report.transactions(rep)) ++ " " ++ Nat.show(JR.Jbd2Report.replayed(rep)))
        Ext4JDrv.dump(us, d, d0)
    case Fail{+e}:
      IO.print("rec " ++ Nat.show(n) ++ " err " ++ Ext4JDrv.err(e))

def Ext4JDrv.crashed(+n: Nat, r: Result<&2, &2, E.Ext4Error, D.MemDev>, +fs: S.Ext4Fs, +jo: O.Jbd2Options, +us: List<&2, Nat>, +d0: D.MemDev, +at: Nat) -> IO(Unit):
  match r:
    case Done{+d}:
      do IO<Unit>:
        IO.print("cut " ++ Nat.show(n) ++ " " ++ Nat.show(at))
        Ext4JDrv.dump(us, d, d0)
        Ext4JDrv.recovered(n, JR.Ext4Journal.recover(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, jo), us, d0)
    case Fail{+e}:
      IO.print("cut " ++ Nat.show(n) ++ " err " ++ Ext4JDrv.err(e))

def Ext4JDrv.cuts(ks: List<&2, Nat>, +d: D.MemDev, +fs: S.Ext4Fs, +jo: O.Jbd2Options, +p: JT.Ext4JPlan, +us: List<&2, Nat>, +d0: D.MemDev) -> IO(Unit):
  match ks:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+k, t}:
      do IO<Unit>:
        Ext4JDrv.crashed(k, JT.Ext4JTx.apply(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, p, k), fs, jo, us, d0, JT.Ext4JPlan.commit_at(p))
        Ext4JDrv.cuts(t, d, fs, jo, p, us, d0)

# the crash points tried: nothing logged yet, half the log, all of it but
# the commit, just committed, half the checkpoint, all but the last step
def Ext4JDrv.points(+tx: JT.Ext4JTx) -> List<&2, Nat>:
  +a = List.length(&2, JT.Ext4JStep, JT.Ext4JTx.pre(tx))
  +c = JT.Ext4JTx.commit_at(tx)
  +np = List.length(&2, JT.Ext4JStep, JT.Ext4JTx.post(tx))
  [a, Nat.add(a, Nat.div(List.length(&2, JT.Ext4JStep, JT.Ext4JTx.log(tx)), 2n)), Nat.sub(c, 1n), c, Nat.add(c, Nat.div(np, 2n)), Nat.add(c, Nat.sub(np, 1n))]

# Transactions

def Ext4JDrv.direct(ops: List<&2, XP.Ext2Op>, r: Result<&2, &2, E.Ext4Error, D.MemDev>, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions) -> Result<&2, &2, E.Ext4Error, D.MemDev>:
  match ops r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{d}:
      Done{d}
    case Con{op, t} Done{d}:
      Ext4JDrv.direct(t, E.Ext4Error.lift(D.MemDev, XR.Ext2Op.run(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, op, d, S.Ext4Fs.ext2(fs), wo)), fs, wo)

type Ext4JState is Data:
  Ext4JState{dj: D.MemDev, dd: D.MemDev, us: List<&2, Nat>}

def Ext4JDrv.keep(r: Result<&2, &2, E.Ext4Error, D.MemDev>, d: D.MemDev) -> D.MemDev:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      d

def Ext4JDrv.show_direct(+k: Nat, r: Result<&2, &2, E.Ext4Error, D.MemDev>) -> String:
  match r:
    case Done{x}:
      "direct " ++ Nat.show(k) ++ " ok"
    case Fail{+e}:
      "direct " ++ Nat.show(k) ++ " err " ++ Ext4JDrv.err(e)

def Ext4JDrv.crash(on: Bool, +d: D.MemDev, +fs: S.Ext4Fs, +jo: O.Jbd2Options, +p: JT.Ext4JPlan, +us: List<&2, Nat>, +d0: D.MemDev) -> IO(Unit):
  match on:
    case True{}:
      Ext4JDrv.cuts(Ext4JDrv.points(JT.Ext4JPlan.tx(p)), d, fs, jo, p, us, d0)
    case False{}:
      IO.pure(Unit, Unit{})


def Ext4JCase.crash(c: Ext4JCase) -> Bool:
  match c:
    case Ext4JCase{n, p, bs, cnt, nz, m, cr, t, x}:
      cr


def Ext4JCase.mode(c: Ext4JCase) -> JT.Jbd2Mode:
  match c:
    case Ext4JCase{n, p, bs, cnt, nz, m, cr, t, x}:
      m


def Ext4JState.us(s: Ext4JState) -> List<&2, Nat>:
  match s:
    case Ext4JState{a, b, u}:
      u


def Ext4JDrv.applied(+k: Nat, r: Result<&2, &2, E.Ext4Error, D.MemDev>, +p: JT.Ext4JPlan, +dj: D.MemDev, +dd: D.MemDev, +fs: S.Ext4Fs, +us: List<&2, Nat>) -> IO(Ext4JState):
  match r:
    case Done{+d2}:
      +tx = JT.Ext4JPlan.tx(p)
      do IO<Ext4JState>:
        IO.print("tx " ++ Nat.show(k) ++ " ok " ++ Nat.show(JT.Ext4JPlan.length(p)) ++ " " ++ Nat.show(JT.Ext4JPlan.commit_at(p)) ++ " " ++ Nat.show(JT.Ext4JTx.log_blocks(tx)) ++ " " ++ Nat.show(List.length(&2, JW.Jbd2Write, JT.Ext4JTx.homes(JT.Ext4JTx.pre(tx)))))
        return Ext4JState{d2, dd, Ext4JDrv.touch(p, dj, fs, us)}
    case Fail{+e}:
      do IO<Ext4JState>:
        IO.print("tx " ++ Nat.show(k) ++ " err apply " ++ Ext4JDrv.err(e))
        return Ext4JState{dj, dd, us}

def Ext4JDrv.planned(+k: Nat, r: Result<&2, &2, E.Ext4Error, JT.Ext4JPlan>, +last: Bool, +c: Ext4JCase, +st: Ext4JState, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions, +jo: O.Jbd2Options, +d0: D.MemDev) -> IO(Ext4JState):
  match r st:
    case Done{+p} Ext4JState{+dj, +dd, +us}:
      do IO<Ext4JState>:
        +st2 : Ext4JState <- Ext4JDrv.applied(k, JT.Ext4JTx.apply(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, dj, fs, p, JT.Ext4JPlan.length(p)), p, dj, dd, fs, us)
        Ext4JDrv.crash(Bool.and(last, Ext4JCase.crash(c)), dj, fs, jo, p, Ext4JState.us(st2), d0)
        return st2
    case Fail{+e} _:
      do IO<Ext4JState>:
        IO.print("tx " ++ Nat.show(k) ++ " err " ++ Ext4JDrv.err(e))
        return st

def Ext4JDrv.with_direct(st: Ext4JState, r: Result<&2, &2, E.Ext4Error, D.MemDev>) -> Ext4JState:
  match st:
    case Ext4JState{a, b, u}:
      Ext4JState{a, Ext4JDrv.keep(r, b), u}

def Ext4JDrv.txs(txs: List<&2, List<&2, XP.Ext2Op>>, +k: Nat, st: Ext4JState, +c: Ext4JCase, +fs: S.Ext4Fs, +wo: XW.Ext2WriteOptions, +jo: O.Jbd2Options, +d0: D.MemDev) -> IO(Ext4JState):
  match txs st:
    case Nil{} _:
      IO.pure(Ext4JState, st)
    case Con{+ops, +t} Ext4JState{+dj, +dd, +us}:
      +rd = Ext4JDrv.direct(ops, Done{dd}, fs, wo)
      do IO<Ext4JState>:
        st2 : Ext4JState <- Ext4JDrv.planned(k, JX.Ext4JExt2.plan(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ops, dj, fs, wo, jo, Ext4JCase.mode(c)), List.is_empty(&2, List<&2, XP.Ext2Op>, t), c, Ext4JState{dj, dd, us}, fs, wo, jo, d0)
        IO.print(Ext4JDrv.show_direct(k, rd))
        Ext4JDrv.txs(t, Nat.add(k, 1n), Ext4JDrv.with_direct(st2, rd), c, fs, wo, jo, d0)

def Ext4JDrv.finish(st: Ext4JState, +d0: D.MemDev) -> IO(Unit):
  match st:
    case Ext4JState{+dj, +dd, +us}:
      do IO<Unit>:
        IO.print("differ" ++ Ext4JDrv.differ(us, dj, dd, ""))
        IO.print("final")
        Ext4JDrv.dump(us, dj, d0)
        IO.print("done")

def Ext4JDrv.opened(r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>, +c: Ext4JCase, +d0: D.MemDev) -> IO(Unit):
  match r c:
    case Done{+fs} Ext4JCase{n, p, bs, cnt, nz, m, cr, +t, txs}:
      +wo = XW.Ext2WriteOptions.with_time(XW.Ext2WriteOptions.default(), t)
      +jo = O.Jbd2Options.with_commit_time(O.Jbd2Options.default(), t, 0)
      do IO<Unit>:
        st : Ext4JState <- Ext4JDrv.txs(txs, 0n, Ext4JState{d0, d0, Nil{}}, c, fs, wo, jo, d0)
        Ext4JDrv.finish(st, d0)
    case Fail{+e} _:
      do IO<Unit>:
        IO.print("open err " ++ Ext4JDrv.err(e))
        IO.print("done")

# a case: printed as above
def Ext4JCase.run(c: Ext4JCase) -> IO(Unit):
  match c:
    case Ext4JCase{+n, +p, +bs, +cnt, +nz, m, cr, t, txs}:
      do IO<Unit>:
        IO.print("case " ++ n)
        +d0 : D.MemDev <- I.Ext4Img.open(p, bs, cnt, nz)
        Ext4JDrv.opened(X4.Ext4.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d0, O.Ext4Options.default()), Ext4JCase{n, p, bs, cnt, nz, m, cr, t, txs}, d0)
