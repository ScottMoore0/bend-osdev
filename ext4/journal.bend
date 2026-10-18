# bend-osdev-ext4: an ext4 filesystem's internal journal (s_journal_inum,
# usually inode 8) on a device: opening it, recovering it (the three
# passes of jlog.bend over the records jscan.bend reads, each surviving
# block read from the log and written home), and committing a transaction
# into it (jwrite.bend's blocks, written at the log's first block).
#
# Recovery ends as the documentation describes a clean journal: s_start 0
# and s_sequence the next transaction's ID in the journal's superblock (one
# ID is skipped, as e2fsprogs's recovery does), and the filesystem's
# needs_recovery feature cleared (its checksum kept right). Committing leaves the journal as a crash right after the commit
# would: s_start at the transaction, needs_recovery set; a recovery (this
# package's, e2fsck's, or the kernel's) then replays it.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ../ext2/inode.bend as N
import ../ext2/file.bend as FL
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./jsuper.bend as J
import ./jblock.bend as JB
import ./jlog.bend as JL
import ./jscan.bend as JN
import ./jwrite.bend as JW
import ./devwrite.bend as DW
import ./overlay.bend as OV

type Ext4Journal is Data:
  Ext4Journal{inode: N.Ext2Inode, sb: J.Jbd2Super, raw: B.Octets, geom: J.Jbd2Geom}

def Ext4Journal.inode(j: Ext4Journal) -> N.Ext2Inode:
  match j:
    case Ext4Journal{i, s, r, g}:
      i

def Ext4Journal.sb(j: Ext4Journal) -> J.Jbd2Super:
  match j:
    case Ext4Journal{i, s, r, g}:
      s

def Ext4Journal.raw(j: Ext4Journal) -> B.Octets:
  match j:
    case Ext4Journal{i, s, r, g}:
      r

def Ext4Journal.geom(j: Ext4Journal) -> J.Jbd2Geom:
  match j:
    case Ext4Journal{i, s, r, g}:
      g

def Ext4Journal.inum.pick(zero: Bool, +n: Nat) -> Nat:
  match zero:
    case True{}:
      8n
    case False{}:
      n

# the journal of an ext4 filesystem, its superblock checked
def Ext4Journal.open(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +opts: O.Jbd2Options) -> Result<&2, &2, E.Ext4Error, Ext4Journal>:
  +f = S.Ext4Fs.ext2(fs)
  +x = S.Ext4Fs.super(fs)
  +n = U32.to_nat(S.Ext4Super.journal_inum(x))
  do Result<&2, &2, E.Ext4Error, Ext4Journal>:
    E.Ext4.require(S.Ext4Fs.has_compat(fs, S.Ext4Super.compat_has_journal()), E.Ext4NoJournal{})
    E.Ext4.require(Bool.not(S.Ext4Fs.has_incompat(fs, S.Ext4Super.incompat_journal_dev())), E.Ext4ExternalJournal{})
    E.Ext4.require(Bool.and(Nat.is_eq(U32.to_nat(S.Ext4Super.journal_dev(x)), 0n), Nat.is_lt(0n, n)), E.Ext4ExternalJournal{})
    +ji : N.Ext2Inode <- E.Ext4Error.lift(N.Ext2Inode, N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, f, n))
    +blk : B.Octets <- E.Ext4Error.lift(B.Octets, FL.Ext2File.read_block(~Dv, ~block_size, ~read_block, d, f, ji, 0n))
    +sb : J.Jbd2Super <- J.Jbd2Super.check(blk, XS.Ext2Fs.block_size(f), FL.Ext2File.blocks_needed(f, ji), opts)
    return Ext4Journal{ji, sb, blk, J.Jbd2Super.geom(sb)}

# journal block p
def Ext4Journal.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +p: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  +f = S.Ext4Fs.ext2(fs)
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    E.Ext4.require(Nat.is_lt(p, J.Jbd2Geom.maxlen(Ext4Journal.geom(j))), E.Ext4JournalBlock{p})
    +o : B.Octets <- E.Ext4Error.lift(B.Octets, FL.Ext2File.read_block(~Dv, ~block_size, ~read_block, d, f, Ext4Journal.inode(j), p))
    E.Ext4.require(Nat.is_eq(B.Octets.len(o), XS.Ext2Fs.block_size(f)), E.Ext4JournalBlock{p})
    return o

def Ext4Journal.home.got(m: Maybe<&2, Nat>, +p: Nat) -> Result<&2, &2, E.Ext4Error, Nat>:
  match m:
    case Some{b}:
      Done{b}
    case None{}:
      Fail{E.Ext4BadJournal{"journal block " ++ Nat.show(p) ++ " is a hole"}}

# the filesystem block holding journal block p
def Ext4Journal.home(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +p: Nat) -> Result<&2, &2, E.Ext4Error, Nat>:
  do Result<&2, &2, E.Ext4Error, Nat>:
    m : Maybe<&2, Nat> <- E.Ext4Error.lift(Maybe<&2, Nat>, FL.Ext2File.map(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), Ext4Journal.inode(j), p))
    Ext4Journal.home.got(m, p)

# the device after journal block p becomes data
def Ext4Journal.put(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +p: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext4Error, Dv>:
  do Result<&2, &2, E.Ext4Error, Dv>:
    b : Nat <- Ext4Journal.home(~Dv, ~block_size, ~read_block, d, fs, j, p)
    DW.Ext4Dev.write(~Dv, ~block_size, ~write_block, d, S.Ext4Fs.block_size(fs), b, data)

# Pass 1, on the device: the log's records, read a block at a time

def Ext4Journal.scan(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fuel: Nat, live: Bool, st: JN.Jbd2Scan, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +check: Bool) -> Result<&2, &2, E.Ext4Error, JN.Jbd2Scan>:
  match fuel live:
    case 0n _:
      Done{st}
    case _ False{}:
      Done{st}
    case 1n+f True{}:
      +s = st
      do Result<&2, &2, E.Ext4Error, JN.Jbd2Scan>:
        blk : B.Octets <- Ext4Journal.read(~Dv, ~block_size, ~read_block, d, fs, j, JN.Jbd2Scan.pos(s))
        +s2 : JN.Jbd2Scan = JN.Jbd2Scan.feed(check, Ext4Journal.geom(j), s, blk)
        Ext4Journal.scan(~Dv, ~block_size, ~read_block, f, JN.Jbd2Scan.live(s2), s2, d, fs, j, check)

def Ext4Journal.scanned(bad: Maybe<&2, Nat>, rs: List<&2, JL.Jbd2Rec>) -> Result<&2, &2, E.Ext4Error, List<&2, JL.Jbd2Rec>>:
  match bad:
    case None{}:
      Done{rs}
    case Some{p}:
      Fail{E.Ext4BadLogCsum{p}}

def Ext4Journal.records.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, empty: Bool, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +check: Bool) -> Result<&2, &2, E.Ext4Error, List<&2, JL.Jbd2Rec>>:
  match empty:
    case True{}:
      Done{Nil{}}
    case False{}:
      +sb = Ext4Journal.sb(j)
      do Result<&2, &2, E.Ext4Error, List<&2, JL.Jbd2Rec>>:
        +st : JN.Jbd2Scan <- Ext4Journal.scan(~Dv, ~block_size, ~read_block, 1n+J.Jbd2Super.maxlen(sb), True{}, JN.Jbd2Scan.start(J.Jbd2Super.start(sb), U32.to_nat(J.Jbd2Super.sequence(sb))), d, fs, j, check)
        Ext4Journal.scanned(JN.Jbd2Scan.bad(st), JN.Jbd2Scan.records(st))

# the journal's records, from s_start on (none when s_start is 0)
def Ext4Journal.records(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +check: Bool) -> Result<&2, &2, E.Ext4Error, List<&2, JL.Jbd2Rec>>:
  Ext4Journal.records.go(~Dv, ~block_size, ~read_block, Nat.is_eq(J.Jbd2Super.start(Ext4Journal.sb(j)), 0n), d, fs, j, check)

# Pass 3, on the device: each block of the plan read from the log, checked,
# and written home

type Ext4Replayed<-Dv: Data> is Data:
  Ext4Replayed{dev: Dv, replayed: Nat, skipped: Nat}

def Ext4Journal.one(~Dv: Data, ~block_size: Dv -> Nat, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, ok: Bool, +skip: Bool, +d: Dv, +fs: S.Ext4Fs, +p: JL.Jbd2Put, +s: Nat, +data: B.Octets, +n: Nat, +k: Nat) -> Result<&2, &2, E.Ext4Error, Ext4Replayed<Dv>>:
  match ok:
    case True{}:
      +b = JL.Jbd2Put.block(p)
      do Result<&2, &2, E.Ext4Error, Ext4Replayed<Dv>>:
        E.Ext4.require(Nat.is_lt(b, XS.Ext2Fs.blocks(S.Ext4Fs.ext2(fs))), E.Ext4BadJournal{"a journalled block outside the filesystem: " ++ Nat.show(b)})
        d2 : Dv <- DW.Ext4Dev.write(~Dv, ~block_size, ~write_block, d, S.Ext4Fs.block_size(fs), b, JB.Jbd2.unescape(J.Jbd2.has(JL.Jbd2Put.flags(p), JB.Jbd2.flag_escape()), data))
        return Ext4Replayed{d2, 1n+n, k}
    case False{}:
      match skip:
        case True{}:
          Done{Ext4Replayed{d, n, 1n+k}}
        case False{}:
          Fail{E.Ext4ReplayCsum{JL.Jbd2Put.block(p), s}}

def Ext4Journal.replay.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, r: Result<&2, &2, E.Ext4Error, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +g: J.Jbd2Geom, +p: JL.Jbd2Put, +s: Nat, +n: Nat, +k: Nat, +opts: O.Jbd2Options) -> Result<&2, &2, E.Ext4Error, Ext4Replayed<Dv>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+data}:
      Ext4Journal.one(~Dv, ~block_size, ~write_block, JB.Jbd2.data_ok(O.Jbd2Options.verify(opts), g, U32.from_nat(s), data, JL.Jbd2Put.csum(p)), O.Jbd2Options.skip_bad_data(opts), d, fs, p, s, data, n, k)

# the plan's blocks replayed in order, a tail call each: r is the device
# and the counts so far; a block whose tag checksum fails is skipped and
# counted (or fails the replay, as the options say)
def Ext4Journal.replay(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, ds: List<&2, JL.Jbd2Do>, r: Result<&2, &2, E.Ext4Error, Ext4Replayed<Dv>>, +fs: S.Ext4Fs, +j: Ext4Journal, +opts: O.Jbd2Options) -> Result<&2, &2, E.Ext4Error, Ext4Replayed<Dv>>:
  match ds r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{x}:
      Done{x}
    case Con{JL.Jbd2Do{+s, +p}, t} Done{Ext4Replayed{+d, n, k}}:
      Ext4Journal.replay(~Dv, ~block_size, ~read_block, ~write_block, t, Ext4Journal.replay.at(~Dv, ~block_size, ~read_block, ~write_block, Ext4Journal.read(~Dv, ~block_size, ~read_block, d, fs, j, JL.Jbd2Put.src(p)), d, fs, Ext4Journal.geom(j), p, s, n, k, opts), fs, j, opts)

# Recovery

type Jbd2Report is Data:
  Jbd2Report{transactions: Nat, replayed: Nat, skipped: Nat, next: Nat}

def Jbd2Report.transactions(r: Jbd2Report) -> Nat:
  match r:
    case Jbd2Report{t, p, s, n}:
      t

def Jbd2Report.replayed(r: Jbd2Report) -> Nat:
  match r:
    case Jbd2Report{t, p, s, n}:
      p

def Jbd2Report.skipped(r: Jbd2Report) -> Nat:
  match r:
    case Jbd2Report{t, p, s, n}:
      s

def Jbd2Report.next(r: Jbd2Report) -> Nat:
  match r:
    case Jbd2Report{t, p, s, n}:
      n

type Ext4Recovered<-Dv: Data> is Data:
  Ext4Recovered{dev: Dv, report: Jbd2Report}

# the ID after the last transaction (s when there is none)
def Ext4Journal.next_seq(txs: List<&2, JL.Jbd2Tx>, s: Nat) -> Nat:
  match txs:
    case Nil{}:
      s
    case Con{x, t}:
      Ext4Journal.next_seq(t, 1n+JL.Jbd2Tx.seq(x))

def Ext4Journal.mark(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, empty: Bool, +d: Dv, +fs: S.Ext4Fs, +j: Ext4Journal, +next: Nat) -> Result<&2, &2, E.Ext4Error, Dv>:
  match empty:
    case True{}:
      Done{d}
    case False{}:
      Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d, fs, j, 0n, J.Jbd2Super.with_log(Ext4Journal.raw(j), 0n, U32.from_nat(next)))

def Ext4Journal.finish(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, x: Ext4Replayed<Dv>, +fs: S.Ext4Fs, +j: Ext4Journal, +count: Nat, +next: Nat) -> Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
  match x:
    case Ext4Replayed{d, n, k}:
      do Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
        d2 : Dv <- Ext4Journal.mark(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_eq(J.Jbd2Super.start(Ext4Journal.sb(j)), 0n), d, fs, j, next)
        d3 : Dv <- DW.Ext4Dev.set_incompat(~Dv, ~block_size, ~read_block, ~write_block, d2, S.Ext4Fs.ext2(fs), 0, S.Ext4Super.incompat_recover())
        return Ext4Recovered{d3, Jbd2Report{count, n, k, next}}

# the next transaction's ID after recovery: one past the ID after the last
# replayed transaction (one is skipped, as e2fsprogs's recovery does: the
# documentation does not say), or s_sequence when the journal was empty
def Ext4Journal.next_id(empty: Bool, txs: List<&2, JL.Jbd2Tx>, +seq: Nat) -> Nat:
  match empty:
    case True{}:
      seq
    case False{}:
      1n+Ext4Journal.next_seq(txs, seq)

# the device after its journal is recovered: every committed transaction
# from s_start on replayed (revoked blocks left out), then the journal
# marked empty and needs_recovery cleared. A journal already empty only
# has needs_recovery cleared. The report counts the transactions, the
# blocks written, the blocks skipped for a bad checksum, and gives the next
# transaction's ID.
def Ext4Journal.recover(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, +opts: O.Jbd2Options) -> Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
  do Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
    +j : Ext4Journal <- Ext4Journal.open(~Dv, ~block_size, ~read_block, d, fs, opts)
    rs : List<&2, JL.Jbd2Rec> <- Ext4Journal.records(~Dv, ~block_size, ~read_block, d, fs, j, O.Jbd2Options.verify(opts))
    +seq : Nat = U32.to_nat(J.Jbd2Super.sequence(Ext4Journal.sb(j)))
    +txs : List<&2, JL.Jbd2Tx> = JL.Jbd2Log.scan(seq, rs)
    x : Ext4Replayed<Dv> <- Ext4Journal.replay(~Dv, ~block_size, ~read_block, ~write_block, JL.Jbd2Log.plan(txs), Done{Ext4Replayed{d, 0n, 0n}}, fs, j, opts)
    Ext4Journal.finish(~Dv, ~block_size, ~read_block, ~write_block, x, fs, j, List.length(&2, JL.Jbd2Tx, txs), Ext4Journal.next_id(Nat.is_eq(J.Jbd2Super.start(Ext4Journal.sb(j)), 0n), txs, seq))

# Committing a transaction

type Ext4Committed<-Dv: Data> is Data:
  Ext4Committed{dev: Dv, seq: Nat, blocks: Nat}

def Ext4Journal.check_writes(ws: List<&2, JW.Jbd2Write>, +bs: Nat, +count: Nat) -> Result<&2, &2, E.Ext4Error, Unit>:
  match ws:
    case Nil{}:
      Done{Unit{}}
    case Con{JW.Jbd2Write{+b, d}, t}:
      do Result<&2, &2, E.Ext4Error, Unit>:
        E.Ext4.require(Nat.is_lt(b, count), E.Ext4BadJournalWrite{b, "outside the filesystem"})
        E.Ext4.require(Nat.is_eq(B.Octets.len(d), bs), E.Ext4BadJournalWrite{b, "not one block of data"})
        Ext4Journal.check_writes(t, bs, count)

def Ext4Journal.put_all(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, os: List<&2, B.Octets>, r: Result<&2, &2, E.Ext4Error, Dv>, +fs: S.Ext4Fs, +j: Ext4Journal, +p: Nat) -> Result<&2, &2, E.Ext4Error, Dv>:
  match os r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{d}:
      Done{d}
    case Con{o, t} Done{d}:
      Ext4Journal.put_all(~Dv, ~block_size, ~read_block, ~write_block, t, Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d, fs, j, p, o), fs, j, Nat.add(p, 1n))

# the superblock with the revoke feature set (when the transaction revokes
# blocks: a journal without it may not be read for revoke blocks)
def Ext4Journal.with_revoke(on: Bool, +o: B.Octets) -> B.Octets:
  match on:
    case True{}:
      J.Jbd2.patch32(o, 40n, U32.or(J.Jbd2.be32(o, 40n), J.Jbd2Super.incompat_revoke()))
    case False{}:
      o

# the device after a transaction is committed to its journal: blocks
# revoked rv and writes ws, in the journal's next transaction, written from
# the log's first block; the journal must be empty (recover it first)
def Ext4Journal.commit(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, +opts: O.Jbd2Options, +rv: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, Ext4Committed<Dv>>:
  +f = S.Ext4Fs.ext2(fs)
  do Result<&2, &2, E.Ext4Error, Ext4Committed<Dv>>:
    +j : Ext4Journal <- Ext4Journal.open(~Dv, ~block_size, ~read_block, d, fs, opts)
    +sb : J.Jbd2Super = Ext4Journal.sb(j)
    E.Ext4.require(Nat.is_eq(J.Jbd2Super.start(sb), 0n), E.Ext4JournalNotEmpty{})
    Ext4Journal.check_writes(ws, XS.Ext2Fs.block_size(f), XS.Ext2Fs.blocks(f))
    +first : Nat = J.Jbd2Super.first(sb)
    +seq : Nat = U32.to_nat(J.Jbd2Super.sequence(sb))
    +os : List<&2, B.Octets> = JW.Jbd2Write.blocks(Ext4Journal.geom(j), J.Jbd2Super.uuid(sb), seq, rv, ws, O.Jbd2Options.commit_sec(opts), O.Jbd2Options.commit_nsec(opts))
    +n : Nat = List.length(&2, B.Octets, os)
    +room : Nat = Nat.sub(J.Jbd2Super.maxlen(sb), first)
    E.Ext4.require(Nat.is_le(n, room), E.Ext4JournalFull{n, room})
    d2 : Dv <- Ext4Journal.put_all(~Dv, ~block_size, ~read_block, ~write_block, os, Done{d}, fs, j, first)
    d3 : Dv <- Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, j, 0n, J.Jbd2Super.with_log(Ext4Journal.with_revoke(Bool.not(List.is_empty(&2, Nat, rv)), Ext4Journal.raw(j)), first, J.Jbd2Super.sequence(sb)))
    d4 : Dv <- DW.Ext4Dev.set_incompat(~Dv, ~block_size, ~read_block, ~write_block, d3, f, S.Ext4Super.incompat_recover(), 0)
    return Ext4Committed{d4, seq, n}

# Journalled updates

def Ext4Journal.transact.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, c: Ext4Committed<Dv>, +fs: S.Ext4Fs, +opts: O.Jbd2Options) -> Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
  match c:
    case Ext4Committed{d, sq, n}:
      Ext4Journal.recover(~Dv, ~block_size, ~read_block, ~write_block, d, fs, opts)

# the device after a journalled update: op runs on an overlay of d (it
# reads through it and its writes are kept aside), its writes are committed
# to the journal as one transaction, and the journal is then recovered,
# which writes them home and marks the journal empty. A crash after the
# commit leaves a journal any recovery replays; a crash during the replay
# leaves the same journal, and replaying again is harmless (LAWS.bend:
# replay_idempotent). op is any writer over blockdev's pure interface and a
# pure write, given Ext4Ov's operations (ext2's writer, for one). The
# device's blocks must be the filesystem's.
def Ext4Journal.transact(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, +opts: O.Jbd2Options, op: OV.Ext4Ov<Dv> -> Result<&2, &2, E.Ext4Error, OV.Ext4Ov<Dv>>) -> Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
  +bs = S.Ext4Fs.block_size(fs)
  do Result<&2, &2, E.Ext4Error, Ext4Recovered<Dv>>:
    E.Ext4.require(Nat.is_eq(block_size(d), bs), E.Ext4BadDevBlock{bs, block_size(d)})
    ov : OV.Ext4Ov<Dv> <- op(OV.Ext4Ov.start(Dv, d))
    c : Ext4Committed<Dv> <- Ext4Journal.commit(~Dv, ~block_size, ~read_block, ~write_block, d, fs, opts, Nil{}, OV.Ext4Ov.writes(Dv, ov))
    Ext4Journal.transact.fin(~Dv, ~block_size, ~read_block, ~write_block, c, fs, opts)
