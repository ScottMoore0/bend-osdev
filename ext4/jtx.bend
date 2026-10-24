# bend-osdev-ext4: a journalled transaction as the ordered list of device
# writes that makes it (the jbd2 documentation, "Journal (jbd2)": blocks
# are logged, the commit block makes the transaction durable, and the
# blocks are then checkpointed to their homes, after which the log may be
# reused).
#
# A transaction's writes (Jbd2Write: a filesystem block and its new
# contents, each block once) become a plan of steps, in order:
#
#   1. data=ordered only: the blocks the transaction allocates (free before
#      it: the caller names them) written in place; the old filesystem
#      never refers to them, so a crash leaves it as it was;
#   2. needs_recovery set in the filesystem's superblock, and the journal's
#      superblock pointed at the log (s_start = s_first, s_sequence the
#      transaction's ID), as a mount and a first transaction leave them;
#   3. the log: descriptor blocks, each followed by the copies of the
#      blocks its tags name (escaped), from s_first on;
#   4. the commit block: from here on, every recovery replays the
#      transaction;
#   5. the checkpoint: every logged block written home;
#   6. the journal's superblock marked empty (s_start 0, s_sequence the next
#      ID) and needs_recovery cleared.
#
# The logged copy of the block holding the primary superblock carries
# needs_recovery set (as the kernel's in-memory superblock does while
# mounted), so that a crash during the checkpoint still leaves a
# filesystem whose recovery is due; step 6 clears it again.
#
# A crash after any number of steps is the device after that prefix of the
# plan (Ext4JTx.apply with a step count). LAWS.bend states what recovery
# makes of every prefix: before the commit step it replays nothing, from it
# on it replays every logged block, and what it replays is what the
# checkpoint writes.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./jsuper.bend as J
import ./jblock.bend as JB
import ./jlog.bend as JL
import ./jwrite.bend as JW
import ./devwrite.bend as DW
import ./journal.bend as JR

# What is logged: every block (data=journal), or every block but the ones
# the transaction allocates, which are written in place before the commit
# (data=ordered's rule for new blocks)
type Jbd2Mode is Data:
  Jbd2DataJournal{}
  Jbd2DataOrdered{}

# A step: one write to the device
type Ext4JStep is Data:
  # a filesystem block written in place
  Ext4JHome{write: JW.Jbd2Write}
  # journal block pos (the journal's superblock: pos 0)
  Ext4JLog{pos: Nat, data: B.Octets}
  # a descriptor block at journal block pos, and the blocks its tags name
  Ext4JDesc{pos: Nat, data: B.Octets, puts: List<&2, JL.Jbd2Put>}
  # the logged copy (escaped) of one block, at journal block pos
  Ext4JData{pos: Nat, put: JL.Jbd2Put, stored: B.Octets}
  # the commit block, at journal block pos
  Ext4JCommit{pos: Nat, data: B.Octets}
  # the filesystem superblock's incompat features changed (set, clear)
  Ext4JFlag{set: U32, clear: U32}

# A transaction: its ID, the steps before the log, the log, the commit
# step, and the steps after it
type Ext4JTx is Data:
  Ext4JTx{seq: Nat, pre: List<&2, Ext4JStep>, log: List<&2, Ext4JStep>, commit: Ext4JStep, post: List<&2, Ext4JStep>}

def Ext4JTx.seq(t: Ext4JTx) -> Nat:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      s

def Ext4JTx.pre(t: Ext4JTx) -> List<&2, Ext4JStep>:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      a

def Ext4JTx.log(t: Ext4JTx) -> List<&2, Ext4JStep>:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      l

def Ext4JTx.commit(t: Ext4JTx) -> Ext4JStep:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      c

def Ext4JTx.post(t: Ext4JTx) -> List<&2, Ext4JStep>:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      p

# every step, in order
def Ext4JTx.steps(t: Ext4JTx) -> List<&2, Ext4JStep>:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      List.append(&2, Ext4JStep, List.append(&2, Ext4JStep, a, l), Con{c, p})

# how many steps up to and including the commit step
def Ext4JTx.commit_at(t: Ext4JTx) -> Nat:
  match t:
    case Ext4JTx{s, a, l, c, p}:
      1n+List.length(&2, Ext4JStep, List.append(&2, Ext4JStep, a, l))

# Reading a plan (the laws are stated with these)

# the records the steps' journal blocks hold (jlog.bend), transaction s:
# a descriptor's, and the commit
def Ext4JTx.records(+s: Nat, xs: List<&2, Ext4JStep>) -> List<&2, JL.Jbd2Rec>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Ext4JDesc{p, o, ps}, t}:
      Con{JL.Jbd2RDesc{s, ps}, Ext4JTx.records(s, t)}
    case Con{Ext4JCommit{p, o}, t}:
      Con{JL.Jbd2RCommit{s}, Ext4JTx.records(s, t)}
    case Con{x, t}:
      Ext4JTx.records(s, t)

# whether the steps hold the commit
def Ext4JTx.committed(xs: List<&2, Ext4JStep>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{Ext4JCommit{p, o}, t}:
      True{}
    case Con{x, t}:
      Ext4JTx.committed(t)

# the puts of the logged copies, in log order
def Ext4JTx.data_puts(xs: List<&2, Ext4JStep>) -> List<&2, JL.Jbd2Put>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Ext4JData{p, u, o}, t}:
      Con{u, Ext4JTx.data_puts(t)}
    case Con{x, t}:
      Ext4JTx.data_puts(t)

# what replaying the logged copies writes: each block home, unescaped as
# its tag says
def Ext4JTx.replay_writes(xs: List<&2, Ext4JStep>) -> List<&2, JW.Jbd2Write>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Ext4JData{p, JL.Jbd2Put{b, src, f, c}, o}, t}:
      Con{JW.Jbd2Write{b, JB.Jbd2.unescape(J.Jbd2.has(f, JB.Jbd2.flag_escape()), o)}, Ext4JTx.replay_writes(t)}
    case Con{x, t}:
      Ext4JTx.replay_writes(t)

# the filesystem blocks the steps write in place
def Ext4JTx.homes(xs: List<&2, Ext4JStep>) -> List<&2, JW.Jbd2Write>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Ext4JHome{w}, t}:
      Con{w, Ext4JTx.homes(t)}
    case Con{x, t}:
      Ext4JTx.homes(t)

# whether every block the steps write in place is in fresh
def Ext4JTx.fresh_homes(+fresh: List<&2, Nat>, xs: List<&2, Ext4JStep>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Ext4JHome{w}, t}:
      Bool.and(JL.Jbd2Log.member(fresh, JW.Jbd2Write.block(w)), Ext4JTx.fresh_homes(fresh, t))
    case Con{x, t}:
      Ext4JTx.fresh_homes(fresh, t)

# whether every write's block number fits a descriptor tag (with 64bit
# below 2^48, else below 2^32: the laws' hypothesis on the writes)
def Ext4JTx.blocks_fit(+wide: Bool, ws: List<&2, JW.Jbd2Write>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{JW.Jbd2Write{b, d}, t}:
      Bool.and(JB.Jbd2.block_fits(wide, b), Ext4JTx.blocks_fit(wide, t))

# Building a plan

def Ext4JTx.keep(hit: Bool, +w: JW.Jbd2Write, rest: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match hit:
    case True{}:
      Con{w, rest}
    case False{}:
      rest

# the writes to blocks in fresh (in), or to blocks not in it (out), in order
def Ext4JTx.fresh_in(+fresh: List<&2, Nat>, ws: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      Ext4JTx.keep(JL.Jbd2Log.member(fresh, JW.Jbd2Write.block(w)), w, Ext4JTx.fresh_in(fresh, t))

def Ext4JTx.fresh_out(+fresh: List<&2, Nat>, ws: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      Ext4JTx.keep(Bool.not(JL.Jbd2Log.member(fresh, JW.Jbd2Write.block(w))), w, Ext4JTx.fresh_out(fresh, t))

# the writes done in place, before the commit
def Ext4JTx.in_place(m: Jbd2Mode, +fresh: List<&2, Nat>, ws: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match m:
    case Jbd2DataJournal{}:
      Nil{}
    case Jbd2DataOrdered{}:
      Ext4JTx.fresh_in(fresh, ws)

def Ext4JTx.unlogged(m: Jbd2Mode, +fresh: List<&2, Nat>, ws: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match m:
    case Jbd2DataJournal{}:
      ws
    case Jbd2DataOrdered{}:
      Ext4JTx.fresh_out(fresh, ws)

# the primary superblock's block and offset in it, for bs-byte blocks
def Ext4JTx.super_block(+bs: Nat) -> Nat:
  DW.Ext4Dev.super_block(Nat.is_eq(bs, 1024n))

def Ext4JTx.super_off(+bs: Nat) -> Nat:
  DW.Ext4Dev.super_off(Nat.is_eq(bs, 1024n))

def Ext4JTx.mark.at(hit: Bool, +bs: Nat, +data: B.Octets) -> B.Octets:
  match hit:
    case True{}:
      +off = Ext4JTx.super_off(bs)
      B.Octets.append(B.Octets.take(off, data), B.Octets.append(DW.Ext4Dev.super_with(B.Octets.slice(off, 1024n, data), S.Ext4Super.incompat_recover(), 0), B.Octets.drop(Nat.add(off, 1024n), data)))
    case False{}:
      data

# the writes with the primary superblock's copy marked needs_recovery
def Ext4JTx.marks(+bs: Nat, ws: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{JW.Jbd2Write{+b, d}, t}:
      Con{JW.Jbd2Write{b, Ext4JTx.mark.at(Nat.is_eq(b, Ext4JTx.super_block(bs)), bs, d)}, Ext4JTx.marks(bs, t)}

# the writes logged (and checkpointed): those not done in place, the
# superblock's marked
def Ext4JTx.logged(m: Jbd2Mode, +fresh: List<&2, Nat>, +bs: Nat, ws: List<&2, JW.Jbd2Write>) -> List<&2, JW.Jbd2Write>:
  Ext4JTx.marks(bs, Ext4JTx.unlogged(m, fresh, ws))

# the writes in groups of at most cap (a group a descriptor): the first
# group may be short, every other is full
def Ext4JTx.chunks.add(full: Bool, +w: JW.Jbd2Write, g: List<&2, JW.Jbd2Write>, rest: List<&2, List<&2, JW.Jbd2Write>>) -> List<&2, List<&2, JW.Jbd2Write>>:
  match full:
    case True{}:
      Con{[w], Con{g, rest}}
    case False{}:
      Con{Con{w, g}, rest}

def Ext4JTx.chunks.put(+w: JW.Jbd2Write, gs: List<&2, List<&2, JW.Jbd2Write>>, +cap: Nat) -> List<&2, List<&2, JW.Jbd2Write>>:
  match gs:
    case Nil{}:
      [[w]]
    case Con{+g, rest}:
      Ext4JTx.chunks.add(Nat.is_le(cap, List.length(&2, JW.Jbd2Write, g)), w, g, rest)

def Ext4JTx.chunks(ws: List<&2, JW.Jbd2Write>, +cap: Nat) -> List<&2, List<&2, JW.Jbd2Write>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      Ext4JTx.chunks.put(w, Ext4JTx.chunks(t, cap), cap)

def Ext4JTx.cap.pick(zero: Bool, +n: Nat) -> Nat:
  match zero:
    case True{}:
      1n
    case False{}:
      n

# tags to a descriptor (at least one)
def Ext4JTx.cap(+g: J.Jbd2Geom) -> Nat:
  +n = JB.Jbd2Desc.capacity(g)
  Ext4JTx.cap.pick(Nat.is_eq(n, 0n), n)

# the logged copies of a group's writes, from journal block pos on; first:
# the group's first tag (it carries the UUID), and the last has LAST_TAG
def Ext4JTx.datas(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, first: Bool, +pos: Nat) -> List<&2, Ext4JStep>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{JW.Jbd2Write{b, +d}, +t}:
      +stored = JB.Jbd2.escape(d)
      +fl = JW.Jbd2Write.flags(JB.Jbd2.needs_escape(d), first, JW.Jbd2Write.is_nil(t))
      Con{Ext4JData{pos, JL.Jbd2Put{b, pos, fl, JB.Jbd2.tag_csum(J.Jbd2Geom.csum(g), g, s, stored)}, stored}, Ext4JTx.datas(t, g, s, False{}, Nat.add(pos, 1n))}

def Ext4JTx.tags(ps: List<&2, JL.Jbd2Put>) -> List<&2, JB.Jbd2Tag>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{JL.Jbd2Put{b, p, f, c}, t}:
      Con{JB.Jbd2Tag{b, f, c}, Ext4JTx.tags(t)}

# one descriptor at journal block pos and its group's copies
def Ext4JTx.group.go(+pos: Nat, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +ds: List<&2, Ext4JStep>) -> List<&2, Ext4JStep>:
  +ps = Ext4JTx.data_puts(ds)
  Con{Ext4JDesc{pos, JB.Jbd2Desc.encode(g, s, Ext4JTx.tags(ps), uuid), ps}, ds}

def Ext4JTx.group(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> List<&2, Ext4JStep>:
  Ext4JTx.group.go(pos, g, s, uuid, Ext4JTx.datas(ws, g, s, True{}, Nat.add(pos, 1n)))

# the log of the groups, from journal block pos on
def Ext4JTx.logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> List<&2, Ext4JStep>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      List.append(&2, Ext4JStep, Ext4JTx.group(h, g, s, uuid, pos), Ext4JTx.logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))))

def Ext4JTx.home_steps(ws: List<&2, JW.Jbd2Write>) -> List<&2, Ext4JStep>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      Con{Ext4JHome{w}, Ext4JTx.home_steps(t)}

# the steps that open the transaction: needs_recovery set, and the
# journal's superblock pointed at the log (s_start first, s_sequence s)
def Ext4JTx.open_steps(+jsb: B.Octets, +first: Nat, +s: U32) -> List<&2, Ext4JStep>:
  [Ext4JFlag{S.Ext4Super.incompat_recover(), 0}, Ext4JLog{0n, J.Jbd2Super.with_log(jsb, first, s)}]

# the steps that close it: the journal marked empty (s_start 0, s_sequence
# the next ID), needs_recovery cleared
def Ext4JTx.close_steps(+jsb: B.Octets, +seq: Nat) -> List<&2, Ext4JStep>:
  [Ext4JLog{0n, J.Jbd2Super.with_log(jsb, 0n, U32.from_nat(1n+seq))}, Ext4JFlag{0, S.Ext4Super.incompat_recover()}]

# the log of the writes lg, from the journal's first block
def Ext4JTx.log_of(+g: J.Jbd2Geom, +uuid: B.Octets, +seq: Nat, lg: List<&2, JW.Jbd2Write>) -> List<&2, Ext4JStep>:
  Ext4JTx.logs(Ext4JTx.chunks(lg, Ext4JTx.cap(g)), g, U32.from_nat(seq), uuid, J.Jbd2Geom.first(g))

def Ext4JTx.build.go(+g: J.Jbd2Geom, +jsb: B.Octets, +seq: Nat, +inp: List<&2, JW.Jbd2Write>, +lg: List<&2, JW.Jbd2Write>, +log: List<&2, Ext4JStep>, +sec: U32, +nsec: U32) -> Ext4JTx:
  +first = J.Jbd2Geom.first(g)
  Ext4JTx{seq, List.append(&2, Ext4JStep, Ext4JTx.home_steps(inp), Ext4JTx.open_steps(jsb, first, U32.from_nat(seq))), log, Ext4JCommit{Nat.add(first, List.length(&2, Ext4JStep, log)), JB.Jbd2Commit.encode(g, U32.from_nat(seq), sec, nsec)}, List.append(&2, Ext4JStep, Ext4JTx.home_steps(lg), Ext4JTx.close_steps(jsb, seq))}

# the plan of transaction seq of the journal whose geometry is g, UUID
# uuid and superblock jsb (its block, as read), for the writes ws (one
# block each, each block once) in mode m; fresh: the blocks free before
# the transaction (data=ordered writes them in place); the commit block
# stamped sec, nsec
def Ext4JTx.build(+g: J.Jbd2Geom, +uuid: B.Octets, +jsb: B.Octets, +seq: Nat, +m: Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>, +sec: U32, +nsec: U32) -> Ext4JTx:
  +lg = Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  Ext4JTx.build.go(g, jsb, seq, Ext4JTx.in_place(m, fresh, ws), lg, Ext4JTx.log_of(g, uuid, seq, lg), sec, nsec)

# The plan on a device: the journal it writes into, and the transaction

type Ext4JPlan is Data:
  Ext4JPlan{journal: JR.Ext4Journal, tx: Ext4JTx}

def Ext4JPlan.journal(p: Ext4JPlan) -> JR.Ext4Journal:
  match p:
    case Ext4JPlan{j, t}:
      j

def Ext4JPlan.tx(p: Ext4JPlan) -> Ext4JTx:
  match p:
    case Ext4JPlan{j, t}:
      t

# the plan's step count, and how many steps reach the commit
def Ext4JPlan.length(p: Ext4JPlan) -> Nat:
  List.length(&2, Ext4JStep, Ext4JTx.steps(Ext4JPlan.tx(p)))

def Ext4JPlan.commit_at(p: Ext4JPlan) -> Nat:
  Ext4JTx.commit_at(Ext4JPlan.tx(p))

# the number of journal blocks a transaction's log takes, the commit block
# included
def Ext4JTx.log_blocks(+t: Ext4JTx) -> Nat:
  1n+List.length(&2, Ext4JStep, Ext4JTx.log(t))

def Ext4JTx.plan.fin(+j: JR.Ext4Journal, +t: Ext4JTx) -> Result<&2, &2, E.Ext4Error, Ext4JPlan>:
  +sb = JR.Ext4Journal.sb(j)
  +n = Ext4JTx.log_blocks(t)
  +room = Nat.sub(J.Jbd2Super.maxlen(sb), J.Jbd2Super.first(sb))
  do Result<&2, &2, E.Ext4Error, Ext4JPlan>:
    E.Ext4.require(Nat.is_le(n, room), E.Ext4JournalFull{n, room})
    return Ext4JPlan{j, t}

# the plan of a transaction of writes ws (each one block, each block once,
# inside the filesystem) into the journal of the filesystem on d, which
# must be empty (recover it first); fresh: the blocks free before the
# transaction, written in place in data=ordered mode. A journal with the
# old compat checksum (journal_checksum, a CRC-32 of the transaction in
# the commit block) is refused: only csum_v2 and csum_v3 are written.
def Ext4JTx.plan(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +opts: O.Jbd2Options, +m: Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, Ext4JPlan>:
  +f = S.Ext4Fs.ext2(fs)
  do Result<&2, &2, E.Ext4Error, Ext4JPlan>:
    +j : JR.Ext4Journal <- JR.Ext4Journal.open(~Dv, ~block_size, ~read_block, d, fs, opts)
    +sb : J.Jbd2Super = JR.Ext4Journal.sb(j)
    E.Ext4.require(Nat.is_eq(J.Jbd2Super.start(sb), 0n), E.Ext4JournalNotEmpty{})
    E.Ext4.require(Bool.not(J.Jbd2.has(J.Jbd2Super.compat(sb), J.Jbd2Super.compat_checksum())), E.Ext4JournalUnsupported{"journal_checksum (the old compat checksum), for writing"})
    JR.Ext4Journal.check_writes(ws, XS.Ext2Fs.block_size(f), XS.Ext2Fs.blocks(f))
    Ext4JTx.plan.fin(j, Ext4JTx.build(JR.Ext4Journal.geom(j), J.Jbd2Super.uuid(sb), JR.Ext4Journal.raw(j), U32.to_nat(J.Jbd2Super.sequence(sb)), m, fresh, ws, O.Jbd2Options.commit_sec(opts), O.Jbd2Options.commit_nsec(opts)))

# Applying a plan

# the device after one step
def Ext4JTx.step(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, x: Ext4JStep, +d: Dv, +fs: S.Ext4Fs, +j: JR.Ext4Journal) -> Result<&2, &2, E.Ext4Error, Dv>:
  match x:
    case Ext4JHome{JW.Jbd2Write{b, o}}:
      DW.Ext4Dev.write(~Dv, ~block_size, ~write_block, d, S.Ext4Fs.block_size(fs), b, o)
    case Ext4JLog{p, o}:
      JR.Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d, fs, j, p, o)
    case Ext4JDesc{p, o, ps}:
      JR.Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d, fs, j, p, o)
    case Ext4JData{p, u, o}:
      JR.Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d, fs, j, p, o)
    case Ext4JCommit{p, o}:
      JR.Ext4Journal.put(~Dv, ~block_size, ~read_block, ~write_block, d, fs, j, p, o)
    case Ext4JFlag{st, cl}:
      DW.Ext4Dev.set_incompat(~Dv, ~block_size, ~read_block, ~write_block, d, S.Ext4Fs.ext2(fs), st, cl)

# the device after the first k steps of xs (all of them when k is at least
# their number), a tail call each: r is the device so far
def Ext4JTx.steps_on(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, k: Nat, xs: List<&2, Ext4JStep>, r: Result<&2, &2, E.Ext4Error, Dv>, +fs: S.Ext4Fs, +j: JR.Ext4Journal) -> Result<&2, &2, E.Ext4Error, Dv>:
  match k xs r:
    case _ _ Fail{e}:
      Fail{e}
    case 0n _ Done{d}:
      Done{d}
    case _ Nil{} Done{d}:
      Done{d}
    case 1n+q Con{x, t} Done{d}:
      Ext4JTx.steps_on(~Dv, ~block_size, ~read_block, ~write_block, q, t, Ext4JTx.step(~Dv, ~block_size, ~read_block, ~write_block, x, d, fs, j), fs, j)

# the device after the plan's first k steps: a crash after them (k at
# least Ext4JPlan.length: the whole transaction)
def Ext4JTx.apply(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, p: Ext4JPlan, k: Nat) -> Result<&2, &2, E.Ext4Error, Dv>:
  match p:
    case Ext4JPlan{+j, t}:
      Ext4JTx.steps_on(~Dv, ~block_size, ~read_block, ~write_block, k, Ext4JTx.steps(t), Done{d}, fs, j)

def Ext4JTx.run.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, +p: Ext4JPlan) -> Result<&2, &2, E.Ext4Error, Dv>:
  Ext4JTx.apply(~Dv, ~block_size, ~read_block, ~write_block, d, fs, p, Ext4JPlan.length(p))

# the device after a whole journalled transaction of the writes ws:
# planned, logged, committed and checkpointed
def Ext4JTx.run(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext4Fs, +opts: O.Jbd2Options, +m: Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, Dv>:
  do Result<&2, &2, E.Ext4Error, Dv>:
    p : Ext4JPlan <- Ext4JTx.plan(~Dv, ~block_size, ~read_block, d, fs, opts, m, fresh, ws)
    Ext4JTx.run.go(~Dv, ~block_size, ~read_block, ~write_block, d, fs, p)
