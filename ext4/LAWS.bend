# Properties, for every input:
#   hashed directories: on every ordered model (htree.bend) the index
#     lookup finds what a linear scan of all leaves finds, for every name
#     whose entries all have the hash the lookup is given; the writer's
#     plan is always ordered, so this holds for every directory it builds;
#   the journal: an incomplete final transaction is never replayed; a
#     revoked block is never replayed from the revoking transaction or an
#     earlier one; a committed transaction replays exactly its unrevoked
#     blocks; replaying is idempotent; every data block the log stores
#     comes back as it was journalled (escaping);
#   journalled writes (drafts): the journalling device reads, after any
#     writes, as the device written directly, and its writes written home
#     give the device written directly; a crash anywhere before a
#     transaction's commit step recovers nothing, and anywhere from it on
#     recovers every logged block; the logged copies are the writes; the
#     checkpoint writes what recovery would; before the commit only fresh
#     blocks are written in place (none in data=journal mode);
#   the journal's codec: the superblock pointed at a log, and descriptor,
#     revoke and commit blocks, read back as written; the plan's log,
#     scanned as a log is read, gives back the plan's records; the
#     needs_recovery mark patches only the incompat field (and the
#     checksum).
# Witnesses that every hypothesis can hold, and vectors: the hashes
# debugfs computes, attribute hashes e2fsprogs stored, a lookup, a
# transaction with a revoke.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../ext2/dir.bend as DR
import ./htree.bend as T
import ./htwrite.bend as HW
import ./jlog.bend as JL
import ./hash.bend as H
import ./xattr.bend as XA
import ./jsuper.bend as J
import ./jblock.bend as JB
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./jwrite.bend as JW
import ./devwrite.bend as DW
import ./overlay.bend as OV
import ./jtx.bend as JT
import ./jscan.bend as JN
import ./super.bend as S
import ../ext2/csum.bend as K

# Hashed directories: on every ordered model (htree.bend), the index lookup
# finds what a linear scan of all leaves finds, for every name whose
# entries all have the hash the lookup is given.

law htree_lookup_scan:
  for ls: List<&2, T.Ext4HtLeaf>
  for +n: B.Octets
  for +h: Nat
  for ord: {T.Ext4Htree.ordered(ls) == True{} : Bool}
  for con: {T.Ext4Htree.consistent(ls, n, h) == True{} : Bool}
  {T.Ext4Htree.lookup(ls, h, n) == T.Ext4Htree.scan(ls, n) : Maybe<&2, T.Ext4HtEnt>}

# The htree writer's plan (htwrite.bend: the entries sorted by hash and
# filled into leaves) is always ordered, for every list of entries and
# every leaf size. So for every directory the writer builds, the index
# lookup finds what a linear scan finds.

law htree_plan_ordered:
  for +es: List<&2, T.Ext4HtEnt>
  for +cap: Nat
  {T.Ext4Htree.ordered(HW.Ext4Htree.plan(es, cap)) == True{} : Bool}

law htree_writer_lookup:
  for +es: List<&2, T.Ext4HtEnt>
  for +cap: Nat
  for +n: B.Octets
  for +h: Nat
  for con: {T.Ext4Htree.consistent(HW.Ext4Htree.plan(es, cap), n, h) == True{} : Bool}
  {T.Ext4Htree.lookup(HW.Ext4Htree.plan(es, cap), h, n) == T.Ext4Htree.scan(HW.Ext4Htree.plan(es, cap), n) : Maybe<&2, T.Ext4HtEnt>}

# The journal (jlog.bend). A transaction without its commit record is never
# replayed: records after the last commit change nothing, whatever they
# are, when no commit follows them (a crash before the commit block was
# written leaves exactly such a tail).

law scan_incomplete:
  for +s: Nat
  for rs: List<&2, JL.Jbd2Rec>
  for +u: List<&2, JL.Jbd2Rec>
  for nc: {JL.Jbd2Log.no_commit(u) == True{} : Bool}
  {JL.Jbd2Log.scan(s, List.append(&2, JL.Jbd2Rec, rs, u)) == JL.Jbd2Log.scan(s, rs) : List<&2, JL.Jbd2Tx>}

# A revoked block is never replayed from the transaction that revokes it or
# an earlier one: no block the plan replays is revoked, in the transactions
# the plan is made from, by a transaction at or after its own.

law plan_revoked:
  for +txs: List<&2, JL.Jbd2Tx>
  {JL.Jbd2Log.none_revoked(txs, JL.Jbd2Log.plan(txs)) == True{} : Bool}

# Replay is idempotent: on an in-memory device (blockdev's MemDev),
# writing a list of good writes (each one block to a block the device has)
# a second time changes no block's contents.

law replay_idempotent:
  for +d: D.MemDev
  for +ws: List<&2, JW.Jbd2Write>
  for +m: Nat
  for +ok: {DW.Ext4Dev.fits(D.MemDev.block_size(d), D.MemDev.block_count(d), ws) == True{} : Bool}
  {DW.Ext4Dev.read_mem(DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d}, D.MemDev.block_size(d)), D.MemDev.block_size(d)), m) == DW.Ext4Dev.read_mem(DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d}, D.MemDev.block_size(d)), m) : Result<&2, &2, E.Ext4Error, B.Octets>}

# A committed transaction replays every block it journals but those it
# revokes itself: the records a transaction writes (a revoke block, a
# descriptor with its blocks, the commit) recover as exactly its blocks.

law commit_replays:
  for +s: Nat
  for +rv: List<&2, Nat>
  for +ps: List<&2, JL.Jbd2Put>
  {JL.Jbd2Log.recover(s, [JL.Jbd2RRevoke{s, rv}, JL.Jbd2RDesc{s, ps}, JL.Jbd2RCommit{s}]) == JL.Jbd2Log.unrevoked(s, rv, ps) : List<&2, JL.Jbd2Do>}

# The log stores every data block faithfully: a block starting with the
# journal's magic number is stored with those four bytes zeroed and its tag
# marked ESCAPE, and the replay puts them back, so for every block the
# replay writes what the transaction journalled.

law escape_round_trip:
  for +d: B.Octets
  {JB.Jbd2.unescape(JB.Jbd2.needs_escape(d), JB.Jbd2.escape(d)) == d : B.Octets}

# The journal's codec (jsuper.bend, jblock.bend): every block the writer
# makes reads back as what was written. The scanner (jscan.bend) reads a
# log block's kind for its transaction: each kind of block the writer makes
# is read as that kind (descriptor 1, revoke 5, commit 2).

law jdesc_kind:
  for +g: J.Jbd2Geom
  for +seq: U32
  for +ts: List<&2, JB.Jbd2Tag>
  for +uuid: B.Octets
  {JB.Jbd2Block.kind(JB.Jbd2Desc.encode(g, seq, ts, uuid), seq) == 1 : U32}

law jrevoke_kind:
  for +g: J.Jbd2Geom
  for +seq: U32
  for +bs: List<&2, Nat>
  {JB.Jbd2Block.kind(JB.Jbd2Revoke.encode(g, seq, bs), seq) == 5 : U32}

law jcommit_kind:
  for +g: J.Jbd2Geom
  for +seq: U32
  for +sec: U32
  for +nsec: U32
  {JB.Jbd2Block.kind(JB.Jbd2Commit.encode(g, seq, sec, nsec), seq) == 2 : U32}

# A commit block's checksum verifies (checked or not), and the block holds
# its time: h_commit_sec at byte 48 (a 64-bit field), h_commit_nsec at 56

law jcommit_ok:
  for +check: Bool
  for +g: J.Jbd2Geom
  for +seq: U32
  for +sec: U32
  for +nsec: U32
  {JB.Jbd2Commit.ok(check, g, JB.Jbd2Commit.encode(g, seq, sec, nsec)) == True{} : Bool}

law jcommit_sec:
  for +g: J.Jbd2Geom
  for +seq: U32
  for +sec: U32
  for +nsec: U32
  {B.Octets.be64_at(JB.Jbd2Commit.encode(g, seq, sec, nsec), 48n) == Some{W.W64.from_parts(0, sec)} : Maybe<&2, W.W64>}

law jcommit_nsec:
  for +g: J.Jbd2Geom
  for +seq: U32
  for +sec: U32
  for +nsec: U32
  {B.Octets.be32_at(JB.Jbd2Commit.encode(g, seq, sec, nsec), 56n) == Some{nsec} : Maybe<&2, U32>}

# A descriptor block reads back as its tags (its checksum checked or not),
# whenever they fit it (Jbd2Desc.fits: each tag storable, only the last
# with LAST_TAG, all inside the block) and the UUID is 16 bytes

law jdesc_round_trip:
  for +check: Bool
  for +g: J.Jbd2Geom
  for +seq: U32
  for +ts: List<&2, JB.Jbd2Tag>
  for +uuid: B.Octets
  for +u: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}
  for +f: {JB.Jbd2Desc.fits(g, ts) == True{} : Bool}
  {JB.Jbd2Desc.decode(check, g, JB.Jbd2Desc.encode(g, seq, ts, uuid)) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}

# A revoke block reads back as its block numbers (checked or not), whenever
# they fit it (Jbd2Revoke.fits: each number fits its record, and r_count
# fits its 32 bits and the block)

law jrevoke_round_trip:
  for +check: Bool
  for +g: J.Jbd2Geom
  for +seq: U32
  for +bs: List<&2, Nat>
  for +f: {JB.Jbd2Revoke.fits(g, bs) == True{} : Bool}
  {JB.Jbd2Revoke.decode(check, g, JB.Jbd2Revoke.encode(g, seq, bs)) == Some{bs} : Maybe<&2, List<&2, Nat>>}

# The journal superblock pointed at a log (Jbd2Super.with_log: the
# writer's way to open and close a transaction) parses as the old one with
# s_sequence and s_start set (s_start as its 32-bit field holds it) and
# every other field kept; with checksums, its checksum verifies. (The
# fields lie in a superblock's first 256 bytes; the journal's block 0 is a
# whole block.)

law jsuper_log_fixed:
  for +o: B.Octets
  for +start: Nat
  for +seq: U32
  for +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}
  {J.Jbd2Super.fixed(J.Jbd2Super.parse(J.Jbd2Super.with_log(o, start, seq))) == J.Jbd2Super.fixed(J.Jbd2Super.parse(o)) : J.Jbd2Super}

law jsuper_log_sequence:
  for +o: B.Octets
  for +start: Nat
  for +seq: U32
  for +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}
  {J.Jbd2Super.sequence(J.Jbd2Super.parse(J.Jbd2Super.with_log(o, start, seq))) == seq : U32}

law jsuper_log_start:
  for +o: B.Octets
  for +start: Nat
  for +seq: U32
  for +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}
  {J.Jbd2Super.start(J.Jbd2Super.parse(J.Jbd2Super.with_log(o, start, seq))) == U32.to_nat(U32.from_nat(start)) : Nat}

law jsuper_log_csum:
  for +o: B.Octets
  for +start: Nat
  for +seq: U32
  for +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}
  for +c: {J.Jbd2Super.has_csum(J.Jbd2Super.parse(o)) == True{} : Bool}
  {J.Jbd2Super.csum(J.Jbd2Super.with_log(o, start, seq)) == J.Jbd2Super.checksum(J.Jbd2Super.parse(J.Jbd2Super.with_log(o, start, seq))) : U32}

# Journalled writes (overlay.bend, jtx.bend). The journalling device (an
# Ext4Ov over blockdev's MemDev) after a list of good writes (each one
# block to a block the device has), and the device written directly:

def Ext4Laws.ov(+d: D.MemDev, ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>:
  DW.Ext4Dev.write_all(~OV.Ext4Ov<D.MemDev>, ~OV.Ext4Ov.mem_block_size, ~OV.Ext4Ov.mem_write, ws, Done{OV.Ext4Ov.start(D.MemDev, d)}, D.MemDev.block_size(d))

def Ext4Laws.direct(+d: D.MemDev, ws: List<&2, JW.Jbd2Write>) -> Result<&2, &2, E.Ext4Error, D.MemDev>:
  DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d}, D.MemDev.block_size(d))

# The journalling device reads every block as the device written directly
# would: so a writer that reaches its device only through block reads and
# writes (ext2's) does on the overlay what it would do on the device.

law ov_reads:
  for +d: D.MemDev
  for +ws: List<&2, JW.Jbd2Write>
  for +m: Nat
  for +ok: {DW.Ext4Dev.fits(D.MemDev.block_size(d), D.MemDev.block_count(d), ws) == True{} : Bool}
  {OV.Ext4Ov.read_mem(Ext4Laws.ov(d, ws), m) == DW.Ext4Dev.read_mem(Ext4Laws.direct(d, ws), m) : Result<&2, &2, E.Ext4Error, B.Octets>}

# The writes the journalling device keeps (each block once, its last
# contents: what a transaction logs), written home, give every block the
# device written directly has: a complete transaction, checkpointed, is the
# unjournalled write.

law ov_flush:
  for +d: D.MemDev
  for +ws: List<&2, JW.Jbd2Write>
  for +m: Nat
  for +ok: {DW.Ext4Dev.fits(D.MemDev.block_size(d), D.MemDev.block_count(d), ws) == True{} : Bool}
  {DW.Ext4Dev.read_mem(OV.Ext4Ov.flush(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, Ext4Laws.ov(d, ws)), m) == DW.Ext4Dev.read_mem(Ext4Laws.direct(d, ws), m) : Result<&2, &2, E.Ext4Error, B.Octets>}

# A transaction's plan (jtx.bend), for every journal geometry, UUID,
# journal superblock, ID, mode, set of fresh blocks, writes and commit time.
# A crash after the plan's first k steps leaves, in the journal, the
# records of those steps (Ext4JTx.records); recovery replays what
# Jbd2Log.recover makes of them.

def Ext4Laws.tx(+g: J.Jbd2Geom, +uuid: B.Octets, +jsb: B.Octets, +seq: Nat, +m: JT.Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>, +sec: U32, +nsec: U32) -> JT.Ext4JTx:
  JT.Ext4JTx.build(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)

# A crash before the commit step: recovery replays nothing, so the
# filesystem is as it was (the only blocks written in place by then are
# fresh ones, jtx_in_place).

law jtx_uncommitted:
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +m: JT.Jbd2Mode
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  for +k: Nat
  for +h: {Nat.is_lt(k, JT.Ext4JTx.commit_at(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec))) == True{} : Bool}
  {JL.Jbd2Log.recover(seq, JT.Ext4JTx.records(seq, List.take(&2, JT.Ext4JStep, JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), k))) == Nil{} : List<&2, JL.Jbd2Do>}

# A crash at the commit step or any number j of steps after it: recovery
# replays every logged copy, in log order, none revoked.

law jtx_committed:
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +m: JT.Jbd2Mode
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  for +j: Nat
  {JL.Jbd2Log.recover(seq, JT.Ext4JTx.records(seq, List.take(&2, JT.Ext4JStep, JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), Nat.add(JT.Ext4JTx.commit_at(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), j)))) == JL.Jbd2Log.unrevoked(seq, Nil{}, JT.Ext4JTx.data_puts(JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)))) : List<&2, JL.Jbd2Do>}

# The logged copies are the writes: replaying them (each home, unescaped as
# its tag says) writes exactly the transaction's writes that are not done
# in place, in order (the superblock's copy marked needs_recovery).

law jtx_copies:
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +m: JT.Jbd2Mode
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  {JT.Ext4JTx.replay_writes(JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec))) == JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws) : List<&2, JW.Jbd2Write>}

# The checkpoint (the steps after the commit) writes home exactly what a
# recovery from the commit on would replay.

law jtx_checkpoint:
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +m: JT.Jbd2Mode
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  {JT.Ext4JTx.homes(List.drop(&2, JT.Ext4JStep, JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), JT.Ext4JTx.commit_at(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)))) == JT.Ext4JTx.replay_writes(JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec))) : List<&2, JW.Jbd2Write>}

# Up to the commit, every block written in place is a fresh one (free
# before the transaction, so the old filesystem never reads it)...

law jtx_in_place:
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +m: JT.Jbd2Mode
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  {JT.Ext4JTx.fresh_homes(fresh, List.take(&2, JT.Ext4JStep, JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), JT.Ext4JTx.commit_at(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)))) == True{} : Bool}

# ...and in data=journal mode there is none.

law jtx_journal_mode:
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  {JT.Ext4JTx.homes(List.take(&2, JT.Ext4JStep, JT.Ext4JTx.steps(Ext4Laws.tx(g, uuid, jsb, seq, JT.Jbd2DataJournal{}, fresh, ws, sec, nsec)), JT.Ext4JTx.commit_at(Ext4Laws.tx(g, uuid, jsb, seq, JT.Jbd2DataJournal{}, fresh, ws, sec, nsec)))) == Nil{} : List<&2, JW.Jbd2Write>}

# The needs_recovery mark and clear (Ext4Dev.super_with: the plan's copy
# of the superblock marked, and its flag steps set and clear the feature
# on the device): on a superblock's 1024 bytes, s_feature_incompat becomes
# (old | set) & ~clear, every byte before it and after it up to the
# checksum is kept, and the checksum field is the new superblock's
# checksum (metadata_csum) or untouched.

law super_with_len:
  for +sb: B.Octets
  for +set: U32
  for +clear: U32
  for +h: {Nat.is_eq(B.Octets.len(sb), 1024n) == True{} : Bool}
  {B.Octets.len(DW.Ext4Dev.super_with(sb, set, clear)) == 1024n : Nat}

law super_with_incompat:
  for +sb: B.Octets
  for +set: U32
  for +clear: U32
  for +h: {Nat.is_eq(B.Octets.len(sb), 1024n) == True{} : Bool}
  {B.Octets.le32_at(DW.Ext4Dev.super_with(sb, set, clear), 96n) == Some{U32.and(U32.or(Maybe.default(&2, U32, B.Octets.le32_at(sb, 96n), 0), set), U32.not(clear))} : Maybe<&2, U32>}

law super_with_head:
  for +sb: B.Octets
  for +set: U32
  for +clear: U32
  for +h: {Nat.is_eq(B.Octets.len(sb), 1024n) == True{} : Bool}
  {B.Octets.slice(0n, 96n, DW.Ext4Dev.super_with(sb, set, clear)) == B.Octets.slice(0n, 96n, sb) : B.Octets}

law super_with_body:
  for +sb: B.Octets
  for +set: U32
  for +clear: U32
  for +h: {Nat.is_eq(B.Octets.len(sb), 1024n) == True{} : Bool}
  {B.Octets.slice(100n, 920n, DW.Ext4Dev.super_with(sb, set, clear)) == B.Octets.slice(100n, 920n, sb) : B.Octets}

law super_with_tail:
  for +sb: B.Octets
  for +set: U32
  for +clear: U32
  for +h: {Nat.is_eq(B.Octets.len(sb), 1024n) == True{} : Bool}
  {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(DW.Ext4Dev.super_with(sb, set, clear), 1020n), 0), K.Ext2Csum.super(DW.Ext4Dev.super_with(sb, set, clear))), B.Octets.is_eq(B.Octets.slice(1020n, 4n, DW.Ext4Dev.super_with(sb, set, clear)), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}

# The plan's logged copy of the superblock's block carries the mark: its
# superblock is the block's, needs_recovery set; the bytes around it are
# kept; a write to any other block is logged as it is.

def Ext4Laws.data_of(ws: List<&2, JW.Jbd2Write>, +d: B.Octets) -> B.Octets:
  match ws:
    case Con{JW.Jbd2Write{b, x}, t}:
      x
    case Nil{}:
      d

def Ext4Laws.marked(+bs: Nat, +d: B.Octets) -> B.Octets:
  Ext4Laws.data_of(JT.Ext4JTx.marks(bs, [JW.Jbd2Write{JT.Ext4JTx.super_block(bs), d}]), d)

law jtx_mark_super:
  for +bs: Nat
  for +d: B.Octets
  for +h: {Nat.is_le(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), B.Octets.len(d)) == True{} : Bool}
  {B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, Ext4Laws.marked(bs, d)) == DW.Ext4Dev.super_with(B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d), S.Ext4Super.incompat_recover(), 0) : B.Octets}

law jtx_mark_before:
  for +bs: Nat
  for +d: B.Octets
  for +h: {Nat.is_le(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), B.Octets.len(d)) == True{} : Bool}
  {B.Octets.take(JT.Ext4JTx.super_off(bs), Ext4Laws.marked(bs, d)) == B.Octets.take(JT.Ext4JTx.super_off(bs), d) : B.Octets}

law jtx_mark_after:
  for +bs: Nat
  for +d: B.Octets
  for +h: {Nat.is_le(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), B.Octets.len(d)) == True{} : Bool}
  {B.Octets.drop(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), Ext4Laws.marked(bs, d)) == B.Octets.drop(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), d) : B.Octets}

law jtx_mark_other:
  for +bs: Nat
  for +b: Nat
  for +d: B.Octets
  for +h: {Nat.is_eq(b, JT.Ext4JTx.super_block(bs)) == False{} : Bool}
  {JT.Ext4JTx.marks(bs, [JW.Jbd2Write{b, d}]) == [JW.Jbd2Write{b, d}] : List<&2, JW.Jbd2Write>}

# The plan's log blocks hold its records: read as a log is read (each
# block in turn, fed to the streaming scanner when it is at the position
# the scanner asks for; the data blocks, whose places the descriptors
# give, are passed over), the descriptors and the commit block give back
# the records the laws above are stated with. For every geometry whose
# descriptor holds a tag, a 16-byte UUID, writes whose block numbers fit a
# tag, and a log the journal holds (Ext4JTx.plan's check), checksums
# checked or not.

def Ext4Laws.feed.at(hit: Bool, +check: Bool, +g: J.Jbd2Geom, +st: JN.Jbd2Scan, +o: B.Octets) -> JN.Jbd2Scan:
  match hit:
    case True{}:
      JN.Jbd2Scan.feed(check, g, st, o)
    case False{}:
      st

def Ext4Laws.feed(xs: List<&2, JT.Ext4JStep>, +check: Bool, +g: J.Jbd2Geom, +st: JN.Jbd2Scan) -> JN.Jbd2Scan:
  match xs:
    case Nil{}:
      st
    case Con{JT.Ext4JDesc{p, o, ps}, t}:
      Ext4Laws.feed(t, check, g, Ext4Laws.feed.at(Nat.is_eq(p, JN.Jbd2Scan.pos(st)), check, g, st, o))
    case Con{JT.Ext4JData{p, u, o}, t}:
      Ext4Laws.feed(t, check, g, Ext4Laws.feed.at(Nat.is_eq(p, JN.Jbd2Scan.pos(st)), check, g, st, o))
    case Con{JT.Ext4JCommit{p, o}, t}:
      Ext4Laws.feed(t, check, g, Ext4Laws.feed.at(Nat.is_eq(p, JN.Jbd2Scan.pos(st)), check, g, st, o))
    case Con{x, t}:
      Ext4Laws.feed(t, check, g, st)

def Ext4Laws.log(+t: JT.Ext4JTx) -> List<&2, JT.Ext4JStep>:
  List.append(&2, JT.Ext4JStep, JT.Ext4JTx.log(t), [JT.Ext4JTx.commit(t)])

law jtx_log_scan:
  for +check: Bool
  for +g: J.Jbd2Geom
  for +uuid: B.Octets
  for +jsb: B.Octets
  for +seq: Nat
  for +m: JT.Jbd2Mode
  for +fresh: List<&2, Nat>
  for +ws: List<&2, JW.Jbd2Write>
  for +sec: U32
  for +nsec: U32
  for +u: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}
  for +c: {Nat.is_lt(0n, JB.Jbd2Desc.capacity(g)) == True{} : Bool}
  for +b: {JT.Ext4JTx.blocks_fit(J.Jbd2Geom.wide(g), ws) == True{} : Bool}
  for +r: {Nat.is_le(JT.Ext4JTx.log_blocks(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), Nat.sub(J.Jbd2Geom.maxlen(g), J.Jbd2Geom.first(g))) == True{} : Bool}
  {JN.Jbd2Scan.records(Ext4Laws.feed(Ext4Laws.log(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), check, g, JN.Jbd2Scan.start(J.Jbd2Geom.first(g), seq))) == JT.Ext4JTx.records(seq, Ext4Laws.log(Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec))) : List<&2, JL.Jbd2Rec>}

# Vectors: directory hashes debugfs's dx_hash gives (e2fsprogs 1.47.0),
# for each hash version (0 legacy, 1 half MD4, 2 TEA; 3 to 5 the same
# reading names as unsigned chars), names with bytes above 127, a name of
# two MD4 blocks and of three TEA blocks, and a seed.

def Ext4Laws.h(v: U32, seed: List<&2, U32>, name: List<&2, U32>) -> Result<&2, &2, E.Ext4Error, H.Ext4DxHash>:
  H.Ext4Hash.name(v, seed, B.Octets.of_list(name))

def Ext4Laws.zero() -> List<&2, U32>:
  [0, 0, 0, 0]

law hash_legacy:
  {Ext4Laws.h(0, Ext4Laws.zero(), [110, 97, 109, 101, 95, 49, 46, 116, 120, 116]) == Done{H.Ext4DxHash{53319862, 0}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_legacy_signed:
  {Ext4Laws.h(0, Ext4Laws.zero(), [99, 97, 102, 195, 169]) == Done{H.Ext4DxHash{2529843756, 0}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_legacy_unsigned:
  {Ext4Laws.h(3, Ext4Laws.zero(), [99, 97, 102, 195, 169]) == Done{H.Ext4DxHash{1843282480, 0}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_half_md4:
  {Ext4Laws.h(1, Ext4Laws.zero(), [110, 97, 109, 101, 95, 49, 46, 116, 120, 116]) == Done{H.Ext4DxHash{482413550, 3850211991}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_half_md4_signed:
  {Ext4Laws.h(1, Ext4Laws.zero(), [99, 97, 102, 195, 169, 45, 255]) == Done{H.Ext4DxHash{943033222, 711138562}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_half_md4_unsigned:
  {Ext4Laws.h(4, Ext4Laws.zero(), [99, 97, 102, 195, 169, 45, 255]) == Done{H.Ext4DxHash{2885418672, 1795652753}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_half_md4_long:
  {Ext4Laws.h(1, Ext4Laws.zero(), [97, 95, 114, 97, 116, 104, 101, 114, 95, 108, 111, 110, 103, 95, 102, 105, 108, 101, 95, 110, 97, 109, 101, 95, 111, 102, 95, 102, 111, 114, 116, 121, 95, 98, 121, 116, 101, 115, 33, 33]) == Done{H.Ext4DxHash{1252937094, 1729849783}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_half_md4_seed:
  {Ext4Laws.h(1, [19088743, 2309737967, 195948557, 324508639], [115, 101, 101, 100, 101, 100]) == Done{H.Ext4DxHash{1537375816, 499138460}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_tea:
  {Ext4Laws.h(2, Ext4Laws.zero(), [87, 71, 113, 107, 55, 77, 98, 101]) == Done{H.Ext4DxHash{2010554832, 1770962636}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_tea_signed:
  {Ext4Laws.h(2, Ext4Laws.zero(), [226, 130, 172, 117, 114, 111]) == Done{H.Ext4DxHash{154278278, 2114761031}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_tea_unsigned:
  {Ext4Laws.h(5, Ext4Laws.zero(), [226, 130, 172, 117, 114, 111]) == Done{H.Ext4DxHash{2847078360, 641360245}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

law hash_tea_long:
  {Ext4Laws.h(2, Ext4Laws.zero(), [97, 95, 114, 97, 116, 104, 101, 114, 95, 108, 111, 110, 103, 95, 102, 105, 108, 101, 95, 110, 97, 109, 101, 95, 111, 102, 95, 102, 111, 114, 116, 121, 95, 98, 121, 116, 101, 115, 33, 33]) == Done{H.Ext4DxHash{2149732818, 1906498331}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

# a filesystem hashing unsigned chars moves the root's version to its twin
law hash_version_unsigned:
  {H.Ext4Hash.version(1, False{}) == 4 : U32}

law hash_bad_version:
  {Ext4Laws.h(6, Ext4Laws.zero(), [97]) == Fail{E.Ext4BadHashVersion{6}} : Result<&2, &2, E.Ext4Error, H.Ext4DxHash>}

# Vectors: extended attribute hashes as e2fsprogs stored them (an entry in
# an attribute block, user.alpha0123456789 = "world_of_values"; an entry
# whose value is in an EA inode, user.huge, the value's crc32c 0xB7744284)

law xattr_entry_hash:
  {XA.Ext4Xattr.entry_hash(False{}, B.Octets.of_string("alpha0123456789"), B.Octets.of_string("world_of_values")) == 3791505720 : U32}

law xattr_inode_hash:
  {XA.Ext4Xattr.inode_hash(False{}, B.Octets.of_string("huge"), 3077849732) == 1878082225 : U32}

# Witnesses: each law's hypotheses can hold

def Ext4Laws.ent(h: Nat, i: U32, name: String) -> T.Ext4HtEnt:
  T.Ext4HtEnt{h, DR.Ext2Dirent{i, 12, 1, 1, B.Octets.of_string(name)}}

def Ext4Laws.leaves() -> List<&2, T.Ext4HtLeaf>:
  [T.Ext4HtLeaf{0n, [Ext4Laws.ent(5n, 12, "a")]}, T.Ext4HtLeaf{10n, [Ext4Laws.ent(12n, 13, "b"), Ext4Laws.ent(14n, 14, "c")]}]

law htree_lookup_scan_witness:
  {Bool.and(T.Ext4Htree.ordered(Ext4Laws.leaves()), T.Ext4Htree.consistent(Ext4Laws.leaves(), B.Octets.of_string("b"), 12n)) == True{} : Bool}

law htree_writer_lookup_witness:
  {T.Ext4Htree.consistent(HW.Ext4Htree.plan([Ext4Laws.ent(7n, 12, "x"), Ext4Laws.ent(3n, 13, "y")], 100n), B.Octets.of_string("x"), 7n) == True{} : Bool}

law scan_incomplete_witness:
  {JL.Jbd2Log.no_commit([JL.Jbd2RDesc{1n, Nil{}}, JL.Jbd2RRevoke{1n, [5n]}]) == True{} : Bool}

law replay_idempotent_witness:
  {DW.Ext4Dev.fits(D.MemDev.block_size(D.MemDev.blank(4n, 2n)), D.MemDev.block_count(D.MemDev.blank(4n, 2n)), [JW.Jbd2Write{1n, B.Octets.of_string("abcd")}]) == True{} : Bool}

# (ov_reads and ov_flush share replay_idempotent's hypothesis, witnessed
# above; a crash after no steps at all comes before every commit)
law jtx_uncommitted_witness:
  {Nat.is_lt(0n, JT.Ext4JTx.commit_at(Ext4Laws.tx(J.Jbd2Geom{1024n, False{}, 0n, 0, 1n, 1024n}, B.Octets.empty(), B.Octets.empty(), 1n, JT.Jbd2DataJournal{}, Nil{}, Nil{}, 0, 0))) == True{} : Bool}

# (the journal codec's and the log scan's hypotheses: a 1 KiB-block
# geometry without checksums, a 16-byte UUID, a journal superblock with
# csum_v3, and a one-block transaction)

def Ext4Laws.g0() -> J.Jbd2Geom:
  J.Jbd2Geom{1024n, False{}, 0n, 0, 1n, 1024n}

def Ext4Laws.jsb_v3() -> B.Octets:
  B.Octets.append(B.Octets.zeros(4n), B.Octets.append(B.Octets.be32(4), B.Octets.append(B.Octets.zeros(32n), B.Octets.append(B.Octets.be32(16), B.Octets.zeros(212n)))))

law jsuper_log_witness:
  {Bool.and(Nat.is_le(256n, B.Octets.len(Ext4Laws.jsb_v3())), J.Jbd2Super.has_csum(J.Jbd2Super.parse(Ext4Laws.jsb_v3()))) == True{} : Bool}

law jdesc_round_trip_witness:
  {Bool.and(Nat.is_eq(B.Octets.len(B.Octets.zeros(16n)), 16n), JB.Jbd2Desc.fits(Ext4Laws.g0(), [JB.Jbd2Tag{5n, 8, 0}])) == True{} : Bool}

law jrevoke_round_trip_witness:
  {JB.Jbd2Revoke.fits(Ext4Laws.g0(), [5n]) == True{} : Bool}

law jtx_log_scan_witness:
  {Bool.and(Nat.is_lt(0n, JB.Jbd2Desc.capacity(Ext4Laws.g0())), Bool.and(JT.Ext4JTx.blocks_fit(False{}, [JW.Jbd2Write{5n, B.Octets.zeros(1024n)}]), Nat.is_le(JT.Ext4JTx.log_blocks(Ext4Laws.tx(Ext4Laws.g0(), B.Octets.zeros(16n), B.Octets.zeros(1024n), 1n, JT.Jbd2DataJournal{}, Nil{}, [JW.Jbd2Write{5n, B.Octets.zeros(1024n)}], 0, 0)), Nat.sub(1024n, 1n)))) == True{} : Bool}

law super_with_witness:
  {Bool.and(Nat.is_eq(B.Octets.len(B.Octets.zeros(1024n)), 1024n), Bool.and(Nat.is_le(Nat.add(JT.Ext4JTx.super_off(1024n), 1024n), B.Octets.len(B.Octets.zeros(1024n))), Bool.not(Nat.is_eq(5n, JT.Ext4JTx.super_block(1024n))))) == True{} : Bool}

# Vectors: the model's lookup on the leaves above, a found and a missing
# name; a transaction revoking one of its two blocks

law htree_lookup_vector:
  {T.Ext4Htree.lookup(Ext4Laws.leaves(), 12n, B.Octets.of_string("b")) == Some{Ext4Laws.ent(12n, 13, "b")} : Maybe<&2, T.Ext4HtEnt>}

law htree_lookup_missing:
  {T.Ext4Htree.lookup(Ext4Laws.leaves(), 12n, B.Octets.of_string("z")) == None{} : Maybe<&2, T.Ext4HtEnt>}

law commit_replays_vector:
  {JL.Jbd2Log.recover(3n, [JL.Jbd2RRevoke{3n, [8n]}, JL.Jbd2RDesc{3n, [JL.Jbd2Put{8n, 1n, 0, 0}, JL.Jbd2Put{9n, 2n, 0, 0}]}, JL.Jbd2RCommit{3n}]) == [JL.Jbd2Do{3n, JL.Jbd2Put{9n, 2n, 0, 0}}] : List<&2, JL.Jbd2Do>}
