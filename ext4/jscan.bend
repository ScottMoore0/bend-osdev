# bend-osdev-ext4: reading a jbd2 log's blocks as records, one block at a
# time (a streaming parser: start, feed, records).
#
# The parser reads the log from the block it starts at, expecting
# transaction s: each block it is fed is the one at its position. A
# descriptor's data blocks are not read: they are the next blocks of the
# log, one per tag, and the parser records where each one is and moves on
# past them. The log ends at the first block that is not a descriptor,
# revoke or commit block of the expected transaction, at a descriptor or
# revoke block whose checksum fails, and at a commit block whose checksum
# fails (that transaction then has no commit, and is not replayed). A
# descriptor or revoke block whose checksum fails ends it too, and is
# reported (Jbd2Scan.bad): recovery then refuses the log.
import Base
import ../bytes/bytes.bend as B
import ./jsuper.bend as J
import ./jblock.bend as JB
import ./jlog.bend as JL

type Jbd2Scan is Data:
  Jbd2Scan{pos: Nat, seq: Nat, recs: List<&2, JL.Jbd2Rec>, live: Bool, bad: Maybe<&2, Nat>}

# a parser at log block pos, expecting transaction seq
def Jbd2Scan.start(pos: Nat, seq: Nat) -> Jbd2Scan:
  Jbd2Scan{pos, seq, Nil{}, True{}, None{}}

# the position of the block the parser wants next
def Jbd2Scan.pos(st: Jbd2Scan) -> Nat:
  match st:
    case Jbd2Scan{p, s, r, l, b}:
      p

# the transaction expected next
def Jbd2Scan.seq(st: Jbd2Scan) -> Nat:
  match st:
    case Jbd2Scan{p, s, r, l, b}:
      s

# whether the log goes on (false once its end is found)
def Jbd2Scan.live(st: Jbd2Scan) -> Bool:
  match st:
    case Jbd2Scan{p, s, r, l, b}:
      l

# the log block whose checksum failed (a descriptor or revoke block), if
# one did: e2fsprogs's recovery refuses such a log as a whole, and so does
# this package's (the documentation does not say)
def Jbd2Scan.bad(st: Jbd2Scan) -> Maybe<&2, Nat>:
  match st:
    case Jbd2Scan{p, s, r, l, b}:
      b

# the records read so far, in log order
def Jbd2Scan.records(st: Jbd2Scan) -> List<&2, JL.Jbd2Rec>:
  match st:
    case Jbd2Scan{p, s, r, l, b}:
      List.reverse(&2, JL.Jbd2Rec, r)

# where each tag's data block is: the log blocks from p on, one each
def Jbd2Scan.place(ts: List<&2, JB.Jbd2Tag>, +g: J.Jbd2Geom, +p: Nat, acc: List<&2, JL.Jbd2Put>) -> List<&2, JL.Jbd2Put> & Nat:
  match ts:
    case Nil{}:
      (List.reverse(&2, JL.Jbd2Put, acc), p)
    case Con{JB.Jbd2Tag{b, f, c}, t}:
      Jbd2Scan.place(t, g, J.Jbd2Geom.next(g, p), Con{JL.Jbd2Put{b, p, f, c}, acc})

def Jbd2Scan.desc.go(r: List<&2, JL.Jbd2Put> & Nat, +s: Nat, rs: List<&2, JL.Jbd2Rec>) -> Jbd2Scan:
  (ps, q) = r
  Jbd2Scan{q, s, Con{JL.Jbd2RDesc{s, ps}, rs}, True{}, None{}}

def Jbd2Scan.desc(m: Maybe<&2, List<&2, JB.Jbd2Tag>>, +g: J.Jbd2Geom, +p: Nat, +s: Nat, rs: List<&2, JL.Jbd2Rec>) -> Jbd2Scan:
  match m:
    case None{}:
      Jbd2Scan{p, s, rs, False{}, Some{p}}
    case Some{ts}:
      Jbd2Scan.desc.go(Jbd2Scan.place(ts, g, J.Jbd2Geom.next(g, p), Nil{}), s, rs)

def Jbd2Scan.revoke(m: Maybe<&2, List<&2, Nat>>, +g: J.Jbd2Geom, +p: Nat, +s: Nat, rs: List<&2, JL.Jbd2Rec>) -> Jbd2Scan:
  match m:
    case None{}:
      Jbd2Scan{p, s, rs, False{}, Some{p}}
    case Some{bs}:
      Jbd2Scan{J.Jbd2Geom.next(g, p), s, Con{JL.Jbd2RRevoke{s, bs}, rs}, True{}, None{}}

def Jbd2Scan.commit(ok: Bool, +g: J.Jbd2Geom, +p: Nat, +s: Nat, rs: List<&2, JL.Jbd2Rec>) -> Jbd2Scan:
  match ok:
    case True{}:
      Jbd2Scan{J.Jbd2Geom.next(g, p), 1n+s, Con{JL.Jbd2RCommit{s}, rs}, True{}, None{}}
    case False{}:
      Jbd2Scan{p, s, rs, False{}, None{}}

def Jbd2Scan.kind(k: Nat, +check: Bool, +g: J.Jbd2Geom, +blk: B.Octets, +p: Nat, +s: Nat, rs: List<&2, JL.Jbd2Rec>) -> Jbd2Scan:
  match k:
    case 1n:
      Jbd2Scan.desc(JB.Jbd2Desc.decode(check, g, blk), g, p, s, rs)
    case 2n:
      Jbd2Scan.commit(JB.Jbd2Commit.ok(check, g, blk), g, p, s, rs)
    case 5n:
      Jbd2Scan.revoke(JB.Jbd2Revoke.decode(check, g, blk), g, p, s, rs)
    case _:
      Jbd2Scan{p, s, rs, False{}, None{}}

def Jbd2Scan.feed.go(live: Bool, +check: Bool, +g: J.Jbd2Geom, +blk: B.Octets, +p: Nat, +s: Nat, rs: List<&2, JL.Jbd2Rec>) -> Jbd2Scan:
  match live:
    case False{}:
      Jbd2Scan{p, s, rs, False{}, None{}}
    case True{}:
      Jbd2Scan.kind(U32.to_nat(JB.Jbd2Block.kind(blk, U32.from_nat(s))), check, g, blk, p, s, rs)

# the parser after the block at its position (blk); check: verify the
# checksums. Once the log has ended, feeding changes nothing.
def Jbd2Scan.feed(+check: Bool, +g: J.Jbd2Geom, st: Jbd2Scan, +blk: B.Octets) -> Jbd2Scan:
  match st:
    case Jbd2Scan{+p, +s, rs, l, b}:
      Jbd2Scan.feed.go(l, check, g, blk, p, s, rs)

# A log held as a list of blocks (block i at position i, the geometry's
# s_maxlen past its end, so it does not wrap): for tests and the laws

def Jbd2Scan.list.go(fuel: Nat, live: Bool, m: Maybe<&2, B.Octets>, st: Jbd2Scan, +check: Bool, +g: J.Jbd2Geom, +blocks: List<&2, B.Octets>) -> Jbd2Scan:
  match fuel live m:
    case 0n _ _:
      st
    case _ False{} _:
      st
    case _ True{} None{}:
      st
    case 1n+f True{} Some{+blk}:
      +st2 = Jbd2Scan.feed(check, g, st, blk)
      Jbd2Scan.list.go(f, Jbd2Scan.live(st2), List.get(&2, B.Octets, blocks, Jbd2Scan.pos(st2)), st2, check, g, blocks)

# the records of a log held as a list, from its first block, transaction s
# first
def Jbd2Scan.list(+check: Bool, +g: J.Jbd2Geom, +blocks: List<&2, B.Octets>, +s: Nat) -> List<&2, JL.Jbd2Rec>:
  Jbd2Scan.records(Jbd2Scan.list.go(1n+List.length(&2, B.Octets, blocks), True{}, List.get(&2, B.Octets, blocks, 0n), Jbd2Scan.start(0n, s), check, g, blocks))
