# bend-osdev-ext4: a jbd2 log as records, and the three passes of recovery
# over them (the jbd2 documentation, "Journal (jbd2)": recovery reads the
# log from s_start, transaction s_sequence on, to its end; a transaction
# counts only once its commit block is found; a revoke record for a block
# in transaction T keeps every copy of that block journalled by T or an
# earlier transaction from being replayed).
#
# A record is what one or more log blocks say: a descriptor and the data
# blocks after it (Jbd2RDesc: each journalled block's home block number,
# the log block holding its copy, and its tag's flags and checksum), a
# revoke block (Jbd2RRevoke) or a commit block (Jbd2RCommit), each with its
# transaction's ID. jscan.bend turns log blocks into records.
#
# The passes:
#   1. scan: group the records into transactions, in order, from the
#      expected ID on; a transaction without its commit (the log's last,
#      when the crash came before its commit) is dropped;
#   2. revoke: the table of every revoke record of those transactions;
#   3. replay: every journalled block of every transaction, in log order,
#      except those a revoke record of the same or a later transaction
#      covers. jreplay.bend reads each from the log and writes it home.
import Base
import ../bytes/bytes.bend as B

type Jbd2Put is Data:
  Jbd2Put{block: Nat, src: Nat, flags: U32, csum: U32}

def Jbd2Put.block(p: Jbd2Put) -> Nat:
  match p:
    case Jbd2Put{b, s, f, c}:
      b

def Jbd2Put.src(p: Jbd2Put) -> Nat:
  match p:
    case Jbd2Put{b, s, f, c}:
      s

def Jbd2Put.flags(p: Jbd2Put) -> U32:
  match p:
    case Jbd2Put{b, s, f, c}:
      f

def Jbd2Put.csum(p: Jbd2Put) -> U32:
  match p:
    case Jbd2Put{b, s, f, c}:
      c

type Jbd2Rec is Data:
  Jbd2RDesc{seq: Nat, puts: List<&2, Jbd2Put>}
  Jbd2RRevoke{seq: Nat, blocks: List<&2, Nat>}
  Jbd2RCommit{seq: Nat}

def Jbd2Rec.seq(r: Jbd2Rec) -> Nat:
  match r:
    case Jbd2RDesc{s, p}:
      s
    case Jbd2RRevoke{s, b}:
      s
    case Jbd2RCommit{s}:
      s

type Jbd2Tx is Data:
  Jbd2Tx{seq: Nat, puts: List<&2, Jbd2Put>, revokes: List<&2, Nat>}

def Jbd2Tx.seq(t: Jbd2Tx) -> Nat:
  match t:
    case Jbd2Tx{s, p, r}:
      s

def Jbd2Tx.puts(t: Jbd2Tx) -> List<&2, Jbd2Put>:
  match t:
    case Jbd2Tx{s, p, r}:
      p

def Jbd2Tx.revokes(t: Jbd2Tx) -> List<&2, Nat>:
  match t:
    case Jbd2Tx{s, p, r}:
      r

# Pass 1: scan

# whether the next record belongs to transaction s
def Jbd2Log.fits(rs: List<&2, Jbd2Rec>, +s: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{r, t}:
      Nat.is_eq(Jbd2Rec.seq(r), s)

def Jbd2Log.rev_onto(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Jbd2Log.rev_onto(A, t, Con{h, acc})

# the transactions of rs, transaction s first: ps and vs gather the open
# transaction's blocks and revokes (last first), out the transactions
# found (last first). A record of another transaction ends the log, and so
# does the end of the records; the open transaction is then dropped.
def Jbd2Log.scan.go(rs: List<&2, Jbd2Rec>, ok: Bool, +s: Nat, ps: List<&2, Jbd2Put>, vs: List<&2, Nat>, out: List<&2, Jbd2Tx>) -> List<&2, Jbd2Tx>:
  match rs ok:
    case Nil{} _:
      List.reverse(&2, Jbd2Tx, out)
    case Con{r, t} False{}:
      List.reverse(&2, Jbd2Tx, out)
    case Con{Jbd2RDesc{q, xs}, +t} True{}:
      Jbd2Log.scan.go(t, Jbd2Log.fits(t, s), s, Jbd2Log.rev_onto(Jbd2Put, xs, ps), vs, out)
    case Con{Jbd2RRevoke{q, bs}, +t} True{}:
      Jbd2Log.scan.go(t, Jbd2Log.fits(t, s), s, ps, Jbd2Log.rev_onto(Nat, bs, vs), out)
    case Con{Jbd2RCommit{q}, +t} True{}:
      Jbd2Log.scan.go(t, Jbd2Log.fits(t, 1n+s), 1n+s, Nil{}, Nil{}, Con{Jbd2Tx{s, List.reverse(&2, Jbd2Put, ps), List.reverse(&2, Nat, vs)}, out})

# pass 1: the committed transactions of the records, from transaction s on
def Jbd2Log.scan(+s: Nat, +rs: List<&2, Jbd2Rec>) -> List<&2, Jbd2Tx>:
  Jbd2Log.scan.go(rs, Jbd2Log.fits(rs, s), s, Nil{}, Nil{}, Nil{})

# Pass 2: the revoke table

type Jbd2Rv is Data:
  Jbd2Rv{block: Nat, seq: Nat}

def Jbd2Log.rvs(bs: List<&2, Nat>, +s: Nat, acc: List<&2, Jbd2Rv>) -> List<&2, Jbd2Rv>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      Jbd2Log.rvs(t, s, Con{Jbd2Rv{b, s}, acc})

def Jbd2Log.table.go(txs: List<&2, Jbd2Tx>, acc: List<&2, Jbd2Rv>) -> List<&2, Jbd2Rv>:
  match txs:
    case Nil{}:
      acc
    case Con{Jbd2Tx{s, ps, vs}, t}:
      Jbd2Log.table.go(t, Jbd2Log.rvs(vs, s, acc))

# pass 2: every revoke record of the transactions, with its transaction
def Jbd2Log.table(txs: List<&2, Jbd2Tx>) -> List<&2, Jbd2Rv>:
  Jbd2Log.table.go(txs, Nil{})

# whether the table revokes block b for transaction s: a record for b in
# transaction s or a later one
def Jbd2Log.revoked(rv: List<&2, Jbd2Rv>, +b: Nat, +s: Nat) -> Bool:
  match rv:
    case Nil{}:
      False{}
    case Con{Jbd2Rv{c, q}, t}:
      Bool.or(Bool.and(Nat.is_eq(c, b), Nat.is_le(s, q)), Jbd2Log.revoked(t, b, s))

# Pass 3: what to replay

type Jbd2Do is Data:
  Jbd2Do{seq: Nat, put: Jbd2Put}

def Jbd2Do.seq(d: Jbd2Do) -> Nat:
  match d:
    case Jbd2Do{s, p}:
      s

def Jbd2Do.put(d: Jbd2Do) -> Jbd2Put:
  match d:
    case Jbd2Do{s, p}:
      p

def Jbd2Log.keep.pick(skip: Bool, +s: Nat, p: Jbd2Put, acc: List<&2, Jbd2Do>) -> List<&2, Jbd2Do>:
  match skip:
    case True{}:
      acc
    case False{}:
      Con{Jbd2Do{s, p}, acc}

def Jbd2Log.keep(ps: List<&2, Jbd2Put>, +s: Nat, +rv: List<&2, Jbd2Rv>, acc: List<&2, Jbd2Do>) -> List<&2, Jbd2Do>:
  match ps:
    case Nil{}:
      acc
    case Con{+p, t}:
      Jbd2Log.keep(t, s, rv, Jbd2Log.keep.pick(Jbd2Log.revoked(rv, Jbd2Put.block(p), s), s, p, acc))

def Jbd2Log.plan.go(txs: List<&2, Jbd2Tx>, +rv: List<&2, Jbd2Rv>, acc: List<&2, Jbd2Do>) -> List<&2, Jbd2Do>:
  match txs:
    case Nil{}:
      List.reverse(&2, Jbd2Do, acc)
    case Con{Jbd2Tx{+s, ps, vs}, t}:
      Jbd2Log.plan.go(t, rv, Jbd2Log.keep(ps, s, rv, acc))

# pass 3: the journalled blocks to replay, in log order, with their
# transactions: every one the revoke table does not revoke
def Jbd2Log.plan(+txs: List<&2, Jbd2Tx>) -> List<&2, Jbd2Do>:
  Jbd2Log.plan.go(txs, Jbd2Log.table(txs), Nil{})

# all three passes, from transaction s on
def Jbd2Log.recover(+s: Nat, +rs: List<&2, Jbd2Rec>) -> List<&2, Jbd2Do>:
  Jbd2Log.plan(Jbd2Log.scan(s, rs))

# Specifications (for the laws)

def Jbd2Log.member(xs: List<&2, Nat>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(Nat.is_eq(x, b), Jbd2Log.member(t, b))

# whether some transaction of txs from s on revokes block b
def Jbd2Log.revoked_in(txs: List<&2, Jbd2Tx>, +b: Nat, +s: Nat) -> Bool:
  match txs:
    case Nil{}:
      False{}
    case Con{Jbd2Tx{q, ps, vs}, t}:
      Bool.or(Bool.and(Nat.is_le(s, q), Jbd2Log.member(vs, b)), Jbd2Log.revoked_in(t, b, s))

# whether no replayed block is one txs revokes for its transaction
def Jbd2Log.none_revoked(+txs: List<&2, Jbd2Tx>, ds: List<&2, Jbd2Do>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{Jbd2Do{s, p}, t}:
      Bool.and(Bool.not(Jbd2Log.revoked_in(txs, Jbd2Put.block(p), s)), Jbd2Log.none_revoked(txs, t))

# whether rs holds no commit record
def Jbd2Log.no_commit(rs: List<&2, Jbd2Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{Jbd2RCommit{q}, t}:
      False{}
    case Con{r, t}:
      Jbd2Log.no_commit(t)

# the blocks of ps, as transaction s replays them, but those rv revokes
def Jbd2Log.unrevoked.pick(hit: Bool, d: Jbd2Do, rest: List<&2, Jbd2Do>) -> List<&2, Jbd2Do>:
  match hit:
    case True{}:
      rest
    case False{}:
      Con{d, rest}

def Jbd2Log.unrevoked(+s: Nat, +rv: List<&2, Nat>, ps: List<&2, Jbd2Put>) -> List<&2, Jbd2Do>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      Jbd2Log.unrevoked.pick(Jbd2Log.member(rv, Jbd2Put.block(p)), Jbd2Do{s, p}, Jbd2Log.unrevoked(s, rv, t))
