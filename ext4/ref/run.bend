# The ref test's program: reads a query file (gen.py writes it), one image
# after another, and prints driver.bend's answers. Built once and run on
# every query file, so the test needs one native build.
#
# The file is whitespace-separated tokens: for each image
#   image NAME PATH BS COUNT VERIFY N B1 .. BN      (the non-zero blocks)
# then its queries, each a word and its fields (byte strings in hex)
#   lookup P | list P | read P | xattrs P | xattr P NAME
#   hash V S0 S1 S2 S3 NAME
#   recover VERIFY SKIP N B1 .. BN                  (blocks to show)
#   commit R RV1 .. RVR W (BLOCK SEED MAGIC)*W N B1 .. BN
#   build INO GEN PARENT PAD N (INO FT NAME)*N
# and then
#   run
import Base
import ../../bytes/bytes.bend as B
import ../../ext2/dir.bend as DR
import ./driver.bend as R

# Tokens

def Ext4Tok.flush(cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      Con{List.reverse(&2, U32, Con{h, t}), acc}

def Ext4Tok.cut(ws: Bool, +c: U32, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, U32> & List<&2, List<&2, U32>>:
  match ws:
    case True{}:
      (Nil{}, Ext4Tok.flush(cur, acc))
    case False{}:
      (Con{c, cur}, acc)

def Ext4Tok.split(xs: List<&2, U32>, st: List<&2, U32> & List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      (cur, acc) = st
      List.reverse(&2, List<&2, U32>, Ext4Tok.flush(cur, acc))
    case Con{+c, t}:
      (cur, acc) = st
      Ext4Tok.split(t, Ext4Tok.cut(U32.is_le(c, 32), c, cur, acc))

def Ext4Tok.nat(t: List<&2, U32>, acc: Nat) -> Nat:
  match t:
    case Nil{}:
      acc
    case Con{c, r}:
      Ext4Tok.nat(r, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))))

def Ext4Tok.hexd.pick(lower: Bool, +c: U32) -> U32:
  match lower:
    case True{}:
      U32.sub(c, 87)
    case False{}:
      U32.sub(c, 48)

def Ext4Tok.hexd(+c: U32) -> U32:
  Ext4Tok.hexd.pick(U32.is_le(97, c), c)

def Ext4Tok.hex(t: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Con{a, Con{b, r}}:
      Ext4Tok.hex(r, Con{U32.or(U32.shln(Ext4Tok.hexd(a), 4n), Ext4Tok.hexd(b)), acc})
    case _:
      List.reverse(&2, U32, acc)

def Ext4Tok.octets(t: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(Ext4Tok.hex(t, Nil{}))

def Ext4Tok.is(t: List<&2, U32>, s: String) -> Bool:
  B.list_eq(t, B.of_string(s))

def Ext4Tok.str.go(t: List<&2, U32>) -> String:
  match t:
    case Nil{}:
      ""
    case Con{c, r}:
      SCon{Chr{c}, Ext4Tok.str.go(r)}

# Reading fields: each reader answers its value and the tokens after it

def Ext4Tok.head(ts: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h

def Ext4Tok.tail(ts: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def Ext4Tok.n(+ts: List<&2, List<&2, U32>>) -> Nat:
  Ext4Tok.nat(Ext4Tok.head(ts), 0n)

def Ext4Tok.u(+ts: List<&2, List<&2, U32>>) -> U32:
  U32.from_nat(Ext4Tok.n(ts))

def Ext4Tok.b(+ts: List<&2, List<&2, U32>>) -> Bool:
  Ext4Tok.is(Ext4Tok.head(ts), "1")

def Ext4Tok.o(+ts: List<&2, List<&2, U32>>) -> B.Octets:
  Ext4Tok.octets(Ext4Tok.head(ts))

# n numbers
def Ext4Tok.nats(n: Nat, +ts: List<&2, List<&2, U32>>, acc: List<&2, Nat>) -> List<&2, Nat> & List<&2, List<&2, U32>>:
  match n:
    case 0n:
      (List.reverse(&2, Nat, acc), ts)
    case 1n+p:
      Ext4Tok.nats(p, Ext4Tok.tail(ts), Con{Ext4Tok.n(ts), acc})

def Ext4Tok.writes(n: Nat, +ts: List<&2, List<&2, U32>>, acc: List<&2, R.Ext4QW>) -> List<&2, R.Ext4QW> & List<&2, List<&2, U32>>:
  match n:
    case 0n:
      (List.reverse(&2, R.Ext4QW, acc), ts)
    case 1n+p:
      +t1 = Ext4Tok.tail(ts)
      +t2 = Ext4Tok.tail(t1)
      Ext4Tok.writes(p, Ext4Tok.tail(t2), Con{R.Ext4QW{Ext4Tok.n(ts), Ext4Tok.u(t1), Ext4Tok.b(t2)}, acc})

def Ext4Tok.ents(n: Nat, +ts: List<&2, List<&2, U32>>, acc: List<&2, DR.Ext2Dirent>) -> List<&2, DR.Ext2Dirent> & List<&2, List<&2, U32>>:
  match n:
    case 0n:
      (List.reverse(&2, DR.Ext2Dirent, acc), ts)
    case 1n+p:
      +t1 = Ext4Tok.tail(ts)
      +t2 = Ext4Tok.tail(t1)
      Ext4Tok.ents(p, Ext4Tok.tail(t2), Con{DR.Ext2Dirent{Ext4Tok.u(ts), 0, 0, Ext4Tok.u(t1), Ext4Tok.o(t2)}, acc})

# Queries

type Ext4Parsed is Data:
  Ext4Parsed{q: Maybe<&2, R.Ext4Q>, rest: List<&2, List<&2, U32>>}

def Ext4Tok.recover(+v: Bool, +k: Bool, r: List<&2, Nat> & List<&2, List<&2, U32>>) -> Ext4Parsed:
  (ns, rest) = r
  Ext4Parsed{Some{R.Ext4QRecover{v, k, ns}}, rest}

def Ext4Tok.commit.show(+rv: List<&2, Nat>, +ws: List<&2, R.Ext4QW>, r: List<&2, Nat> & List<&2, List<&2, U32>>) -> Ext4Parsed:
  (ns, rest) = r
  Ext4Parsed{Some{R.Ext4QCommit{rv, ws, ns}}, rest}

def Ext4Tok.commit.ws(+rv: List<&2, Nat>, r: List<&2, R.Ext4QW> & List<&2, List<&2, U32>>) -> Ext4Parsed:
  (ws, +rest) = r
  Ext4Tok.commit.show(rv, ws, Ext4Tok.nats(Ext4Tok.n(rest), Ext4Tok.tail(rest), Nil{}))

def Ext4Tok.commit(r: List<&2, Nat> & List<&2, List<&2, U32>>) -> Ext4Parsed:
  (rv, +rest) = r
  Ext4Tok.commit.ws(rv, Ext4Tok.writes(Ext4Tok.n(rest), Ext4Tok.tail(rest), Nil{}))

def Ext4Tok.build(+ino: U32, +gen: U32, +parent: U32, +pad: Nat, r: List<&2, DR.Ext2Dirent> & List<&2, List<&2, U32>>) -> Ext4Parsed:
  (es, rest) = r
  Ext4Parsed{Some{R.Ext4QBuild{ino, gen, parent, pad, es}}, rest}

def Ext4Tok.query.pick(lookup: Bool, list: Bool, read: Bool, xattrs: Bool, xattr: Bool, hash: Bool, recover: Bool, commit: Bool, build: Bool, +ts: List<&2, List<&2, U32>>, +t1: List<&2, List<&2, U32>>, +t2: List<&2, List<&2, U32>>, +t3: List<&2, List<&2, U32>>, +t4: List<&2, List<&2, U32>>, +t5: List<&2, List<&2, U32>>, +t6: List<&2, List<&2, U32>>) -> Ext4Parsed:
  match lookup list read xattrs xattr hash recover commit build:
    case True{} _ _ _ _ _ _ _ _:
      Ext4Parsed{Some{R.Ext4QLookup{Ext4Tok.o(ts)}}, t1}
    case False{} True{} _ _ _ _ _ _ _:
      Ext4Parsed{Some{R.Ext4QList{Ext4Tok.o(ts)}}, t1}
    case False{} False{} True{} _ _ _ _ _ _:
      Ext4Parsed{Some{R.Ext4QRead{Ext4Tok.o(ts)}}, t1}
    case False{} False{} False{} True{} _ _ _ _ _:
      Ext4Parsed{Some{R.Ext4QXattrs{Ext4Tok.o(ts)}}, t1}
    case False{} False{} False{} False{} True{} _ _ _ _:
      Ext4Parsed{Some{R.Ext4QXattr{Ext4Tok.o(ts), Ext4Tok.o(t1)}}, t2}
    case False{} False{} False{} False{} False{} True{} _ _ _:
      Ext4Parsed{Some{R.Ext4QHash{Ext4Tok.u(ts), [Ext4Tok.u(t1), Ext4Tok.u(t2), Ext4Tok.u(t3), Ext4Tok.u(t4)], Ext4Tok.o(t5)}}, t6}
    case False{} False{} False{} False{} False{} False{} True{} _ _:
      Ext4Tok.recover(Ext4Tok.b(ts), Ext4Tok.b(t1), Ext4Tok.nats(Ext4Tok.n(t2), t3, Nil{}))
    case False{} False{} False{} False{} False{} False{} False{} True{} _:
      Ext4Tok.commit(Ext4Tok.nats(Ext4Tok.n(ts), t1, Nil{}))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Ext4Tok.build(Ext4Tok.u(ts), Ext4Tok.u(t1), Ext4Tok.u(t2), Ext4Tok.n(t3), Ext4Tok.ents(Ext4Tok.n(t4), t5, Nil{}))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      Ext4Parsed{None{}, ts}

def Ext4Tok.query(+w: List<&2, U32>, +ts: List<&2, List<&2, U32>>) -> Ext4Parsed:
  +t1 = Ext4Tok.tail(ts)
  +t2 = Ext4Tok.tail(t1)
  +t3 = Ext4Tok.tail(t2)
  +t4 = Ext4Tok.tail(t3)
  +t5 = Ext4Tok.tail(t4)
  +t6 = Ext4Tok.tail(t5)
  Ext4Tok.query.pick(Ext4Tok.is(w, "lookup"), Ext4Tok.is(w, "list"), Ext4Tok.is(w, "read"), Ext4Tok.is(w, "xattrs"), Ext4Tok.is(w, "xattr"), Ext4Tok.is(w, "hash"), Ext4Tok.is(w, "recover"), Ext4Tok.is(w, "commit"), Ext4Tok.is(w, "build"), ts, t1, t2, t3, t4, t5, t6)

# the queries up to "run"
type Ext4QState is Data:
  Ext4QState{done: Bool, ts: List<&2, List<&2, U32>>, acc: List<&2, R.Ext4Q>}

def Ext4Tok.next(p: Ext4Parsed, acc: List<&2, R.Ext4Q>) -> Ext4QState:
  match p:
    case Ext4Parsed{Some{q}, rest}:
      Ext4QState{False{}, rest, Con{q, acc}}
    case Ext4Parsed{None{}, rest}:
      Ext4QState{True{}, rest, acc}

def Ext4Tok.step(run: Bool, +ts: List<&2, List<&2, U32>>, acc: List<&2, R.Ext4Q>) -> Ext4QState:
  match run:
    case True{}:
      Ext4QState{True{}, Ext4Tok.tail(ts), acc}
    case False{}:
      Ext4Tok.next(Ext4Tok.query(Ext4Tok.head(ts), Ext4Tok.tail(ts)), acc)

def Ext4Tok.queries(fuel: Nat, st: Ext4QState) -> List<&2, R.Ext4Q> & List<&2, List<&2, U32>>:
  match fuel st:
    case 0n Ext4QState{d, ts, acc}:
      (List.reverse(&2, R.Ext4Q, acc), ts)
    case _ Ext4QState{True{}, ts, acc}:
      (List.reverse(&2, R.Ext4Q, acc), ts)
    case 1n+f Ext4QState{False{}, +ts, acc}:
      Ext4Tok.queries(f, Ext4Tok.step(Ext4Tok.is(Ext4Tok.head(ts), "run"), ts, acc))

# Images

def Ext4Run.image.fin(+name: String, +path: String, +bs: Nat, +count: Nat, +v: Bool, nz: List<&2, Nat>, r: List<&2, R.Ext4Q> & List<&2, List<&2, U32>>) -> R.Ext4ImgCase & List<&2, List<&2, U32>>:
  (qs, rest) = r
  (R.Ext4ImgCase{name, path, bs, count, nz, v, qs}, rest)

def Ext4Run.image(+name: String, +path: String, +bs: Nat, +count: Nat, +v: Bool, r: List<&2, Nat> & List<&2, List<&2, U32>>, +fuel: Nat) -> R.Ext4ImgCase & List<&2, List<&2, U32>>:
  (nz, +rest) = r
  Ext4Run.image.fin(name, path, bs, count, v, nz, Ext4Tok.queries(fuel, Ext4QState{False{}, rest, Nil{}}))

def Ext4Run.parse(+ts: List<&2, List<&2, U32>>, +fuel: Nat) -> R.Ext4ImgCase & List<&2, List<&2, U32>>:
  +t1 = Ext4Tok.tail(ts)
  +t2 = Ext4Tok.tail(t1)
  +t3 = Ext4Tok.tail(t2)
  +t4 = Ext4Tok.tail(t3)
  +t5 = Ext4Tok.tail(t4)
  Ext4Run.image(Ext4Tok.str.go(Ext4Tok.head(ts)), Ext4Tok.str.go(Ext4Tok.head(t1)), Ext4Tok.n(t2), Ext4Tok.n(t3), Ext4Tok.b(t4), Ext4Tok.nats(Ext4Tok.n(t5), Ext4Tok.tail(t5), Nil{}), fuel)

def Ext4Run.is_nil(ts: List<&2, List<&2, U32>>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# each image in turn: r is the next image's case and the tokens after it
# (more: whether there is one)
def Ext4Run.go(fuel: Nat, more: Bool, r: R.Ext4ImgCase & List<&2, List<&2, U32>>) -> IO(Unit):
  match fuel more:
    case 0n _:
      IO.pure(Unit, Unit{})
    case _ False{}:
      IO.pure(Unit, Unit{})
    case 1n+f True{}:
      (c, +rest) = r
      +t = Ext4Tok.tail(rest)
      do IO<Unit>:
        R.Ext4ImgCase.run(c)
        Ext4Run.go(f, Bool.not(Ext4Run.is_nil(rest)), Ext4Run.parse(t, Nat.add(List.length(&2, List<&2, U32>, t), 1n)))

def Ext4Run.file.read(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, res) = r
  match res:
    case Done{xs}:
      +ts = Ext4Tok.split(xs, (Nil{}, Nil{}))
      do IO<Unit>:
        File.close(f)
        Ext4Run.go(Nat.add(List.length(&2, List<&2, U32>, ts), 1n), Bool.not(Ext4Run.is_nil(ts)), Ext4Run.parse(Ext4Tok.tail(ts), Nat.add(List.length(&2, List<&2, U32>, ts), 1n)))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("cannot read the query file")

def Ext4Run.file.sized(r: File & Result<&1, &1, U32 & String, U32>) -> IO(Unit):
  (f, res) = r
  match res:
    case Done{n}:
      do IO<Unit>:
        q : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        Ext4Run.file.read(q)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("cannot size the query file")

def Ext4Run.file(m: Maybe<&1, String>) -> IO(Unit):
  match m:
    case None{}:
      IO.print("usage: run QUERYFILE")
    case Some{path}:
      do IO<Unit>:
        f : File <- IO.try(File, File.open(path, "r"))
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Ext4Run.file.sized(r)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Ext4Run.file(List.get(&1, String, args, 1n))
