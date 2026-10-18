# The journalled-writes test's program: reads the cases jgen.py wrote (a
# text file named on the command line, one directive a line, its first
# word a letter) and runs each through jdriver.bend's Ext4JCase.run when
# its E line is read. Built once, run once.
#
#   C NAME                          a case
#   F PATH BS COUNT                 its image file; Z N N ... lines list its
#                                   non-zero blocks
#   M MODE CRASH TIME               j (data=journal) or o (data=ordered);
#                                   1: crash the last transaction; the time
#   T                               a new transaction
#   c PATH MODE | m PATH MODE | s PATH TARGET | l TARGET PATH | u PATH |
#   r PATH | n FROM TO | w PATH OFF LEN SEED | a PATH LEN SEED |
#   t PATH SIZE                     its operations (paths in hex)
#   E                               the end of the case: run it
import Base
import ../../bytes/bytes.bend as B
import ../../ext2/ops.bend as XP
import ../jtx.bend as JT
import ./jdriver.bend as R

# Lines and words

def Ext4JMain.flush(cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      Con{List.reverse(&2, U32, Con{h, t}), acc}

def Ext4JMain.is_sep(xs: List<&2, U32>, +sep: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      U32.is_eq(x, sep)

def Ext4JMain.split.go(xs: List<&2, U32>, hit: Bool, +sep: U32, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs hit:
    case Nil{} _:
      List.reverse(&2, List<&2, U32>, Ext4JMain.flush(cur, acc))
    case Con{x, +t} True{}:
      Ext4JMain.split.go(t, Ext4JMain.is_sep(t, sep), sep, Nil{}, Ext4JMain.flush(cur, acc))
    case Con{x, +t} False{}:
      Ext4JMain.split.go(t, Ext4JMain.is_sep(t, sep), sep, Con{x, cur}, acc)

# the pieces of xs between the separators (empty ones dropped)
def Ext4JMain.split(+xs: List<&2, U32>, +sep: U32) -> List<&2, List<&2, U32>>:
  Ext4JMain.split.go(xs, Ext4JMain.is_sep(xs, sep), sep, Nil{}, Nil{})

def Ext4JMain.nat.go(xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Ext4JMain.nat.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(x, 48))))

def Ext4JMain.nat(xs: List<&2, U32>) -> Nat:
  Ext4JMain.nat.go(xs, 0n)

def Ext4JMain.u32(xs: List<&2, U32>) -> U32:
  U32.from_nat(Ext4JMain.nat(xs))

def Ext4JMain.hexval.pick(digit: Bool, +c: U32) -> U32:
  match digit:
    case True{}:
      U32.sub(c, 48)
    case False{}:
      U32.sub(c, 87)

def Ext4JMain.hexval(+c: U32) -> U32:
  Ext4JMain.hexval.pick(U32.is_lt(c, 58), c)

def Ext4JMain.unhex(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Ext4JMain.unhex(t, Con{U32.or(U32.shln(Ext4JMain.hexval(a), 4n), Ext4JMain.hexval(b)), acc})
    case _:
      List.reverse(&2, U32, acc)

def Ext4JMain.hex(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(Ext4JMain.unhex(xs, Nil{}))

def Ext4JMain.first(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

# n pseudo-random bytes from seed s (a linear congruential generator, as
# jgen.py computes them)
def Ext4JMain.bytes.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      Ext4JMain.bytes.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def Ext4JMain.bytes(n: Nat, s: U32) -> B.Octets:
  B.Octets.of_list(Ext4JMain.bytes.go(n, s, Nil{}))

# What a line says

type Ext4JLine is Data:
  Ext4JLCase{name: String}
  Ext4JLFile{path: String, bs: Nat, count: Nat}
  Ext4JLNz{blocks: List<&2, Nat>}
  Ext4JLMode{mode: JT.Jbd2Mode, crash: Bool, time: U32}
  Ext4JLTx{}
  Ext4JLOp{op: XP.Ext2Op}
  Ext4JLEnd{}
  Ext4JLBad{}

def Ext4JMain.nats(ws: List<&2, List<&2, U32>>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{w, t}:
      Ext4JMain.nats(t, Con{Ext4JMain.nat(w), acc})

def Ext4JMain.op4(k: U32, a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>, d: List<&2, U32>) -> Ext4JLine:
  match k:
    case 119:
      Ext4JLOp{XP.Ext2OpWrite{Ext4JMain.hex(a), Ext4JMain.nat(b), Ext4JMain.bytes(Ext4JMain.nat(c), Ext4JMain.u32(d))}}
    case _:
      Ext4JLBad{}

def Ext4JMain.mode(m: U32, c: U32, +t: U32) -> Ext4JLine:
  match m:
    case 111:
      Ext4JLMode{JT.Jbd2DataOrdered{}, U32.is_eq(c, 49), t}
    case _:
      Ext4JLMode{JT.Jbd2DataJournal{}, U32.is_eq(c, 49), t}


def Ext4JMain.op3(k: U32, a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> Ext4JLine:
  match k:
    case 97:
      Ext4JLOp{XP.Ext2OpAppend{Ext4JMain.hex(a), Ext4JMain.bytes(Ext4JMain.nat(b), Ext4JMain.u32(c))}}
    case 77:
      Ext4JMain.mode(Ext4JMain.first(a), Ext4JMain.first(b), Ext4JMain.u32(c))
    case _:
      Ext4JLBad{}

def Ext4JMain.op2(k: U32, a: List<&2, U32>, b: List<&2, U32>) -> Ext4JLine:
  match k:
    case 99:
      Ext4JLOp{XP.Ext2OpCreate{Ext4JMain.hex(a), Ext4JMain.u32(b)}}
    case 109:
      Ext4JLOp{XP.Ext2OpMkdir{Ext4JMain.hex(a), Ext4JMain.u32(b)}}
    case 115:
      Ext4JLOp{XP.Ext2OpSymlink{Ext4JMain.hex(a), Ext4JMain.hex(b)}}
    case 108:
      Ext4JLOp{XP.Ext2OpLink{Ext4JMain.hex(a), Ext4JMain.hex(b)}}
    case 110:
      Ext4JLOp{XP.Ext2OpRename{Ext4JMain.hex(a), Ext4JMain.hex(b)}}
    case 116:
      Ext4JLOp{XP.Ext2OpTruncate{Ext4JMain.hex(a), Ext4JMain.nat(b)}}
    case _:
      Ext4JLBad{}

def Ext4JMain.op1(k: U32, a: List<&2, U32>) -> Ext4JLine:
  match k:
    case 117:
      Ext4JLOp{XP.Ext2OpUnlink{Ext4JMain.hex(a)}}
    case 114:
      Ext4JLOp{XP.Ext2OpRmdir{Ext4JMain.hex(a)}}
    case _:
      Ext4JLBad{}

def Ext4JMain.file(ws: List<&2, List<&2, U32>>) -> Ext4JLine:
  match ws:
    case Con{p, Con{bs, Con{c, t}}}:
      Ext4JLFile{B.to_string(p), Ext4JMain.nat(bs), Ext4JMain.nat(c)}
    case _:
      Ext4JLBad{}

def Ext4JMain.line.key(+k: U32, args: List<&2, List<&2, U32>>) -> Ext4JLine:
  match k:
    case 67:
      Ext4JLCase{B.to_string(List.concat(&2, U32, args))}
    case 70:
      Ext4JMain.file(args)
    case 90:
      Ext4JLNz{Ext4JMain.nats(args, Nil{})}
    case 84:
      Ext4JLTx{}
    case 69:
      Ext4JLEnd{}
    case _:
      match args:
        case Con{a, Con{b, Con{c, Con{d, t}}}}:
          Ext4JMain.op4(k, a, b, c, d)
        case Con{a, Con{b, Con{c, Nil{}}}}:
          Ext4JMain.op3(k, a, b, c)
        case Con{a, Con{b, Nil{}}}:
          Ext4JMain.op2(k, a, b)
        case Con{a, Nil{}}:
          Ext4JMain.op1(k, a)
        case _:
          Ext4JLBad{}

def Ext4JMain.line(ws: List<&2, List<&2, U32>>) -> Ext4JLine:
  match ws:
    case Nil{}:
      Ext4JLBad{}
    case Con{key, args}:
      Ext4JMain.line.key(Ext4JMain.first(key), args)

# Building a case from its lines (transactions and their operations kept
# last first until the case ends)

type Ext4JBuild is Data:
  Ext4JBuild{name: String, path: String, bs: Nat, count: Nat, nz: List<&2, Nat>, mode: JT.Jbd2Mode, crash: Bool, time: U32, txs: List<&2, List<&2, XP.Ext2Op>>}

def Ext4JMain.empty() -> Ext4JBuild:
  Ext4JBuild{"", "", 1024n, 0n, Nil{}, JT.Jbd2DataJournal{}, False{}, 0, Nil{}}

def Ext4JMain.push(op: XP.Ext2Op, txs: List<&2, List<&2, XP.Ext2Op>>) -> List<&2, List<&2, XP.Ext2Op>>:
  match txs:
    case Nil{}:
      [[op]]
    case Con{h, t}:
      Con{Con{op, h}, t}

def Ext4JMain.rev_all(txs: List<&2, List<&2, XP.Ext2Op>>, acc: List<&2, List<&2, XP.Ext2Op>>) -> List<&2, List<&2, XP.Ext2Op>>:
  match txs:
    case Nil{}:
      acc
    case Con{h, t}:
      Ext4JMain.rev_all(t, Con{List.reverse(&2, XP.Ext2Op, h), acc})

type Ext4JAct is Data:
  Ext4JGo{b: Ext4JBuild}
  Ext4JRun{c: R.Ext4JCase, b: Ext4JBuild}

def Ext4JMain.act(l: Ext4JLine, b: Ext4JBuild) -> Ext4JAct:
  match l b:
    case Ext4JLCase{n} _:
      Ext4JGo{Ext4JBuild{n, "", 1024n, 0n, Nil{}, JT.Jbd2DataJournal{}, False{}, 0, Nil{}}}
    case Ext4JLFile{p, bs, c} Ext4JBuild{n, x, y, z, nz, m, cr, t, txs}:
      Ext4JGo{Ext4JBuild{n, p, bs, c, nz, m, cr, t, txs}}
    case Ext4JLNz{ks} Ext4JBuild{n, p, bs, c, nz, m, cr, t, txs}:
      Ext4JGo{Ext4JBuild{n, p, bs, c, List.reverse.go(&2, Nat, ks, nz), m, cr, t, txs}}
    case Ext4JLMode{m2, cr2, t2} Ext4JBuild{n, p, bs, c, nz, m, cr, t, txs}:
      Ext4JGo{Ext4JBuild{n, p, bs, c, nz, m2, cr2, t2, txs}}
    case Ext4JLTx{} Ext4JBuild{n, p, bs, c, nz, m, cr, t, txs}:
      Ext4JGo{Ext4JBuild{n, p, bs, c, nz, m, cr, t, Con{Nil{}, txs}}}
    case Ext4JLOp{op} Ext4JBuild{n, p, bs, c, nz, m, cr, t, txs}:
      Ext4JGo{Ext4JBuild{n, p, bs, c, nz, m, cr, t, Ext4JMain.push(op, txs)}}
    case Ext4JLEnd{} Ext4JBuild{n, p, bs, c, nz, m, cr, t, txs}:
      Ext4JRun{R.Ext4JCase{n, p, bs, c, List.reverse(&2, Nat, nz), m, cr, t, Ext4JMain.rev_all(txs, Nil{})}, Ext4JMain.empty()}
    case Ext4JLBad{} _:
      Ext4JGo{b}

def Ext4JMain.go(ls: List<&2, List<&2, U32>>, a: Ext4JAct) -> IO(Unit):
  match ls a:
    case Nil{} Ext4JRun{c, b}:
      R.Ext4JCase.run(c)
    case Nil{} Ext4JGo{b}:
      IO.pure(Unit, Unit{})
    case Con{l, t} Ext4JRun{c, b}:
      do IO<Unit>:
        R.Ext4JCase.run(c)
        Ext4JMain.go(t, Ext4JMain.act(Ext4JMain.line(Ext4JMain.split(l, 32)), b))
    case Con{l, t} Ext4JGo{b}:
      Ext4JMain.go(t, Ext4JMain.act(Ext4JMain.line(Ext4JMain.split(l, 32)), b))

def Ext4JMain.size(p: File & Result<&1, &1, U32 & String, U32>) -> IO(File & U32):
  (f, r) = p
  IO.pure(File & U32, (f, Result.default(&1, &1, U32 & String, U32, r, 0)))

def Ext4JMain.close(q: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (f, r) = q
  do IO<List<&2, U32>>:
    File.close(f)
    return Result.default(&1, &1, U32 & String, List<&2, U32>, r, Nil{})

def Ext4JMain.read(p: File & U32) -> IO(List<&2, U32>):
  (f, n) = p
  do IO<List<&2, U32>>:
    q : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
    Ext4JMain.close(q)

def Ext4JMain.path(args: List<String>) -> String:
  match args:
    case Con{prog, Con{p, t}}:
      p
    case _:
      "jcases.txt"

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    f : File <- IO.try(File, File.open(Ext4JMain.path(args), "r"))
    sz : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    fz : File & U32 <- Ext4JMain.size(sz)
    xs : List<&2, U32> <- Ext4JMain.read(fz)
    Ext4JMain.go(Ext4JMain.split(xs, 10), Ext4JGo{Ext4JMain.empty()})
