# The differential test's runner (gen.py writes its input): for each file
# named in the ops file, FileIO.open (creating it if the case says so),
# then every operation through the effects, each answer printed.
#
# The ops file is little-endian u32 words: a count of files, then for each
# the path's length and bytes, the create flag, the count of operations,
# and the operations (an offset is two words, high then low):
#   0 hi lo max          FileIO.read_at
#   1 hi lo len bytes... FileIO.write_at
#   2                    FileIO.size
#   3                    FileIO.sync
import Base
import ../../word64/word64.bend as W
import ../fileio.bend as F

# Parsing

def word(xs: List<&2, U32>) -> U32 & List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      (U32.or(a, U32.or(U32.shln(b, 8n), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))), t)
    case _:
      (0, Nil{})

def rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev(t, Con{h, acc})

# the first n elements (reversed onto acc) and the rest
def split(n: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n xs:
    case 0n _:
      (rev(acc, Nil{}), xs)
    case 1n+p Nil{}:
      (rev(acc, Nil{}), Nil{})
    case 1n+p Con{h, t}:
      split(p, t, Con{h, acc})

def chars(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Chr{h}, chars(t)}

# Showing results

def hexd.pick(lt: Bool, d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def hexd(+d: U32) -> Char:
  hexd.pick(U32.is_lt(d, 10), d)

def hexs(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{+h, t}:
      SCon{hexd(U32.shrn(h, 4n)), SCon{hexd(U32.and(15, h)), hexs(t)}}

def err(e: U32 & String) -> String:
  (c, m) = e
  "failed " ++ U32.show(c)

def lsay(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(File):
  (f, x) = r
  match x:
    case Done{xs}:
      do IO<File>:
        IO.print("r ok " ++ hexs(xs))
        return f
    case Fail{e}:
      do IO<File>:
        IO.print("r " ++ err(e))
        return f

def usay(tag: String, r: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (f, x) = r
  match x:
    case Done{u}:
      do IO<File>:
        IO.print(tag ++ " ok")
        return f
    case Fail{e}:
      do IO<File>:
        IO.print(tag ++ " " ++ err(e))
        return f

def ssay(r: File & Result<&1, &1, U32 & String, W.W64>) -> IO(File):
  (f, x) = r
  match x:
    case Done{n}:
      do IO<File>:
        IO.print("s " ++ W.W64.show(n))
        return f
    case Fail{e}:
      do IO<File>:
        IO.print("s " ++ err(e))
        return f

# The operations

def op.read(f: File, +hi: U32, +lo: U32, r: U32 & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (max, rest) = r
  do IO<Unit>:
    x : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, W.W64.from_parts(hi, lo), max)
    f : File <- lsay(x)
    k(f, rest)

def op.write.go(f: File, +hi: U32, +lo: U32, p: List<&2, U32> & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (data, rest) = p
  do IO<Unit>:
    x : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.from_parts(hi, lo), data)
    f : File <- usay("w", x)
    k(f, rest)

def op.write(f: File, +hi: U32, +lo: U32, r: U32 & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (n, rest) = r
  op.write.go(f, hi, lo, split(U32.to_nat(n), rest, Nil{}), k)

def op.at.pick(rd: Bool, f: File, +hi: U32, +lo: U32, r: U32 & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  match rd:
    case True{}:
      op.read(f, hi, lo, r, k)
    case False{}:
      op.write(f, hi, lo, r, k)

def op.at.lo(+kind: U32, f: File, +hi: U32, r: U32 & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (lo, rest) = r
  op.at.pick(U32.is_eq(kind, 0), f, hi, lo, word(rest), k)

def op.at(+kind: U32, f: File, r: U32 & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (hi, rest) = r
  op.at.lo(kind, f, hi, word(rest), k)

def op.size(f: File, rest: List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  do IO<Unit>:
    x : File & Result<&1, &1, U32 & String, W.W64> <- F.FileIO.size(f)
    f : File <- ssay(x)
    k(f, rest)

def op.sync(f: File, rest: List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  do IO<Unit>:
    x : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.sync(f)
    f : File <- usay("y", x)
    k(f, rest)

def op.pick(at: Bool, sz: Bool, +kind: U32, f: File, rest: List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  match at sz:
    case True{} _:
      op.at(kind, f, word(rest), k)
    case False{} True{}:
      op.size(f, rest, k)
    case False{} False{}:
      op.sync(f, rest, k)

def op(f: File, r: U32 & List<&2, U32>, k: File -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (+kind, rest) = r
  op.pick(U32.is_lt(kind, 2), U32.is_eq(kind, 2), kind, f, rest, k)

# the operations, then the rest of the ops file to k
def ops(n: Nat, f: File, xs: List<&2, U32>, k: List<&2, U32> -> IO(Unit)) -> IO(Unit):
  match n:
    case 0n:
      do IO<Unit>:
        File.close(f)
        k(xs)
    case 1n+p:
      op(f, word(xs), f2 => ys => ops(p, f2, ys, k))

def section.opened(r: Result<&1, &1, U32 & String, File>, n: Nat, xs: List<&2, U32>, k: List<&2, U32> -> IO(Unit)) -> IO(Unit):
  match r:
    case Done{f}:
      do IO<Unit>:
        IO.print("open ok")
        ops(n, f, xs, k)
    case Fail{e}:
      do IO<Unit>:
        IO.print("open " ++ err(e))
        k(xs)

def section.n(path: String, +create: U32, r: U32 & List<&2, U32>, k: List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (n, xs) = r
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- F.FileIO.open(path, U32.is_eq(create, 1))
    section.opened(o, U32.to_nat(n), xs, k)

def section.create(path: String, r: U32 & List<&2, U32>, k: List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (create, xs) = r
  section.n(path, create, word(xs), k)

def section.path(p: List<&2, U32> & List<&2, U32>, k: List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (name, xs) = p
  +path = chars(name)
  do IO<Unit>:
    IO.print("file " ++ path)
    section.create(path, word(xs), k)

def section.len(r: U32 & List<&2, U32>, k: List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (n, xs) = r
  section.path(split(U32.to_nat(n), xs, Nil{}), k)

def sections(n: Nat, xs: List<&2, U32>) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      section.len(word(xs), ys => sections(p, ys))

def go.run(r: U32 & List<&2, U32>) -> IO(Unit):
  (n, ys) = r
  sections(U32.to_nat(n), ys)

def go(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, x) = r
  match x:
    case Done{xs}:
      do IO<Unit>:
        File.close(f)
        go.run(word(xs))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("cannot read the ops")

def path(args: List<&1, String>) -> String:
  match args:
    case Con{prog, Con{p, rest}}:
      p
    case _:
      "ops.bin"

def main() -> IO(Unit):
  do IO<Unit>:
    a : List<&1, String> <- IO.args()
    f : File <- IO.try(File, File.open(path(a), "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 16777216)
    go(r)
