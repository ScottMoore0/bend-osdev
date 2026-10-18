# A runnable check of every effect, on files in /tmp: open read-write
# (without truncating, and creating only when asked), positioned writes and
# reads (before and past 4 GiB, in a sparse file), the size, sync, a handle
# shared with Base's File defs, and the failures. The files are emptied
# again at the end.
import Base
import ../word64/word64.bend as W
import ./off.bend as O
import ./fileio.bend as F

def path() -> String:
  "/tmp/bend-osdev-fileio-check.bin"

def made() -> String:
  "/tmp/bend-osdev-fileio-check-made.bin"

# 2^32 + k
def past4g(k: U32) -> W.W64:
  W.W64.from_parts(1, k)

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
        IO.print("ok " ++ hexs(xs))
        return f
    case Fail{e}:
      do IO<File>:
        IO.print(err(e))
        return f

def usay(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (f, x) = r
  match x:
    case Done{u}:
      do IO<File>:
        IO.print("ok")
        return f
    case Fail{e}:
      do IO<File>:
        IO.print(err(e))
        return f

def ssay(r: File & Result<&1, &1, U32 & String, W.W64>) -> IO(File):
  (f, x) = r
  match x:
    case Done{n}:
      do IO<File>:
        IO.print("size " ++ W.W64.show(n))
        return f
    case Fail{e}:
      do IO<File>:
        IO.print(err(e))
        return f

def bsay(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(File):
  lsay(r)

def fresh(p: String, xs: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(p, "w"))
    w : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, xs)
    f : File <- usay(w)
    File.close(f)

def checks(f: File) -> IO(Unit):
  do IO<Unit>:
    s : File & Result<&1, &1, U32 & String, W.W64> <- F.FileIO.size(f)
    f : File <- ssay(s)
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.from_u32(2), [88, 89, 90])
    f : File <- usay(w)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, W.W64.zero(), 20)
    f : File <- lsay(r)
    s : File & Result<&1, &1, U32 & String, W.W64> <- F.FileIO.size(f)
    f : File <- ssay(s)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4)
    f : File <- bsay(r)
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, past4g(5), [104, 105])
    f : File <- usay(w)
    s : File & Result<&1, &1, U32 & String, W.W64> <- F.FileIO.size(f)
    f : File <- ssay(s)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, past4g(3), 10)
    f : File <- lsay(r)
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.from_u32(4294967294), [1, 2, 3, 4])
    f : File <- usay(w)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, W.W64.from_u32(4294967293), 6)
    f : File <- lsay(r)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, past4g(100), 4)
    f : File <- lsay(r)
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.zero(), [1, 256])
    f : File <- usay(w)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, W.W64.zero(), 2)
    f : File <- lsay(r)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, W.W64.max(), 2)
    f : File <- lsay(r)
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.max(), [])
    f : File <- usay(w)
    y : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.sync(f)
    f : File <- usay(y)
    File.close(f)

def opened(r: Result<&1, &1, U32 & String, File>, k: File -> IO(Unit)) -> IO(Unit):
  match r:
    case Done{f}:
      k(f)
    case Fail{e}:
      IO.print("open " ++ err(e))

def made_checks(f: File) -> IO(Unit):
  do IO<Unit>:
    s : File & Result<&1, &1, U32 & String, W.W64> <- F.FileIO.size(f)
    f : File <- ssay(s)
    w : File & Result<&1, &1, U32 & String, Unit> <- F.FileIO.write_at(f, W.W64.from_u32(3), [7])
    f : File <- usay(w)
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- F.FileIO.read_at(f, W.W64.zero(), 9)
    f : File <- lsay(r)
    File.close(f)

def pair(p: U32 & U32) -> String:
  (h, l) = p
  U32.show(h) ++ " " ++ U32.show(l)

def halves(v: W.W64) -> String:
  pair(O.FileIO.off.halves(v))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(halves(past4g(7)) ++ " " ++ W.W64.show(O.FileIO.off.join((1, 7))) ++ " " ++ Bool.show(O.FileIO.off.fits32(past4g(7))))
    fresh(path(), [97, 98, 99, 100, 101, 102, 103, 104, 105, 106])
    a : Result<&1, &1, U32 & String, File> <- F.FileIO.open_rw(path())
    opened(a, checks)
    b : Result<&1, &1, U32 & String, File> <- F.FileIO.open_rw("/nonexistent/bend-osdev-fileio.bin")
    opened(b, checks)
    fresh(made(), [9, 9])
    c : Result<&1, &1, U32 & String, File> <- F.FileIO.open(made(), True{})
    opened(c, made_checks)
    d : Result<&1, &1, U32 & String, File> <- F.FileIO.open(made(), False{})
    opened(d, made_checks)
    fresh(path(), [])

#|1 7 4294967303 False
#|ok
#|size 10
#|ok
#|ok 616258595a666768696a
#|size 10
#|ok 61625859
#|ok
#|size 4294967303
#|ok 00006869
#|ok
#|ok 000102030400
#|ok 
#|failed 22
#|ok 6162
#|failed 22
#|ok
#|ok
#|open failed 2
#|ok
#|size 2
#|ok
#|ok 09090007
#|size 4
#|ok
#|ok 09090007
#|ok
