# The differential test over 4 GiB (gen.py --big writes its input): a
# sparse image file of more than 4 GiB opened as a FileRW on
# bend-osdev-fileio's effects, its block count printed, then reads and
# writes through the IO helpers, before, across and past the 4 GiB mark
# and into the final partial block, each answer printed.
#
# The ops file is little-endian u32 words: the path's length and bytes,
# the block size, the count of operations, and the operations (an offset
# is two words, high then low):
#   0 hi lo len            read_bytes
#   1 hi lo len bytes...   write_bytes
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../iodev.bend as V
import ../filedev.bend as F
import ../filerw.bend as R
import ../../fileio/fileio.bend as FIO

def word(xs: List<&2, U32>) -> U32 & List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      (U32.or(a, U32.or(U32.shln(b, 8n), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))), t)
    case _:
      (0, Nil{})

def nat.fin(r: U32 & List<&2, U32>) -> Nat & List<&2, U32>:
  (w, t) = r
  (U32.to_nat(w), t)

def nat(xs: List<&2, U32>) -> Nat & List<&2, U32>:
  nat.fin(word(xs))

def err(e: D.DevError) -> String:
  match e:
    case D.DevOutOfRange{n}:
      "out of range " ++ Nat.show(n)
    case D.DevBadLength{x, g}:
      "bad length " ++ Nat.show(x) ++ " " ++ Nat.show(g)
    case D.DevFailed{c}:
      "failed " ++ U32.show(c)

def say(r: R.FileRW & Result<&2, &2, D.DevError, B.Octets>) -> IO(R.FileRW):
  (d, x) = r
  match x:
    case Done{o}:
      do IO<R.FileRW>:
        IO.print("w ok " ++ B.Octets.hex(o))
        return d
    case Fail{e}:
      do IO<R.FileRW>:
        IO.print("w " ++ err(e))
        return d

def usay(r: R.FileRW & Result<&2, &2, D.DevError, Unit>) -> IO(R.FileRW):
  (d, x) = r
  match x:
    case Done{u}:
      do IO<R.FileRW>:
        IO.print("w ok")
        return d
    case Fail{e}:
      do IO<R.FileRW>:
        IO.print("w " ++ err(e))
        return d

def op.read(d: R.FileRW, +off: Nat, r: Nat & List<&2, U32>, k: R.FileRW -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (len, rest) = r
  do IO<Unit>:
    x : R.FileRW & Result<&2, &2, D.DevError, B.Octets> <- V.IODev.read_bytes(~R.FileRW, ~R.FileRW.block_size, ~R.FileRW.read_block(~FIO.FileIO.read_at), d, off, len)
    d : R.FileRW <- say(x)
    k(d, rest)

def op.write(d: R.FileRW, +off: Nat, r: Nat & List<&2, U32>, k: R.FileRW -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (+len, +rest) = r
  do IO<Unit>:
    x : R.FileRW & Result<&2, &2, D.DevError, Unit> <- V.IODev.write_bytes(~R.FileRW, ~R.FileRW.block_size, ~R.FileRW.read_block(~FIO.FileIO.read_at), ~R.FileRW.write_block(~FIO.FileIO.write_at), d, off, B.Octets.of_list(B.take.fast(len, rest)))
    d : R.FileRW <- usay(x)
    k(d, B.drop(len, rest))

def op.pick(rd: Bool, d: R.FileRW, +off: Nat, r: Nat & List<&2, U32>, k: R.FileRW -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  match rd:
    case True{}:
      op.read(d, off, r, k)
    case False{}:
      op.write(d, off, r, k)

def op.lo(+kind: U32, d: R.FileRW, +hi: Nat, r: Nat & List<&2, U32>, k: R.FileRW -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (lo, rest) = r
  op.pick(U32.is_eq(kind, 0), d, Nat.add(Nat.mul(hi, Nat.add(4294967295n, 1n)), lo), nat(rest), k)

def op.hi(+kind: U32, d: R.FileRW, r: Nat & List<&2, U32>, k: R.FileRW -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (hi, rest) = r
  op.lo(kind, d, hi, nat(rest), k)

def op(d: R.FileRW, r: U32 & List<&2, U32>, k: R.FileRW -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (+kind, rest) = r
  op.hi(kind, d, nat(rest), k)

def ops(n: Nat, d: R.FileRW, xs: List<&2, U32>) -> IO(Unit):
  match n:
    case 0n:
      R.FileRW.close(d)
    case 1n+p:
      op(d, word(xs), d2 => ys => ops(p, d2, ys))

def counted(r: R.FileRW & Nat, n: Nat, xs: List<&2, U32>) -> IO(Unit):
  (d, k) = r
  do IO<Unit>:
    IO.print("w count " ++ Nat.show(k))
    ops(n, d, xs)

def opened(r: Result<&1, &1, F.FileDevError, R.FileRW>, n: Nat, xs: List<&2, U32>) -> IO(Unit):
  match r:
    case Done{d}:
      IO.bind(R.FileRW & Nat, Unit, R.FileRW.block_count(d), c => counted(c, n, xs))
    case Fail{e}:
      IO.print("w open failed")

def head.n(path: String, +bs: Nat, r: Nat & List<&2, U32>) -> IO(Unit):
  (n, xs) = r
  do IO<Unit>:
    o : Result<&1, &1, F.FileDevError, R.FileRW> <- R.FileRW.open(~FIO.FileIO.open_rw, ~FIO.FileIO.size, path, bs)
    opened(o, n, xs)

def head.bs(path: String, r: Nat & List<&2, U32>) -> IO(Unit):
  (bs, xs) = r
  head.n(path, bs, nat(xs))

def head.path(r: Nat & List<&2, U32>) -> IO(Unit):
  (+plen, +ys) = r
  head.bs(B.to_string.fast(B.take.fast(plen, ys)), nat(B.drop(plen, ys)))

def go(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, x) = r
  match x:
    case Done{xs}:
      do IO<Unit>:
        File.close(f)
        head.path(nat(xs))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("cannot read the ops")

def path(args: List<&1, String>) -> String:
  match args:
    case Con{prog, Con{p, rest}}:
      p
    case _:
      "big-ops.bin"

def main() -> IO(Unit):
  do IO<Unit>:
    a : List<&1, String> <- IO.args()
    f : File <- IO.try(File, File.open(path(a), "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 16777216)
    go(r)
