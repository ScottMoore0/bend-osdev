# The size measurement (measure.sh runs it): every block of an image file
# read through a FileDev, one at a time (IODev.fold_blocks), into a byte
# sum and a hash (h = 31 h + byte, mod 2^32), or, with "count", only
# counted, so the time is the reads'. Arguments: the image, the block size,
# and "sum" or "count".
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../iodev.bend as V
import ../filedev.bend as F

type MeasureSum is Data:
  MeasureSum{blocks: U32, bytes: U32, sum: U32, hash: U32}

def sum.go(xs: List<&2, U32>, +s: U32, +h: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (s, h)
    case Con{+x, t}:
      sum.go(t, U32.add(s, x), U32.add(U32.mul(h, 31), x))

def sum.fin(+n: U32, +len: U32, r: U32 & U32) -> MeasureSum:
  (s, h) = r
  MeasureSum{U32.add(n, 1), len, s, h}

def sum_step(acc: MeasureSum, blk: B.Octets) -> MeasureSum:
  match acc:
    case MeasureSum{n, len, s, h}:
      +xs = B.Octets.to_list(blk)
      sum.fin(n, U32.add(len, U32.from_nat(B.len.fast(xs))), sum.go(xs, s, h))

def count_step(acc: MeasureSum, blk: B.Octets) -> MeasureSum:
  match acc:
    case MeasureSum{n, len, s, h}:
      MeasureSum{U32.add(n, 1), U32.add(len, U32.from_nat(B.Octets.len(blk))), s, h}

def show(r: Result<&2, &2, D.DevError, MeasureSum>) -> String:
  match r:
    case Done{MeasureSum{n, len, s, h}}:
      "blocks " ++ U32.show(n) ++ " bytes " ++ U32.show(len) ++ " sum " ++ U32.show(s) ++ " hash " ++ U32.show(h)
    case Fail{e}:
      "read failed"

def fin(r: F.FileDev & Result<&2, &2, D.DevError, MeasureSum>) -> IO(Unit):
  (d, x) = r
  do IO<Unit>:
    IO.print(show(x))
    F.FileDev.close(d)

def fold(count: Bool, d: F.FileDev, +n: Nat) -> IO(F.FileDev & Result<&2, &2, D.DevError, MeasureSum>):
  match count:
    case True{}:
      V.IODev.fold_blocks(~MeasureSum, ~F.FileDev, ~F.FileDev.read_block, ~count_step, n, d, 0n, MeasureSum{0, 0, 0, 0})
    case False{}:
      V.IODev.fold_blocks(~MeasureSum, ~F.FileDev, ~F.FileDev.read_block, ~sum_step, n, d, 0n, MeasureSum{0, 0, 0, 0})

def counted(+count: Bool, r: F.FileDev & Nat) -> IO(Unit):
  (d, n) = r
  IO.bind(F.FileDev & Result<&2, &2, D.DevError, MeasureSum>, Unit, fold(count, d, n), fin)

def opened(+count: Bool, r: Result<&1, &1, F.FileDevError, F.FileDev>) -> IO(Unit):
  match r:
    case Done{d}:
      IO.bind(F.FileDev & Nat, Unit, F.FileDev.block_count(d), counted(count))
    case Fail{e}:
      IO.print("open failed")

def nat.go(s: List<&2, Char>, +acc: Nat) -> Nat:
  match s:
    case Nil{}:
      acc
    case Con{c, t}:
      nat.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(Char.to_u32(c), 48))))

def run(args: List<&1, String>) -> IO(Unit):
  match args:
    case Con{prog, Con{path, Con{bs, Con{mode, rest}}}}:
      IO.bind(Result<&1, &1, F.FileDevError, F.FileDev>, Unit, F.FileDev.open(path, nat.go(String.to_list(bs), 0n)), opened(String.eq(mode, "count")))
    case _:
      IO.print("usage: measure <image> <block size> sum|count")

def main() -> IO(Unit):
  IO.bind(List<&1, String>, Unit, IO.args(), run)
