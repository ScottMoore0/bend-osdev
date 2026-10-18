# The in-place write measurement (measure.sh runs it): every block of an
# image file rewritten in place through a FileRW on bend-osdev-fileio's
# effects, one at a time, block n filled with the byte n mod 256; measure.sh
# then checks the file with Python. Arguments: the image, the block size.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../filedev.bend as F
import ../filerw.bend as R
import ../../fileio/fileio.bend as FIO

def fill.go(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      fill.go(p, b, Con{b, acc})

def fill(+bs: Nat, +n: Nat) -> B.Octets:
  B.Octets.of_list(fill.go(bs, U32.and(255, U32.from_nat(n)), Nil{}))

def wrote(r: R.FileRW & Result<&2, &2, D.DevError, Unit>, k: R.FileRW -> IO(Unit)) -> IO(Unit):
  (d, x) = r
  match x:
    case Done{u}:
      k(d)
    case Fail{e}:
      do IO<Unit>:
        IO.print("write failed")
        R.FileRW.close(d)

def go(count: Nat, +bs: Nat, d: R.FileRW, +n: Nat) -> IO(Unit):
  match count:
    case 0n:
      do IO<Unit>:
        IO.print("blocks " ++ Nat.show(n))
        R.FileRW.close(d)
    case 1n+p:
      IO.bind(R.FileRW & Result<&2, &2, D.DevError, Unit>, Unit, R.FileRW.write_block(~FIO.FileIO.write_at, d, n, fill(bs, n)), r => wrote(r, d2 => go(p, bs, d2, Nat.add(n, 1n))))

def counted(+bs: Nat, r: R.FileRW & Nat) -> IO(Unit):
  (d, c) = r
  go(c, bs, d, 0n)

def opened(+bs: Nat, r: Result<&1, &1, F.FileDevError, R.FileRW>) -> IO(Unit):
  match r:
    case Done{d}:
      IO.bind(R.FileRW & Nat, Unit, R.FileRW.block_count(d), counted(bs))
    case Fail{e}:
      IO.print("open failed")

def nat.go(s: List<&2, Char>, +acc: Nat) -> Nat:
  match s:
    case Nil{}:
      acc
    case Con{c, t}:
      nat.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(Char.to_u32(c), 48))))

def run.bs(path: String, +bs: Nat) -> IO(Unit):
  IO.bind(Result<&1, &1, F.FileDevError, R.FileRW>, Unit, R.FileRW.open(~FIO.FileIO.open_rw, ~FIO.FileIO.size, path, bs), opened(bs))

def run(args: List<&1, String>) -> IO(Unit):
  match args:
    case Con{prog, Con{path, Con{bs, rest}}}:
      run.bs(path, nat.go(String.to_list(bs), 0n))
    case _:
      IO.print("usage: measure_rw <image> <block size>")

def main() -> IO(Unit):
  IO.bind(List<&1, String>, Unit, IO.args(), run)
