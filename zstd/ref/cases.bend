import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../error.bend as E
import ../xxh64.bend as X
import ../frame.bend as F
import ../zstd.bend as Z
import ../compress.bend as C

# The differential test's runner: it reads the cases gen.py writes (a file
# named on the command line: cases.bin, the decoding cases, or ccases.bin,
# the compression cases).
# Each record: a kind byte (0: decode; 1: compress), then
#   decode: a limit flag byte (1: limited), the limit (4 bytes), a verify
#   byte, the dictionary (a 4-byte length, the bytes), the frame (the same);
#   compress: the block size (4 bytes), a checksum byte, a matcher byte,
#   the content (a 4-byte length, the bytes).
# For each record it prints the answer: the content's length and XXH64, or
# the failure (decoding); the frame in hex, and whether the check kept it
# (compressing).

def show(r: Result<&2, &2, E.ZstdError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "ERR " ++ E.ZstdError.show(e)
    case Done{+o}:
      Nat.show(B.Octets.len(o)) ++ " " ++ W.W64.show_hex(X.ZstdXxh64.hash(W.W64.zero(), o))

def cshow(+c: B.Octets, +u: B.Octets) -> String:
  B.Octets.hex(c) ++ " " ++ Bool.show(B.Octets.is_eq(c, u))

def nat(xs: List<&2, U32>, i: Nat) -> Nat:
  U32.to_nat(B.byte(Maybe.default(&2, U32, B.at(xs, i), 0)))

def le32(+xs: List<&2, U32>) -> Nat:
  Nat.add(Nat.add(nat(xs, 0n), Nat.mul(nat(xs, 1n), 256n)), Nat.add(Nat.mul(nat(xs, 2n), 65536n), Nat.mul(nat(xs, 3n), 16777216n)))

def flag(+xs: List<&2, U32>) -> Bool:
  Nat.is_eq(nat(xs, 0n), 1n)

# a field of n bytes, and the bytes after it
type Cut is Data:
  Cut{head: List<&2, U32>, rest: List<&2, U32>}

def cut(+n: Nat, +xs: List<&2, U32>) -> Cut:
  Cut{B.take.fast(n, xs), B.drop(n, xs)}

def Cut.head(c: Cut) -> List<&2, U32>:
  match c:
    case Cut{head, rest}:
      head

def Cut.rest(c: Cut) -> List<&2, U32>:
  match c:
    case Cut{head, rest}:
      rest

# a length-prefixed byte string
def blob(+xs: List<&2, U32>) -> Cut:
  cut(le32(xs), B.drop(4n, xs))

def limit(+on: Bool, +v: Nat) -> F.ZstdLimit:
  match on:
    case True{}:
      F.ZstdLimit{U32.from_nat(v)}
    case False{}:
      F.ZstdNoLimit{}

# the answer to one record, and the records after it
type Ans is Data:
  Ans{line: String, rest: List<&2, U32>}

def decode(+xs: List<&2, U32>) -> Ans:
  +lim = limit(flag(xs), le32(B.drop(1n, xs)))
  +verify = flag(B.drop(5n, xs))
  +d = blob(B.drop(6n, xs))
  +f = blob(Cut.rest(d))
  Ans{show(Z.decompress_with(Z.ZstdOptions{lim, verify, B.Octets.of_list(Cut.head(d)), 134217728}, B.Octets.of_list(Cut.head(f)))), Cut.rest(f)}

def compress(+xs: List<&2, U32>) -> Ans:
  +o = {C.ZstdCompressOptions{U32.from_nat(le32(xs)), flag(B.drop(4n, xs)), flag(B.drop(5n, xs))} : C.ZstdCompressOptions}
  +c = blob(B.drop(6n, xs))
  +data = B.Octets.of_list(Cut.head(c))
  Ans{cshow(C.compress_with(o, data), C.compress_unchecked(o, data)), Cut.rest(c)}

def record.pick(dec: Bool, +xs: List<&2, U32>) -> Ans:
  match dec:
    case True{}:
      decode(xs)
    case False{}:
      compress(xs)

def record(+xs: List<&2, U32>) -> Maybe<&2, Ans>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{record.pick(Nat.is_eq(U32.to_nat(B.byte(h)), 0n), t)}

def run(fuel: Nat, +k: Nat, m: Maybe<&2, Ans>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      match m:
        case None{}:
          IO.pure(Unit, Unit{})
        case Some{Ans{line, rest}}:
          do IO<Unit>:
            IO.print(Nat.show(k) ++ " " ++ line)
            run(f, 1n+k, record(rest))

def go(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, x) = r
  match x:
    case Done{+xs}:
      do IO<Unit>:
        File.close(f)
        run(B.len.fast(xs), 0n, record(xs))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        IO.print("cannot read the cases")

# the file named on the command line (default: cases.bin)
def path(args: List<&1, String>) -> String:
  match args:
    case Con{prog, Con{p, rest}}:
      p
    case _:
      "cases.bin"

def main() -> IO(Unit):
  do IO<Unit>:
    a : List<&1, String> <- IO.args()
    f : File <- IO.try(File, File.open(path(a), "r"))
    r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1073741824)
    go(r)
