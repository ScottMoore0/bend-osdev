# The differential test's runner (see gen.py). Its arguments come in
# threes: an action, an input file and a name.
#   d FILE NAME   decode FILE; print "NAME LEN CRC32" (CRC-32 of the output,
#                 zlib's, from the crc package) or "NAME error KIND"
#   cN FILE NAME  compress FILE at level N into NAME.bz2; print "NAME written"
#   sN FILE NAME  the same through the streaming writer, fed in three pieces
import Base
import ../../bytes/bytes.bend as B
import ../../crc/crc.bend as CR
import ../error.bend as E
import ../stream.bend as S
import ../compress.bend as Z

def report(+name: String, r: Result<&2, &2, E.Bzip2Error, B.Octets>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(name ++ " error " ++ E.Bzip2Error.show(e))
    case Done{+o}:
      IO.print(name ++ " " ++ Nat.show(B.Octets.len(o)) ++ " " ++ U32.show(CR.crc32(o)))

def level(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{v}:
      v
    case None{}:
      9

# the action's level: the digit after its letter
def act.level(a: String) -> U32:
  match a:
    case SCon{c, t}:
      level(U32.read(t))
    case SNil{}:
      9

def act.kind(a: String) -> U32:
  match a:
    case SCon{c, t}:
      match c:
        case Chr{v}:
          v
    case SNil{}:
      0

def streamed(+lv: U32, +o: B.Octets) -> B.Octets:
  +n = B.Octets.len(o)
  +a = Nat.div(n, 3n)
  +w0 = Z.Bzip2Writer.start(Z.Bzip2CompressOptions{lv, 17})
  +r1 = Z.Bzip2Writer.feed(w0, B.Octets.take(a, o))
  +r2 = Z.Bzip2Writer.feed(Z.wr.written.writer(r1), B.Octets.slice(a, a, o))
  +r3 = Z.Bzip2Writer.feed(Z.wr.written.writer(r2), B.Octets.drop(Nat.add(a, a), o))
  B.Octets.concat([Z.wr.written.bytes(r1), Z.wr.written.bytes(r2), Z.wr.written.bytes(r3), Z.Bzip2Writer.finish(Z.wr.written.writer(r3))])

def save(+name: String, o: B.Octets) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(name ++ ".bz2", "w"))
    fr : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, B.Octets.to_list(o))
    IO.print(name ++ " written")

def act.pick(dec: Bool, str: Bool, +lv: U32, +name: String, xs: List<&2, U32>) -> IO(Unit):
  match dec:
    case True{}:
      report(name, S.stream_decode(S.Bzip2Options{4000000000, True{}}, B.Octets.of_list(xs)))
    case False{}:
      match str:
        case True{}:
          save(name, streamed(lv, B.Octets.of_list(xs)))
        case False{}:
          save(name, Z.compress_with(Z.Bzip2CompressOptions{lv, 17}, B.Octets.of_list(xs)))

def act.on(+k: U32, +lv: U32, +name: String, xs: List<&2, U32>) -> IO(Unit):
  act.pick(U32.is_eq(k, 100), U32.is_eq(k, 115), lv, name, xs)

def act.read(r: Result<&1, &1, U32 & String, List<&2, U32>>, +k: U32, +lv: U32, +name: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(name ++ " unreadable")
    case Done{xs}:
      act.on(k, lv, name, xs)

def act.got(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>, +k: U32, +lv: U32, +name: String) -> IO(Unit):
  (f, r) = fr
  act.read(r, k, lv, name)

def act(+a: String, file: String, +name: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(file, "r"))
    fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4000000000)
    act.got(fr, act.kind(a), act.level(a), name)

def run(args: List<&1, String>) -> IO(Unit):
  match args:
    case Con{a, Con{file, Con{name, rest}}}:
      do IO<Unit>:
        act(a, file, name)
        run(rest)
    case _:
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args
    run(List.tail(&1, String, args))
