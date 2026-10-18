# The differential test's runner (see gen.py): reads cases.bin, a run of
# records (an action byte, a 4-byte big-endian argument, a 4-byte big-endian
# length, the bytes), and prints one line per record:
#   d  decompress the bytes, at most arg bytes      "=HEX" or "!ERROR"
#   p  the same through the reader, in pieces of arg bytes (max 2^30)
#   c  compress_with (arg: the strategy, below)     "=HEX"
#   u  compress_unchecked (arg: the strategy)       "=HEX"
#   l  literals                                     "=HEX"
#   t  tokens (the format's parser)                 the token count, or "!ERROR"
# A strategy argument of 0 is C842NoMatch; otherwise its bytes 1 to 3 are
# the table bits for 8-, 4- and 2-byte phrases.
import Base
import ../../bytes/bytes.bend as B
import ../error.bend as E
import ../format.bend as F
import ../decode.bend as D
import ../match.bend as M
import ../encode.bend as C

def show(r: Result<&2, &2, E.C842Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "!" ++ E.C842Error.show(e)
    case Done{o}:
      "=" ++ B.Octets.hex(o)

def show_toks(r: Result<&2, &2, E.C842Error, List<&2, F.C842Token>>) -> String:
  match r:
    case Fail{e}:
      "!" ++ E.C842Error.show(e)
    case Done{ts}:
      Nat.show(List.length(&2, F.C842Token, ts))

def strategy.pick(none: Bool, +a: U32) -> M.C842Strategy:
  match none:
    case True{}:
      M.C842NoMatch{}
    case False{}:
      M.C842Hash{U32.to_nat(U32.and(U32.shrn(a, 16n), 255)), U32.to_nat(U32.and(U32.shrn(a, 8n), 255)), U32.to_nat(U32.and(a, 255))}

def strategy(+a: U32) -> C.C842CompressOptions:
  C.C842CompressOptions{strategy.pick(U32.is_eq(a, 0), a)}

# the bytes in pieces of k (k at least 1): c bytes left in the current piece
def pieces.go(xs: List<&2, U32>, +k: Nat, c: Nat, cur: List<&2, U32>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      List.reverse(&2, B.Octets, Con{B.Octets.of_list(B.rev(cur)), acc})
    case Con{x, t}:
      match c:
        case 0n:
          pieces.go(t, k, Nat.sub(k, 1n), [x], Con{B.Octets.of_list(B.rev(cur)), acc})
        case 1n+d:
          pieces.go(t, k, d, Con{x, cur}, acc)

def pieces(+k: Nat, o: B.Octets) -> List<&2, B.Octets>:
  pieces.go(B.Octets.to_list(o), k, k, Nil{}, Nil{})

def act.l(hit: Bool, +op: U32, +o: B.Octets) -> String:
  match hit:
    case True{}:
      "=" ++ B.Octets.hex(C.c842.literals(o))
    case False{}:
      show_toks(F.c842.tokens(o))

def act.u(hit: Bool, +op: U32, +a: U32, +o: B.Octets) -> String:
  match hit:
    case True{}:
      "=" ++ B.Octets.hex(C.c842.compress_unchecked(strategy(a), o))
    case False{}:
      act.l(U32.is_eq(op, 108), op, o)

def act.c(hit: Bool, +op: U32, +a: U32, +o: B.Octets) -> String:
  match hit:
    case True{}:
      "=" ++ B.Octets.hex(C.c842.compress_with(strategy(a), o))
    case False{}:
      act.u(U32.is_eq(op, 117), op, a, o)

def act.p(hit: Bool, +op: U32, +a: U32, +o: B.Octets) -> String:
  match hit:
    case True{}:
      show(D.c842.reader_decompress(1073741824n, pieces(U32.to_nat(a), o)))
    case False{}:
      act.c(U32.is_eq(op, 99), op, a, o)

def act.d(hit: Bool, +op: U32, +a: U32, +o: B.Octets) -> String:
  match hit:
    case True{}:
      show(D.c842.decompress(o, U32.to_nat(a)))
    case False{}:
      act.p(U32.is_eq(op, 112), op, a, o)

def act(+op: U32, +a: U32, +o: B.Octets) -> String:
  act.d(U32.is_eq(op, 100), op, a, o)

def be32(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(U32.shln(a, 24n), U32.shln(b, 16n)), U32.or(U32.shln(c, 8n), d))

def run(fuel: Nat, +xs: List<&2, U32>, +k: Nat) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      match xs:
        case Con{op, Con{a0, Con{a1, Con{a2, Con{a3, Con{l0, Con{l1, Con{l2, Con{l3, rest}}}}}}}}}:
          +n = U32.to_nat(be32(l0, l1, l2, l3))
          do IO<Unit>:
            IO.print(Nat.show(k) ++ " " ++ act(op, be32(a0, a1, a2, a3), B.Octets.of_list(B.take.fast(n, rest))))
            run(f, B.drop(n, rest), 1n+k)
        case _:
          IO.pure(Unit, Unit{})

def got(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, r) = fr
  match r:
    case Fail{e}:
      IO.print("cases.bin unreadable")
    case Done{+xs}:
      run(B.len.fast(xs), xs, 0n)

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("cases.bin", "r"))
    fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4000000000)
    got(fr)
