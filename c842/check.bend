import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./format.bend as F
import ./decode.bend as D
import ./match.bend as M
import ./encode.bend as C
import ./c842.bend as L

def show(r: Result<&2, &2, E.C842Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.C842Error.show(e)
    case Done{o}:
      "done [" ++ B.Octets.to_string(o) ++ "]"

def show_same(r: Result<&2, &2, E.C842Error, B.Octets>, +o: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.C842Error.show(e)
    case Done{+d}:
      "done, " ++ Nat.show(B.Octets.len(d)) ++ " bytes, the input " ++ Bool.show(B.Octets.is_eq(d, o))

def show_toks(r: Result<&2, &2, E.C842Error, List<&2, F.C842Token>>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.C842Error.show(e)
    case Done{ts}:
      Nat.show(List.length(&2, F.C842Token, ts)) ++ " tokens"

# n pseudo-random bytes, each one of k (a power of two) values from 97 on
def rnd.go(n: Nat, +k: U32, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +t = U32.add(U32.mul(s, 1103515245), 12345)
      rnd.go(p, k, t, Con{U32.add(97, U32.and(U32.shrn(t, 16n), U32.sub(k, 1))), acc})

def rnd(n: Nat, k: U32, seed: U32) -> B.Octets:
  B.Octets.of_list(rnd.go(n, k, seed, Nil{}))

# words from a short list, as text
def words.at(ws: List<&2, String>, n: Nat) -> String:
  match ws:
    case Nil{}:
      ""
    case Con{w, t}:
      match n:
        case 0n:
          w
        case 1n+p:
          words.at(t, p)

def words.pick.at(+i: U32) -> String:
  words.at(["the ", "842 ", "phrase ", "chunk ", "zero ", "index ", "ring ", "fifo "], U32.to_nat(i))

def words.pick(+i: U32) -> String:
  words.pick.at(U32.and(i, 7))

def text.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +t = U32.add(U32.mul(s, 1103515245), 12345)
      text.go(p, t, B.rev_onto(B.of_string(words.pick(U32.shrn(t, 16n))), acc))

# n words of text
def text(n: Nat) -> B.Octets:
  B.Octets.of_list(B.rev(text.go(n, 5, Nil{})))

def main() -> IO(Unit):
  +txt = text(12000n)
  +ztxt = L.compress(txt)
  +big = rnd(65536n, 64, 7)
  +zbig = L.compress(big)
  +nomatch : C.C842CompressOptions = C.C842CompressOptions{M.C842NoMatch{}}
  do IO<Unit>:
    IO.print("literals of hello: " ++ B.Octets.hex(C.c842.literals(B.Octets.of_string("hello"))))
    IO.print("1 KB of zeros: " ++ B.Octets.hex(L.compress(B.Octets.zeros(1024n))))
    IO.print("the paper's Z8, RPT(63): " ++ show_same(L.decompress(B.Octets.of_list([230, 254, 240, 0, 0, 0, 0, 0])), B.Octets.zeros(512n)))
    IO.print("text, " ++ Nat.show(B.Octets.len(txt)) ++ " bytes, compressed to " ++ Nat.show(B.Octets.len(ztxt)))
    IO.print("text back: " ++ show_same(L.decompress(ztxt), txt))
    IO.print("text, no matching: " ++ Nat.show(B.Octets.len(L.compress_with(nomatch, txt))))
    IO.print("text, 4-bit tables: " ++ Nat.show(B.Octets.len(L.compress_with(C.C842CompressOptions{M.C842Hash{4n, 4n, 4n}}, txt))))
    IO.print("text, one byte short: " ++ show_same(D.c842.decompress(ztxt, Nat.sub(B.Octets.len(txt), 1n)), txt))
    IO.print("text in three pieces: " ++ show_same(D.c842.reader_decompress(1073741824n, [B.Octets.take(100n, ztxt), B.Octets.slice(100n, 1000n, ztxt), B.Octets.drop(1100n, ztxt)]), txt))
    IO.print("text as tokens: " ++ show_toks(F.c842.tokens(ztxt)))
    IO.print("64 KB, 64 letters, compressed to " ++ Nat.show(B.Octets.len(zbig)) ++ " (the worst case " ++ Nat.show(F.c842.worst_bytes(65536n)) ++ ")")
    IO.print("64 KB back: " ++ show_same(L.decompress(zbig), big))
    IO.print("literal stream of 1000 bytes: " ++ Nat.show(B.Octets.len(C.c842.literals(rnd(1000n, 256, 3)))) ++ " bytes, the worst case " ++ Nat.show(F.c842.worst_bytes(1000n)))
    IO.print("a bad CRC: " ++ show(L.decompress(B.Octets.of_list([0, 8, 16, 24, 32, 40, 48, 56, 71, 159, 66, 205, 160, 64, 0, 0]))))

#|literals of hello: ed68656c6c6ff50ef10af00000000000
#|1 KB of zeros: e6ffdfde00000000
#|the paper's Z8, RPT(63): done, 512 bytes, the input True
#|text, 62783 bytes, compressed to 19616
#|text back: done, 62783 bytes, the input True
#|text, no matching: 67672
#|text, 4-bit tables: 49224
#|text, one byte short: fail OutputTooLarge
#|text in three pieces: done, 62783 bytes, the input True
#|text as tokens: 7849 tokens
#|64 KB, 64 letters, compressed to 69288 (the worst case 70664)
#|64 KB back: done, 65536 bytes, the input True
#|literal stream of 1000 bytes: 1088 bytes, the worst case 1088
#|a bad CRC: fail BadCrc
