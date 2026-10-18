import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as Bi
import ./fse.bend as F
import ./huffman.bend as H
import ./xxh64.bend as X
import ./frame.bend as Fr
import ./zstd.bend as Z
import ./compress.bend as C

def show(r: Result<&2, &2, E.ZstdError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.ZstdError.show(e)
    case Done{o}:
      B.Octets.to_string(o)

def size(r: Result<&2, &2, E.ZstdError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.ZstdError.show(e)
    case Done{+o}:
      Nat.show(B.Octets.len(o)) ++ " bytes, xxh64 " ++ W.W64.show_hex(X.ZstdXxh64.hash(W.W64.zero(), o))

def bits(bs: List<&2, Bool>, acc: String) -> String:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      match b:
        case True{}:
          bits(t, acc ++ "1")
        case False{}:
          bits(t, acc ++ "0")

def mbits(m: Maybe<&2, List<&2, Bool>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{b}:
      bits(b, "")

def syms(m: Maybe<&2, F.ZstdFseSyms>) -> String:
  match m:
    case None{}:
      "none"
    case Some{F.ZstdFseSyms{xs, rest}}:
      List.show(~&2, ~Nat, ~Nat.show, xs)

def blk.pick(letter: Bool, +c: U32) -> U32:
  match letter:
    case True{}:
      c
    case False{}:
      32

# n bytes of text-like data (8 letters, spaces), repeating every 7 blocks of 4 KB
def blk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      +r = U32.and(U32.shrn(s2, 16n), 255)
      blk.go(p, s2, Con{blk.pick(U32.is_lt(r, 220), U32.add(97, U32.and(r, 7))), acc})

def gen.go(k: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      gen.go(p, U32.add(i, 1), B.rev_onto(blk.go(4096n, U32.mod(i, 7), Nil{}), acc))

# a stream fed in pieces: the output taken after each
def stream(pieces: List<&2, B.Octets>, t: Z.ZstdPiece, acc: String) -> String:
  match pieces:
    case Nil{}:
      match t:
        case Z.ZstdPiece{d, out}:
          acc ++ "[" ++ B.Octets.to_string(out) ++ "] end: <" ++ show(Z.Zstd.finish(d)) ++ ">"
    case Con{p, rest}:
      match t:
        case Z.ZstdPiece{d, out}:
          stream(rest, Z.Zstd.take(Z.Zstd.feed(d, p)), acc ++ "[" ++ B.Octets.to_string(out) ++ "]")

def frame_abc() -> B.Octets:
  B.Octets.of_list([40, 181, 47, 253, 32, 3, 25, 0, 0, 97, 98, 99])

def main() -> IO(Unit):
  +big = B.Octets.of_list(gen.go(25n, 0, Nil{}))
  +packed = C.compress(big)
  do IO<Unit>:
    IO.print(show(Z.decompress(frame_abc())))
    IO.print(show(Z.decompress(B.Octets.of_list([40, 181, 47, 253, 32, 20, 101, 0, 0, 48, 98, 101, 110, 100, 45, 33, 1, 0, 144, 139, 22]))))
    IO.print(show(Z.decompress(B.Octets.of_list([1, 2, 3, 4, 5]))))
    IO.print(show(Z.decompress_with(Z.ZstdOptions{Fr.ZstdLimit{2}, True{}, B.Octets.empty(), 134217728}, frame_abc())))
    IO.print(show(Z.decompress_with(Z.ZstdOptions{Fr.ZstdLimit{100}, True{}, B.Octets.of_string("0123456789abcdef"), 134217728}, B.Octets.of_list([40, 181, 47, 253, 32, 8, 53, 0, 0, 0, 1, 0, 67, 76, 32]))))
    IO.print(stream([B.Octets.of_list([40, 181, 47, 253, 32, 3]), B.Octets.of_list([25, 0, 0, 97]), B.Octets.of_list([98, 99, 40, 181, 47, 253, 32, 2, 17, 0, 0, 100, 101])], Z.ZstdPiece{Z.Zstd.start(Z.ZstdOptions.default()), B.Octets.empty()}, ""))
    IO.print(B.Octets.hex(C.compress(B.Octets.of_string("hello hello hello hello"))))
    IO.print(show(Z.decompress(C.compress(B.Octets.of_string("hello hello hello hello")))))
    IO.print(mbits(F.ZstdFse.encode(F.ZstdFse.table_ll(), [0n, 1n, 2n, 3n, 35n])))
    IO.print(syms(F.ZstdFse.decode(F.ZstdFse.table_ll(), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}], 5n)))
    IO.print(mbits(H.ZstdHuf.encode(H.ZstdHuf.of_all_weights([4n, 3n, 2n, 0n, 1n, 1n], 4n), [0n, 1n, 2n, 4n, 5n, 0n])))
    IO.print(W.W64.show_hex(X.ZstdXxh64.hash(W.W64.zero(), B.Octets.of_string("abc"))))
    IO.print("input " ++ Nat.show(B.Octets.len(big)) ++ " bytes, frame " ++ Nat.show(B.Octets.len(packed)) ++ " bytes")
    IO.print(size(Z.decompress(packed)))
    IO.print(size(Done{big}))

#|abc
#|bend-bend-bend-bend!
#|error BadMagic
#|error OutputTooLarge
#|01234567
#|[][][a][bcde] end: <>
#|28b52ffd24176500003068656c6c6f200100994b11175eae0d
#|hello hello hello hello
#|0000000010011010111011100
#|[0, 1, 2, 3, 35]
#|101001000000011
#|44bc2cf5ad770999
#|input 102400 bytes, frame 22951 bytes
#|102400 bytes, xxh64 acd95a751cc9e930
#|102400 bytes, xxh64 acd95a751cc9e930
