import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./decode.bend as D
import ./encode.bend as C
import ./lzo.bend as L
import ./adler32.bend as A
import ./lzop.bend as P

def show(r: Result<&2, &2, E.LzoError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.LzoError.show(e)
    case Done{o}:
      "done [" ++ B.Octets.to_string(o) ++ "]"

def show_same(r: Result<&2, &2, E.LzoError, B.Octets>, +o: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.LzoError.show(e)
    case Done{+d}:
      "done, " ++ Nat.show(B.Octets.len(d)) ++ " bytes, the input " ++ Bool.show(B.Octets.is_eq(d, o))

# n pseudo-random letters over k (a power of two) of them
def rnd.go(n: Nat, +k: U32, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +t = U32.add(U32.mul(s, 1103515245), 12345)
      rnd.go(p, k, t, Con{U32.add(97, U32.and(U32.shrn(t, 16n), U32.sub(k, 1))), acc})

def rnd(n: Nat, k: U32, seed: U32) -> B.Octets:
  B.Octets.of_list(rnd.go(n, k, seed, Nil{}))

# a stream: n literals (0000 0000 and length bytes), then the instruction
# bytes ins, then the end marker
def run_then(+data: B.Octets, ins: List<&2, U32>) -> B.Octets:
  B.Octets.concat([B.Octets.of_list(Con{0, C.ext.bytes(Nat.sub(B.Octets.len(data), 18n))}), data, B.Octets.of_list(ins), C.lzo1x_end()])

# the stream for data followed by a copy of its first 3 bytes
def copies3(+data: B.Octets, ins: List<&2, U32>) -> String:
  show_same(D.lzo1x_decompress(run_then(data, ins), 100000n), B.Octets.append(data, B.Octets.take(3n, data)))

def every_sum() -> P.LzopWriteOptions:
  P.LzopWriteOptions{65536, True{}, True{}, True{}, True{}, True{}, 1, 5, B.Octets.of_string("big.txt"), 33188, 0, C.LzoCompressOptions.default()}

def main() -> IO(Unit):
  +big = rnd(71680n, 8, 11)
  +zbig = C.lzo1x_compress(big)
  do IO<Unit>:
    IO.print(B.Octets.hex(C.lzo1x_literals(B.Octets.of_string("hello"))))
    IO.print(show(D.lzo1x_decompress(B.Octets.of_list([20, 97, 98, 99, 168, 0, 17, 0, 0]), 100n)))
    IO.print(show(D.lzo1x_decompress(B.Octets.of_list([21, 97, 98, 99, 100, 40, 14, 0, 120, 121, 17, 0, 0]), 100n)))
    IO.print(show(D.lzo1x_decompress(B.Octets.of_list([18, 97, 40, 4, 0, 17, 0, 0]), 100n)))
    IO.print("M1 after many literals, distance 2052: " ++ copies3(rnd(2052n, 16, 1), [12, 0]))
    IO.print("M4 with H = 0, distance 16385: " ++ copies3(rnd(16385n, 16, 2), [17, 4, 0]))
    IO.print("M4 with H = 1, distance 32769: " ++ copies3(rnd(32769n, 16, 3), [25, 4, 0]))
    IO.print("M4 with H = 1, distance 49151: " ++ copies3(rnd(49151n, 16, 4), [25, 252, 255]))
    IO.print("70 KB compressed to " ++ Nat.show(B.Octets.len(zbig)) ++ " bytes")
    IO.print("70 KB back: " ++ show_same(D.lzo1x_decompress(zbig, 71680n), big))
    IO.print("70 KB, one byte short: " ++ show_same(D.lzo1x_decompress(zbig, 71679n), big))
    IO.print("70 KB in three pieces: " ++ show_same(D.reader_decompress(71680n, [B.Octets.take(1000n, zbig), B.Octets.slice(1000n, 20000n, zbig), B.Octets.drop(21000n, zbig)]), big))
    IO.print("64 KB of zeros compressed to " ++ Nat.show(B.Octets.len(C.lzo1x_compress(B.Octets.zeros(65536n)))) ++ " bytes")
    IO.print("lzop, defaults: " ++ show_same(P.lzop_decompress(P.LzopOptions.default(), P.lzop_compress(P.LzopWriteOptions.default(), big)), big))
    IO.print("lzop, 64 KB blocks, every checksum: " ++ show_same(P.lzop_decompress(P.LzopOptions.default(), P.lzop_compress(every_sum(), big)), big))
    IO.print("Adler-32 of Wikipedia: " ++ U32.show(A.adler32(B.Octets.of_string("Wikipedia"))))

#|0268656c6c6f110000
#|done [abcabcabc]
#|done [abcdabcdabcdabxy]
#|fail BadDistance
#|M1 after many literals, distance 2052: done, 2055 bytes, the input True
#|M4 with H = 0, distance 16385: done, 16388 bytes, the input True
#|M4 with H = 1, distance 32769: done, 32772 bytes, the input True
#|M4 with H = 1, distance 49151: done, 49154 bytes, the input True
#|70 KB compressed to 50557 bytes
#|70 KB back: done, 71680 bytes, the input True
#|70 KB, one byte short: fail OutputTooLarge
#|70 KB in three pieces: done, 71680 bytes, the input True
#|64 KB of zeros compressed to 265 bytes
#|lzop, defaults: done, 71680 bytes, the input True
#|lzop, 64 KB blocks, every checksum: done, 71680 bytes, the input True
#|Adler-32 of Wikipedia: 300286872
