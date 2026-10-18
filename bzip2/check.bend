import Base
import ../bytes/bytes.bend as B
import ./list.bend as L
import ./error.bend as E
import ./rle.bend as R
import ./mtf.bend as M
import ./bwt.bend as W
import ./stream.bend as S
import ./compress.bend as C
import ./bzip2.bend as Z

def show(r: Result<&2, &2, E.Bzip2Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      "error " ++ E.Bzip2Error.show(e)

# length and CRC of a long output
def sum(r: Result<&2, &2, E.Bzip2Error, B.Octets>) -> String:
  match r:
    case Done{+o}:
      Nat.show(B.Octets.len(o)) ++ " " ++ U32.show(S.bzip2_crc(o))
    case Fail{e}:
      "error " ++ E.Bzip2Error.show(e)

def bwt.sh(b: W.Bzip2Bwt) -> String:
  match b:
    case W.Bzip2Bwt{l, p}:
      B.Octets.to_string(l) ++ " " ++ U32.show(p)

def bwt.undo(b: W.Bzip2Bwt) -> String:
  match b:
    case W.Bzip2Bwt{l, +p}:
      show(W.bwt_inverse(l, p))

# bz2.compress(b"a"), and copies of it changed: byte 13 (the CRC), byte 14
# (the randomised bit), byte 4 (the block magic), byte 3 (the level), cut
def a_bz2() -> List<&2, U32>:
  [66, 90, 104, 57, 49, 65, 89, 38, 83, 89, 25, 147, 155, 107, 0, 0, 0, 1, 0, 32, 0, 32, 0, 33, 24, 70, 130, 238, 72, 167, 10, 18, 3, 50, 115, 109, 96]

def set.at(xs: List<&2, U32>, n: Nat, +v: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match n:
        case 0n:
          Con{v, t}
        case 1n+p:
          Con{h, set.at(t, p, v)}

def a_with(+n: Nat, +v: U32) -> B.Octets:
  B.Octets.of_list(set.at(a_bz2(), n, v))

# bz2.compress(b"banana")
def banana_bz2() -> B.Octets:
  B.Octets.of_list([66, 90, 104, 57, 49, 65, 89, 38, 83, 89, 239, 182, 236, 1, 0, 0, 1, 129, 0, 48, 1, 32, 0, 48, 204, 12, 122, 136, 94, 46, 228, 138, 112, 161, 33, 223, 109, 216, 2])

# bz2.compress(b"first ", 9) + bz2.compress(b"second", 1)
def two_bz2() -> B.Octets:
  B.Octets.of_list([66, 90, 104, 57, 49, 65, 89, 38, 83, 89, 164, 99, 157, 187, 0, 0, 0, 145, 128, 64, 0, 1, 32, 28, 0, 32, 0, 33, 128, 12, 3, 39, 46, 226, 238, 72, 167, 10, 18, 20, 140, 115, 183, 96, 66, 90, 104, 49, 49, 65, 89, 38, 83, 89, 38, 138, 2, 52, 0, 0, 2, 129, 128, 14, 1, 136, 0, 32, 0, 34, 24, 104, 48, 7, 2, 152, 93, 201, 20, 225, 66, 64, 154, 40, 8, 208])

def word.lo(a: Bool, b: Bool) -> String:
  match a:
    case True{}:
      match b:
        case True{}:
          "block "
        case False{}:
          "sorting "
    case False{}:
      "huffman, "

def word.hi(a: Bool, b: Bool, c: Bool) -> String:
  match a:
    case True{}:
      match b:
        case True{}:
          "burrows "
        case False{}:
          "wheeler "
    case False{}:
      match c:
        case True{}:
          "move-to-front "
        case False{}:
          "run\n"

def word.pick2(lo: Bool, +i: U32) -> String:
  match lo:
    case True{}:
      word.lo(U32.is_lt(i, 2), U32.is_eq(i, 0))
    case False{}:
      word.hi(U32.is_lt(i, 6), U32.is_eq(i, 4), U32.is_eq(i, 6))

def word.pick(+i: U32) -> String:
  word.pick2(U32.is_lt(i, 4), i)

# n bytes of words from a small vocabulary (a linear congruential generator)
def word(+s: U32) -> String:
  word.pick(U32.and(U32.shrn(s, 16n), 7))

def text.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      text.go(p, s2, L.bz.push(B.of_string.fast(word(s2)), acc))

def text(n: Nat) -> B.Octets:
  B.Octets.of_list(L.bz.rev(text.go(n, 7, Nil{})))

def rnd.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      rnd.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def rnd(n: Nat) -> B.Octets:
  B.Octets.of_list(rnd.go(n, 11, Nil{}))

def streamed(+o1: B.Octets, +o2: B.Octets, +o3: B.Octets) -> B.Octets:
  +w0 = C.Bzip2Writer.start(C.Bzip2CompressOptions{1, 17})
  +r1 = C.Bzip2Writer.feed(w0, o1)
  +r2 = C.Bzip2Writer.feed(C.wr.written.writer(r1), o2)
  +r3 = C.Bzip2Writer.feed(C.wr.written.writer(r2), o3)
  B.Octets.concat([C.wr.written.bytes(r1), C.wr.written.bytes(r2), C.wr.written.bytes(r3), C.Bzip2Writer.finish(C.wr.written.writer(r3))])

def main() -> IO(Unit):
  +t1 = text(40000n)
  +big = B.Octets.append(t1, rnd(30000n))
  +z1 = Z.compress_with(C.Bzip2CompressOptions{1, 17}, big)
  +s3 = streamed(B.Octets.take(100000n, big), B.Octets.slice(100000n, 150000n, big), B.Octets.drop(250000n, big))
  +run = B.Octets.of_list(L.bz.rep(1000n, 120))
  do IO<Unit>:
    IO.print(show(Z.decompress(B.Octets.of_list(a_bz2()))))
    IO.print(show(Z.decompress(banana_bz2())))
    IO.print(show(Z.decompress(two_bz2())))
    IO.print(show(Z.decompress_with(S.Bzip2Options{5, True{}}, banana_bz2())))
    IO.print(show(Z.decompress(a_with(13n, 106))))
    IO.print(show(Z.decompress(a_with(14n, 128))))
    IO.print(show(Z.decompress(a_with(4n, 50))))
    IO.print(show(Z.decompress(a_with(3n, 48))))
    IO.print(show(Z.decompress(B.Octets.take(30n, B.Octets.of_list(a_bz2())))))
    IO.print(show(Z.decompress(B.Octets.of_string("BZ"))))
    IO.print(show(Z.decompress(B.Octets.empty())))
    IO.print(B.Octets.hex(Z.compress(B.Octets.of_string("banana"))))
    IO.print(show(Z.decompress(Z.compress(B.Octets.of_string("banana")))))
    IO.print(show(Z.decompress(Z.compress(B.Octets.empty()))))
    IO.print(sum(Z.decompress(Z.compress(run))))
    IO.print(B.Octets.hex(R.rle1_encode(run)))
    IO.print(bwt.sh(W.bwt_forward(B.Octets.of_string("abracadabra, abracadabra"))))
    IO.print(bwt.sh(W.bwt_forward_ref(B.Octets.of_string("abracadabra, abracadabra"))))
    IO.print(bwt.undo(W.bwt_forward(B.Octets.of_string("abracadabra, abracadabra"))))
    IO.print(B.Octets.to_string(M.symbol_map(B.Octets.of_string("abracadabra, abracadabra"))))
    IO.print(Nat.show(B.Octets.len(big)) ++ " " ++ U32.show(S.bzip2_crc(big)))
    IO.print(Nat.show(B.Octets.len(z1)))
    IO.print(sum(Z.decompress(z1)))
    IO.print(U32.show(S.bzip2_crc(s3)) ++ " " ++ U32.show(S.bzip2_crc(z1)))

#|a
#|banana
#|first second
#|error OutputTooLarge
#|error BadBlockCrc
#|error Randomised
#|error BadBlockMagic
#|error BadBlockSize
#|error Truncated
#|error Truncated
#|error Truncated
#|425a6839314159265359efb6ec01000001810030012000218f5063d442f177245385090efb6ec010
#|banana
#|
#|1000 2630125351
#|78787878fb78787878fb78787878fb78787878e7
#|,arrdda rrccaaaaaaaabbbb 6
#|,arrdda rrccaaaaaaaabbbb 6
#|abracadabra, abracadabra
#| ,abcdr
#|359187 4223911435
#|51913
#|359187 4223911435
#|3238278361 3238278361
