import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./huffman.bend as H
import ./adler32.bend as A
import ./match.bend as M
import ./block.bend as L
import ./inflate.bend as I
import ./deflate.bend as D
import ./zlib.bend as Z
import ./gzip.bend as G

def show(r: Result<&2, &2, E.DeflateError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.DeflateError.show(e)
    case Done{o}:
      "done [" ++ B.Octets.to_string(o) ++ "]"

def same(+o: B.Octets, r: Result<&2, &2, E.DeflateError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.DeflateError.show(e)
    case Done{+x}:
      "done, " ++ Nat.show(B.Octets.len(x)) ++ " bytes, the input " ++ Bool.show(B.Octets.is_eq(x, o))

def bits.go(p: List<&2, Bool>, acc: String) -> String:
  match p:
    case Nil{}:
      acc
    case Con{b, t}:
      match b:
        case True{}:
          bits.go(t, acc ++ "1")
        case False{}:
          bits.go(t, acc ++ "0")

def bits(m: Maybe<&2, List<&2, Bool>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{p}:
      bits.go(p, "")

def opts(+max: U32) -> I.InflateOptions:
  I.InflateOptions{max, B.Octets.empty(), True{}}

def big.word.pick(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, g: Bool) -> String:
  match a:
    case True{}:
      "deflate "
    case False{}:
      match b:
        case True{}:
          "inflate "
        case False{}:
          match c:
            case True{}:
              "huffman "
            case False{}:
              match d:
                case True{}:
                  "window, "
                case False{}:
                  match e:
                    case True{}:
                      "block "
                    case False{}:
                      match f:
                        case True{}:
                          "lz77 "
                        case False{}:
                          match g:
                            case True{}:
                              "zlib\n"
                            case False{}:
                              "gzip "

def big.word.at(+k: U32) -> List<&2, U32>:
  B.of_string(big.word.pick(U32.is_eq(k, 0), U32.is_eq(k, 1), U32.is_eq(k, 2), U32.is_eq(k, 3), U32.is_eq(k, 4), U32.is_eq(k, 5), U32.is_eq(k, 6)))

# 200 KB of pseudo-random words: text with matches near and up to 32 KB
# back, past the window
def big.word(+k: U32) -> List<&2, U32>:
  big.word.at(U32.and(k, 7))

def big.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +t = U32.add(U32.mul(s, 1103515245), 12345)
      big.go(p, t, B.rev_onto(big.word(U32.shrn(t, 16n)), acc))

def big() -> B.Octets:
  B.Octets.of_list(B.rev(big.go(28000n, 7, Nil{})))

# streaming: the inflater fed in three pieces
def thirds(+o: B.Octets) -> List<&2, B.Octets>:
  +n = B.Octets.len(o)
  +a = Nat.div(n, 3n)
  [B.Octets.take(a, o), B.Octets.slice(a, a, o), B.Octets.drop(Nat.add(a, a), o)]

type Acc is Data:
  Acc{inf: I.Inflater, out: List<&2, B.Octets>}

def feed.one(r: I.DflFed, out: List<&2, B.Octets>) -> Acc:
  match r:
    case I.DflFed{i, o}:
      Acc{i, Con{o, out}}

def feed.all(ps: List<&2, B.Octets>, a: Acc) -> Acc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case Acc{i, out}:
          feed.all(rest, feed.one(I.inflate_feed(i, p), out))

def stream.end(r: Result<&2, &2, E.DeflateError, I.DflInflated>, out: List<&2, B.Octets>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{I.DflInflated{o, rest}}:
      Done{B.Octets.concat(List.reverse(&2, B.Octets, Con{o, out}))}

def stream.fin(a: Acc) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match a:
    case Acc{i, out}:
      stream.end(I.inflate_finish(i), out)

def stream(+o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  stream.fin(feed.all(thirds(o), Acc{I.inflate_start(opts(4000000000)), Nil{}}))

# the streaming deflater, fed in three pieces
type WAcc is Data:
  WAcc{d: D.Deflater, out: List<&2, B.Octets>}

def wfeed.one(r: D.DflDeflated, out: List<&2, B.Octets>) -> WAcc:
  match r:
    case D.DflDeflated{d, o}:
      WAcc{d, Con{o, out}}

def wfeed.all(ps: List<&2, B.Octets>, a: WAcc) -> WAcc:
  match ps:
    case Nil{}:
      a
    case Con{p, rest}:
      match a:
        case WAcc{d, out}:
          wfeed.all(rest, wfeed.one(D.deflate_feed(d, p), out))

def wfin(a: WAcc) -> B.Octets:
  match a:
    case WAcc{d, out}:
      B.Octets.concat(List.reverse(&2, B.Octets, Con{D.deflate_finish(d), out}))

def wstream(+l: U32, +o: B.Octets) -> B.Octets:
  wfin(wfeed.all(thirds(o), WAcc{D.deflate_start(D.DeflateOptions.level(l)), Nil{}}))

def round(+l: U32, +o: B.Octets) -> String:
  +c = D.deflate_level(l, o)
  "level " ++ U32.show(l) ++ ": " ++ Nat.show(B.Octets.len(c)) ++ " bytes, " ++ same(o, I.inflate_with(opts(4000000000), c)) ++ ", streamed the same " ++ Bool.show(B.Octets.is_eq(c, wstream(l, o)))

def hello() -> B.Octets:
  B.Octets.of_string("hello hello hello hello")

def main() -> IO(Unit):
  do IO<Unit>:
    # RFC 1951, 3.2.2's example and 3.2.6's fixed code of 0
    IO.print(bits(H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 6)) ++ " " ++ bits(H.huff_code([3, 3, 3, 3, 3, 2, 4, 4], 5)) ++ " " ++ bits(H.huff_code(H.huff_fixed_lit(), 0)))
    # a stored block, a fixed block from zlib, a dynamic block, an empty stream
    IO.print(show(I.inflate_with(opts(100), B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99]))))
    IO.print(show(I.inflate_with(opts(100), B.Octets.of_list([203, 72, 205, 201, 201, 87, 200, 64, 144, 0]))))
    IO.print(show(I.inflate_with(opts(100), B.Octets.of_list([3, 0]))))
    # refused
    IO.print(show(I.inflate_with(opts(100), B.Octets.of_list([7, 0, 0]))))
    IO.print(show(I.inflate_with(opts(100), B.Octets.of_list([1, 3, 0, 252, 254, 97, 98, 99]))))
    IO.print(show(I.inflate_with(opts(2), B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99]))))
    IO.print(show(I.inflate_with(opts(100), B.Octets.of_list([1, 3, 0, 252, 255, 97, 98]))))
    IO.print(show(I.inflate_with(I.InflateOptions{100, B.Octets.empty(), False{}}, B.Octets.of_list([1, 3, 0, 252, 255, 97, 98, 99, 120]))))
    # compressing
    IO.print(B.Octets.hex(D.deflate(hello())))
    IO.print(show(D.inflate(D.deflate(hello()))))
    IO.print(B.Octets.hex(D.deflate_level(0, hello())))
    IO.print(B.Octets.hex(D.deflate(B.Octets.empty())))
    IO.print(B.Octets.hex(D.stored_stream(B.Octets.of_string("abc"))))
    IO.print(show(D.inflate(D.stored_stream(hello()))))
    IO.print(B.Octets.hex(D.deflate_with(D.DeflateOptions.with_blocks(D.DeflateOptions.default(), L.DflBlockDynamic{}), hello())))
    IO.print(B.Octets.hex(D.deflate_with(D.DeflateOptions.with_matcher(D.DeflateOptions.default(), M.DflStratRle{}), B.Octets.of_string("aaaaaaaaaaaaaaaaaaaab"))))
    # zlib and gzip
    IO.print(B.Octets.hex(Z.zlib_compress(hello())))
    IO.print(show(Z.zlib_decompress(Z.zlib_compress(hello()))))
    IO.print(B.Octets.hex(G.gzip_compress(B.Octets.of_string("hello gzip"))))
    IO.print(show(G.gzip_decompress(G.gzip_compress(B.Octets.of_string("hello gzip")))))
    IO.print(show(G.gzip_decompress(B.Octets.append(G.gzip_compress(B.Octets.of_string("one, ")), G.gzip_compress(B.Octets.of_string("two"))))))
    IO.print(U32.show(A.adler32(B.Octets.of_string("Wikipedia"))) ++ " " ++ U32.show(G.gzip_crc32(B.Octets.of_string("123456789"))))
    # 200 KB of text, at three levels, and the streaming inflater
    IO.print(round(1, big()))
    IO.print(round(6, big()))
    IO.print(round(9, big()))
    IO.print(same(big(), stream(D.deflate(big()))))
#|1110 00 00110000
#|done [abc]
#|done [hello hello hello]
#|done []
#|fail BadBlockType
#|fail BadStoredLength
#|fail OutputTooLarge
#|fail Truncated
#|fail TrailingData
#|cb48cdc9c957c02001
#|done [hello hello hello hello]
#|011700e8ff68656c6c6f2068656c6c6f2068656c6c6f2068656c6c6f
#|0300
#|000300fcff616263010000ffff
#|done [hello hello hello hello]
#|65c4310900000002c12a96131c1eecbf19c01b2e86ea1e
#|4bc4029200
#|789ccb48cdc9c957c02001680308b1
#|done [hello hello hello hello]
#|1f8b08000000000000ffcb48cdc9c95748afca2c0000196ad2df0a000000
#|done [hello gzip]
#|done [one, two]
#|300286872 3421780262
#|level 1: 27502 bytes, done, 185771 bytes, the input True, streamed the same True
#|level 6: 19353 bytes, done, 185771 bytes, the input True, streamed the same True
#|level 9: 17962 bytes, done, 185771 bytes, the input True, streamed the same True
#|done, 185771 bytes, the input True
