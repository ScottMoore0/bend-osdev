import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./container.bend as C
import ./integrity.bend as I
import ./delta.bend as D
import ./lzma2.bend as L2
import ./xz.bend as X
import ./alone.bend as A
import ../word64/word64.bend as W
import ../crc/crc.bend as Cr

def xzcheck_show(r: Result<&2, &2, E.XzError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.XzError.show(e)
    case Done{o}:
      "\"" ++ B.Octets.to_string(o) ++ "\""

def xzcheck_u32(r: Result<&2, &2, E.XzError, U32>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.XzError.show(e)
    case Done{v}:
      U32.show(v)

def xzcheck_dict(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{n}:
      U32.show(n)
    case None{}:
      "none"

def xzcheck_join(r: Result<&2, &2, E.XzError, B.Octets>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{B.Octets.append(acc, o)}

# an .xz file fed to the streaming decoder one byte at a time
def xzcheck_bytewise(xs: List<&2, U32>, r: Result<&2, &1, E.XzError, X.XzFed>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match xs:
    case Nil{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{X.XzFed{d, out}}:
          xzcheck_join(X.XzDecoder.finish(d), B.Octets.append(acc, out))
    case Con{h, t}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{X.XzFed{d, out}}:
          xzcheck_bytewise(t, X.XzDecoder.feed(d, B.Octets.of_list([h])), B.Octets.append(acc, out))

# Large inputs (beyond the runtime's stack depth if the decoder recursed once
# per byte): 100 KiB of output from an 820-byte .xz file, and a raw LZMA2
# stream of two uncompressed chunks (64 KiB and 36 KiB), each checked
# by length and CRC32 against Python's zlib

def xzcheck_big(r: Result<&2, &2, E.XzError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.XzError.show(e)
    case Done{+o}:
      Nat.show(B.Octets.len(o)) ++ " bytes, crc32 " ++ U32.show(Cr.crc32(o))

# n bytes from position i on, byte j being (31 j + j / 256) mod 256, pushed
# onto acc (so in reverse)
def xzcheck_gen.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      xzcheck_gen.go(p, U32.add(i, 1), Con{U32.and(U32.add(U32.mul(i, 31), U32.shrn(i, 8n)), 255), acc})

# the raw stream: the first 64 KiB of those bytes in a chunk that resets the
# dictionary, then the next 36 KiB, then the end marker
def xzcheck_raw() -> List<&2, U32>:
  Con{1, Con{255, Con{255, B.rev_onto(xzcheck_gen.go(65536n, 0, Nil{}), Con{2, Con{143, Con{255, B.rev_onto(xzcheck_gen.go(36864n, 65536, Nil{}), [0])}}})}}}

def xzcheck_big_xz() -> B.Octets:
  B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 1, 105, 34, 222, 54, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 225, 143, 255, 2, 245, 93, 0, 0, 2, 15, 87, 2, 104, 198, 120, 206, 216, 15, 144, 230, 235, 182, 221, 31, 112, 98, 176, 33, 39, 20, 249, 177, 149, 138, 88, 96, 33, 122, 44, 172, 231, 119, 152, 223, 69, 134, 218, 172, 105, 52, 105, 13, 56, 100, 85, 226, 183, 24, 22, 170, 68, 21, 153, 190, 162, 144, 139, 9, 214, 31, 201, 71, 255, 239, 222, 154, 198, 141, 191, 51, 217, 181, 212, 106, 175, 22, 237, 244, 131, 188, 105, 116, 209, 35, 230, 199, 132, 30, 18, 155, 166, 117, 144, 86, 144, 137, 114, 26, 88, 127, 90, 62, 128, 6, 76, 86, 101, 63, 120, 235, 173, 215, 198, 85, 59, 31, 103, 227, 168, 55, 138, 25, 153, 242, 76, 230, 165, 203, 0, 113, 137, 91, 207, 22, 35, 129, 146, 241, 247, 7, 191, 155, 238, 220, 250, 22, 19, 14, 81, 208, 16, 105, 136, 62, 222, 228, 189, 195, 166, 224, 149, 131, 43, 75, 168, 149, 117, 152, 122, 27, 138, 2, 116, 120, 166, 161, 252, 106, 96, 240, 165, 173, 42, 200, 85, 196, 207, 47, 6, 15, 98, 27, 157, 133, 185, 21, 28, 200, 155, 148, 25, 102, 212, 6, 32, 134, 38, 163, 173, 124, 104, 132, 2, 47, 123, 143, 43, 87, 114, 50, 86, 179, 216, 136, 15, 77, 127, 3, 86, 61, 195, 213, 154, 175, 21, 234, 153, 176, 249, 193, 55, 255, 26, 253, 169, 83, 128, 87, 32, 233, 44, 32, 84, 71, 136, 77, 15, 171, 74, 122, 230, 80, 254, 111, 195, 51, 79, 202, 216, 20, 221, 61, 26, 143, 191, 61, 123, 68, 114, 86, 65, 126, 111, 24, 88, 165, 98, 11, 76, 104, 150, 50, 129, 252, 184, 73, 174, 89, 151, 118, 78, 151, 158, 85, 9, 21, 74, 210, 131, 232, 58, 174, 105, 47, 214, 74, 160, 204, 32, 6, 156, 237, 88, 170, 239, 104, 0, 140, 136, 74, 88, 173, 20, 207, 75, 30, 176, 3, 157, 95, 251, 71, 171, 99, 239, 171, 224, 88, 106, 108, 119, 77, 36, 60, 170, 114, 234, 201, 195, 227, 134, 164, 223, 238, 38, 170, 203, 55, 179, 250, 69, 73, 242, 40, 120, 241, 207, 50, 44, 219, 156, 24, 17, 185, 32, 245, 233, 202, 125, 252, 202, 233, 158, 180, 34, 253, 194, 58, 78, 153, 252, 213, 146, 205, 27, 254, 26, 135, 221, 9, 41, 181, 141, 30, 133, 33, 181, 40, 168, 128, 245, 140, 65, 76, 31, 73, 174, 90, 51, 111, 81, 18, 4, 147, 11, 40, 202, 92, 194, 144, 140, 74, 212, 122, 140, 239, 90, 171, 200, 116, 224, 23, 148, 90, 230, 99, 190, 86, 161, 47, 133, 243, 102, 91, 226, 239, 59, 8, 241, 116, 168, 31, 229, 132, 225, 132, 218, 93, 146, 71, 21, 74, 111, 198, 191, 245, 161, 72, 54, 21, 127, 184, 133, 162, 133, 20, 84, 191, 123, 54, 215, 106, 97, 33, 143, 174, 30, 210, 87, 137, 229, 202, 80, 111, 72, 84, 57, 104, 144, 75, 24, 231, 56, 226, 249, 210, 86, 34, 158, 168, 147, 205, 90, 10, 215, 218, 176, 234, 161, 107, 121, 9, 48, 81, 167, 109, 26, 74, 70, 114, 110, 116, 81, 171, 169, 2, 204, 8, 21, 209, 88, 93, 21, 77, 97, 124, 155, 2, 133, 191, 49, 207, 226, 130, 200, 133, 67, 75, 56, 54, 158, 170, 252, 142, 169, 166, 52, 250, 217, 48, 78, 9, 235, 252, 183, 134, 139, 43, 236, 149, 174, 73, 102, 203, 33, 13, 10, 125, 205, 68, 173, 157, 6, 255, 116, 214, 251, 49, 41, 169, 21, 22, 122, 5, 235, 6, 86, 152, 246, 250, 50, 239, 59, 243, 70, 139, 217, 115, 3, 140, 112, 191, 41, 212, 235, 109, 62, 232, 212, 249, 204, 104, 175, 249, 232, 105, 75, 109, 142, 117, 244, 99, 109, 230, 32, 217, 139, 212, 179, 134, 182, 252, 129, 228, 165, 222, 111, 148, 201, 226, 127, 96, 231, 34, 152, 135, 26, 61, 95, 13, 253, 148, 76, 110, 203, 3, 94, 213, 123, 54, 107, 245, 233, 196, 73, 71, 24, 191, 74, 50, 154, 114, 197, 72, 78, 84, 195, 75, 78, 43, 58, 90, 194, 223, 43, 76, 58, 72, 43, 169, 65, 211, 15, 127, 211, 65, 128, 200, 166, 78, 3, 58, 27, 120, 161, 112, 144, 148, 39, 221, 19, 42, 65, 0, 0, 0, 0, 0, 99, 42, 204, 45, 0, 1, 141, 6, 128, 160, 6, 0, 166, 106, 64, 140, 62, 48, 13, 139, 2, 0, 0, 0, 0, 1, 89, 90])

# a .lzma file fed to the streaming decoder one byte at a time
def xzcheck_alone_bytewise(xs: List<&2, U32>, r: Result<&2, &1, E.XzError, A.XzAloneFed>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match xs:
    case Nil{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{A.XzAloneFed{d, out}}:
          xzcheck_join(A.XzAlone.finish(d), B.Octets.append(acc, out))
    case Con{h, t}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{A.XzAloneFed{d, out}}:
          xzcheck_alone_bytewise(t, A.XzAlone.feed(d, B.Octets.of_list([h])), B.Octets.append(acc, out))

def xzcheck_size(m: Maybe<&2, W.W64>) -> String:
  match m:
    case None{}:
      "unknown"
    case Some{w}:
      W.W64.show(w)

def xzcheck_alone_header(r: Result<&2, &2, E.XzError, A.XzAloneHeader>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.XzError.show(e)
    case Done{A.XzAloneHeader{lc, lp, pb, d, s}}:
      "lc " ++ Nat.show(lc) ++ ", lp " ++ Nat.show(lp) ++ ", pb " ++ Nat.show(pb) ++ ", dictionary " ++ U32.show(d) ++ ", size " ++ xzcheck_size(s)

# xz --format=lzma -6 of 100 KiB over seven letters: 125 bytes, the size
# unknown
def xzcheck_big_lzma() -> B.Octets:
  B.Octets.of_list([93, 0, 0, 128, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 48, 153, 200, 255, 254, 27, 117, 108, 82, 152, 228, 240, 109, 38, 188, 16, 34, 147, 53, 182, 184, 188, 132, 88, 157, 135, 133, 39, 112, 205, 233, 88, 47, 220, 13, 224, 232, 89, 125, 111, 93, 179, 237, 27, 204, 251, 195, 35, 170, 228, 73, 10, 50, 156, 241, 117, 192, 14, 223, 91, 9, 170, 114, 107, 35, 13, 129, 179, 98, 112, 71, 175, 0, 53, 238, 172, 214, 60, 10, 22, 161, 205, 14, 197, 159, 77, 117, 20, 157, 84, 36, 176, 127, 185, 209, 166, 207, 1, 74, 249, 106, 157, 209, 21, 99, 255, 255, 88, 116, 0, 0])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("hello: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("empty: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 0, 255, 18, 217, 65, 0, 0, 0, 0, 28, 223, 68, 33, 6, 114, 158, 122, 1, 0, 0, 0, 0, 0, 89, 90]))))
    IO.print("bad magic: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([252, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("header crc: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 231, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("check 2: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 2, 211, 115, 215, 175, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 91, 173, 100, 52, 0, 1, 29, 9, 147, 97, 54, 166, 42, 19, 144, 148, 1, 0, 0, 0, 0, 2, 89, 90]))))
    IO.print("x86: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 1, 4, 0, 33, 1, 22, 0, 13, 134, 53, 31, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("max 4: " ++ xzcheck_show(X.xz_decode(X.XzParams{4}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("truncated: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0]))))
    IO.print("block check: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 70, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("block header crc: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 1, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("index crc: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 196, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90]))))
    IO.print("footer magic: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 91]))))
    IO.print("stream padding: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90, 0, 0, 0]))))
    IO.print("garbage after: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90, 106, 117, 110, 107]))))
    IO.print("padded: " ++ xzcheck_show(X.xz_decode(X.XzParams{1000}, B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90, 0, 0, 0, 0, 0, 0, 0, 0]))))
    IO.print("streamed: " ++ xzcheck_show(xzcheck_bytewise(B.Octets.to_list(B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70, 2, 0, 33, 1, 22, 0, 0, 0, 116, 47, 229, 163, 1, 0, 8, 104, 101, 108, 108, 111, 44, 32, 120, 122, 0, 0, 0, 0, 180, 37, 202, 210, 99, 136, 22, 71, 0, 1, 33, 9, 108, 24, 197, 213, 31, 182, 243, 125, 1, 0, 0, 0, 0, 4, 89, 90])), Done{X.XzFed{X.XzDecoder.start(X.XzParams.default()), B.Octets.empty()}}, B.Octets.empty())))
    IO.print("lzma2: " ++ xzcheck_show(L2.XzLzma2.decode(4096, 100, B.Octets.of_list([224, 0, 11, 0, 8, 93, 0, 48, 152, 136, 167, 234, 37, 0, 0, 0]))))
    IO.print("lzma2 control 3: " ++ xzcheck_show(L2.XzLzma2.decode(4096, 100, B.Octets.of_list([3, 0]))))
    IO.print("lzma2 no reset: " ++ xzcheck_show(L2.XzLzma2.decode(4096, 100, B.Octets.of_list([2, 0, 0, 65, 0]))))
    IO.print("lzma2 trailing: " ++ xzcheck_show(L2.XzLzma2.decode(4096, 100, B.Octets.of_list([1, 0, 0, 65, 0, 0]))))
    IO.print("header: " ++ xzcheck_u32(C.XzStream.header(B.Octets.of_list([253, 55, 122, 88, 90, 0, 0, 4, 230, 214, 180, 70]))))
    IO.print("delta: " ++ B.Octets.hex(D.XzDelta.decode(2, B.Octets.of_list([1, 2, 1, 1, 1, 1, 254]))))
    IO.print("dict sizes: " ++ xzcheck_dict(L2.XzLzma2.dict_size(0)) ++ " " ++ xzcheck_dict(L2.XzLzma2.dict_size(19)) ++ " " ++ xzcheck_dict(L2.XzLzma2.dict_size(40)) ++ " " ++ xzcheck_dict(L2.XzLzma2.dict_size(41)))
    IO.print("check sizes: " ++ Nat.show(I.XzCheck.size(0)) ++ " " ++ Nat.show(I.XzCheck.size(1)) ++ " " ++ Nat.show(I.XzCheck.size(4)) ++ " " ++ Nat.show(I.XzCheck.size(10)) ++ " " ++ Nat.show(I.XzCheck.size(15)))
    IO.print("unsupported: " ++ E.XzError.show(E.XzUnsupportedFilter{11n}))
    IO.print("100 KiB file: " ++ xzcheck_big(X.xz_decode(X.XzParams{1048576}, xzcheck_big_xz())))
    IO.print("100 KiB raw: " ++ xzcheck_big(L2.XzLzma2.decode(65536, 1048576, B.Octets.of_list(xzcheck_raw()))))
    IO.print(".lzma, size unknown: " ++ xzcheck_show(A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0]))))
    IO.print(".lzma, size known: " ++ xzcheck_show(A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0]))))
    IO.print(".lzma, streamed: " ++ xzcheck_show(xzcheck_alone_bytewise([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0], Done{A.XzAloneFed{A.XzAlone.start(A.XzAloneParams.default()), B.Octets.empty()}}, B.Octets.empty())))
    IO.print(".lzma header: " ++ xzcheck_alone_header(A.XzAlone.header(B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0]))))
    IO.print(".lzma header bytes: " ++ B.Octets.hex(A.XzAlone.header_bytes(A.XzAloneHeader{3n, 0n, 2n, 8388608, None{}})))
    IO.print(".lzma bad props: " ++ xzcheck_show(A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([103, 0, 16, 0, 0]))))
    IO.print(".lzma short header: " ++ xzcheck_show(A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.of_list([93, 0, 16, 0, 0, 255]))))
    IO.print(".lzma trailing: " ++ xzcheck_show(A.XzAlone.decode(A.XzAloneParams.default(), B.Octets.append(B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0]), B.Octets.of_list([0])))))
    IO.print(".lzma max 4: " ++ xzcheck_show(A.XzAlone.decode(A.XzAloneParams{4}, B.Octets.of_list([93, 0, 16, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 0, 52, 25, 73, 238, 142, 104, 33, 255, 255, 255, 185, 224, 0, 0]))))
    IO.print("100 KiB .lzma: " ++ xzcheck_big(A.XzAlone.decode(A.XzAloneParams.default(), xzcheck_big_lzma())))

#|hello: "hello, xz"
#|empty: ""
#|bad magic: error: not an .xz stream (bad header magic)
#|header crc: error: stream header CRC32 mismatch
#|check 2: error: unsupported check 2 (reserved)
#|x86: error: unsupported filter 4 (x86 BCJ)
#|max 4: error: output larger than the maximum
#|truncated: error: truncated input
#|block check: error: block check mismatch: the data is corrupt
#|block header crc: error: block header CRC32 mismatch
#|index crc: error: index CRC32 mismatch
#|footer magic: error: bad stream footer magic
#|stream padding: error: non-null or misaligned padding
#|garbage after: error: not an .xz stream (bad header magic)
#|padded: "hello, xz"
#|streamed: "hello, xz"
#|lzma2: "abcabcabcabc"
#|lzma2 control 3: error: corrupt LZMA data
#|lzma2 no reset: error: corrupt LZMA data
#|lzma2 trailing: error: data after the end of the stream
#|header: 4
#|delta: 01020203030401
#|dict sizes: 4096 3145728 4294967295 none
#|check sizes: 0 4 8 32 64
#|unsupported: unsupported filter 11 (RISC-V BCJ)
#|100 KiB file: 102400 bytes, crc32 768354915
#|100 KiB raw: 102400 bytes, crc32 2816042322
#|.lzma, size unknown: "hello"
#|.lzma, size known: "hello"
#|.lzma, streamed: "hello"
#|.lzma header: lc 3, lp 0, pb 2, dictionary 4096, size unknown
#|.lzma header bytes: 5d00008000ffffffffffffffff
#|.lzma bad props: error: malformed filter properties
#|.lzma short header: error: truncated input
#|.lzma trailing: error: data after the end of the stream
#|.lzma max 4: error: output larger than the maximum
#|100 KiB .lzma: 102400 bytes, crc32 2820342978
