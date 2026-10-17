import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./container.bend as C
import ./integrity.bend as I
import ./delta.bend as D
import ./lzma2.bend as L2
import ./xz.bend as X

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
#|lzma2 control 3: error: corrupt LZMA2 data
#|lzma2 no reset: error: corrupt LZMA2 data
#|lzma2 trailing: error: data after the end of the LZMA2 stream
#|header: 4
#|delta: 01020203030401
#|dict sizes: 4096 3145728 4294967295 none
#|check sizes: 0 4 8 32 64
#|unsupported: unsupported filter 11 (RISC-V BCJ)
