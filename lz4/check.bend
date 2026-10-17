import Base
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./frame.bend as F
import ./lz4.bend as L
import ./compress.bend as C

def show(r: Result<&2, &2, K.Lz4Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ K.Lz4Error.show(e)
    case Done{o}:
      "done [" ++ B.Octets.to_string(o) ++ "]"

def show_len(r: Result<&2, &2, K.Lz4Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ K.Lz4Error.show(e)
    case Done{o}:
      "done, " ++ Nat.show(B.Octets.len(o)) ++ " bytes"

def show_info(r: Result<&2, &2, K.Lz4Error, F.Lz4FrameInfo>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ K.Lz4Error.show(e)
    case Done{F.Lz4FrameInfo{indep, bsum, csum, size, did, bmax}}:
      "indep " ++ Bool.show(indep) ++ ", block checksums " ++ Bool.show(bsum) ++ ", content checksum " ++ Bool.show(csum) ++ ", block max " ++ U32.show(bmax)

# what the lz4 tool writes for empty input
def empty_frame() -> B.Octets:
  B.Octets.of_list([4, 34, 77, 24, 100, 64, 167, 0, 0, 0, 0, 5, 93, 204, 2])

# "abc" * 8: one compressed block, block checksums, content size and checksum
def abc_frame() -> B.Octets:
  B.Octets.of_list([4, 34, 77, 24, 92, 64, 24, 0, 0, 0, 0, 0, 0, 0, 146, 12, 0, 0, 0, 60, 97, 98, 99, 3, 0, 80, 98, 99, 97, 98, 99, 8, 58, 99, 182, 0, 0, 0, 0, 254, 224, 41, 171])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(B.Octets.hex(K.block_literals(B.Octets.of_string("hello"))))
    IO.print(show(K.block_decompress(K.block_literals(B.Octets.of_string("hello")), 5n)))
    IO.print(show(K.block_decompress(B.Octets.of_list([38, 97, 98, 2, 0, 80, 99, 100, 101, 102, 103]), 100n)))
    IO.print(show(K.block_decompress(B.Octets.of_list([16, 97, 0, 0, 80, 97, 98, 99, 100, 101]), 100n)))
    IO.print(show(K.block_decompress(B.Octets.of_list([16, 97, 2, 0, 80, 97, 98, 99, 100, 101]), 100n)))
    IO.print(show(K.block_decompress(B.Octets.of_list([80, 97, 98]), 100n)))
    IO.print(show(K.block_decompress(K.block_literals(B.Octets.of_string("hello")), 4n)))
    IO.print(show(K.block_decompress(B.Octets.of_list([16, 97, 1, 0, 64, 97, 98, 99, 100]), 100n)))
    IO.print(show(K.block_decompress_dict(B.Octets.of_string("abcd"), B.Octets.of_list([4, 4, 0, 80, 101, 102, 103, 104, 105]), 100n)))
    IO.print(show(L.decompress(empty_frame())))
    IO.print(show(L.decompress(abc_frame())))
    IO.print(show_info(F.frame_header(abc_frame())))
    IO.print(show(L.decompress(B.Octets.append(abc_frame(), empty_frame()))))
    IO.print(show(L.decompress(B.Octets.take(20n, abc_frame()))))
    IO.print(show(L.decompress_with(F.Lz4Options{10, True{}, B.Octets.empty()}, abc_frame())))
    IO.print(U32.show(F.frame_checksum(B.Octets.empty())))
    IO.print(B.Octets.hex(C.compress(B.Octets.of_string("hello hello hello hello hello"))))
    IO.print(B.Octets.hex(C.block_compress(B.Octets.of_string("abcabcabcabcabcabcabcabc"))))
    IO.print(show(L.decompress(C.compress(B.Octets.of_string("compressed, then decompressed")))))
    IO.print(show(L.decompress(C.frame_stream(C.Lz4FrameOptions{C.Lz4Max64KB{}, 8, False{}, True{}, True{}, False{}}, [B.Octets.of_string("fed "), B.Octets.of_string("in pieces, fed in pieces")]))))
    IO.print(show_len(K.block_decompress(C.block_compress(B.Octets.zeros(1000n)), 1000n)))

#|5068656c6c6f
#|done [hello]
#|done [ababababababcdefg]
#|fail BadOffset
#|fail BadOffset
#|fail Truncated
#|fail OutputTooLarge
#|fail BadBlockEnd
#|done [abcdabcdefghi]
#|done []
#|done [abcabcabcabcabcabcabcabc]
#|indep False, block checksums True, content checksum True, block max 65536
#|done [abcabcabcabcabcabcabcabc]
#|fail Truncated
#|fail OutputTooLarge
#|46947589
#|04224d186440a70f0000006e68656c6c6f2006005068656c6c6f0000000079b1fff9
#|3c6162630300506263616263
#|done [compressed, then decompressed]
#|done [fed in pieces, fed in pieces]
#|done, 1000 bytes
