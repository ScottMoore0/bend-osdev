# md-engine on its own: the word helpers and a block's words, the digest
# bytes of each chaining value type, the Merkle-Damgard padding's length,
# and the engine over a toy compression function (the chaining value times
# 31 plus the block's bytes: not a hash, but enough to show the engine
# buffers, counts and compresses whole blocks the same in one piece and in
# three). The hash packages (md4, md5, sha1, ripemd160, sm3, streebog,
# michael) test the engine under real compression functions, against
# Python's hashlib and the specifications' vectors.
import Base
import ../bytes/bytes.bend as B
import ./md-engine.bend as Hs

def eng.sum(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      eng.sum(t, U32.add(acc, x))

# the toy compression function
def eng.toy(cv: U32, blk: List<&2, U32>) -> U32:
  eng.sum(blk, U32.mul(cv, 31))

# its digest: the chaining value, big-endian
def eng.out(x: U32) -> B.Octets:
  B.Octets.of_list(B.be32(x))

# the bytes 1, 6, 11, ... (1 + 5i mod 256), n of them, last first
def eng.msg.go(n: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      eng.msg.go(p, U32.add(x, 5), Con{U32.and(x, 255), acc})

def eng.msg(n: Nat) -> B.Octets:
  B.Octets.of_list(B.rev(eng.msg.go(n, 1, Nil{})))

# the bytes 0 to n - 1
def eng.iota.go(+n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      eng.iota.go(p, Con{U32.from_nat(p), acc})

# the first and last of a block's sixteen words
def eng.ends(x: Hs.HsW16) -> String:
  match x:
    case Hs.HsW16{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
      U32.show(x0) ++ " " ++ U32.show(x15)

# the state's parts: chaining value, pending bytes, count, blocks, bits
def eng.state(+s: Hs.HsMdState<U32>) -> String:
  U32.show(Hs.HsMd.cv(~U32, s)) ++ " " ++ B.Octets.hex(B.Octets.of_list(Hs.HsMd.pending(~U32, s))) ++ " " ++ U32.show(Hs.HsMd.count(~U32, s)) ++ " " ++ B.Octets.hex(B.Octets.of_list(B.be64(Hs.HsMd.blocks(~U32, s)))) ++ " " ++ B.Octets.hex(B.Octets.of_list(B.be64(Hs.HsMd.bits(~U32, ~63, s))))

def eng.update(s: Hs.HsMdState<U32>, o: B.Octets) -> Hs.HsMdState<U32>:
  Hs.HsMd.update(~U32, ~eng.toy, ~63, s, o)

def eng.final(+s: Hs.HsMdState<U32>) -> B.Octets:
  Hs.HsMd.final_md(~U32, ~eng.toy, ~63, ~Hs.hs.len.be, ~eng.out, s)

# the padding's length after cnt bytes, with an 8-byte length field
def eng.pad(~last: U32, +cnt: U32) -> String:
  Nat.show(B.len(Hs.HsMd.md_pad(~last, cnt, B.zeros(8n))))

def main() -> IO(Unit):
  +blk = eng.iota.go(64n, Nil{})
  +m = eng.msg(200n)
  +whole = eng.update(Hs.HsMd.start(~U32, 7), m)
  +pieces = eng.update(eng.update(eng.update(Hs.HsMd.start(~U32, 7), B.Octets.take(10n, m)), B.Octets.take(120n, B.Octets.drop(10n, m))), B.Octets.drop(130n, m))
  do IO<Unit>:
    IO.print("rotl " ++ U32.show(Hs.hs.rotl(2147483649, 1n)) ++ " " ++ U32.show(Hs.hs.rotl(305419896, 8n)))
    IO.print("words " ++ U32.show(Hs.hs.le(1, 2, 3, 4)) ++ " " ++ U32.show(Hs.hs.be(1, 2, 3, 4)))
    IO.print("block le " ++ eng.ends(Hs.hs.block.le(blk)) ++ ", be " ++ eng.ends(Hs.hs.block.be(blk)))
    IO.print("w2 le " ++ B.Octets.hex(Hs.HsW2.le(Hs.HsW2{1, 2})))
    IO.print("w4 le " ++ B.Octets.hex(Hs.HsW4.le(Hs.HsW4{1, 2, 3, 4})))
    IO.print("w5 le " ++ B.Octets.hex(Hs.HsW5.le(Hs.HsW5{1, 2, 3, 4, 5})) ++ ", be " ++ B.Octets.hex(Hs.HsW5.be(Hs.HsW5{1, 2, 3, 4, 5})))
    IO.print("w8 be " ++ B.Octets.hex(Hs.HsW8.be(Hs.HsW8{1, 2, 3, 4, 5, 6, 7, 8})))
    IO.print("padding after 0, 55, 56, 63 bytes: " ++ eng.pad(~63, 0) ++ " " ++ eng.pad(~63, 55) ++ " " ++ eng.pad(~63, 56) ++ " " ++ eng.pad(~63, 63) ++ "; 4-byte blocks, after 1: " ++ eng.pad(~3, 1))
    IO.print("state " ++ eng.state(whole))
    IO.print("state in pieces " ++ eng.state(pieces))
    IO.print("final " ++ B.Octets.hex(eng.final(whole)) ++ " " ++ B.Octets.hex(eng.final(pieces)))
    IO.print("final of nothing " ++ B.Octets.hex(eng.final(Hs.HsMd.start(~U32, 7))))

#|rotl 3 878082066
#|words 67305985 16909060
#|block le 50462976 1061043516, be 66051 1010646591
#|w2 le 0100000002000000
#|w4 le 01000000020000000300000004000000
#|w5 le 0100000002000000030000000400000005000000, be 0000000100000002000000030000000400000005
#|w8 be 0000000100000002000000030000000400000005000000060000000700000008
#|padding after 0, 55, 56, 63 bytes: 64 9 72 65; 4-byte blocks, after 1: 11
#|state 7010361 c1c6cbd0d5dadfe4 8 0000000000000003 0000000000000640
#|state in pieces 7010361 c1c6cbd0d5dadfe4 8 0000000000000003 0000000000000640
#|final 0cf41641 0cf41641
#|final of nothing 00000159
