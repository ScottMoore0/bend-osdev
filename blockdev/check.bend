import Base
import ../bytes/bytes.bend as B
import ./blockdev.bend as D
import ./imgdev.bend as I

def dev() -> D.MemDev:
  D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij"))

def show(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "ok " ++ B.Octets.hex(o)
    case Fail{D.DevOutOfRange{n}}:
      "out of range " ++ Nat.show(n)
    case Fail{D.DevBadLength{e, g}}:
      "bad length " ++ Nat.show(e) ++ " " ++ Nat.show(g)
    case Fail{D.DevFailed{c}}:
      "failed " ++ U32.show(c)

def bytes(+off: Nat, +len: Nat) -> String:
  show(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dev(), off, len))

def ishow(r: I.ImgDev & Result<&2, &2, D.DevError, B.Octets>) -> String:
  (img, x) = r
  show(x)

def iwrite(r: I.ImgDev & Result<&2, &2, D.DevError, Unit>) -> I.ImgDev:
  (img, x) = r
  img

def owned(r: D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> String:
  (d, x) = r
  show(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(D.MemDev.block_count(dev())))
    IO.print(show(D.MemDev.read_block(dev(), 2n)))
    IO.print(show(D.MemDev.read_block(dev(), 5n)))
    IO.print(bytes(3n, 6n))
    IO.print(bytes(11n, 2n))
    IO.print(bytes(40n, 0n))
    IO.print(B.Octets.to_string(B.Octets.take(10n, D.MemDev.to_octets(D.MemDev.update(dev(), 1n, B.Octets.of_string("EFGH"))))))
    IO.print(owned(D.ODev.read_bytes(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, dev(), 3n, 6n)))
    IO.print(show(D.MemDev.read_block(D.MemDev.blank(4n, 1000000n), 999999n)))
    IO.print(ishow(I.ImgDev.read_block(I.ImgDev.of_octets(1n, B.Octets.of_string("abcdefghij")), 1n)))
    IO.print(ishow(I.ImgDev.read_block(iwrite(I.ImgDev.write_block(I.ImgDev.of_octets(1n, B.Octets.of_string("abcdefghij")), 2n, B.Octets.of_string("WXYZ"))), 2n)))
    IO.print(ishow(I.ImgDev.read_block(iwrite(I.ImgDev.write_block(I.ImgDev.blank(1n, 4n), 0n, B.Octets.of_string("xyz"))), 0n)))
    IO.print(ishow(D.ODev.read_bytes(~I.ImgDev, ~I.ImgDev.block_size, ~I.ImgDev.read_block, I.ImgDev.of_octets(1n, B.Octets.of_string("abcdefghij")), 3n, 6n)))
    IO.print(B.Octets.to_string(B.Octets.take(10n, D.MemDev.to_octets(I.ImgDev.freeze(I.ImgDev.of_octets(2n, B.Octets.of_string("abcdefghij")))))))

#|3
#|ok 696a0000
#|out of range 5
#|ok 646566676869
#|out of range 3
#|ok 
#|abcdEFGHij
#|ok 646566676869
#|ok 00000000
#|ok 65666768
#|ok 5758595a
#|ok 00000000
#|ok 646566676869
#|abcdefghij
