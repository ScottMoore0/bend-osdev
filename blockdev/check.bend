import Base
import ../bytes/bytes.bend as B
import ./blockdev.bend as D

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

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(D.MemDev.block_count(dev())))
    IO.print(show(D.MemDev.read_block(dev(), 2n)))
    IO.print(show(D.MemDev.read_block(dev(), 5n)))
    IO.print(bytes(3n, 6n))
    IO.print(bytes(11n, 2n))
    IO.print(bytes(40n, 0n))
    IO.print(B.Octets.to_string(B.Octets.take(10n, D.MemDev.to_octets(D.MemDev.update(dev(), 1n, B.Octets.of_string("EFGH"))))))

#|3
#|ok 696a0000
#|out of range 5
#|ok 646566676869
#|out of range 3
#|ok 
#|abcdEFGHij
