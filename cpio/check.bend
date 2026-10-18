import Base
import ../bytes/bytes.bend as B
import ./hexfield.bend as H
import ./cpio.bend as C

def files() -> List<&2, C.CpioEntry>:
  [C.CpioEntry.file("init", 33261, B.Octets.of_string("#!/bin/sh\n")), C.CpioEntry.file("dev", 16877, B.Octets.empty())]

def err(e: C.CpioError) -> String:
  match e:
    case C.CpioTruncated{}:
      "truncated"
    case C.CpioBadMagic{}:
      "bad magic"
    case C.CpioBadHex{}:
      "bad hex"
    case C.CpioBadNameSize{}:
      "bad name size"
    case C.CpioNoNul{}:
      "no nul"
    case C.CpioBadChecksum{}:
      "bad checksum"
    case C.CpioNoTrailer{}:
      "no trailer"

def names(es: List<&2, C.CpioEntry>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      " " ++ C.CpioEntry.name_string(e) ++ names(t)

def show(m: Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>) -> String:
  match m:
    case Fail{e}:
      "error: " ++ err(e)
    case Done{es}:
      "entries:" ++ names(es)

# A larger archive, as a regression test for long inputs: one file of n
# pseudo-random bytes (a linear congruential generator) and k files of 64
# zero bytes, named d/00000001 and on

def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def many.go(k: Nat, +i: U32, acc: List<&2, C.CpioEntry>) -> List<&2, C.CpioEntry>:
  match k:
    case 0n:
      acc
    case 1n+p:
      many.go(p, U32.add(i, 1), Con{C.CpioEntry{i, 33188, 0, 0, 1, 0, 0, 0, 0, 0, B.Octets.append(B.Octets.of_string("d/"), H.hexfield_encode(i)), B.Octets.zeros(64n)}, acc})

def many(n: Nat, k: Nat) -> List<&2, C.CpioEntry>:
  Con{C.CpioEntry.file("big", 33188, B.Octets.of_list(bulk.go(n, 7, Nil{}))), many.go(k, 1, Nil{})}

# the number of entries, and the sum of their data's checksums
def tally.go(es: List<&2, C.CpioEntry>, n: Nat, acc: U32) -> String:
  match es:
    case Nil{}:
      Nat.show(n) ++ " entries, data sum " ++ U32.show(acc)
    case Con{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, dmaj, dmin, rmaj, rmin, name, data}, t}:
      tally.go(t, 1n+n, U32.add(acc, C.Cpio.checksum(data)))

def tally(m: Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>) -> String:
  match m:
    case Fail{e}:
      "error: " ++ err(e)
    case Done{es}:
      tally.go(es, 0n, 0)

def main() -> IO(Unit):
  +big = C.Cpio.build(C.CpioCrc{}, many(49152n, 250n))
  do IO<Unit>:
    IO.print(B.Octets.to_string(H.hexfield_encode(3735928559)))
    IO.print(Maybe.show(~&2, ~U32, ~U32.show, H.hexfield_decode(B.Octets.of_string("0000beef"))))
    IO.print(B.Octets.hex(C.Cpio.build(C.CpioFormat.default(), files())))
    IO.print(show(C.Cpio.parse(C.Cpio.build(C.CpioNewc{}, files()))))
    IO.print(show(C.Cpio.parse(C.Cpio.build(C.CpioCrc{}, files()))))
    IO.print(U32.show(C.Cpio.checksum(B.Octets.of_string("#!/bin/sh\n"))))
    IO.print(show(C.Cpio.parse(B.Octets.take(130n, C.Cpio.build(C.CpioNewc{}, files())))))
    IO.print(show(C.Cpio.parse(B.Octets.of_string("070707"))))
    IO.print(Nat.show(B.Octets.len(big)) ++ " bytes, sum " ++ U32.show(C.Cpio.checksum(big)))
    IO.print(tally(C.Cpio.parse(big)))

#|DEADBEEF
#|Some(48879)
#|3037303730313030303030303030303030303831454430303030303030303030303030303030303030303030303130303030303030303030303030303041303030303030303030303030303030303030303030303030303030303030303030303030303030353030303030303030696e6974000023212f62696e2f73680a000030373037303130303030303030303030303034314544303030303030303030303030303030303030303030303031303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303430303030303030306465760000003037303730313030303030303030303030303030303030303030303030303030303030303030303030303030303130303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030423030303030303030545241494c455221212100000000
#|entries: init dev
#|entries: init dev
#|704
#|error: truncated
#|error: bad magic
#|96392 bytes, sum 7769034
#|251 entries, data sum 6277407
