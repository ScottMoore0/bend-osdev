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

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(B.Octets.to_string(H.hexfield_encode(3735928559)))
    IO.print(Maybe.show(~&2, ~U32, ~U32.show, H.hexfield_decode(B.Octets.of_string("0000beef"))))
    IO.print(B.Octets.hex(C.Cpio.build(C.CpioFormat.default(), files())))
    IO.print(show(C.Cpio.parse(C.Cpio.build(C.CpioNewc{}, files()))))
    IO.print(show(C.Cpio.parse(C.Cpio.build(C.CpioCrc{}, files()))))
    IO.print(U32.show(C.Cpio.checksum(B.Octets.of_string("#!/bin/sh\n"))))
    IO.print(show(C.Cpio.parse(B.Octets.take(130n, C.Cpio.build(C.CpioNewc{}, files())))))
    IO.print(show(C.Cpio.parse(B.Octets.of_string("070707"))))

#|DEADBEEF
#|Some(48879)
#|3037303730313030303030303030303030303831454430303030303030303030303030303030303030303030303130303030303030303030303030303041303030303030303030303030303030303030303030303030303030303030303030303030303030353030303030303030696e6974000023212f62696e2f73680a000030373037303130303030303030303030303034314544303030303030303030303030303030303030303030303031303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303430303030303030306465760000003037303730313030303030303030303030303030303030303030303030303030303030303030303030303030303130303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030423030303030303030545241494c455221212100000000
#|entries: init dev
#|entries: init dev
#|704
#|error: truncated
#|error: bad magic
