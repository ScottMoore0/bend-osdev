import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./view.bend as V
import ./packing.bend as P

def err(e: P.PkError) -> String:
  match e:
    case P.PkBadRange{}:
      "PkBadRange"
    case P.PkTooWide{}:
      "PkTooWide"
    case P.PkOutOfBuffer{}:
      "PkOutOfBuffer"
    case P.PkBadLength{}:
      "PkBadLength"
    case P.PkOverflow{}:
      "PkOverflow"

def show_b(r: Result<&2, &2, P.PkError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      err(e)

def show_v(r: Result<&2, &2, P.PkError, W.W64>) -> String:
  match r:
    case Done{v}:
      W.W64.show_hex(v)
    case Fail{e}:
      err(e)

def q(m: Bool, le: Bool, lsw: Bool) -> V.PkQuirks:
  V.PkQuirks{m, le, lsw}

def zeros(n: Nat) -> B.Octets:
  B.Octets.zeros(n)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_b(P.packing.pack(V.packing.quirks_none(), zeros(4n), 15n, 8n, W.W64.from_u32(171))))
    IO.print(show_b(P.packing.pack(q(False{}, True{}, False{}), zeros(4n), 15n, 8n, W.W64.from_u32(171))))
    IO.print(show_b(P.packing.pack(q(True{}, False{}, False{}), zeros(4n), 7n, 0n, W.W64.from_u32(1))))
    IO.print(show_b(P.packing.pack(q(False{}, False{}, True{}), zeros(8n), 7n, 0n, W.W64.from_u32(5))))
    IO.print(show_b(P.packing.pack(q(False{}, True{}, True{}), zeros(8n), 39n, 32n, W.W64.from_u32(9))))
    IO.print(show_v(P.packing.unpack(V.packing.quirks_none(), B.Octets.of_list([18, 52, 86, 120]), 19n, 4n)))
    IO.print(show_v(P.packing.unpack(q(False{}, True{}, False{}), B.Octets.of_list([18, 52, 86, 120]), 19n, 4n)))
    IO.print(show_v(P.packing.unpack(V.packing.quirks_none(), B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8, 9]), 71n, 8n)))
    IO.print(show_b(P.packing.pack(V.packing.quirks_none(), zeros(9n), 69n, 6n, W.W64.from_parts(4294967295, 4294967295))))
    IO.print(show_b(P.packing.pack(V.packing.quirks_none(), zeros(4n), 3n, 5n, W.W64.from_u32(1))))
    IO.print(show_b(P.packing.pack(V.packing.quirks_none(), zeros(16n), 70n, 0n, W.W64.from_u32(1))))
    IO.print(show_b(P.packing.pack(V.packing.quirks_none(), zeros(4n), 40n, 32n, W.W64.from_u32(1))))
    IO.print(show_b(P.packing.pack(q(False{}, True{}, False{}), zeros(6n), 7n, 0n, W.W64.from_u32(1))))
    IO.print(show_b(P.packing.pack(V.packing.quirks_none(), zeros(4n), 7n, 0n, W.W64.from_u32(300))))
    IO.print(show_b(P.packing.pack_masked(V.packing.quirks_none(), zeros(4n), 7n, 0n, W.W64.from_u32(300))))
    IO.print(Bool.show(P.packing.bit(q(True{}, False{}, False{}), B.Octets.of_list([0, 0, 0, 128]), 0n)))

#|0000ab00
#|00ab0000
#|00000080
#|0000000500000000
#|0000000009000000
#|0000000000004567
#|0000000000006341
#|0102030405060708
#|3fffffffffffffffc0
#|PkBadRange
#|PkTooWide
#|PkOutOfBuffer
#|PkBadLength
#|PkOverflow
#|0000002c
#|True
