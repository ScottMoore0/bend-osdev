# bend-osdev-acpi, slit.bend: the System Locality Distance Information
# Table, "SLIT" (ACPI 6.5, section 5.2.17): after the header, the number of
# system localities N (8 bytes, offset 36), then the N x N matrix of
# relative distances, one byte each, row by row, from offset 44. Entry
# (i, i) is 10 (a locality's distance to itself); 0xFF means unreachable.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F

type AcpiSlit is Data:
  AcpiSlit{header: H.AcpiHeader, count: Nat, matrix: B.Octets}

def AcpiSlit.count(s: AcpiSlit) -> Nat:
  match s:
    case AcpiSlit{h, n, m}:
      n

def slit.mk(ok: Bool, +h: H.AcpiHeader, +n: Nat, +body: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSlit>:
  match ok:
    case False{}:
      Fail{E.AcpiBadSize{B.Octets.len(body)}}
    case True{}:
      Done{AcpiSlit{h, n, B.Octets.slice(8n, Nat.mul(n, n), body)}}

def slit.body(ok: Bool, +h: H.AcpiHeader, +body: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSlit>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{44n, Nat.add(36n, B.Octets.len(body))}}
    case True{}:
      +big = F.AcpiF.u64(body, 0n)
      +n = U32.to_nat(W.W64.lo(big))
      slit.mk(Bool.and(U32.is_eq(W.W64.hi(big), 0), Bool.and(U32.is_lt(W.W64.lo(big), 65536), Nat.is_le(Nat.add(8n, Nat.mul(n, n)), B.Octets.len(body)))), h, n, body)

# a checked table as an SLIT: the N x N matrix must fit in the body
# (AcpiBadSize otherwise; N is limited to 65535)
def AcpiSlit.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiSlit>:
  match t:
    case H.AcpiSdt{h, +body}:
      slit.body(Nat.is_le(8n, B.Octets.len(body)), h, body)

def slit.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiSlit>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiSlit.of_sdt(t)

def AcpiSlit.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiSlit>:
  slit.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("SLIT"), o))

def slit.at(ok: Bool, +n: Nat, +m: B.Octets, +i: Nat, j: Nat) -> Maybe<&2, U32>:
  match ok:
    case False{}:
      None{}
    case True{}:
      B.Octets.at(m, Nat.add(Nat.mul(i, n), j))

# the distance from locality i to locality j, if both are below N
def AcpiSlit.distance(s: AcpiSlit, +i: Nat, +j: Nat) -> Maybe<&2, U32>:
  match s:
    case AcpiSlit{h, +n, m}:
      slit.at(Bool.and(Nat.is_lt(i, n), Nat.is_lt(j, n)), n, m, i, j)

# the table, from N and the matrix (fitted to N x N bytes)
def AcpiSlit.build(s: AcpiSlit) -> B.Octets:
  match s:
    case AcpiSlit{H.AcpiHeader{sg, l, r, c, o, t, orv, ci, cr}, +n, m}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("SLIT"), l, r, c, o, t, orv, ci, cr}, B.Octets.append(B.Octets.le64(W.W64.from_nat(n)), F.AcpiF.fit(Nat.mul(n, n), m)))
