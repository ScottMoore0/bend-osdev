# bend-osdev-asn1, length octets (ITU-T X.690 (02/2021) 8.1.3): the definite
# short form (one octet, bit 8 zero, 8.1.3.4), the definite long form (an
# initial octet 80 hex + k, k from 1 to 126, then k octets of the length,
# big-endian, 8.1.3.5; FF is not used), and the indefinite form (80 hex,
# 8.1.3.6). The encoder writes the definite form in the fewest octets, as
# DER requires (10.1).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./number.bend as Nu

# Length octets, read: a definite length (with the octets it took), the
# indefinite form, or an error
type A1Len is Data:
  A1LDef{len: Nat, used: List<&2, U32>, rest: List<&2, U32>}
  A1LIndef{rest: List<&2, U32>}
  A1LErr{error: E.Asn1Error}

def a1.len_pick(lt: Bool, +n: Nat) -> List<&2, U32>:
  match lt:
    case True{}:
      [Nu.a1.b(n)]
    case False{}:
      +ds = Nu.a1.be(n)
      Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, ds))), ds}

# the definite length octets of n, as few as possible (8.1.3.3, 10.1)
def a1.len_bytes(+n: Nat) -> List<&2, U32>:
  a1.len_pick(Nat.is_lt(n, 128n), n)

def a1.len_ok.pick(lt: Bool, +n: Nat) -> Bool:
  match lt:
    case True{}:
      True{}
    case False{}:
      Nat.is_le(List.length(&2, U32, Nu.a1.be(n)), Nu.a1.max_octets())

# whether n has length octets here: the long form holds at most 126 octets
# (8.1.3.5), and this implementation reads at most six (number.bend)
def a1.len_ok(+n: Nat) -> Bool:
  a1.len_ok.pick(Nat.is_lt(n, 128n), n)

def a1.len.bytes(y: U32, m: Maybe<&2, Nu.A1Num>) -> A1Len:
  match m:
    case None{}:
      A1LErr{E.Asn1Truncated{}}
    case Some{Nu.A1Num{n, u, r}}:
      A1LDef{n, Con{y, u}, r}

def a1.len.many(big: Bool, +k: Nat, y: U32, +t: List<&2, U32>) -> A1Len:
  match big:
    case True{}:
      A1LErr{E.Asn1TooLong{}}
    case False{}:
      a1.len.bytes(y, Nu.a1.rbe(k, t))

def a1.len.reserved(is127: Bool, +k: Nat, y: U32, +t: List<&2, U32>) -> A1Len:
  match is127:
    case True{}:
      A1LErr{E.Asn1BadLength{}}
    case False{}:
      a1.len.many(Nat.is_lt(Nu.a1.max_octets(), k), k, y, t)

def a1.len.long(+k: Nat, y: U32, +t: List<&2, U32>) -> A1Len:
  match k:
    case 0n:
      A1LIndef{t}
    case 1n+j:
      a1.len.reserved(Nat.is_eq(k, 127n), k, y, t)

def a1.len.first(lt: Bool, +v: Nat, y: U32, +t: List<&2, U32>) -> A1Len:
  match lt:
    case True{}:
      A1LDef{v, [y], t}
    case False{}:
      a1.len.long(Nat.sub(v, 128n), y, t)

# the length octets at the start of xs
def a1.len.read(xs: List<&2, U32>) -> A1Len:
  match xs:
    case Nil{}:
      A1LErr{E.Asn1Truncated{}}
    case Con{+y, +t}:
      +v = U32.to_nat(y)
      a1.len.first(Nat.is_lt(v, 128n), v, y, t)
