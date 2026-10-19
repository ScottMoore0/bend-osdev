# bend-osdev-asn1, numbers in octets: the digits of a natural number in a
# base, read back by Horner's rule; the base-128 form with bit 8 set on every
# octet but the last (X.690 8.1.2.4.2 for high tag numbers, 8.19.2 for
# object identifier subidentifiers); and the unsigned big-endian form of the
# long length octets (8.1.3.5). Internal: the public readers and writers are
# in tag.bend, length.bend and the typed files.
#
# Bend evaluates arguments before a call, so a recursive def that must stop
# takes the test for stopping as a parameter, computed by its caller
# (a1.digits.go's lt, a1.r128's more).
import Base
import ../bytes/bytes.bend as B

# A number read from octets: its value, the octets it took, and the rest
type A1Num is Data:
  A1Num{value: Nat, used: List<&2, U32>, rest: List<&2, U32>}

# the byte of a value below 256 (the encoder's form of a byte: masked)
def a1.b(n: Nat) -> U32:
  B.byte(U32.from_nat(n))

# the digits of n in base b (b at least 2), most significant first; [n]
# when n < b (lt says whether n < b; fuel bounds the digits)
def a1.digits.go(fuel: Nat, lt: Bool, +b: Nat, +n: Nat) -> List<&2, Nat>:
  match fuel lt:
    case _ True{}:
      [n]
    case 0n False{}:
      [n]
    case 1n+f False{}:
      +q = Nat.div(n, b)
      List.append(&2, Nat, a1.digits.go(f, Nat.is_lt(q, b), b, q), [Nat.mod(n, b)])

def a1.digits(+b: Nat, +n: Nat) -> List<&2, Nat>:
  a1.digits.go(n, Nat.is_lt(n, b), b, n)

# Horner's rule: the value of digits ds in base b, after acc
def a1.horner(ds: List<&2, Nat>, +b: Nat, acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      a1.horner(t, b, Nat.add(Nat.mul(acc, b), d))

# each digit as a byte
def a1.bytes_of(ds: List<&2, Nat>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{a1.b(d), a1.bytes_of(t)}

def a1.enc128.c(d: Nat, t: List<&2, Nat>, rest: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Nil{}:
      [a1.b(d)]
    case Con{e, u}:
      Con{a1.b(Nat.add(128n, d)), rest}

# base-128 digits as octets: bit 8 set on all but the last
def a1.enc128(ds: List<&2, Nat>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, +t}:
      a1.enc128.c(d, t, a1.enc128(t))

# n in base-128 octets (a high tag number, a subidentifier)
def a1.b128(+n: Nat) -> List<&2, U32>:
  a1.enc128(a1.digits(128n, n))

# n as unsigned big-endian octets, as few as there can be (one for 0)
def a1.be(+n: Nat) -> List<&2, U32>:
  a1.bytes_of(a1.digits(256n, n))

def a1.num_cons(x: U32, m: Maybe<&2, A1Num>) -> Maybe<&2, A1Num>:
  match m:
    case None{}:
      None{}
    case Some{A1Num{v, u, r}}:
      Some{A1Num{v, Con{x, u}, r}}

# reading base-128 octets while the last had bit 8 set (more), at most k
# more of them; acc is the value so far. None if the octets end first or
# there are more than k.
def a1.r128(xs: List<&2, U32>, more: Bool, k: Nat, +acc: Nat) -> Maybe<&2, A1Num>:
  match xs more k:
    case _ False{} _:
      Some{A1Num{acc, Nil{}, xs}}
    case Nil{} True{} _:
      None{}
    case Con{x, t} True{} 0n:
      None{}
    case Con{+x, t} True{} 1n+j:
      +v = U32.to_nat(x)
      +ge = Nat.is_le(128n, v)
      a1.num_cons(x, a1.r128(t, ge, j, Nat.add(Nat.mul(acc, 128n), Nat.sub(v, Bool.pick(Nat, ge, 128n, 0n)))))

# The implementation's bound on numbers read from octets: Bend's natural
# numbers are immediate values below 2^48 at run time, so a base-128 number
# (a high tag number, a subidentifier) has at most six octets (42 bits) and
# a length at most six octets (48 bits)
def a1.max_octets() -> Nat:
  6n

# the value of big-endian octets, after acc
def a1.fold256(xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      a1.fold256(t, Nat.add(Nat.mul(acc, 256n), U32.to_nat(x)))

def a1.rbe.pick(ok: Bool, +k: Nat, +xs: List<&2, U32>) -> Maybe<&2, A1Num>:
  match ok:
    case True{}:
      +u = B.take(k, xs)
      Some{A1Num{a1.fold256(u, 0n), u, B.drop(k, xs)}}
    case False{}:
      None{}

# k big-endian octets; None if there are fewer
def a1.rbe(+k: Nat, +xs: List<&2, U32>) -> Maybe<&2, A1Num>:
  a1.rbe.pick(Nat.is_le(k, List.length(&2, U32, xs)), k, xs)

# element-wise equality of byte lists
def a1.leq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(U32.is_eq(a, b), a1.leq(s, t))
    case _ _:
      False{}
