# Byte-string helpers the encodings share: XOR over the first operand's
# length, a byte repeated, the leftmost bits of a string cleared, and
# whether a string is all zeros.
import Base
import ../bytes/bytes.bend as B

# a XOR b over a's length (b's missing bytes taken as 0)
def rsa.xor(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Con{U32.xor(x, y), rsa.xor(xt, yt)}
    case Con{x, xt} Nil{}:
      Con{x, rsa.xor(xt, Nil{})}
    case Nil{} _:
      Nil{}

def RsaOct.xor(a: B.Octets, b: B.Octets) -> B.Octets:
  B.Octets.of_list(rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b)))

def rsa.rep(n: Nat, +b: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{b, rsa.rep(p, b)}

# n copies of the byte b
def RsaOct.rep(n: Nat, +b: U32) -> B.Octets:
  B.Octets.of_list(rsa.rep(n, b))

def rsa.allz(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(U32.is_zero(x), rsa.allz(t))

# whether every byte is 0
def RsaOct.all_zero(o: B.Octets) -> Bool:
  rsa.allz(B.Octets.to_list(o))

def rsa.nozero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(Bool.not(U32.is_zero(x)), rsa.nozero(t))

# whether no byte is 0
def RsaOct.no_zero(o: B.Octets) -> Bool:
  rsa.nozero(B.Octets.to_list(o))

# the first element ANDed with s
def rsa.mask1(xs: List<&2, U32>, +s: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.and(x, s), t}

# the first byte ANDed with s
def RsaOct.mask_first(o: B.Octets, +s: U32) -> B.Octets:
  B.Octets.of_list(rsa.mask1(B.Octets.to_list(o), s))

# the leftmost bits bits (0 to 8) of the first byte set to 0
def RsaOct.clear_left(o: B.Octets, +bits: Nat) -> B.Octets:
  RsaOct.mask_first(o, U32.shrn(255, bits))

def rsa.sep.go(z: Bool, one: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match z one:
    case True{} _:
      Maybe.map(&2, Nat, Nat, i => 1n+i, rest)
    case False{} True{}:
      Some{0n}
    case False{} False{}:
      None{}

# the index of the first nonzero byte, if it is 0x01 (the separator of
# EME-OAEP's and EMSA-PSS's data blocks), or None
def rsa.sep(xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, t}:
      rsa.sep.go(U32.is_zero(x), U32.is_eq(x, 1), rsa.sep(t))

# the first byte (0 for an empty string)
def RsaOct.first(o: B.Octets) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, 0n), 0)

# the last byte (0 for an empty string)
def RsaOct.last(+o: B.Octets) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, Nat.sub(B.Octets.len(o), 1n)), 0)
