# bend-osdev-selinux: small sets of indices as lists of bits.
#
# A set of types, permissions, categories, roles or booleans is a
# List<&2, Bool>: bit i (counting from the head, from 0) says whether index i
# is in the set. Trailing False bits do not change the set; SeBits.norm drops
# them, giving the canonical form (SeBits.is_norm). Every operation is a
# fold over the bits, so its laws are proved by induction (PROOF.bend).
import Base

def SeBits.empty() -> List<&2, Bool>:
  Nil{}

# index k is in the set
def SeBits.has(b: List<&2, Bool>, k: Nat) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{h, t}:
      match k:
        case 0n:
          h
        case 1n+p:
          SeBits.has(t, p)

# {k}
def SeBits.single(k: Nat) -> List<&2, Bool>:
  match k:
    case 0n:
      Con{True{}, Nil{}}
    case 1n+p:
      Con{False{}, SeBits.single(p)}

# {0, ..., n - 1}
def SeBits.full(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{True{}, SeBits.full(p)}

def SeBits.or(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      b
    case Con{x, xs}:
      match b:
        case Nil{}:
          Con{x, xs}
        case Con{y, ys}:
          Con{Bool.or(x, y), SeBits.or(xs, ys)}

def SeBits.and(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      match b:
        case Nil{}:
          Nil{}
        case Con{y, ys}:
          Con{Bool.and(x, y), SeBits.and(xs, ys)}

# a without the members of b
def SeBits.andnot(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      match b:
        case Nil{}:
          Con{x, xs}
        case Con{y, ys}:
          Con{Bool.and(x, Bool.not(y)), SeBits.andnot(xs, ys)}

def SeBits.xor(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      b
    case Con{x, xs}:
      match b:
        case Nil{}:
          Con{x, xs}
        case Con{y, ys}:
          Con{Bool.xor(x, y), SeBits.xor(xs, ys)}

def SeBits.of_list(ks: List<&2, Nat>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, t}:
      SeBits.or(SeBits.single(k), SeBits.of_list(t))

# the set is not empty
def SeBits.any(b: List<&2, Bool>) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(h, SeBits.any(t))

# every member of a is a member of b
def SeBits.subset(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{x, xs}:
      match b:
        case Nil{}:
          Bool.and(Bool.not(x), SeBits.subset(xs, Nil{}))
        case Con{y, ys}:
          Bool.and(Bool.or(Bool.not(x), y), SeBits.subset(xs, ys))

# the set with index k set to v
def SeBits.set(k: Nat, b: List<&2, Bool>, v: Bool) -> List<&2, Bool>:
  match k:
    case 0n:
      match b:
        case Nil{}:
          Con{v, Nil{}}
        case Con{h, t}:
          Con{v, t}
    case 1n+p:
      match b:
        case Nil{}:
          Con{False{}, SeBits.set(p, Nil{}, v)}
        case Con{h, t}:
          Con{h, SeBits.set(p, t, v)}

# the last bit of x, xs
def SeBits.last(xs: List<&2, Bool>, x: Bool) -> Bool:
  match xs:
    case Nil{}:
      x
    case Con{y, ys}:
      SeBits.last(ys, y)

# canonical: no trailing False bit
def SeBits.is_norm(b: List<&2, Bool>) -> Bool:
  match b:
    case Nil{}:
      True{}
    case Con{x, xs}:
      SeBits.last(xs, x)

def SeBits.norm.put(r: List<&2, Bool>, x: Bool) -> List<&2, Bool>:
  match r:
    case Nil{}:
      match x:
        case True{}:
          Con{True{}, Nil{}}
        case False{}:
          Nil{}
    case Con{y, ys}:
      Con{x, Con{y, ys}}

# the same set, canonical
def SeBits.norm(b: List<&2, Bool>) -> List<&2, Bool>:
  match b:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      SeBits.norm.put(SeBits.norm(xs), x)

def SeBits.to_list.go(b: List<&2, Bool>, +i: Nat) -> List<&2, Nat>:
  match b:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      match x:
        case True{}:
          Con{i, SeBits.to_list.go(xs, 1n+i)}
        case False{}:
          SeBits.to_list.go(xs, 1n+i)

# the members, in increasing order
def SeBits.to_list(b: List<&2, Bool>) -> List<&2, Nat>:
  SeBits.to_list.go(b, 0n)

def SeBits.to_u32.go(b: List<&2, Bool>, +w: U32, acc: U32) -> U32:
  match b:
    case Nil{}:
      acc
    case Con{x, xs}:
      match x:
        case True{}:
          SeBits.to_u32.go(xs, U32.shl(w), U32.or(acc, w))
        case False{}:
          SeBits.to_u32.go(xs, U32.shl(w), acc)

# members 0 to 31 as a 32-bit access vector (bit i for index i)
def SeBits.to_u32(b: List<&2, Bool>) -> U32:
  SeBits.to_u32.go(b, 1, 0)
