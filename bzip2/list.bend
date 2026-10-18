# bend-osdev-bzip2, internal: the list helpers every stage uses.
#
# The stages keep their output in an accumulator, reversed, so that every
# loop over the data is a tail call; bz.push moves a list onto such an
# accumulator. The structural forms (bz.app, bz.rep) are what the proofs
# reason about.
import Base

# xs pushed onto acc one by one: (reverse xs) ++ acc, tail-recursively
def bz.push(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      bz.push(t, Con{h, acc})

def bz.rev(xs: List<&2, U32>) -> List<&2, U32>:
  bz.push(xs, Nil{})

# xs ++ ys, structurally (for proofs and short lists)
def bz.app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, bz.app(t, ys)}

# n copies of x, structurally
def bz.rep(n: Nat, +x: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{x, bz.rep(p, x)}

# n copies of x pushed onto acc, tail-recursively
def bz.push_rep(n: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      bz.push_rep(p, x, Con{x, acc})

# the length, tail-recursively
def bz.len.go(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      bz.len.go(t, 1n+n)

def bz.len(xs: List<&2, U32>) -> Nat:
  bz.len.go(xs, 0n)
