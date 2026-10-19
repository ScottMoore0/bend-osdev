# Byte-string helpers the modes and MACs share: XOR of two byte strings, a
# byte repeated, and a message cut into pieces of a block size.
import Base
import ../bytes/bytes.bend as B

# xs xor ys, element by element, over xs's length (a missing element of ys
# counts as 0)
def cr.oct.xorl(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Con{U32.xor(x, 0), cr.oct.xorl(xt, Nil{})}
        case Con{y, yt}:
          Con{U32.xor(x, y), cr.oct.xorl(xt, yt)}

# a xor b, byte by byte, over a's length (b's missing bytes count as 0)
def CrOct.xor(a: B.Octets, b: B.Octets) -> B.Octets:
  B.Octets.of_list(cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(b)))

def cr.oct.rep(n: Nat, +b: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{b, cr.oct.rep(p, b)}

# the byte b, n times
def CrOct.rep(n: Nat, +b: U32) -> B.Octets:
  B.Octets.of_list(cr.oct.rep(n, b))

def cr.oct.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      cr.oct.rev(t, Con{h, acc})

def cr.oct.revs(xs: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      cr.oct.revs(t, Con{h, acc})

def cr.oct.flush(cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      Con{cr.oct.rev(Con{h, t}, Nil{}), acc}

def cr.oct.pieces.step(full: Bool, +c: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match full:
    case True{}:
      Con{cr.oct.rev(c, Nil{}), acc}
    case False{}:
      acc

def cr.oct.pieces.cur(full: Bool, +c: List<&2, U32>) -> List<&2, U32>:
  match full:
    case True{}:
      Nil{}
    case False{}:
      c

def cr.oct.pieces.i(full: Bool, +i: Nat) -> Nat:
  match full:
    case True{}:
      0n
    case False{}:
      i

# the pieces of xs, last first: whole n-byte pieces, then what is left
# (cur: the piece being filled, reversed, i bytes long)
def cr.oct.pieces.go(xs: List<&2, U32>, +n: Nat, +i: Nat, +cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      cr.oct.flush(cur, acc)
    case Con{x, t}:
      +c : List<&2, U32> = Con{x, cur}
      +full = Nat.is_eq(1n+i, n)
      cr.oct.pieces.go(t, n, cr.oct.pieces.i(full, 1n+i), cr.oct.pieces.cur(full, c), cr.oct.pieces.step(full, c, acc))

# xs cut into pieces of n bytes, in order: every piece but the last has n
# bytes, the last 1 to n (no pieces for no bytes)
def CrOct.pieces(n: Nat, xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  cr.oct.revs(cr.oct.pieces.go(xs, n, 0n, Nil{}, Nil{}), Nil{})
