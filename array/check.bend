import Base
import ./array.bend as A

# Arrays.is_perfect and Arrays.leaves are specifications: they match on
# ALeaf / ANode for any element type, which the compiled runtime (holding an
# array natively) does not run, so they appear in laws only (LAWS.bend has
# their vectors). Base's Array.to_list lists the same slots at run time.

def show_list(xs: List<U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      U32.show(h) ++ " " ++ show_list(t)

# a depth-3 array (8 slots) with slots 1, 5 and 6 written (14 wraps to 6)
def sample() -> Array<U32>:
  a = Array.new(U32, 3n, 0)
  a = Array.set(U32, a, 1, 10)
  a = Array.set(U32, a, 5, 50)
  Array.set(U32, a, 14, 60)

# the reads of indices from i on, n of them (r: the read of index i)
def reads.go(n: Nat, +i: U32, r: Array<U32> & U32) -> String:
  match n:
    case 0n:
      (a, x) = r
      U32.show(x)
    case 1n+p:
      (a, x) = r
      U32.show(x) ++ " " ++ reads.go(p, U32.add(i, 1), Array.get(U32, a, U32.add(i, 1)))

def reads(n: Nat, a: Array<U32>) -> String:
  reads.go(n, 0, Array.get(U32, a, 0))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(reads(9n, sample()))
    IO.print(show_list(Array.to_list(~U32, sample())))
    IO.print(Nat.show(A.Arrays.index(3n, 14)) ++ " " ++ Nat.show(A.Arrays.slots(3n)))

#|0 10 0 0 0 50 60 0 0 10
#|0 10 0 0 0 50 60 0 
#|6 8
