# bend-osdev-array: laws about Base's Array, the specification they are
# stated in, and the list model they are stated against.
#
# Base defines Array<T> in Bend itself, as a tree of ALeaf / ANode, and
# indexes it by U32 (Array.size, Array.swap, Array.set, Array.get, Array.new).
# An array built by Array.new(T, d, v) is a perfect tree of depth d: 2^d
# slots, every leaf at depth d. Array.get and Array.set mask the index to its
# low d bits, so they read and write slot `Arrays.index(d, i)`.
#
# This file holds only the vocabulary the laws use; LAWS.bend states them and
# PROOF.bend proves them.
import Base

# 2^d, the slot count of an array of depth d
def Arrays.slots(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Arrays.slots(p))

# whether a is a perfect tree of depth d (every leaf at depth d), the shape
# Array.new builds and Array.set keeps
def Arrays.is_perfect(-T: Type, +d: Nat, a: Array<T>) -> Bool:
  match d a:
    case 0n ALeaf{x}:
      True{}
    case 0n ANode{xs, ys}:
      False{}
    case 1n+p ALeaf{x}:
      False{}
    case 1n+p ANode{xs, ys}:
      Bool.and(Arrays.is_perfect(T, p, xs), Arrays.is_perfect(T, p, ys))

# the slots of an array, in index order: the list model the laws compare
# Array.get and Array.set with (a specification: it walks the whole array)
def Arrays.leaves(-T: Data, a: Array<T>) -> List<&2, T>:
  match a:
    case ALeaf{x}:
      Con{x, Nil{}}
    case ANode{xs, ys}:
      List.append(&2, T, Arrays.leaves(T, xs), Arrays.leaves(T, ys))

# the slot that Array.get and Array.set use for index i on an array of depth
# d: i masked to its low d bits, as Base computes it
def Arrays.index(d: Nat, i: U32) -> Nat:
  U32.to_nat(U32.and(i, U32.sub(U32.shln(1, d), 1)))

# The list model's element at slot k, or fill past its end
def Arrays.nth.or(-T: Data, m: Maybe<&2, T>, fill: T) -> T:
  match m:
    case Some{x}:
      x
    case None{}:
      fill

def Arrays.nth(-T: Data, xs: List<&2, T>, k: Nat, fill: T) -> T:
  Arrays.nth.or(T, List.get(&2, T, xs, k), fill)

# The perfect array of depth d whose slots are xs in order (cut to 2^d
# slots, or padded with fill): an array built from a Data list, so that a
# proof can name it as often as it likes (a specification, like leaves)
def Arrays.of_list(-T: Data, +d: Nat, +xs: List<&2, T>, +fill: T) -> Array<T>:
  match d:
    case 0n:
      ALeaf{Arrays.nth(T, xs, 0n, fill)}
    case 1n+p:
      +s = Arrays.slots(p)
      ANode{Arrays.of_list(T, p, List.take(&2, T, xs, s), fill), Arrays.of_list(T, p, List.drop(&2, T, xs, s), fill)}
