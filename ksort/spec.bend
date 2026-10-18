# bend-osdev-ksort, the vocabulary of its laws: what "sorted", "a
# permutation" and "stable" mean, as functions that run.
#
#   ksort.count(~A, ~f, xs)         how many elements satisfy f; two lists
#                                   are permutations of each other when
#                                   every f counts the same on both
#   ksort.sorted(~A, ~le, xs)       each element le the next
#   ksort.sorted_by(~A, ~key, xs)   each element's key at most the next's
#   ksort.keep(~A, ~key, k, xs)     the elements whose key is k, in order;
#                                   a sort by key is stable when keep of its
#                                   output is keep of its input, for every k
import Base

def ksort.count.add(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def ksort.count(~A: Data, ~f: A -> Bool, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+h, t}:
      ksort.count.add(f(h), ksort.count(~A, ~f, t))

# each element of xs le the next, x before them all
def ksort.sorted.from(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, +x: A) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+y, t}:
      Bool.and(le(x, y), ksort.sorted.from(~A, ~le, t, y))

def ksort.sorted(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      ksort.sorted.from(~A, ~le, t, x)

# each key at least k and at most the next
def ksort.sorted_by.from(~A: Data, ~key: A -> Nat, xs: List<&2, A>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+y, t}:
      +ky = key(y)
      Bool.and(Nat.is_le(k, ky), ksort.sorted_by.from(~A, ~key, t, ky))

def ksort.sorted_by(~A: Data, ~key: A -> Nat, xs: List<&2, A>) -> Bool:
  ksort.sorted_by.from(~A, ~key, xs, 0n)

def ksort.keep.put(-A: Data, b: Bool, x: A, r: List<&2, A>) -> List<&2, A>:
  match b:
    case True{}:
      Con{x, r}
    case False{}:
      r

def ksort.keep(~A: Data, ~key: A -> Nat, +k: Nat, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      ksort.keep.put(A, Nat.is_eq(key(h), k), h, ksort.keep(~A, ~key, k, t))
