# bend-osdev-ksort: a stable merge sort on lists, the counterpart of the
# kernel's list_sort.
#
# The comparison is a template argument ~le: le(a, b) says that a may come
# before b. ksort.list_sort is stable: of two elements that compare equal
# (each le the other), the one first in the input stays first. It splits the
# list into its front and back halves, sorts each, and merges them; the
# merge takes from the front half while le(front, back) holds, which is what
# keeps it stable.
#
# ksort.list_sort_by sorts by a Nat key, the form the sortedness and
# stability laws are proved for (see the README).
import Base

# Merging

# x <> xt and y <> yt merged, where c is le(x, y): the comparison of the
# heads is passed in, so that each step matches on a parameter
def ksort.merge.go(~A: Data, ~le: A -> A -> Bool, xt: List<&2, A>, yt: List<&2, A>, c: Bool, +x: A, +y: A) -> List<&2, A>:
  match xt yt c:
    case Nil{} ys True{}:
      Con{x, Con{y, ys}}
    case Con{+x2, xt2} ys True{}:
      Con{x, ksort.merge.go(~A, ~le, xt2, ys, le(x2, y), x2, y)}
    case xs Nil{} False{}:
      Con{y, Con{x, xs}}
    case xs Con{+y2, yt2} False{}:
      Con{y, ksort.merge.go(~A, ~le, xs, yt2, le(x, y2), x, y2)}

# two sorted lists merged into one; on ties the element of xs comes first
def ksort.merge(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs ys:
    case Nil{} b:
      b
    case Con{x, xt} Nil{}:
      Con{x, xt}
    case Con{+x, xt} Con{+y, yt}:
      ksort.merge.go(~A, ~le, xt, yt, le(x, y), x, y)

# Sorting

# n / 2, rounded down
def ksort.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+ksort.half(q)

# the merge sort, with fuel bounding the depth: a list of at most fuel
# elements is sorted (ksort.list_sort passes the length)
def ksort.msort(~A: Data, ~le: A -> A -> Bool, +fuel: Nat, xs: List<&2, A>) -> List<&2, A>:
  match fuel xs:
    case 0n ys:
      ys
    case 1n+f Nil{}:
      Nil{}
    case 1n+f Con{x, Nil{}}:
      Con{x, Nil{}}
    case 1n+f Con{x, Con{y, t}}:
      +ys = {Con{x, Con{y, t}} : List<&2, A>}
      +h = ksort.half(List.length(&2, A, ys))
      ksort.merge(~A, ~le, ksort.msort(~A, ~le, f, List.take(&2, A, ys, h)), ksort.msort(~A, ~le, f, List.drop(&2, A, ys, h)))

# xs sorted by le, stably (list_sort)
def ksort.list_sort(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> List<&2, A>:
  ksort.msort(~A, ~le, List.length(&2, A, xs), xs)

# xs sorted by a Nat key, smallest first, stably: list_sort with
# le(a, b) = key(a) <= key(b)
def ksort.list_sort_by(~A: Data, ~key: A -> Nat, xs: List<&2, A>) -> List<&2, A>:
  ksort.list_sort(~A, ~(a => b => Nat.is_le(key(a), key(b))), xs)
