import Base
import ../word64/word64.bend as W
import ./algo.bend as A
import ./bitmap.bend as M
import ./bsearch.bend as S

def show_maybe(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      Nat.show(v)

def fill(xs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{x, t}:
      fill(t, U32.inc(i), Array.set(U32, a, i, x))

def show_val(r: Array<U32> & U32) -> String:
  (a, x) = r
  U32.show(x)

def show_opt(r: Array<U32> & Maybe<&2, U32>) -> String:
  (a, m) = r
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

def sorted() -> List<&2, U32>:
  [2, 3, 5, 7, 11, 13, 17, 19]

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(A.bits32.popcount(3735928559)))
    IO.print(Nat.show(A.bits32.ffs(40)) ++ " " ++ Nat.show(A.bits32.fls(40)))
    IO.print(Nat.show(A.bits32.ctz(40)) ++ " " ++ Nat.show(A.bits32.clz(40)))
    IO.print(show_maybe(A.bits32.first_set(0)) ++ " " ++ show_maybe(A.bits32.last_set(2147483648)))
    IO.print(Nat.show(A.bits64.ctz(W.W64.from_parts(16, 0))) ++ " " ++ Nat.show(A.bits64.clz(W.W64.from_parts(16, 0))))
    IO.print(Nat.show(A.bits64.popcount(W.W64.max())))
    IO.print(Nat.show(M.bitmap.next_set([0, 8], 64n, 3n)) ++ " " ++ Nat.show(M.bitmap.next_clear([4294967295, 1], 64n, 0n)))
    IO.print(Nat.show(M.bitmap.first_set([0, 0], 64n)))
    IO.print(Nat.show(S.bsearch.lower_bound(sorted(), 12)) ++ " " ++ show_maybe(S.bsearch.find(sorted(), 13)))
    IO.print(show_val(S.bsearch.array_lower_bound(fill(sorted(), 0, [0 : U32*8n]), 8, 12)) ++ " " ++ show_opt(S.bsearch.array_find(fill(sorted(), 0, [0 : U32*8n]), 8, 4)))

#|24
#|4 6
#|3 26
#|none 31
#|36 27
#|64
#|35 33
#|64
#|5 5
#|5 none
