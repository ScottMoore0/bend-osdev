import Base
import ./ksort.bend as K
import ./spec.bend as S
import ./heapsort.bend as H

def show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "-"
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ "," ++ show(t)

# an array of depth d, every slot 9, with xs written from slot 0
def fill.go(xs: List<&2, U32>, a: Array<U32>, +i: U32) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{x, t}:
      fill.go(t, Array.set(U32, a, i, x), U32.inc(i))

def fill(d: Nat, xs: List<&2, U32>) -> Array<U32>:
  fill.go(xs, Array.new(U32, d, 9), 0)

# Array.to_list's list, as a reusable one
def slots(xs: List<&1, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{x, slots(t)}

def heap(+xs: List<&2, U32>) -> List<&2, U32>:
  slots(Array.to_list(~U32, H.ksort.heap_sort(~U32, ~U32.is_le, fill(3n, xs), U32.from_nat(List.length(&2, U32, xs)))))

# the list of len digits (base 4) of k, lowest first
def digits(len: Nat, +k: U32) -> List<&2, U32>:
  match len:
    case 0n:
      Nil{}
    case 1n+p:
      Con{U32.and(k, 3), digits(p, U32.shrn(k, 2n))}

def eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(U32.is_eq(x, y), eq(xt, yt))
    case _ _:
      False{}

def pad(+n: Nat) -> List<&2, U32>:
  List.replicate(U32, Nat.sub(8n, n), 9)

# heap_sort agrees with list_sort on xs, and leaves the slots past it alone
def agree(+xs: List<&2, U32>) -> Bool:
  eq(heap(xs), List.append(&2, U32, K.ksort.list_sort(~U32, ~U32.is_le, xs), pad(List.length(&2, U32, xs))))

# every list of len elements from 0 to 3: the number that disagree
def exhaust.go(fuel: Nat, +len: Nat, +k: U32, +bad: Nat) -> Nat:
  match fuel:
    case 0n:
      bad
    case 1n+f:
      exhaust.go(f, len, U32.inc(k), Bool.pick(Nat, agree(digits(len, k)), bad, 1n+bad))

def exhaust(+len: Nat) -> Nat:
  exhaust.go(Nat.pow(4n, len), len, 0, 0n)

def exhaust_all(+n: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      Nat.add(acc, exhaust(0n))
    case 1n+p:
      exhaust_all(p, Nat.add(acc, exhaust(1n+p)))

def key16(x: U32) -> Nat:
  U32.to_nat(U32.shrn(x, 4n))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(K.ksort.list_sort(~U32, ~U32.is_le, [5, 3, 9, 1, 4, 1, 8])))
    IO.print(show(K.ksort.list_sort(~U32, ~U32.is_ge, [5, 3, 9, 1, 4, 1, 8])))
    IO.print(show(K.ksort.list_sort_by(~U32, ~key16, [32, 17, 34, 3, 20, 37])))
    IO.print(Nat.show(S.ksort.count(~U32, ~(x => U32.is_lt(x, 4)), K.ksort.list_sort(~U32, ~U32.is_le, [5, 3, 9, 1, 4, 1, 8]))))
    IO.print(show(heap([5, 3, 9, 1, 4, 1, 8])))
    IO.print(show(slots(Array.to_list(~U32, H.ksort.heap_sort(~U32, ~U32.is_le, fill(2n, [4, 3, 2, 1]), 3)))))
    IO.print(show(slots(Array.to_list(~U32, H.ksort.heap_sort_by(~U32, ~key16, fill(3n, [32, 17, 34, 3, 20, 37]), 6)))))
    IO.print("exhaustive: " ++ Nat.show(exhaust_all(7n, 0n)) ++ " of 21845 lists differ")

#|1,1,3,4,5,8,9
#|9,8,5,4,3,1,1
#|3,17,20,32,34,37
#|3
#|1,1,3,4,5,8,9,9
#|2,3,4,1
#|3,17,20,34,37,32,9,9
#|exhaustive: 0 of 21845 lists differ
