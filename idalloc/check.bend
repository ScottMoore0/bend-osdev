import Base
import ./idalloc.bend as I

def show_id(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{i}:
      Nat.show(i)

def show_ids(ks: List<&2, Nat>) -> String:
  match ks:
    case Nil{}:
      "-"
    case Con{k, Nil{}}:
      Nat.show(k)
    case Con{k, t}:
      Nat.show(k) ++ "," ++ show_ids(t)

def show_err(r: Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>) -> String:
  match r:
    case Done{I.IdrAlloc{t, i}}:
      Nat.show(i)
    case Fail{I.IdExhausted{}}:
      "IdExhausted"
    case Fail{I.IdBadRange{}}:
      "IdBadRange"
    case Fail{I.IdNotFound{}}:
      "IdNotFound"

def show_m(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

# allocate n IDs from s, with the default range
def take(n: Nat, +s: I.Idr<Unit>) -> I.Idr<Unit>:
  match n:
    case 0n:
      s
    case 1n+p:
      take(p, I.ida.state(I.ida.alloc(s), s))

def four() -> I.Idr<Unit>:
  take(4n, I.ida.new())

def handles() -> I.Idr<U32>:
  I.idr.state(U32, I.idr.alloc(U32, I.idr.state(U32, I.idr.alloc(U32, I.idr.new(U32), 100), I.idr.new(U32)), 200), I.idr.new(U32))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_ids(I.ida.ids(four())))
    IO.print(show_id(I.ida.id(I.ida.alloc(I.ida.free(I.ida.free(four(), 2n), 1n)))))
    IO.print(show_id(I.ida.id(I.ida.alloc_min(four(), 2n))))
    IO.print(show_id(I.ida.id(I.ida.alloc_min(I.ida.new(), 1000n))))
    IO.print(show_err(I.ida.alloc_range(four(), I.IdRange{0n, 3n})))
    IO.print(show_err(I.ida.alloc_range(four(), I.IdRange{5n, 4n})))
    IO.print(Bool.show(I.ida.in_use(four(), 3n)) ++ " " ++ Bool.show(I.ida.in_use(I.ida.free(four(), 3n), 3n)))
    IO.print(show_m(I.idr.find(U32, handles(), 1n)) ++ " " ++ show_m(I.idr.find(U32, handles(), 2n)))

#|0,1,2,3
#|1
#|4
#|1000
#|IdExhausted
#|IdBadRange
#|True False
#|200 none
