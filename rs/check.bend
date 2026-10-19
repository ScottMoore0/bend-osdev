import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./arith.bend as A
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as Sy
import ./bm.bend as Bm
import ./chien.bend as Ch
import ./rs.bend as D

def showl(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ " " ++ showl(t)

def showr(r: Result<&2, &2, E.RsError, List<&2, U32>>) -> String:
  match r:
    case Done{w}:
      showl(w)
    case Fail{e}:
      "fail"

def showfix(r: Result<&2, &2, E.RsError, D.RsFixed>) -> String:
  match r:
    case Done{x}:
      match x:
        case D.RsFixed{w, n}:
          showl(w) ++ " (" ++ Nat.show(n) ++ " corrected)"
    case Fail{e}:
      "fail"

def lf(r: Bm.RsLfsr) -> String:
  match r:
    case Bm.RsLfsr{c, l}:
      showl(c) ++ " L=" ++ Nat.show(l)

def cw(r: Result<&2, &2, E.RsError, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case Done{w}:
      w
    case Fail{e}:
      Nil{}

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def lst_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(U32.is_eq(x, y), lst_eq(s, t))
    case _ _:
      False{}

def ok(r: Result<&2, &2, E.RsError, List<&2, U32>>, +want: List<&2, U32>) -> Nat:
  match r:
    case Done{w}:
      one(lst_eq(w, want))
    case Fail{e}:
      0n

# Geisel's (15,9) example: the received word with errors at X^8 and X^2,
# and with errors at X^8 and X and erasures at X^7 and X^2
def recv() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 1, 14, 0, 5, 7, 3, 8, 5, 15]

def recv2() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 1, 11, 0, 5, 7, 3, 8, 10, 15]

# Every error pattern of weight at most 2 of a code with 2t = 4: on each
# word, for i <= j every position pair and values a (at i) and b (at j)
# from 0 to 2^m - 1; the count decoded to the message
def t8() -> C.RsCode:
  C.Rs.code(M.GfmField{3n, 11}, 1, 1, 4)

def pat.b(k: Nat, +c: C.RsCode, +w: List<&2, U32>, +msg: List<&2, U32>, +i: Nat, +j: Nat, +a: U32, +b: U32, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      pat.b(r, c, w, msg, i, j, a, U32.add(b, 1), Nat.add(acc, ok(D.Rs.decode(c, D.Rs.inject(D.Rs.inject(w, i, a), j, b), Nil{}), msg)))

def pat.a(k: Nat, +q: Nat, +c: C.RsCode, +w: List<&2, U32>, +msg: List<&2, U32>, +i: Nat, +j: Nat, +a: U32, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      pat.a(r, q, c, w, msg, i, j, U32.add(a, 1), pat.b(q, c, w, msg, i, j, a, 0, acc))

def pat.j(k: Nat, +q: Nat, +c: C.RsCode, +w: List<&2, U32>, +msg: List<&2, U32>, +i: Nat, +j: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      pat.j(r, q, c, w, msg, i, 1n+j, pat.a(q, q, c, w, msg, i, j, 0, acc))

def pat.i(k: Nat, +q: Nat, +n: Nat, +c: C.RsCode, +w: List<&2, U32>, +msg: List<&2, U32>, +i: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      pat.i(r, q, n, c, w, msg, 1n+i, pat.j(Nat.sub(n, i), q, c, w, msg, i, i, acc))

# all patterns of weight <= 2 added to the codeword of msg: decoded right
def all2(+c: C.RsCode, +q: Nat, +msg: List<&2, U32>) -> Nat:
  +w = cw(E.Rs.encode(c, msg))
  +n = List.length(&2, U32, w)
  pat.i(n, q, n, c, w, msg, 0n, 0n)

# how many patterns all2 tries: for i <= j, q^2 values each
def all2.count(+n: Nat, +q: Nat) -> Nat:
  Nat.mul(Nat.div(Nat.mul(n, 1n+n), 2n), Nat.mul(q, q))

# Erasures: every set of e erasures (as index lists) with junk values,
# and no errors
def era.junk(es: List<&2, Nat>, w: List<&2, U32>, +v: U32) -> List<&2, U32>:
  match es:
    case Nil{}:
      w
    case Con{i, t}:
      era.junk(t, D.Rs.inject(w, i, v), U32.add(U32.mul(v, 5), 3))

def era.one(+c: C.RsCode, +w: List<&2, U32>, +msg: List<&2, U32>, +es: List<&2, Nat>, +junk: U32) -> Nat:
  ok(D.Rs.decode(c, era.junk(es, w, junk), es), msg)

def main() -> IO(Unit):
  +g = C.Rs.geisel15_9()
  +f16 = M.Gfm.gf16()
  +t = t8()
  do IO<Unit>:
    IO.print(showl(C.Rs.generator(g)))
    IO.print(showr(E.Rs.encode(g, [0, 0, 0, 0, 0, 0, 0, 14, 0])))
    IO.print(showl(Sy.Rs.syndromes(g, recv())))
    IO.print(lf(Bm.RsBm.lfsr(f16, Sy.Rs.syndromes(g, recv()))))
    IO.print(showl(Ch.RsChien.roots(f16, [1, 1, 7], C.Rs.beta_inv(g), 15)))
    IO.print(showfix(D.Rs.correct(g, recv(), Nil{})))
    IO.print(showfix(D.Rs.correct(g, recv2(), [7n, 12n])))
    IO.print(showr(D.Rs.decode(g, recv2(), Nil{})))
    IO.print(lf(Bm.RsBm.lfsr(f16, [1, 0, 1, 0, 0])))
    IO.print(Nat.show(all2(t, 8n, [3, 5, 6])) ++ " of " ++ Nat.show(all2.count(7n, 8n)))
    IO.print(Nat.show(all2(t, 8n, [0, 0, 0])) ++ " of " ++ Nat.show(all2.count(7n, 8n)))
    IO.print(Nat.show(all2(t, 8n, [7])) ++ " of " ++ Nat.show(all2.count(5n, 8n)))
    IO.print(Nat.show(all2(g, 16n, [9, 1, 4, 15, 0, 7, 2, 12, 11])) ++ " of " ++ Nat.show(all2.count(15n, 16n)))
    IO.print(Nat.show(Nat.add(era.one(t, cw(E.Rs.encode(t, [3, 5, 6])), [3, 5, 6], [0n, 2n, 4n, 6n], 1), era.one(g, cw(E.Rs.encode(g, [1, 2, 3])), [1, 2, 3], [0n, 1n, 2n, 3n, 4n, 5n], 9))))
    IO.print(showr(E.Rs.encode(t, [1, 2, 3, 4])))
    IO.print(showr(D.Rs.decode(t, [1, 2, 3], Nil{})))
    IO.print(showr(D.Rs.decode(t, cw(E.Rs.encode(t, [1, 2, 3])), [9n])))
    IO.print(showr(D.Rs.decode(t, cw(E.Rs.encode(t, [1, 2, 3])), [1n, 1n])))
    IO.print(U32.show(A.RsGf.inv(M.Gfm.bch13(), 1234)))

#|12 10 12 3 9 7 1
#|0 0 0 0 0 0 0 14 0 5 7 3 9 5 15
#|1 1 6 1 0 7
#|1 1 7 L=2
#|2 8
#|0 0 0 0 0 0 0 14 0 5 7 3 9 5 15 (2 corrected)
#|0 0 0 0 0 0 0 14 0 5 7 3 9 5 15 (4 corrected)
#|fail
#|1 L=3
#|1792 of 1792
#|1792 of 1792
#|960 of 960
#|30720 of 30720
#|2
#|fail
#|fail
#|fail
#|fail
#|2297
