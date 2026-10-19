import Base
import ../bytes/bytes.bend as B
import ../gf/gfm.bend as M
import ./code.bend as C
import ./bits.bend as T
import ./encode.bend as E
import ./syndrome.bend as S
import ./bch.bend as D

def showb(xs: List<&2, Bool>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{b, t}:
      match b:
        case True{}:
          "1" ++ showb(t)
        case False{}:
          "0" ++ showb(t)

def showl(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ " " ++ showl(t)

def showfix(r: Result<&2, &2, E.BchError, D.BchFixed>) -> String:
  match r:
    case Done{x}:
      match x:
        case D.BchFixed{w, n}:
          showb(w) ++ " (" ++ Nat.show(n) ++ " flipped)"
    case Fail{e}:
      "fail"

def showdec(r: Result<&2, &2, E.BchError, D.BchDecoded>) -> String:
  match r:
    case Done{x}:
      match x:
        case D.BchDecoded{d, e, n}:
          B.Octets.hex(e) ++ " (" ++ Nat.show(n) ++ " flipped)"
    case Fail{e}:
      "fail"

def showo(r: Result<&2, &2, E.BchError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      "fail"

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def beq(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(Bool.not(Bool.xor(x, y)), beq(s, t))
    case _ _:
      False{}

def ok(r: Result<&2, &2, E.BchError, List<&2, Bool>>, +want: List<&2, Bool>) -> Nat:
  match r:
    case Done{w}:
      one(beq(w, want))
    case Fail{e}:
      0n

# the k-bit message of the number v, most significant bit first
def msg(k: Nat, +v: U32) -> List<&2, Bool>:
  match k:
    case 0n:
      Nil{}
    case 1n+(+j):
      Con{Bool.not(U32.is_eq(U32.and(U32.shrn(v, j), 1), 0)), msg(j, v)}

# every pattern of up to two flipped bits (i <= j) of the codeword of msg:
# the number decoded back to msg
def p2.j(k: Nat, +c: C.BchCode, +w: List<&2, Bool>, +m: List<&2, Bool>, +i: Nat, +j: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      p2.j(r, c, w, m, i, 1n+j, Nat.add(acc, ok(D.Bch.decode_bits(c, D.Bch.flip_at(D.Bch.flip_at(w, i), j)), m)))

def p2.i(k: Nat, +n: Nat, +c: C.BchCode, +w: List<&2, Bool>, +m: List<&2, Bool>, +i: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      p2.i(r, n, c, w, m, 1n+i, p2.j(Nat.sub(n, i), c, w, m, i, i, acc))

# ... and of up to three
def p3.k(k: Nat, +c: C.BchCode, +w: List<&2, Bool>, +m: List<&2, Bool>, +i: Nat, +j: Nat, +l: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      p3.k(r, c, w, m, i, j, 1n+l, Nat.add(acc, ok(D.Bch.decode_bits(c, D.Bch.flip_at(D.Bch.flip_at(D.Bch.flip_at(w, i), j), l)), m)))

def p3.j(k: Nat, +n: Nat, +c: C.BchCode, +w: List<&2, Bool>, +m: List<&2, Bool>, +i: Nat, +j: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      p3.j(r, n, c, w, m, i, 1n+j, p3.k(Nat.sub(n, j), c, w, m, i, j, j, acc))

def p3.i(k: Nat, +n: Nat, +c: C.BchCode, +w: List<&2, Bool>, +m: List<&2, Bool>, +i: Nat, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+r:
      p3.i(r, n, c, w, m, 1n+i, p3.j(Nat.sub(n, i), n, c, w, m, i, i, acc))

def all.pick(three: Bool, +n: Nat, +c: C.BchCode, +w: List<&2, Bool>, +m: List<&2, Bool>) -> Nat:
  match three:
    case True{}:
      p3.i(n, n, c, w, m, 0n, 0n)
    case False{}:
      p2.i(n, n, c, w, m, 0n, 0n)

# n pseudo-random bytes

# every message of k bits, every pattern of up to t = 2 or 3 flips
def all.m(cnt: Nat, +c: C.BchCode, +k: Nat, +three: Bool, +v: U32, acc: Nat) -> Nat:
  match cnt:
    case 0n:
      acc
    case 1n+r:
      +m = msg(k, v)
      +w = E.Bch.codeword(c, m)
      +n = List.length(&2, Bool, w)
      all.m(r, c, k, three, U32.add(v, 1), Nat.add(acc, all.pick(three, n, c, w, m)))

def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat, seed: U32) -> B.Octets:
  B.Octets.of_list(bulk.go(n, seed, Nil{}))

# bits flipped at indexes 7, 7 + 263, 7 + 2 * 263, ... (k of them), in the
# sector's bits and then its ECC's
def spread(k: Nat, w: List<&2, Bool>, +i: Nat) -> List<&2, Bool>:
  match k:
    case 0n:
      w
    case 1n+j:
      spread(j, D.Bch.flip_at(w, i), Nat.add(i, 263n))

def flipbytes(+o: T.BchOrder, +k: Nat, +d: B.Octets, +e: B.Octets) -> B.Octets:
  T.Bch.octets_of(o, spread(k, List.append(&2, Bool, T.Bch.bits_of(o, d), T.Bch.bits_of(o, e)), 7n))

def nand_same(same: Bool, n: Nat) -> String:
  match same:
    case True{}:
      "data back, " ++ Nat.show(n) ++ " flipped"
    case False{}:
      "wrong data"

def nand_show(r: Result<&2, &2, E.BchError, D.BchDecoded>, +d: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{x}:
      match x:
        case D.BchDecoded{d2, e2, n}:
          nand_same(B.Octets.is_eq(d2, d), n)

def nand_try(+c: C.BchCode, +k: Nat, +d: B.Octets, r: Result<&2, &2, E.BchError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "encode failed"
    case Done{+ecc}:
      +both = flipbytes(T.Bch.order(), k, d, ecc)
      +dl = B.Octets.len(d)
      nand_show(D.Bch.decode(c, B.Octets.take(dl, both), B.Octets.drop(dl, both)), d)

def recv() -> List<&2, Bool>:
  [False{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}, True{}]

def main() -> IO(Unit):
  +sector = bulk(512n, 7)
  +t4 = C.Bch.nand_t4()
  +t8 = C.Bch.nand_t8()
  +t16 = C.Bch.nand_t16()
  do IO<Unit>:
    IO.print(showb(C.Bch.generator(C.Bch.bch15_7())))
    IO.print(showb(C.Bch.generator(C.Bch.bch15_5())))
    IO.print(Nat.show(C.Bch.parity_bits(t4)) ++ " " ++ Nat.show(C.Bch.parity_bits(t8)) ++ " " ++ Nat.show(C.Bch.parity_bits(t16)))
    IO.print(showl(S.Bch.syndromes(C.Bch.bch15_5(), recv())))
    IO.print(showfix(D.Bch.correct(C.Bch.bch15_5(), recv())))
    IO.print(Nat.show(all.m(128n, C.Bch.bch15_7(), 7n, False{}, 0, 0n)) ++ " of " ++ Nat.show(Nat.mul(128n, 120n)))
    IO.print(Nat.show(all.m(32n, C.Bch.bch15_5(), 5n, True{}, 0, 0n)) ++ " of " ++ Nat.show(Nat.mul(32n, 680n)))
    IO.print(showo(D.Bch.encode(t4, sector)))
    IO.print(showo(D.Bch.encode(t8, sector)))
    IO.print(nand_try(t4, 4n, sector, D.Bch.encode(t4, sector)))
    IO.print(nand_try(t8, 8n, sector, D.Bch.encode(t8, sector)))
    IO.print(nand_try(t16, 16n, sector, D.Bch.encode(t16, sector)))
    IO.print(nand_try(t8, 9n, sector, D.Bch.encode(t8, sector)))

#|100010111
#|11101100101
#|52 104 208
#|2 4 13 3 0 14
#|010011011100001 (2 flipped)
#|15360 of 15360
#|21760 of 21760
#|bbebb3c71f6aa0
#|6db91e5330d796bf174c2594ad
#|data back, 4 flipped
#|data back, 8 flipped
#|data back, 16 flipped
#|fail
