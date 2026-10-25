# Proofs of LAWS_ctr.bend, from bytes' laws.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./stream.bend as St
import ./modes.bend as Md
import ./proof_bits.bend as Bits
import ./LAWS_ctr.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# How the proof goes. The next counter block is one added to the counter's
# bytes reversed (least significant first), with a carry from byte to byte,
# reversed back (ct.add1_ad: modes.bend's loop is a structural form ct.ad).
# Each byte b and carry c in give b + c = b' + 256 c' for the byte b' and
# carry c' out (ct.bf, from the generated region: every byte value checked),
# so for n bytes, value + c = value' + c_out 256^n (ct.key, by induction,
# 256^n never closed: crctr.pw of the list's length). A value of n bytes is
# below 256^n (ct.bound), so value' is value + 1 when there is no carry out,
# and 0 = value + 1 - 256^n when there is: value + 1 modulo 256^n either way
# (ct.fin, on Base's Nat.divmod.go).


# Booleans and naturals

def ct.bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def ct.bd(h: {False{} == True{} : Bool}) -> Empty:
  %h : ct.bdisc(_)
  Unit{}

def ct.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, ct.bd(h))

def ct.and_l(a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}:
  match a:
    case False{}:
      h => h
    case True{}:
      h => {==}

def ct.and_r(a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case False{}:
      h => ct.absurd({b == True{} : Bool}, h)
    case True{}:
      h => h

def ct.true_and(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def ct.b2n(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def ct.le0(+y: Nat) -> {Nat.is_le(0n, y) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ct.le_trans(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(b, c) == True{} : Bool} -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      h1 => h2 => {==}
    case 0n _ 1n+cp:
      h1 => h2 => {==}
    case 1n+ap 0n _:
      h1 => h2 => ct.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, h1)
    case 1n+ap 1n+bp 0n:
      h1 => h2 => ct.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, h2)
    case 1n+ap 1n+bp 1n+cp:
      h1 => h2 => ct.le_trans(ap, bp, cp)(h1)(h2)

def ct.add_sub(+d: Nat, +n: Nat) -> {Nat.is_le(d, n) == True{} : Bool} -> {Nat.add(d, Nat.sub(n, d)) == n : Nat}:
  match d n:
    case 0n 0n:
      h => {==}
    case 0n 1n+np:
      h => {==}
    case 1n+dp 0n:
      h => ct.absurd({Nat.add(1n+dp, Nat.sub(0n, 1n+dp)) == 0n : Nat}, h)
    case 1n+dp 1n+np:
      h => %ct.add_sub(dp, np)(h) : {1n+Nat.add(dp, Nat.sub(np, dp)) == 1n+_ : Nat}
        {==}

# x + a <= x + b, and a + x <= b + x, when a <= b
def ct.le_add_mono_r(+x: Nat, +a: Nat, +b: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(Nat.add(x, a), Nat.add(x, b)) == True{} : Bool}:
  match x:
    case 0n:
      h => h
    case 1n+p:
      h => ct.le_add_mono_r(p, a, b)(h)

def ct.le_add_mono_l(+a: Nat, +b: Nat, +x: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(Nat.add(a, x), Nat.add(b, x)) == True{} : Bool}:
  h => %UL.nat_add_comm(x, a) : {Nat.is_le(_, Nat.add(b, x)) == True{} : Bool}
    %UL.nat_add_comm(x, b) : {Nat.is_le(Nat.add(x, a), _) == True{} : Bool}
    ct.le_add_mono_r(x, a, b)(h)

def ct.mul_mono(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  match a b:
    case 0n _:
      h => ct.le0(Nat.mul(b, c))
    case 1n+ap 0n:
      h => ct.absurd({Nat.is_le(Nat.mul(1n+ap, c), 0n) == True{} : Bool}, h)
    case 1n+ap 1n+bp:
      h => ct.le_add_mono_r(c, Nat.mul(ap, c), Nat.mul(bp, c))(ct.mul_mono(ap, bp, c)(h))

# Base's division: a dividend below the divisor is its own remainder, and
# a whole divisor more leaves the same remainder

def ct.snd_small(+x: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(x, m) == True{} : Bool} -> {Pair.snd(Nat, Nat, Nat.divmod.go(x, m, d, r)) == Nat.add(x, r) : Nat}:
  match x:
    case 0n:
      h => {==}
    case 1n+xp:
      match m:
        case 0n:
          h => ct.absurd({Pair.snd(Nat, Nat, Nat.divmod.go(1n+xp, 0n, d, r)) == Nat.add(1n+xp, r) : Nat}, h)
        case 1n+mp:
          h => Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(xp, mp, d, 1n+r)), Nat.add(xp, 1n+r), 1n+Nat.add(xp, r), ct.snd_small(xp, mp, d, 1n+r)(h), UL.nat_add_succ(xp, r))

def ct.mod_small(+x: Nat, +q: Nat) -> {Nat.is_le(x, q) == True{} : Bool} -> {Nat.mod(x, 1n+q) == x : Nat}:
  h => Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(x, q, 0n, 0n)), Nat.add(x, 0n), x, ct.snd_small(x, q, 0n, 0n)(h), UL.nat_add_zero(x))

def ct.snd_go(+n: Nat, +m: Nat, +d1: Nat, +d2: Nat, +r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d1, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d2, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          ct.snd_go(np, r, 1n+d1, 1n+d2, 0n)
        case 1n+mp:
          ct.snd_go(np, mp, d1, d2, 1n+r)

def ct.go_skip(+m: Nat, +x: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(1n+Nat.add(m, x), m, d, r) == Nat.divmod.go(x, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      Equal.trans(Nat & Nat, Nat.divmod.go(1n+Nat.add(mp, x), mp, d, 1n+r), Nat.divmod.go(x, Nat.add(mp, 1n+r), 1n+d, 0n), Nat.divmod.go(x, 1n+Nat.add(mp, r), 1n+d, 0n), ct.go_skip(mp, x, d, 1n+r), Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(x, z, 1n+d, 0n), Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), UL.nat_add_succ(mp, r)))

def ct.mod_wrap(+q: Nat, +x: Nat) -> {Nat.mod(Nat.add(1n+q, x), 1n+q) == Nat.mod(x, 1n+q) : Nat}:
  Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(1n+Nat.add(q, x), q, 0n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(x, Nat.add(q, 0n), 1n, 0n)), Nat.mod(x, 1n+q), Equal.cong(Nat & Nat, Nat, p => Pair.snd(Nat, Nat, p), Nat.divmod.go(1n+Nat.add(q, x), q, 0n, 0n), Nat.divmod.go(x, Nat.add(q, 0n), 1n, 0n), ct.go_skip(q, x, 0n, 0n)), Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(x, Nat.add(q, 0n), 1n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(x, q, 1n, 0n)), Nat.mod(x, 1n+q), Equal.cong(Nat, Nat, z => Pair.snd(Nat, Nat, Nat.divmod.go(x, z, 1n, 0n)), Nat.add(q, 0n), q, UL.nat_add_zero(q)), ct.snd_go(x, q, 1n, 0n, 0n)))

# BEGIN GENERATED by gen/ctr_proof.py: bytes
# one added to the byte of bits c0 (least significant) .. c7, with its carry
def ct.e1(c0: Bool, c1: Bool, c2: Bool, c3: Bool, c4: Bool, c5: Bool, c6: Bool, c7: Bool) -> {Nat.add(U32.to_nat(B.byte(U32.add(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(24n)}}}}}}}}}, 1))), Nat.mul(ct.b2n(U32.is_eq(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(24n)}}}}}}}}}, 255)), 256n)) == Nat.add(U32.to_nat(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(24n)}}}}}}}}}), 1n) : Nat}:
  match c0 c1 c2 c3 c4 c5 c6 c7:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

# the byte's value is at most 255
def ct.e2(c0: Bool, c1: Bool, c2: Bool, c3: Bool, c4: Bool, c5: Bool, c6: Bool, c7: Bool) -> {Nat.is_le(U32.to_nat(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(24n)}}}}}}}}}), 255n) == True{} : Bool}:
  match c0 c1 c2 c3 c4 c5 c6 c7:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
# END GENERATED: bytes

# A byte: one added with its carry, and its bound (from the generated
# region, on the byte's eight bits)

def ct.bf(c: Bool, +z: U32) -> {Nat.add(U32.to_nat(Md.cr.ctr.sum(c, B.byte(z))), Nat.mul(ct.b2n(Md.cr.ctr.carry(c, B.byte(z))), 256n)) == Nat.add(U32.to_nat(B.byte(z)), ct.b2n(c)) : Nat}:
  match c:
    case False{}:
      {==}
    case True{}:
      match z:
        case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
          ct.e1(c0, c1, c2, c3, c4, c5, c6, c7)

def ct.b255(+z: U32) -> {Nat.is_le(U32.to_nat(B.byte(z)), 255n) == True{} : Bool}:
  match z:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      ct.e2(c0, c1, c2, c3, c4, c5, c6, c7)

# The counter's bytes, least significant first: one added, structurally
# (modes.bend's cr.ctr.add1 without its accumulator), and the carry out

def ct.ad(rs: List<&2, U32>, +c: Bool) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      Con{Md.cr.ctr.sum(c, b), ct.ad(t, Md.cr.ctr.carry(c, b))}

def ct.co(rs: List<&2, U32>, +c: Bool) -> Bool:
  match rs:
    case Nil{}:
      c
    case Con{+b, t}:
      ct.co(t, Md.cr.ctr.carry(c, b))

def ct.add1_ad(+rs: List<&2, U32>, +c: Bool, +acc: List<&2, U32>) -> {Md.cr.ctr.add1(rs, c, acc) == St.cr.rev_onto(ct.ad(rs, c), acc) : List<&2, U32>}:
  match rs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      ct.add1_ad(t, Md.cr.ctr.carry(c, b), Con{Md.cr.ctr.sum(c, b), acc})

# Lists: bytes' rev and the stream's rev_onto are one function; masking and
# reversing commute

def ct.rev_same(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.rev_onto(xs, acc) == St.cr.rev_onto(xs, acc) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      ct.rev_same(t, Con{h, acc})

def ct.app_nil(+p: List<&2, U32>) -> {B.append(p, Nil{}) == p : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %ct.app_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def ct.rro(+p: List<&2, U32>, +c: List<&2, U32>, +z: List<&2, U32>) -> {B.rev_onto(St.cr.rev_onto(p, c), z) == B.rev_onto(c, B.append(p, z)) : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ct.rro(t, Con{x, c}, z)

def ct.rr(+p: List<&2, U32>) -> {B.rev(St.cr.rev_onto(p, Nil{})) == p : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.rev_onto(St.cr.rev_onto(p, Nil{}), Nil{}), B.append(p, Nil{}), p, ct.rro(p, Nil{}, Nil{}), ct.app_nil(p))

def ct.rev_mask(+ys: List<&2, U32>, +acc: List<&2, U32>) -> {St.cr.rev_onto(B.mask(ys), B.mask(acc)) == B.mask(St.cr.rev_onto(ys, acc)) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      ct.rev_mask(t, Con{y, acc})

def ct.len_rev(+c: List<&2, U32>, +z: List<&2, U32>) -> {B.len(St.cr.rev_onto(c, z)) == Nat.add(B.len(c), B.len(z)) : Nat}:
  match c:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      Equal.trans(Nat, B.len(St.cr.rev_onto(t, Con{y, z})), Nat.add(B.len(t), 1n+B.len(z)), 1n+Nat.add(B.len(t), B.len(z)), ct.len_rev(t, Con{y, z}), UL.nat_add_succ(B.len(t), B.len(z)))

def ct.len_ad(+rs: List<&2, U32>, +c: Bool) -> {B.len(ct.ad(rs, c)) == B.len(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %ct.len_ad(t, Md.cr.ctr.carry(c, b)) : {1n+B.len(ct.ad(t, Md.cr.ctr.carry(c, b))) == 1n+_ : Nat}
      {==}

# every element is a byte's value, at most 255
def ct.allb(rs: List<&2, U32>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+b, t}:
      Bool.and(Nat.is_le(U32.to_nat(b), 255n), ct.allb(t))

def ct.allb_mask(+zs: List<&2, U32>) -> {ct.allb(B.mask(zs)) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      ct.true_and(Nat.is_le(U32.to_nat(B.byte(z)), 255n), ct.allb(B.mask(t)), ct.b255(z), ct.allb_mask(t))

def ct.allb_ad(+rs: List<&2, U32>, c: Bool) -> {ct.allb(rs) == True{} : Bool} -> {ct.allb(ct.ad(rs, c)) == True{} : Bool}:
  match rs:
    case Nil{}:
      h => {==}
    case Con{+b, +t}:
      match c:
        case False{}:
          +h => ct.true_and(Nat.is_le(U32.to_nat(b), 255n), ct.allb(ct.ad(t, False{})), ct.and_l(Nat.is_le(U32.to_nat(b), 255n), ct.allb(t))(h), ct.allb_ad(t, False{})(ct.and_r(Nat.is_le(U32.to_nat(b), 255n), ct.allb(t))(h)))
        case True{}:
          +h => ct.true_and(Nat.is_le(U32.to_nat(B.byte(U32.add(b, 1))), 255n), ct.allb(ct.ad(t, U32.is_eq(b, 255))), ct.b255(U32.add(b, 1)), ct.allb_ad(t, U32.is_eq(b, 255))(ct.and_r(Nat.is_le(U32.to_nat(b), 255n), ct.allb(t))(h)))

# The carry: the bytes plus one are the result plus the carry out times
# 256^n (least significant byte first)
def ct.key(+zs: List<&2, U32>, +c: Bool) -> {Nat.add(Laws.crctr.vle(ct.ad(B.mask(zs), c)), Nat.mul(ct.b2n(ct.co(B.mask(zs), c)), Laws.crctr.pw(B.len(B.mask(zs))))) == Nat.add(Laws.crctr.vle(B.mask(zs)), ct.b2n(c)) : Nat}:
  match zs:
    case Nil{}:
      UL.nat_mul_one(ct.b2n(c))
    case Con{+z, +t}:
      +ns = U32.to_nat(Md.cr.ctr.sum(c, B.byte(z)))
      +nz = U32.to_nat(B.byte(z))
      +c2 = Md.cr.ctr.carry(c, B.byte(z))
      +vr = Laws.crctr.vle(ct.ad(B.mask(t), Md.cr.ctr.carry(c, B.byte(z))))
      +cw = ct.b2n(ct.co(B.mask(t), Md.cr.ctr.carry(c, B.byte(z))))
      +pt = Laws.crctr.pw(B.len(B.mask(t)))
      +vt = Laws.crctr.vle(B.mask(t))
      +ih = ct.key(t, Md.cr.ctr.carry(c, B.byte(z)))
      +e1 = UL.nat_add_assoc(ns, Nat.mul(vr, 256n), Nat.mul(cw, Nat.mul(pt, 256n)))
      # the rest: (vr + cr pt) 256 = (vt + c2) 256
      +e2 = Equal.trans(Nat, Nat.add(Nat.mul(vr, 256n), Nat.mul(cw, Nat.mul(pt, 256n))), Nat.add(Nat.mul(vr, 256n), Nat.mul(Nat.mul(cw, pt), 256n)), Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n)), Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(vr, 256n), y), Nat.mul(cw, Nat.mul(pt, 256n)), Nat.mul(Nat.mul(cw, pt), 256n), Equal.sym(Nat, Nat.mul(Nat.mul(cw, pt), 256n), Nat.mul(cw, Nat.mul(pt, 256n)), UL.nat_mul_assoc(cw, pt, 256n))), Equal.trans(Nat, Nat.add(Nat.mul(vr, 256n), Nat.mul(Nat.mul(cw, pt), 256n)), Nat.mul(Nat.add(vr, Nat.mul(cw, pt)), 256n), Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n)), Equal.sym(Nat, Nat.mul(Nat.add(vr, Nat.mul(cw, pt)), 256n), Nat.add(Nat.mul(vr, 256n), Nat.mul(Nat.mul(cw, pt), 256n)), UL.nat_add_mul(vr, Nat.mul(cw, pt), 256n)), Equal.trans(Nat, Nat.mul(Nat.add(vr, Nat.mul(cw, pt)), 256n), Nat.mul(Nat.add(vt, ct.b2n(c2)), 256n), Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n)), Equal.cong(Nat, Nat, y => Nat.mul(y, 256n), Nat.add(vr, Nat.mul(cw, pt)), Nat.add(vt, ct.b2n(c2)), ih), UL.nat_add_mul(vt, ct.b2n(c2), 256n))))
      # then regroup, and the byte's own carry
      +e3 = Equal.trans(Nat, Nat.add(ns, Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n))), Nat.add(ns, Nat.add(Nat.mul(ct.b2n(c2), 256n), Nat.mul(vt, 256n))), Nat.add(Nat.add(ns, Nat.mul(ct.b2n(c2), 256n)), Nat.mul(vt, 256n)), Equal.cong(Nat, Nat, y => Nat.add(ns, y), Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n)), Nat.add(Nat.mul(ct.b2n(c2), 256n), Nat.mul(vt, 256n)), UL.nat_add_comm(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n))), Equal.sym(Nat, Nat.add(Nat.add(ns, Nat.mul(ct.b2n(c2), 256n)), Nat.mul(vt, 256n)), Nat.add(ns, Nat.add(Nat.mul(ct.b2n(c2), 256n), Nat.mul(vt, 256n))), UL.nat_add_assoc(ns, Nat.mul(ct.b2n(c2), 256n), Nat.mul(vt, 256n))))
      +e4 = Equal.cong(Nat, Nat, y => Nat.add(y, Nat.mul(vt, 256n)), Nat.add(ns, Nat.mul(ct.b2n(c2), 256n)), Nat.add(nz, ct.b2n(c)), ct.bf(c, z))
      +e5 = Equal.trans(Nat, Nat.add(Nat.add(nz, ct.b2n(c)), Nat.mul(vt, 256n)), Nat.add(nz, Nat.add(ct.b2n(c), Nat.mul(vt, 256n))), Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), UL.nat_add_assoc(nz, ct.b2n(c), Nat.mul(vt, 256n)), Equal.trans(Nat, Nat.add(nz, Nat.add(ct.b2n(c), Nat.mul(vt, 256n))), Nat.add(nz, Nat.add(Nat.mul(vt, 256n), ct.b2n(c))), Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), Equal.cong(Nat, Nat, y => Nat.add(nz, y), Nat.add(ct.b2n(c), Nat.mul(vt, 256n)), Nat.add(Nat.mul(vt, 256n), ct.b2n(c)), UL.nat_add_comm(ct.b2n(c), Nat.mul(vt, 256n))), Equal.sym(Nat, Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), Nat.add(nz, Nat.add(Nat.mul(vt, 256n), ct.b2n(c))), UL.nat_add_assoc(nz, Nat.mul(vt, 256n), ct.b2n(c)))))
      Equal.trans(Nat, Nat.add(Nat.add(ns, Nat.mul(vr, 256n)), Nat.mul(cw, Nat.mul(pt, 256n))), Nat.add(ns, Nat.add(Nat.mul(vr, 256n), Nat.mul(cw, Nat.mul(pt, 256n)))), Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), e1, Equal.trans(Nat, Nat.add(ns, Nat.add(Nat.mul(vr, 256n), Nat.mul(cw, Nat.mul(pt, 256n)))), Nat.add(ns, Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n))), Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), Equal.cong(Nat, Nat, y => Nat.add(ns, y), Nat.add(Nat.mul(vr, 256n), Nat.mul(cw, Nat.mul(pt, 256n))), Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n)), e2), Equal.trans(Nat, Nat.add(ns, Nat.add(Nat.mul(vt, 256n), Nat.mul(ct.b2n(c2), 256n))), Nat.add(Nat.add(ns, Nat.mul(ct.b2n(c2), 256n)), Nat.mul(vt, 256n)), Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), e3, Equal.trans(Nat, Nat.add(Nat.add(ns, Nat.mul(ct.b2n(c2), 256n)), Nat.mul(vt, 256n)), Nat.add(Nat.add(nz, ct.b2n(c)), Nat.mul(vt, 256n)), Nat.add(Nat.add(nz, Nat.mul(vt, 256n)), ct.b2n(c)), e4, e5))))

# n bytes' value is below 256^n
def ct.bound(+rs: List<&2, U32>) -> {ct.allb(rs) == True{} : Bool} -> {Nat.is_le(1n+Laws.crctr.vle(rs), Laws.crctr.pw(B.len(rs))) == True{} : Bool}:
  match rs:
    case Nil{}:
      h => {==}
    case Con{+b, +t}:
      +h => ct.le_trans(Nat.add(1n+U32.to_nat(b), Nat.mul(Laws.crctr.vle(t), 256n)), Nat.add(256n, Nat.mul(Laws.crctr.vle(t), 256n)), Nat.mul(Laws.crctr.pw(B.len(t)), 256n))(ct.le_add_mono_l(1n+U32.to_nat(b), 256n, Nat.mul(Laws.crctr.vle(t), 256n))(ct.and_l(Nat.is_le(U32.to_nat(b), 255n), ct.allb(t))(h)))(ct.mul_mono(1n+Laws.crctr.vle(t), Laws.crctr.pw(B.len(t)), 256n)(ct.bound(t)(ct.and_r(Nat.is_le(U32.to_nat(b), 255n), ct.allb(t))(h))))

# from the carry equation and the bound: v' is v + 1 modulo p = 1 + q
def ct.bq(+vn: Nat, +p: Nat, +q: Nat, ep: {Nat.add(1n, q) == p : Nat}, bd: {Nat.is_le(1n+vn, p) == True{} : Bool}) -> {Nat.is_le(vn, q) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(1n+vn, Nat.add(1n, q)), Nat.is_le(1n+vn, p), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(1n+vn, w), Nat.add(1n, q), p, ep), bd)

# from the carry equation and the bound: v' is v + 1 modulo p = 1 + q
def ct.fin(cv: Bool, +vn: Nat, +v: Nat, +p: Nat, +q: Nat, +ep: {Nat.add(1n, q) == p : Nat}, +bd: {Nat.is_le(1n+vn, p) == True{} : Bool}) -> {Nat.add(vn, Nat.mul(ct.b2n(cv), p)) == Nat.add(v, 1n) : Nat} -> {vn == Nat.mod(Nat.add(v, 1n), p) : Nat}:
  match cv:
    case False{}:
      key => %Equal.trans(Nat, vn, Nat.add(vn, 0n), Nat.add(v, 1n), Equal.sym(Nat, Nat.add(vn, 0n), vn, UL.nat_add_zero(vn)), key) : {vn == Nat.mod(_, p) : Nat}
        %ep : {vn == Nat.mod(vn, _) : Nat}
        Equal.sym(Nat, Nat.mod(vn, 1n+q), vn, ct.mod_small(vn, q)(ct.bq(vn, p, q, ep, bd)))
    case True{}:
      key => %key : {vn == Nat.mod(_, p) : Nat}
        %Equal.trans(Nat, Nat.add(p, vn), Nat.add(vn, p), Nat.add(vn, Nat.add(p, 0n)), UL.nat_add_comm(p, vn), Equal.cong(Nat, Nat, w => Nat.add(vn, w), p, Nat.add(p, 0n), Equal.sym(Nat, Nat.add(p, 0n), p, UL.nat_add_zero(p)))) : {vn == Nat.mod(_, p) : Nat}
        %ep : {vn == Nat.mod(Nat.add(_, vn), _) : Nat}
        %Equal.sym(Nat, Nat.mod(Nat.add(1n+q, vn), 1n+q), Nat.mod(vn, 1n+q), ct.mod_wrap(q, vn)) : {vn == _ : Nat}
        Equal.sym(Nat, Nat.mod(vn, 1n+q), vn, ct.mod_small(vn, q)(ct.bq(vn, p, q, ep, bd)))

# the counter's bytes, least significant first and masked, plus one
def ct.core(+zs: List<&2, U32>) -> {Laws.crctr.vle(ct.ad(B.mask(zs), True{})) == Nat.mod(Nat.add(Laws.crctr.vle(B.mask(zs)), 1n), Laws.crctr.pw(B.len(B.mask(zs)))) : Nat}:
  +vn = Laws.crctr.vle(ct.ad(B.mask(zs), True{}))
  +p = Laws.crctr.pw(B.len(B.mask(zs)))
  +bd = Equal.trans(Bool, Nat.is_le(1n+vn, p), Nat.is_le(1n+vn, Laws.crctr.pw(B.len(ct.ad(B.mask(zs), True{})))), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(1n+vn, Laws.crctr.pw(w)), B.len(B.mask(zs)), B.len(ct.ad(B.mask(zs), True{})), Equal.sym(Nat, B.len(ct.ad(B.mask(zs), True{})), B.len(B.mask(zs)), ct.len_ad(B.mask(zs), True{}))), ct.bound(ct.ad(B.mask(zs), True{}))(ct.allb_ad(B.mask(zs), True{})(ct.allb_mask(zs))))
  +ep = ct.add_sub(1n, p)(ct.le_trans(1n, 1n+vn, p)(ct.le0(vn))(bd))
  ct.fin(ct.co(B.mask(zs), True{}), vn, Laws.crctr.vle(B.mask(zs)), p, Nat.sub(p, 1n), ep, bd)(ct.key(zs, True{}))

def Laws.ctr_counter_increment(K, Blk, enc, blk_of, blk_to, k, iv):
  +l = B.Octets.to_list(iv)
  +r = St.cr.rev_onto(B.Octets.to_list(iv), Nil{})
  # the counter's bytes are bytes, so their reversal is masked
  +ml = Equal.trans(List<&2, U32>, B.Octets.to_list(iv), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(iv))), B.mask(B.Octets.to_list(iv)), Equal.cong(B.Octets, List<&2, U32>, o => B.Octets.to_list(o), iv, B.Octets.of_list(B.Octets.to_list(iv)), Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(iv)), iv, BL.octets_of_to(iv))), BL.octets_to_of(B.Octets.to_list(iv)))
  +mr = Equal.trans(List<&2, U32>, B.mask(r), St.cr.rev_onto(B.mask(l), B.mask(Nil{})), r, Equal.sym(List<&2, U32>, St.cr.rev_onto(B.mask(l), B.mask(Nil{})), B.mask(r), ct.rev_mask(l, Nil{})), Equal.cong(List<&2, U32>, List<&2, U32>, y => St.cr.rev_onto(y, Nil{}), B.mask(l), l, Equal.sym(List<&2, U32>, l, B.mask(l), ml)))
  # the next counter is one added to the reversed bytes, reversed back
  %Equal.sym(List<&2, U32>, Md.cr.ctr.add1(r, True{}, Nil{}), St.cr.rev_onto(ct.ad(r, True{}), Nil{}), ct.add1_ad(r, True{}, Nil{})) : {Laws.crctr.val(_) == Nat.mod(Nat.add(Laws.crctr.val(l), 1n), Laws.crctr.pw(B.Octets.len(iv))) : Nat}
  %Equal.sym(List<&2, U32>, B.rev(St.cr.rev_onto(ct.ad(r, True{}), Nil{})), ct.ad(r, True{}), ct.rr(ct.ad(r, True{}))) : {Laws.crctr.vle(_) == Nat.mod(Nat.add(Laws.crctr.val(l), 1n), Laws.crctr.pw(B.Octets.len(iv))) : Nat}
  %Equal.sym(List<&2, U32>, B.rev_onto(l, Nil{}), r, ct.rev_same(l, Nil{})) : {Laws.crctr.vle(ct.ad(r, True{})) == Nat.mod(Nat.add(Laws.crctr.vle(_), 1n), Laws.crctr.pw(B.Octets.len(iv))) : Nat}
  # the length
  %Equal.sym(Nat, B.Octets.len(iv), B.len(l), BL.octets_len_list(iv)) : {Laws.crctr.vle(ct.ad(r, True{})) == Nat.mod(Nat.add(Laws.crctr.vle(r), 1n), Laws.crctr.pw(_)) : Nat}
  %Equal.trans(Nat, B.len(r), Nat.add(B.len(l), 0n), B.len(l), ct.len_rev(l, Nil{}), UL.nat_add_zero(B.len(l))) : {Laws.crctr.vle(ct.ad(r, True{})) == Nat.mod(Nat.add(Laws.crctr.vle(r), 1n), Laws.crctr.pw(_)) : Nat}
  %Bits.mask_len(r) : {Laws.crctr.vle(ct.ad(r, True{})) == Nat.mod(Nat.add(Laws.crctr.vle(r), 1n), Laws.crctr.pw(_)) : Nat}
  # and the bytes masked
  %mr : {Laws.crctr.vle(ct.ad(_, True{})) == Nat.mod(Nat.add(Laws.crctr.vle(_), 1n), Laws.crctr.pw(B.len(B.mask(r)))) : Nat}
  ct.core(r)
