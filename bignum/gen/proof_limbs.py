#!/usr/bin/env python3
"""Writes bignum/PROOF_limbs.bend: the proofs of the limb
laws (of_limbs_valid, add_value, add_valid, cmp_value, sub_value,
sub_valid).

  python3 gen/proof_limbs.py

A limb is a U32 below 2^16 (bnlaw.ok: its bits from 16 up are 0); a list
of limbs stands for sum x_i 2^(16 i) (bnlaw.val). One step of bn.add takes
t = x + y + c (no 32-bit wrap: the three are below 2^16), puts down
t & 65535 = low16(t) and carries t >> 16 = high16(t) < 2^16, so by
induction on the lists the value of the sum is the sum of the values. bn.cmp
compares the high limbs last: below two equal high parts the low limbs
decide, else the high parts do (bq.cn). One step of bn.sub takes t = x +
2^16 - y - w, puts down low16(t) and borrows 1 - high16(t) (high16(t) is 0
or 1); the borrow is the one the rest needs (bq.pre), and the values add
up (bq.post). BnNat.sub compares first, and norm keeps the value.

The Nat reasoning about 2^16 is done for a width h that is a variable
(the K-lemmas, used at h = 16 with hypotheses of exactly that type), so
that no closed power of two is compared by computation (u32/README.md,
"Stating the bounds"); ring identities are written by scripts/natproof.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "scripts"))
import natproof as N  # noqa: E402
from natproof import absurd, bcong, btrans, btrue, calc, hyp, le_from, lt_from, lt_rw, sym, wit_le, wit_lt  # noqa: E402

N.CFG["law"] = "UL."
N.OUT.prefix = "bq.r"
PROOF = os.path.join(HERE, "..", "PROOF_limbs.bend")

out = []
_flushed = [0]


def put(s=""):
    defs = N.OUT.defs[_flushed[0]:]
    if defs:
        out.append("\n".join(defs))
        _flushed[0] = len(N.OUT.defs)
    out.append(s)


def v(x):
    return f"U32.to_nat({x})"


def V(xs):
    return f"Laws.bnlaw.val({xs})"


def OK(xs):
    return f"Laws.bnlaw.ok({xs})"


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


def D16(x):
    return D("16n", x)


W16 = D("16n", "1n")
W32 = D("32n", "1n")
LIST = "List<&2, U32>"


def SH(x):
    return f"U32.shrn({x}, 16n)"


def VALID(x):
    return f"{{U32.is_zero({SH(x)}) == True{{}} : Bool}}"


def LT16(x):
    return btrue(f"Nat.is_lt({v(x)}, {W16})")


def AND(x):
    return f"U32.and(65535, {x})"


def basics():
    N.bend_order(put, "bq")
    put(f"""# Bools, limbs as values, and the parts of a limb sum

def bq.a0(+X: Nat) -> {{Nat.add(0n, X) == X : Nat}}:
  {{==}}

def bq.le00(x: Nat, h: {btrue('Nat.is_le(x, 0n)')}) -> {{x == 0n : Nat}}:
  match x:
    case 0n:
      {{==}}
    case 1n+ +p:
      Empty.absurd({{1n+p == 0n : Nat}}, bq.ft(h))

def bq.and1(a: Bool, b: Bool, h: {{Bool.and(a, b) == True{{}} : Bool}}) -> {{a == True{{}} : Bool}}:
  match a:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({{False{{}} == True{{}} : Bool}}, bq.ft(h))

def bq.and2(a: Bool, b: Bool, h: {{Bool.and(a, b) == True{{}} : Bool}}) -> {{b == True{{}} : Bool}}:
  match a:
    case True{{}}:
      h
    case False{{}}:
      Empty.absurd({{b == True{{}} : Bool}}, bq.ft(h))

def bq.and3(a: Bool, b: Bool, ha: {{a == True{{}} : Bool}}, hb: {{b == True{{}} : Bool}}) -> {{Bool.and(a, b) == True{{}} : Bool}}:
  match a:
    case True{{}}:
      hb
    case False{{}}:
      Empty.absurd({{Bool.and(False{{}}, b) == True{{}} : Bool}}, bq.ft(ha))

def bq.ceq(a: Nat, b: Nat, e: {{Nat.cmp(a, b) == EQ{{}} : Cmp}}) -> {{a == b : Nat}}:
  match a b:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      Empty.absurd({{0n == 1n+q : Nat}}, bq.ft(Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), LT{{}}, EQ{{}}, e)))
    case 1n+p 0n:
      Empty.absurd({{1n+p == 0n : Nat}}, bq.ft(Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), GT{{}}, EQ{{}}, e)))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, zz => 1n+zz, p, q, bq.ceq(p, q, e))

def bq.ct(c: Cmp, e: {{Cmp.is_lt(c) == True{{}} : Bool}}) -> {{c == LT{{}} : Cmp}}:
  match c:
    case LT{{}}:
      {{==}}
    case EQ{{}}:
      Empty.absurd({{EQ{{}} == LT{{}} : Cmp}}, bq.ft(e))
    case GT{{}}:
      Empty.absurd({{GT{{}} == LT{{}} : Cmp}}, bq.ft(e))

def bq.lg(a: Nat, b: Nat, e: {btrue('Nat.is_lt(b, a)')}) -> {{Nat.cmp(a, b) == GT{{}} : Cmp}}:
  match a b:
    case 0n 0n:
      Empty.absurd({{Nat.cmp(0n, 0n) == GT{{}} : Cmp}}, bq.ft(e))
    case 0n 1n+q:
      Empty.absurd({{Nat.cmp(0n, 1n+q) == GT{{}} : Cmp}}, bq.ft(e))
    case 1n+p 0n:
      {{==}}
    case 1n+p 1n+q:
      bq.lg(p, q, e)

def bq.gl(a: Nat, b: Nat, e: {{Nat.cmp(a, b) == GT{{}} : Cmp}}) -> {btrue('Nat.is_lt(b, a)')}:
  match a b:
    case 0n 0n:
      Empty.absurd({btrue('Nat.is_lt(0n, 0n)')}, bq.ft(Equal.cong(Cmp, Bool, zz => Cmp.is_gt(zz), EQ{{}}, GT{{}}, e)))
    case 0n 1n+q:
      Empty.absurd({btrue('Nat.is_lt(1n+q, 0n)')}, bq.ft(Equal.cong(Cmp, Bool, zz => Cmp.is_gt(zz), LT{{}}, GT{{}}, e)))
    case 1n+p 0n:
      {{==}}
    case 1n+p 1n+q:
      bq.gl(p, q, e)

def bq.st(c: Cmp) -> {{N.bn.step(c, EQ{{}}) == c : Cmp}}:
  match c:
    case LT{{}}:
      {{==}}
    case EQ{{}}:
      {{==}}
    case GT{{}}:
      {{==}}

def bq.ca0(+k: Nat, +x: Nat, +y: Nat) -> {{Nat.cmp(Nat.add(k, x), Nat.add(k, y)) == Nat.cmp(x, y) : Cmp}}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +p:
      bq.ca0(p, x, y)

def bq.ca(+x: Nat, +y: Nat, +k: Nat) -> {{Nat.cmp(Nat.add(x, k), Nat.add(y, k)) == Nat.cmp(x, y) : Cmp}}:
  %UL.nat_add_comm(k, x) : {{Nat.cmp(_, Nat.add(y, k)) == Nat.cmp(x, y) : Cmp}}
  %UL.nat_add_comm(k, y) : {{Nat.cmp(Nat.add(k, x), _) == Nat.cmp(x, y) : Cmp}}
  bq.ca0(k, x, y)

def bq.sl(a: Nat, b: Nat, h: {btrue('Nat.is_lt(a, b)')}) -> {{Nat.sub(a, b) == 0n : Nat}}:
  match a b:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      {{==}}
    case 1n+p 0n:
      Empty.absurd({{Nat.sub(1n+p, 0n) == 0n : Nat}}, bq.ft(h))
    case 1n+p 1n+q:
      bq.sl(p, q, h)

def bq.subk(+b: Nat, +a: Nat) -> {{Nat.sub(Nat.add(b, a), b) == a : Nat}}:
  match b:
    case 0n:
      bq.sub0(a)
    case 1n+ +p:
      bq.subk(p, a)

def bq.s1le(k: Nat) -> {btrue('Nat.is_le(Nat.sub(1n, k), 1n)')}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +p:
      {{==}}

def bq.le1(k: Nat, h: {btrue('Nat.is_lt(k, 2n)')}) -> {btrue('Nat.is_le(k, 1n)')}:
  match k:
    case 0n:
      {{==}}
    case 1n+p:
      match p:
        case 0n:
          {{==}}
        case 1n+q:
          match q:
            case 0n:
              Empty.absurd({btrue('Nat.is_le(2n, 1n)')}, bq.ft(h))
            case 1n+ +r:
              Empty.absurd({btrue('Nat.is_le(3n+r, 1n)')}, bq.ft(h))

def bq.ltle(+a: Nat, +b: Nat, +c: Nat, h1: {btrue('Nat.is_lt(a, b)')}, h2: {btrue('Nat.is_le(b, c)')}) -> {btrue('Nat.is_lt(a, c)')}:
  bq.le_lt(a, c, bq.le_trans(1n+a, b, c, bq.lt_sle(a, b, h1), h2))

def bq.lelt(+a: Nat, +b: Nat, +c: Nat, h1: {btrue('Nat.is_le(a, b)')}, h2: {btrue('Nat.is_lt(b, c)')}) -> {btrue('Nat.is_lt(a, c)')}:
  bq.le_lt(a, c, bq.le_trans(1n+a, 1n+b, c, h1, bq.lt_sle(b, c, h2)))
""")
    # a limb's value below 2^16, both ways; and(65535, t) is the low 16 bits
    x = "x"
    sh = SH(x)
    hz = (f"bq.z0({v(sh)}, Equal.trans(Bool, Nat.is_eq({v(sh)}, 0n), U32.is_eq({sh}, 0), True{{}}, "
          f"Equal.sym(Bool, U32.is_eq({sh}, 0), Nat.is_eq({v(sh)}, 0n), UL.u32_eq_value({sh}, 0)), h))")
    lo, hi = f"U.U32Nat.low(16n, {v(x)})", f"U.U32Nat.high(16n, {v(x)})"
    HH = hyp("hh", hi, "0n")
    LV = calc(lo, (f"Nat.add({lo}, 0n)", sym(hyp(f"UL.nat_add_zero({lo})", f"Nat.add({lo}, 0n)", lo))),
              (f"Nat.add({lo}, {D16('0n')})", "="),
              (f"Nat.add({lo}, {D16(hi)})", sym(HH)),
              (v(x), hyp(f"UL.low_high(16n, {v(x)})", f"Nat.add({lo}, {D16(hi)})", v(x))))
    h0 = f"Equal.sym(Nat, 0n, {hi}, UL.high_unique(16n, {v(x)}, {v(x)}, 0n, UL.nat_add_zero({v(x)}), h))"
    put(f"""def bq.lv(+x: U32, h: {VALID('x')}) -> {LT16('x')}:
  +hz = {hz}
  +hh = Equal.trans(Nat, {hi}, {v(sh)}, 0n, Equal.sym(Nat, {v(sh)}, {hi}, UL.u32_shrn_value(x, 16n)), hz)
  {lt_rw(lo, W16, v(x), W16, LV.text, None, f"UL.low_lt(16n, {v(x)})")}

def bq.vl(+x: U32, h: {LT16('x')}) -> {VALID('x')}:
  Equal.trans(Bool, U32.is_eq({sh}, 0), Nat.is_eq({v(sh)}, 0n), True{{}}, UL.u32_eq_value({sh}, 0), Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 0n), {v(sh)}, 0n, Equal.trans(Nat, {v(sh)}, {hi}, 0n, UL.u32_shrn_value(x, 16n), {h0})))

def bq.lo(+t: U32) -> {{{v(AND('t'))} == U.U32Nat.low(16n, {v('t')}) : Nat}}:
  Equal.trans(Nat, {v(AND('t'))}, {v('U32.and(t, 65535)')}, U.U32Nat.low(16n, {v('t')}), Equal.cong(U32, Nat, zz => U32.to_nat(zz), {AND('t')}, U32.and(t, 65535), UL.u32_and_comm(65535, t)), UL.u32_and_65535(t))

def bq.mk(+t: U32) -> {VALID(AND('t'))}:
  bq.vl({AND('t')}, {lt_rw(f"U.U32Nat.low(16n, {v('t')})", W16, v(AND('t')), W16, f"Equal.sym(Nat, {v(AND('t'))}, U.U32Nat.low(16n, {v('t')}), bq.lo(t))", None, f"UL.low_lt(16n, {v('t')})")})
""")


def klemmas():
    put("# Sums of limbs do not wrap: x + y + c < 2^(2h) and x + 2^h < 2^(2h), for x, y, c < 2^h, h >= 2\n")
    S = "Nat.add(Nat.add(x, y), c)"
    Dh = D("h", "1n")
    WX = hyp("wx", "Nat.add(Nat.sub(U.U32Nat.dbl(h, 1n), 1n+x), 1n+x)", Dh)
    WY = hyp("wy", "Nat.add(Nat.sub(U.U32Nat.dbl(h, 1n), 1n+y), 1n+y)", Dh)
    WC = hyp("wc", "Nat.add(Nat.sub(U.U32Nat.dbl(h, 1n), 1n+c), 1n+c)", Dh)
    a, b, cc = ("Nat.sub(U.U32Nat.dbl(h, 1n), 1n+x)", "Nat.sub(U.U32Nat.dbl(h, 1n), 1n+y)", "Nat.sub(U.U32Nat.dbl(h, 1n), 1n+c)")
    w = f"Nat.add(Nat.add(Nat.add({a}, {b}), {cc}), Nat.add(2n, {Dh}))"
    pf = calc(f"Nat.add({w}, 1n+{S})",
              (f"Nat.add(Nat.add(Nat.add({a}, 1n+x), Nat.add({b}, 1n+y)), Nat.add(Nat.add({cc}, 1n+c), {Dh}))", "ring"),
              (f"Nat.add(Nat.add({Dh}, Nat.add({b}, 1n+y)), Nat.add(Nat.add({cc}, 1n+c), {Dh}))", WX),
              (f"Nat.add(Nat.add({Dh}, {Dh}), Nat.add(Nat.add({cc}, 1n+c), {Dh}))", WY),
              (f"Nat.add(Nat.add({Dh}, {Dh}), Nat.add({Dh}, {Dh}))", WC),
              (f"Nat.double(Nat.double({Dh}))", "ring"))
    lt1 = lt_from(S, f"Nat.double(Nat.double({Dh}))", w, pf)
    h2 = btrans("Nat.is_le(2n, h)", "Nat.is_le(2n, 2n+j)", "True{}",
                f"Equal.sym(Bool, Nat.is_le(2n, 2n+j), Nat.is_le(2n, h), Equal.cong(Nat, Bool, zz => Nat.is_le(2n, zz), 2n+j, h, eh))", "bq.le0(j)")
    put(f"""def bq.k3(+h: Nat, +j: Nat, +m: Nat, +x: Nat, +y: Nat, +c: Nat, eh: {{2n+j == h : Nat}}, e: {{Nat.add(h, h) == m : Nat}}, hx: {btrue(f'Nat.is_lt(x, {Dh})')}, hy: {btrue(f'Nat.is_lt(y, {Dh})')}, hc: {btrue(f'Nat.is_lt(c, {Dh})')}) -> {btrue(f'Nat.is_lt({S}, {D("m", "1n")})')}:
  %e : {btrue(f'Nat.is_lt({S}, {D("_", "1n")})')}
  %UL.dbl_dbl(h, h, 1n) : {btrue(f'Nat.is_lt({S}, _)')}
  +wx = UL.nat_lt_witness(x, {Dh}, hx)
  +wy = UL.nat_lt_witness(y, {Dh}, hy)
  +wc = UL.nat_lt_witness(c, {Dh}, hc)
  bq.ltle({S}, Nat.double(Nat.double({Dh})), {D("h", Dh)}, {lt1}, UL.dbl_le_exp(2n, h, {Dh}, {h2}))
""")
    S2 = f"Nat.add(x, {Dh})"
    w2 = a
    pf2 = calc(f"Nat.add({w2}, 1n+{S2})", (f"Nat.add(Nat.add({a}, 1n+x), {Dh})", "ring"), (f"Nat.add({Dh}, {Dh})", WX), (f"Nat.double({Dh})", "ring"))
    lt2 = lt_from(S2, f"Nat.double({Dh})", w2, pf2)
    h1 = btrans("Nat.is_le(1n, h)", "Nat.is_le(1n, 2n+j)", "True{}",
                f"Equal.sym(Bool, Nat.is_le(1n, 2n+j), Nat.is_le(1n, h), Equal.cong(Nat, Bool, zz => Nat.is_le(1n, zz), 2n+j, h, eh))", "{==}")
    put(f"""def bq.k2w(+h: Nat, +j: Nat, +m: Nat, +x: Nat, eh: {{2n+j == h : Nat}}, e: {{Nat.add(h, h) == m : Nat}}, hx: {btrue(f'Nat.is_lt(x, {Dh})')}) -> {btrue(f'Nat.is_lt({S2}, {D("m", "1n")})')}:
  %e : {btrue(f'Nat.is_lt({S2}, {D("_", "1n")})')}
  %UL.dbl_dbl(h, h, 1n) : {btrue(f'Nat.is_lt({S2}, _)')}
  +wx = UL.nat_lt_witness(x, {Dh}, hx)
  bq.ltle({S2}, Nat.double({Dh}), {D("h", Dh)}, {lt2}, UL.dbl_le_exp(1n, h, {Dh}, {h1}))
""")


def sums():
    put("# The 32-bit sums of a step\n")
    x, y, c = "x", "y", "c"
    S = f"Nat.add(Nat.add({v(x)}, {v(y)}), {v(c)})"
    k3 = f"bq.k3(16n, 14n, 32n, {v(x)}, {v(y)}, {v(c)}, {{==}}, {{==}}, hx, hy, hc)"
    le = le_from(f"Nat.add({v(x)}, {v(y)})", S, v(c), calc(f"Nat.add({v(c)}, Nat.add({v(x)}, {v(y)}))", (S, "ring")))
    lt2 = f"bq.lelt(Nat.add({v(x)}, {v(y)}), {S}, {W32}, {le}, {k3})"
    AXY = "U32.add(x, y)"
    a1 = (f"UL.dbl_nowrap(32n, U.U32Nat.bit(U32.is_lt({AXY}, x)), {v(AXY)}, Nat.add({v(x)}, {v(y)}), Nat.add({v(x)}, {v(y)}), "
          f"UL.u32_add_wrap(x, y), UL.nat_le_refl(Nat.add({v(x)}, {v(y)})), {lt2})")
    A3 = f"U32.add({AXY}, c)"
    b3 = f"U.U32Nat.bit(U32.is_lt({A3}, {AXY}))"
    e2 = calc(f"Nat.add({v(A3)}, {D('32n', b3)})",
              (f"Nat.add({v(AXY)}, {v(c)})", hyp(f"UL.u32_add_wrap({AXY}, c)", f"Nat.add({v(A3)}, {D('32n', b3)})", f"Nat.add({v(AXY)}, {v(c)})")),
              (S, hyp("a1", v(AXY), f"Nat.add({v(x)}, {v(y)})")))
    put(f"""def bq.b3(+x: U32, +y: U32, +c: U32, hx: {LT16('x')}, hy: {LT16('y')}, hc: {LT16('c')}) -> {btrue(f'Nat.is_lt({S}, {W32})')}:
  {k3}

def bq.s3(+x: U32, +y: U32, +c: U32, +hx: {LT16('x')}, +hy: {LT16('y')}, +hc: {LT16('c')}) -> {{{v(A3)} == {S} : Nat}}:
  +a1 = {a1}
  UL.dbl_nowrap(32n, {b3}, {v(A3)}, {S}, {S}, {e2.text}, UL.nat_le_refl({S}), {k3})
""")
    # x + c, as x + c + 0
    S2 = f"Nat.add({v(x)}, {v(c)})"
    k3b = f"bq.k3(16n, 14n, 32n, {v(x)}, {v(c)}, 0n, {{==}}, {{==}}, hx, hc, {{==}})"
    le2 = le_from(S2, f"Nat.add({S2}, 0n)", "0n", calc(f"Nat.add(0n, {S2})", (f"Nat.add({S2}, 0n)", "ring")))
    b2 = f"bq.lelt({S2}, Nat.add({S2}, 0n), {W32}, {le2}, {k3b})"
    AXC = "U32.add(x, c)"
    put(f"""def bq.b2(+x: U32, +c: U32, hx: {LT16('x')}, hc: {LT16('c')}) -> {btrue(f'Nat.is_lt({S2}, {W32})')}:
  {b2}

def bq.s2(+x: U32, +c: U32, +hx: {LT16('x')}, +hc: {LT16('c')}) -> {{{v(AXC)} == {S2} : Nat}}:
  UL.dbl_nowrap(32n, U.U32Nat.bit(U32.is_lt({AXC}, x)), {v(AXC)}, {S2}, {S2}, UL.u32_add_wrap(x, c), UL.nat_le_refl({S2}), bq.b2(x, c, hx, hc))
""")


def adds():
    put("# carry and add: the value, and the limbs stay 16-bit\n")
    c = "c"
    put(f"""def bq.lone(+c: U32, z: Bool, ez: {{U32.is_zero(c) == z : Bool}}) -> {{{V('N.bn.lone(z, c)')} == {v(c)} : Nat}}:
  match z:
    case True{{}}:
      Equal.sym(Nat, {v(c)}, 0n, bq.z0({v(c)}, Equal.trans(Bool, Nat.is_eq({v(c)}, 0n), U32.is_eq(c, 0), True{{}}, Equal.sym(Bool, U32.is_eq(c, 0), Nat.is_eq({v(c)}, 0n), UL.u32_eq_value(c, 0)), ez)))
    case False{{}}:
      UL.nat_add_zero({v(c)})

def bq.okl(+c: U32, z: Bool, ez: {{U32.is_zero(c) == z : Bool}}, hc: {LT16('c')}) -> {{{OK('N.bn.lone(z, c)')} == True{{}} : Bool}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      bq.and3(U32.is_zero({SH('c')}), True{{}}, bq.vl(c, hc), {{==}})
""")
    # carry
    t = "U32.add(z, c)"
    T = v(t)
    cp = SH(t)
    hcp = lt_rw(f"U.U32Nat.high(16n, {T})", W16, v(cp), W16, f"Equal.sym(Nat, {v(cp)}, U.U32Nat.high(16n, {T}), UL.u32_shrn_value({t}, 16n))", None,
                f"UL.high_lt(16n, 16n, 32n, {T}, {{==}}, {lt_rw(f'Nat.add({v(chr(122))}, {v(c)})', W32, T, W32, f'Equal.sym(Nat, {T}, Nat.add({v(chr(122))}, {v(c)}), st)', None, 'bq.b2(z, c, hz, hc)')})")
    lo, hi = f"U.U32Nat.low(16n, {T})", f"U.U32Nat.high(16n, {T})"
    REST = f"N.bn.carry(zs, {cp})"
    chain = calc(f"Nat.add({v(AND(t))}, {D16(V(REST))})",
                 (f"Nat.add({lo}, {D16(V(REST))})", hyp(f"bq.lo({t})", v(AND(t)), lo)),
                 (f"Nat.add({lo}, {D16(f'Nat.add({V(chr(122) + chr(115))}, {v(cp)})')})", hyp("ih", V(REST), f"Nat.add({V('zs')}, {v(cp)})")),
                 (f"Nat.add({lo}, {D16(f'Nat.add({V(chr(122) + chr(115))}, {hi})')})", hyp(f"UL.u32_shrn_value({t}, 16n)", v(cp), hi)),
                 (f"Nat.add(Nat.add({lo}, {D16(hi)}), {D16(V('zs'))})", "ring"),
                 (f"Nat.add({T}, {D16(V('zs'))})", hyp(f"UL.low_high(16n, {T})", f"Nat.add({lo}, {D16(hi)})", T)),
                 (f"Nat.add(Nat.add({v('z')}, {v(c)}), {D16(V('zs'))})", hyp("st", T, f"Nat.add({v('z')}, {v(c)})")),
                 (f"Nat.add(Nat.add({v('z')}, {D16(V('zs'))}), {v(c)})", "ring"))
    hzs = f"bq.and2(U32.is_zero({SH('z')}), {OK('zs')}, hx)"
    hz = f"bq.lv(z, bq.and1(U32.is_zero({SH('z')}), {OK('zs')}, hx))"
    put(f"""def bq.cv(xs: {LIST}, +c: U32, +hx: {{{OK('xs')} == True{{}} : Bool}}, +hc: {LT16('c')}) -> {{{V('N.bn.carry(xs, c)')} == Nat.add({V('xs')}, {v(c)}) : Nat}}:
  match xs:
    case Nil{{}}:
      bq.lone(c, U32.is_zero(c), {{==}})
    case Con{{+z, +zs}}:
      +hz = {hz}
      +st = bq.s2(z, c, hz, hc)
      +ih = bq.cv(zs, {cp}, {hzs}, {hcp})
      {chain.text}

def bq.ck(xs: {LIST}, +c: U32, +hx: {{{OK('xs')} == True{{}} : Bool}}, +hc: {LT16('c')}) -> {{{OK('N.bn.carry(xs, c)')} == True{{}} : Bool}}:
  match xs:
    case Nil{{}}:
      bq.okl(c, U32.is_zero(c), {{==}}, hc)
    case Con{{+z, +zs}}:
      +hz = {hz}
      +st = bq.s2(z, c, hz, hc)
      bq.and3(U32.is_zero({SH(AND(t))}), {OK(REST)}, bq.mk({t}), bq.ck(zs, {cp}, {hzs}, {hcp}))
""")
    # add
    t = "U32.add(U32.add(x, y), c)"
    T = v(t)
    cp = SH(t)
    S3 = f"Nat.add(Nat.add({v('x')}, {v('y')}), {v(c)})"
    hcp = lt_rw(f"U.U32Nat.high(16n, {T})", W16, v(cp), W16, f"Equal.sym(Nat, {v(cp)}, U.U32Nat.high(16n, {T}), UL.u32_shrn_value({t}, 16n))", None,
                f"UL.high_lt(16n, 16n, 32n, {T}, {{==}}, {lt_rw(S3, W32, T, W32, f'Equal.sym(Nat, {T}, {S3}, st)', None, 'bq.b3(x, y, c, hx1, hy1, hc)')})")
    lo, hi = f"U.U32Nat.low(16n, {T})", f"U.U32Nat.high(16n, {T})"
    REST = f"N.bn.add(xs, ys, {cp})"
    VV = f"Nat.add({V('xs')}, {V('ys')})"
    chain = calc(f"Nat.add({v(AND(t))}, {D16(V(REST))})",
                 (f"Nat.add({lo}, {D16(V(REST))})", hyp(f"bq.lo({t})", v(AND(t)), lo)),
                 (f"Nat.add({lo}, {D16(f'Nat.add({VV}, {v(cp)})')})", hyp("ih", V(REST), f"Nat.add({VV}, {v(cp)})")),
                 (f"Nat.add({lo}, {D16(f'Nat.add({VV}, {hi})')})", hyp(f"UL.u32_shrn_value({t}, 16n)", v(cp), hi)),
                 (f"Nat.add(Nat.add({lo}, {D16(hi)}), {D16(VV)})", "ring"),
                 (f"Nat.add({T}, {D16(VV)})", hyp(f"UL.low_high(16n, {T})", f"Nat.add({lo}, {D16(hi)})", T)),
                 (f"Nat.add({S3}, {D16(VV)})", hyp("st", T, S3)),
                 (f"Nat.add(Nat.add(Nat.add({v('x')}, {D16(V('xs'))}), Nat.add({v('y')}, {D16(V('ys'))})), {v(c)})", "ring"))
    pre = (f"      +hx1 = bq.lv(x, bq.and1(U32.is_zero({SH('x')}), {OK('xs')}, hx))\n"
           f"      +hy1 = bq.lv(y, bq.and1(U32.is_zero({SH('y')}), {OK('ys')}, hy))\n"
           f"      +st = bq.s3(x, y, c, hx1, hy1, hc)\n")
    hxs = f"bq.and2(U32.is_zero({SH('x')}), {OK('xs')}, hx)"
    hys = f"bq.and2(U32.is_zero({SH('y')}), {OK('ys')}, hy)"
    sig = f"(xs: {LIST}, ys: {LIST}, +c: U32, +hx: {{{OK('xs')} == True{{}} : Bool}}, +hy: {{{OK('ys')} == True{{}} : Bool}}, +hc: {LT16('c')})"
    put(f"""def bq.av{sig} -> {{{V('N.bn.add(xs, ys, c)')} == Nat.add(Nat.add({V('xs')}, {V('ys')}), {v(c)}) : Nat}}:
  match xs ys:
    case Nil{{}} Nil{{}}:
      bq.cv(Nil{{}}, c, {{==}}, hc)
    case Nil{{}} Con{{+y, +ys}}:
      bq.cv(Con{{y, ys}}, c, hy, hc)
    case Con{{+x, +xs}} Nil{{}}:
      %Equal.sym(Nat, Nat.add({V('Con{x, xs}')}, 0n), {V('Con{x, xs}')}, UL.nat_add_zero({V('Con{x, xs}')})) : {{{V('N.bn.add(Con{x, xs}, Nil{}, c)')} == Nat.add(_, {v(c)}) : Nat}}
      bq.cv(Con{{x, xs}}, c, hx, hc)
    case Con{{+x, +xs}} Con{{+y, +ys}}:
{pre}      +ih = bq.av(xs, ys, {cp}, {hxs}, {hys}, {hcp})
      {chain.text}

def bq.ak{sig} -> {{{OK('N.bn.add(xs, ys, c)')} == True{{}} : Bool}}:
  match xs ys:
    case Nil{{}} Nil{{}}:
      bq.ck(Nil{{}}, c, {{==}}, hc)
    case Nil{{}} Con{{+y, +ys}}:
      bq.ck(Con{{y, ys}}, c, hy, hc)
    case Con{{+x, +xs}} Nil{{}}:
      bq.ck(Con{{x, xs}}, c, hx, hc)
    case Con{{+x, +xs}} Con{{+y, +ys}}:
{pre}      bq.and3(U32.is_zero({SH(AND(t))}), {OK(REST)}, bq.mk({t}), bq.ak(xs, ys, {cp}, {hxs}, {hys}, {hcp}))

def bq.ol(xs: {LIST}) -> {{{OK('N.bn.mask16(xs)')} == True{{}} : Bool}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      bq.and3(U32.is_zero({SH(AND('x'))}), {OK('N.bn.mask16(t)')}, bq.mk(x), bq.ol(t))

def Laws.of_limbs_valid(xs):
  bq.ol(xs)

def Laws.add_value(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      %UL.nat_add_zero(Nat.add({V('x')}, {V('y')})) : {{{V('N.bn.add(x, y, 0)')} == _ : Nat}}
      bq.av(x, y, 0, ha, hb, {{==}})

def Laws.add_valid(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bq.ak(x, y, 0, ha, hb, {{==}})
""")


def cmps():
    put("# Comparison: the high limbs decide, unless they are equal\n")
    Dh = D("h", "1n")
    X = "Nat.add(x, U.U32Nat.dbl(h, A))"
    Y = "Nat.add(y, U.U32Nat.dbl(h, B))"
    # A < B: X < Y
    g, G = wit_lt("A", "B", "alb")
    gx, GX = wit_lt("x", Dh, "hx")
    w = f"Nat.add(Nat.add(y, U.U32Nat.dbl(h, {g})), {gx})"
    pf = calc(f"Nat.add({w}, 1n+{X})",
              (f"Nat.add(y, Nat.add(U.U32Nat.dbl(h, {g}), Nat.add(Nat.add({gx}, 1n+x), U.U32Nat.dbl(h, A))))", "ring"),
              (f"Nat.add(y, Nat.add(U.U32Nat.dbl(h, {g}), Nat.add({Dh}, U.U32Nat.dbl(h, A))))", GX),
              (f"Nat.add(y, U.U32Nat.dbl(h, Nat.add({g}, 1n+A)))", "ring"),
              (Y, G))
    ltxy = lt_from(X, Y, w, pf)
    g2, G2 = wit_lt("B", "A", "bla")
    gy, GY = wit_lt("y", Dh, "hy")
    w2 = f"Nat.add(Nat.add(x, U.U32Nat.dbl(h, {g2})), {gy})"
    pf2 = calc(f"Nat.add({w2}, 1n+{Y})",
               (f"Nat.add(x, Nat.add(U.U32Nat.dbl(h, {g2}), Nat.add(Nat.add({gy}, 1n+y), U.U32Nat.dbl(h, B))))", "ring"),
               (f"Nat.add(x, Nat.add(U.U32Nat.dbl(h, {g2}), Nat.add({Dh}, U.U32Nat.dbl(h, B))))", GY),
               (f"Nat.add(x, U.U32Nat.dbl(h, Nat.add({g2}, 1n+B)))", "ring"),
               (X, G2))
    ltyx = lt_from(Y, X, w2, pf2)
    goal = f"{{N.bn.step(c, N.bn.step(Nat.cmp(x, y), acc)) == N.bn.step(Nat.cmp({X}, {Y}), acc) : Cmp}}"
    put(f"""def bq.cn(+h: Nat, +x: Nat, +y: Nat, +A: Nat, +B: Nat, +hx: {btrue(f'Nat.is_lt(x, {Dh})')}, +hy: {btrue(f'Nat.is_lt(y, {Dh})')}, +acc: Cmp, c: Cmp, ec: {{Nat.cmp(A, B) == c : Cmp}}) -> {goal}:
  match c:
    case EQ{{}}:
      %bq.ceq(A, B, ec) : {{N.bn.step(EQ{{}}, N.bn.step(Nat.cmp(x, y), acc)) == N.bn.step(Nat.cmp({X}, Nat.add(y, U.U32Nat.dbl(h, _))), acc) : Cmp}}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(x, U.U32Nat.dbl(h, A)), Nat.add(y, U.U32Nat.dbl(h, A))), Nat.cmp(x, y), bq.ca(x, y, U.U32Nat.dbl(h, A))) : {{N.bn.step(EQ{{}}, N.bn.step(Nat.cmp(x, y), acc)) == N.bn.step(_, acc) : Cmp}}
      {{==}}
    case LT{{}}:
      +alb = Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Nat.cmp(A, B), LT{{}}, ec)
      %Equal.sym(Cmp, Nat.cmp({X}, {Y}), LT{{}}, bq.ct(Nat.cmp({X}, {Y}), {ltxy})) : {{N.bn.step(LT{{}}, N.bn.step(Nat.cmp(x, y), acc)) == N.bn.step(_, acc) : Cmp}}
      {{==}}
    case GT{{}}:
      +bla = bq.gl(A, B, ec)
      %Equal.sym(Cmp, Nat.cmp({X}, {Y}), GT{{}}, bq.lg({X}, {Y}, {ltyx})) : {{N.bn.step(GT{{}}, N.bn.step(Nat.cmp(x, y), acc)) == N.bn.step(_, acc) : Cmp}}
      {{==}}
""")
    # allz and the value 0
    put(f"""def bq.ez0(+h: Nat, b: Nat) -> {{Nat.is_eq(U.U32Nat.dbl(h, b), 0n) == Nat.is_eq(b, 0n) : Bool}}:
  match b:
    case 0n:
      %Equal.sym(Nat, U.U32Nat.dbl(h, 0n), 0n, UL.dbl_zero(h)) : {{Nat.is_eq(_, 0n) == True{{}} : Bool}}
      {{==}}
    case 1n+ +p:
      +lt = Equal.trans(Bool, Nat.is_lt(0n, U.U32Nat.dbl(h, 1n+p)), Nat.is_lt(U.U32Nat.dbl(h, 0n), U.U32Nat.dbl(h, 1n+p)), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, U.U32Nat.dbl(h, 1n+p)), 0n, U.U32Nat.dbl(h, 0n), Equal.sym(Nat, U.U32Nat.dbl(h, 0n), 0n, UL.dbl_zero(h))), UL.dbl_lt(h, 0n, 1n+p))
      bq.nz1(U.U32Nat.dbl(h, 1n+p), lt)

def bq.nz1(y: Nat, h: {btrue('Nat.is_lt(0n, y)')}) -> {{Nat.is_eq(y, 0n) == False{{}} : Bool}}:
  match y:
    case 0n:
      Empty.absurd({{Nat.is_eq(0n, 0n) == False{{}} : Bool}}, bq.ft(h))
    case 1n+ +p:
      {{==}}

def bq.ez(+h: Nat, a: Nat, +b: Nat) -> {{Nat.is_eq(Nat.add(a, U.U32Nat.dbl(h, b)), 0n) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 0n)) : Bool}}:
  match a:
    case 0n:
      bq.ez0(h, b)
    case 1n+ +p:
      {{==}}

def bq.zv(xs: {LIST}) -> {{N.bn.allz(xs) == Nat.is_eq({V('xs')}, 0n) : Bool}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      %Equal.sym(Bool, Nat.is_eq(Nat.add({v('x')}, {D16(V('t'))}), 0n), Bool.and(Nat.is_eq({v('x')}, 0n), Nat.is_eq({V('t')}, 0n)), bq.ez(16n, {v('x')}, {V('t')})) : {{N.bn.allz(Con{{x, t}}) == _ : Bool}}
      %Equal.sym(Bool, U32.is_eq(x, 0), Nat.is_eq({v('x')}, U32.to_nat(0)), UL.u32_eq_value(x, 0)) : {{Bool.and(_, N.bn.allz(t)) == Bool.and(Nat.is_eq({v('x')}, 0n), Nat.is_eq({V('t')}, 0n)) : Bool}}
      %Equal.sym(Bool, N.bn.allz(t), Nat.is_eq({V('t')}, 0n), bq.zv(t)) : {{Bool.and(Nat.is_eq({v('x')}, 0n), _) == Bool.and(Nat.is_eq({v('x')}, 0n), Nat.is_eq({V('t')}, 0n)) : Bool}}
      {{==}}
""")
    # bq.ez0 calls bq.nz1, so nz1 must come first: reorder
    i = out[-1].index("def bq.nz1(")
    j = out[-1].index("def bq.ez(")
    nz1 = out[-1][i:j]
    out[-1] = nz1 + out[-1][:i] + out[-1][j:]
    put(f"""def bq.cnl(+ys: {LIST}, +acc: Cmp, z: Bool, ez: {{N.bn.allz(ys) == z : Bool}}) -> {{N.bn.or_rest(z, acc, LT{{}}) == N.bn.step(Nat.cmp(0n, {V('ys')}), acc) : Cmp}}:
  match z:
    case True{{}}:
      %Equal.sym(Nat, {V('ys')}, 0n, bq.z0({V('ys')}, Equal.trans(Bool, Nat.is_eq({V('ys')}, 0n), N.bn.allz(ys), True{{}}, Equal.sym(Bool, N.bn.allz(ys), Nat.is_eq({V('ys')}, 0n), bq.zv(ys)), ez))) : {{acc == N.bn.step(Nat.cmp(0n, _), acc) : Cmp}}
      {{==}}
    case False{{}}:
      %Equal.sym(Cmp, Nat.cmp(0n, {V('ys')}), LT{{}}, bq.ct(Nat.cmp(0n, {V('ys')}), bq.nz({V('ys')}, Equal.trans(Bool, Nat.is_eq({V('ys')}, 0n), N.bn.allz(ys), False{{}}, Equal.sym(Bool, N.bn.allz(ys), Nat.is_eq({V('ys')}, 0n), bq.zv(ys)), ez)))) : {{LT{{}} == N.bn.step(_, acc) : Cmp}}
      {{==}}

def bq.cnr(+xs: {LIST}, +acc: Cmp, z: Bool, ez: {{N.bn.allz(xs) == z : Bool}}) -> {{N.bn.or_rest(z, acc, GT{{}}) == N.bn.step(Nat.cmp({V('xs')}, 0n), acc) : Cmp}}:
  match z:
    case True{{}}:
      %Equal.sym(Nat, {V('xs')}, 0n, bq.z0({V('xs')}, Equal.trans(Bool, Nat.is_eq({V('xs')}, 0n), N.bn.allz(xs), True{{}}, Equal.sym(Bool, N.bn.allz(xs), Nat.is_eq({V('xs')}, 0n), bq.zv(xs)), ez))) : {{acc == N.bn.step(Nat.cmp(_, 0n), acc) : Cmp}}
      {{==}}
    case False{{}}:
      %Equal.sym(Cmp, Nat.cmp({V('xs')}, 0n), GT{{}}, bq.lg({V('xs')}, 0n, bq.nz({V('xs')}, Equal.trans(Bool, Nat.is_eq({V('xs')}, 0n), N.bn.allz(xs), False{{}}, Equal.sym(Bool, N.bn.allz(xs), Nat.is_eq({V('xs')}, 0n), bq.zv(xs)), ez)))) : {{GT{{}} == N.bn.step(_, acc) : Cmp}}
      {{==}}
""")
    hx1 = f"bq.lv(x, bq.and1(U32.is_zero({SH('x')}), {OK('xs')}, hx))"
    hy1 = f"bq.lv(y, bq.and1(U32.is_zero({SH('y')}), {OK('ys')}, hy))"
    hxs = f"bq.and2(U32.is_zero({SH('x')}), {OK('xs')}, hx)"
    hys = f"bq.and2(U32.is_zero({SH('y')}), {OK('ys')}, hy)"
    A2 = "N.bn.step(U32.cmp(x, y), acc)"
    M1 = f"N.bn.step(Nat.cmp({V('xs')}, {V('ys')}), {A2})"
    M2 = f"N.bn.step(Nat.cmp({V('xs')}, {V('ys')}), N.bn.step(Nat.cmp({v('x')}, {v('y')}), acc))"
    RHS = f"N.bn.step(Nat.cmp(Nat.add({v('x')}, {D16(V('xs'))}), Nat.add({v('y')}, {D16(V('ys'))})), acc)"
    put(f"""def bq.cm(xs: {LIST}, ys: {LIST}, +acc: Cmp, +hx: {{{OK('xs')} == True{{}} : Bool}}, +hy: {{{OK('ys')} == True{{}} : Bool}}) -> {{N.bn.cmp(xs, ys, acc) == N.bn.step(Nat.cmp({V('xs')}, {V('ys')}), acc) : Cmp}}:
  match xs ys:
    case Nil{{}} Nil{{}}:
      {{==}}
    case Nil{{}} Con{{+y, +ys}}:
      bq.cnl(Con{{y, ys}}, acc, N.bn.allz(Con{{y, ys}}), {{==}})
    case Con{{+x, +xs}} Nil{{}}:
      bq.cnr(Con{{x, xs}}, acc, N.bn.allz(Con{{x, xs}}), {{==}})
    case Con{{+x, +xs}} Con{{+y, +ys}}:
      Equal.trans(Cmp, N.bn.cmp(xs, ys, {A2}), {M1}, {RHS}, bq.cm(xs, ys, {A2}, {hxs}, {hys}), Equal.trans(Cmp, {M1}, {M2}, {RHS}, Equal.cong(Cmp, Cmp, zz => N.bn.step(Nat.cmp({V('xs')}, {V('ys')}), N.bn.step(zz, acc)), U32.cmp(x, y), Nat.cmp({v('x')}, {v('y')}), UL.u32_cmp_value(x, y)), bq.cn(16n, {v('x')}, {v('y')}, {V('xs')}, {V('ys')}, {hx1}, {hy1}, acc, Nat.cmp({V('xs')}, {V('ys')}), {{==}})))

def Laws.cmp_value(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      Equal.trans(Cmp, N.bn.cmp(x, y, EQ{{}}), N.bn.step(Nat.cmp({V('x')}, {V('y')}), EQ{{}}), Nat.cmp({V('x')}, {V('y')}), bq.cm(x, y, EQ{{}}, ha, hb), bq.st(Nat.cmp({V('x')}, {V('y')})))
""")


def subs():
    put("# Subtraction: one step's borrow, and the values\n")
    Dh = D("h", "1n")
    # the K-lemmas, for T + Y + Wv = X + 2^h (te), X, Y < 2^h, Wv <= 1
    TE = hyp("te", "Nat.add(Nat.add(T, Y), Wv)", f"Nat.add(X, {Dh})")
    gx, GX = wit_lt("X", Dh, "hx")
    w = f"Nat.add(Nat.add({gx}, Y), Wv)"
    p = calc(f"Nat.add(X, Nat.add({w}, 1n+T))",
             (f"Nat.add(Nat.add(Nat.add(T, Y), Wv), Nat.add({gx}, 1n+X))", "ring"),
             (f"Nat.add(Nat.add(X, {Dh}), Nat.add({gx}, 1n+X))", TE),
             (f"Nat.add(Nat.add(X, {Dh}), {Dh})", GX),
             (f"Nat.add(X, Nat.add({Dh}, {Dh}))", "ring"))
    c2 = hyp(f"UL.nat_add_cancel(X, Nat.add({w}, 1n+T), Nat.add({Dh}, {Dh}), {p.text})", f"Nat.add({w}, 1n+T)", f"Nat.add({Dh}, {Dh})")
    t2 = lt_from("T", f"Nat.add({Dh}, {Dh})", w, c2)
    e2 = (f"Equal.trans(Nat, Nat.add({Dh}, {Dh}), {D('h', '2n')}, {D('Nat.add(h, 1n)', '1n')}, Equal.sym(Nat, {D('h', '2n')}, Nat.add({Dh}, {Dh}), UL.dbl_add(h, 1n, 1n)), UL.dbl_dbl(h, 1n, 1n))")
    t2b = lt_rw("T", f"Nat.add({Dh}, {Dh})", "T", D("Nat.add(h, 1n)", "1n"), None, e2, t2)
    hargs = ("+h: Nat, +T: Nat, +X: Nat, +Y: Nat, +Wv: Nat, +te: {Nat.add(Nat.add(T, Y), Wv) == " + f"Nat.add(X, {Dh}) : Nat}}, "
             f"+hx: {btrue(f'Nat.is_lt(X, {Dh})')}")
    put(f"""def bq.h2(+h: Nat, +T: Nat, +X: Nat, +Y: Nat, +Wv: Nat, te: {{Nat.add(Nat.add(T, Y), Wv) == Nat.add(X, {Dh}) : Nat}}, hx: {btrue(f'Nat.is_lt(X, {Dh})')}) -> {btrue('Nat.is_lt(U.U32Nat.high(h, T), 2n)')}:
  UL.high_lt(h, 1n, Nat.add(h, 1n), T, {{==}}, {t2b})
""")
    hiT, loT = "U.U32Nat.high(h, T)", "U.U32Nat.low(h, T)"
    LH = hyp("UL.low_high(h, T)", f"Nat.add({loT}, {D('h', hiT)})", "T")
    EN0 = hyp("en", hiT, "0n")
    EN1 = hyp("en", hiT, "1n")
    # PRE: the borrow the rest needs
    VX, VY = "VX", "VY"
    FULLY = f"Nat.add(Nat.add(Y, {D('h', VY)}), Wv)"
    FULLX = f"Nat.add(X, {D('h', VX)})"
    hle = btrue(f"Nat.is_le({FULLY}, {FULLX})")
    gle, GLE = wit_le(FULLY, FULLX, "hle")
    # n = 0: T = L < 2^h, VY + 1 <= VX
    u0, U0 = wit_lt(VX, f"Nat.add({VY}, 1n)", "nl")
    # VY = u0 + VX
    vye0 = calc(f"Nat.add(1n, {VY})", (f"Nat.add({VY}, 1n)", "ring"), (f"Nat.add({u0}, 1n+{VX})", sym(U0)), (f"Nat.add(1n, Nat.add({u0}, {VX}))", "ring"))
    VYE0 = hyp(f"UL.nat_add_cancel(1n, {VY}, Nat.add({u0}, {VX}), {vye0.text})", VY, f"Nat.add({u0}, {VX})")
    Xp0 = f"Nat.add({gle}, Nat.add(Nat.add(Y, Wv), {D('h', u0)}))"
    xe0 = calc(f"Nat.add({D('h', VX)}, {Xp0})",
               (f"Nat.add({gle}, Nat.add(Nat.add(Y, {D('h', f'Nat.add({u0}, {VX})')}), Wv))", "ring"),
               (f"Nat.add({gle}, {FULLY})", VYE0),
               (FULLX, GLE),
               (f"Nat.add({D('h', VX)}, X)", "ring"))
    XE0 = hyp(f"UL.nat_add_cancel({D('h', VX)}, {Xp0}, X, {xe0.text})", Xp0, "X")
    TL0 = calc("T", (f"Nat.add({loT}, {D('h', hiT)})", sym(LH)), (f"Nat.add({loT}, {D('h', '0n')})", EN0), (f"Nat.add({loT}, 0n)", hyp("UL.dbl_zero(h)", D("h", "0n"), "0n")), (loT, hyp(f"UL.nat_add_zero({loT})", f"Nat.add({loT}, 0n)", loT)))
    gt0, GT0 = wit_lt("T", Dh, lt_rw(loT, Dh, "T", Dh, f"Equal.sym(Nat, T, {loT}, {TL0.text})", None, "UL.low_lt(h, T)"))
    Z = "Nat.add(Nat.add(T, Y), Wv)"
    K0 = f"Nat.add({gle}, Nat.add(Nat.add({D('h', u0)}, {gt0}), 0n))"
    ab0 = calc(f"Nat.add({K0}, 1n+{Z})",
               (f"Nat.add({Xp0}, Nat.add({gt0}, 1n+T))", "ring"),
               (f"Nat.add({Xp0}, {Dh})", GT0),
               (f"Nat.add(X, {Dh})", XE0),
               (Z, sym(TE)))
    # n = 1: T = L + 2^h, VY <= VX
    u1, U1 = wit_lt(VX, f"Nat.add({VY}, 0n)", "nl")
    vye1 = calc(VY, (f"Nat.add({VY}, 0n)", sym(hyp(f"UL.nat_add_zero({VY})", f"Nat.add({VY}, 0n)", VY))), (f"Nat.add({u1}, 1n+{VX})", sym(U1)))
    VYE1 = hyp("vye1", VY, f"Nat.add({u1}, 1n+{VX})")
    TL1 = calc("T", (f"Nat.add({loT}, {D('h', hiT)})", sym(LH)), (f"Nat.add({loT}, {Dh})", EN1))
    # L + Y + Wv = X
    le1 = calc(f"Nat.add({Dh}, Nat.add(Nat.add({loT}, Y), Wv))", (f"Nat.add(Nat.add(Nat.add({loT}, {Dh}), Y), Wv)", "ring"), (Z, sym(TL1)), (f"Nat.add(X, {Dh})", TE), (f"Nat.add({Dh}, X)", "ring"))
    LE1 = hyp(f"UL.nat_add_cancel({Dh}, Nat.add(Nat.add({loT}, Y), Wv), X, {le1.text})", f"Nat.add(Nat.add({loT}, Y), Wv)", "X")
    Xp1 = f"Nat.add({gle}, Nat.add(Nat.add(Y, Wv), Nat.add({D('h', u1)}, {Dh})))"
    xe1 = calc(f"Nat.add({D('h', VX)}, {Xp1})",
               (f"Nat.add({gle}, Nat.add(Nat.add(Y, {D('h', f'Nat.add({u1}, 1n+{VX})')}), Wv))", "ring"),
               (f"Nat.add({gle}, {FULLY})", sym(VYE1)),
               (FULLX, GLE),
               (f"Nat.add({D('h', VX)}, X)", "ring"))
    XE1 = hyp(f"UL.nat_add_cancel({D('h', VX)}, {Xp1}, X, {xe1.text})", Xp1, "X")
    gx1, GX1 = wit_lt("X", Dh, "hx")
    K1 = f"Nat.add(Nat.add({gle}, Nat.add(Nat.add(Y, Wv), {D('h', u1)})), {gx1})"
    ab1 = calc(f"Nat.add({K1}, 1n+X)",
               (f"Nat.add(Nat.add({gle}, Nat.add(Nat.add(Y, Wv), {D('h', u1)})), Nat.add({gx1}, 1n+X))", "ring"),
               (f"Nat.add(Nat.add({gle}, Nat.add(Nat.add(Y, Wv), {D('h', u1)})), {Dh})", GX1),
               (Xp1, "ring"),
               ("X", XE1))
    pre_goal = btrue(f"Nat.is_le(Nat.add({VY}, Nat.sub(1n, n)), {VX})")
    n2 = (f"bq.n2(q, Equal.trans(Bool, Nat.is_lt(2n+q, 2n), Nat.is_lt({hiT}, 2n), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, 2n), 2n+q, {hiT}, Equal.sym(Nat, {hiT}, 2n+q, en)), bq.h2(h, T, X, Y, Wv, te, hx)))")
    put(f"""def bq.n2(q: Nat, h: {btrue('Nat.is_lt(2n+q, 2n)')}) -> Empty:
  match q:
    case 0n:
      bq.ft(h)
    case 1n+ +r:
      bq.ft(h)

def bq.pre(+h: Nat, +T: Nat, +X: Nat, +Y: Nat, +Wv: Nat, +VX: Nat, +VY: Nat, +te: {{{Z} == Nat.add(X, {Dh}) : Nat}}, +hx: {btrue(f'Nat.is_lt(X, {Dh})')}, +hle: {hle}, n: Nat, +en: {{{hiT} == n : Nat}}, z: Bool, ez: {{Nat.is_le(Nat.add({VY}, Nat.sub(1n, n)), {VX}) == z : Bool}}) -> {pre_goal}:
  match n:
    case 0n:
      match z:
        case True{{}}:
          ez
        case False{{}}:
          +nl = bq.nle_lt(Nat.add({VY}, 1n), {VX}, ez)
          {absurd(btrue(f'Nat.is_le(Nat.add({VY}, 1n), {VX})'), K0, Z, ab0)}
    case 1n+m:
      match m:
        case 0n:
          match z:
            case True{{}}:
              ez
            case False{{}}:
              +nl = bq.nle_lt(Nat.add({VY}, 0n), {VX}, ez)
              +vye1 = {vye1.text}
              {absurd(btrue(f'Nat.is_le(Nat.add({VY}, 0n), {VX})'), K1, "X", ab1)}
        case 1n+ +q:
          Empty.absurd({btrue(f'Nat.is_le(Nat.add({VY}, Nat.sub(1n, 2n+q)), {VX})')}, {n2})
""")
    # POST: the values add up
    VS = "VS"
    IHt = f"{{Nat.add(Nat.add({VS}, {VY}), Nat.sub(1n, n)) == {VX} : Nat}}"
    G = f"Nat.add(Nat.add(Nat.add({loT}, {D('h', VS)}), Nat.add(Y, {D('h', VY)})), Wv)"
    IH0 = hyp("ih", f"Nat.add(Nat.add({VS}, {VY}), 1n)", VX)
    po0 = calc(G, (f"Nat.add(Nat.add(Nat.add({loT}, Y), Wv), {D('h', f'Nat.add({VS}, {VY})')})", "ring"),
               (f"Nat.add({Z}, {D('h', f'Nat.add({VS}, {VY})')})", hyp("tl0", loT, "T")),
               (f"Nat.add(Nat.add(X, {Dh}), {D('h', f'Nat.add({VS}, {VY})')})", TE),
               (f"Nat.add(X, {D('h', f'Nat.add(Nat.add({VS}, {VY}), 1n)')})", "ring"),
               (FULLX, IH0))
    IH1 = hyp("ih", f"Nat.add(Nat.add({VS}, {VY}), 0n)", VX)
    po1 = calc(G, (f"Nat.add(Nat.add(Nat.add({loT}, Y), Wv), {D('h', f'Nat.add({VS}, {VY})')})", "ring"),
               (f"Nat.add(X, {D('h', f'Nat.add({VS}, {VY})')})", LE1),
               (f"Nat.add(X, {D('h', f'Nat.add(Nat.add({VS}, {VY}), 0n)')})", sym(hyp(f"UL.nat_add_zero(Nat.add({VS}, {VY}))", f"Nat.add(Nat.add({VS}, {VY}), 0n)", f"Nat.add({VS}, {VY})"))),
               (FULLX, IH1))
    put(f"""def bq.post(+h: Nat, +T: Nat, +X: Nat, +Y: Nat, +Wv: Nat, +VX: Nat, +VY: Nat, +VS: Nat, +te: {{{Z} == Nat.add(X, {Dh}) : Nat}}, +hx: {btrue(f'Nat.is_lt(X, {Dh})')}, n: Nat, +en: {{{hiT} == n : Nat}}, ih: {IHt}) -> {{{G} == {FULLX} : Nat}}:
  match n:
    case 0n:
      +tl0 = Equal.sym(Nat, T, {loT}, {TL0.text})
      {po0.text}
    case 1n+m:
      match m:
        case 0n:
          {po1.text}
        case 1n+ +q:
          Empty.absurd({{{G} == {FULLX} : Nat}}, {n2})
""")
    _ = hargs
    sub_glue()


def sub_glue():
    # one step on the words: t = x + 65536 - y - w
    x, y, w = "x", "y", "w"
    SH1 = "U32.shln(1, 16n)"
    A1 = f"U32.add(x, {SH1})"
    A2 = f"U32.sub({A1}, y)"
    T = f"U32.sub({A2}, w)"
    Tst = "U32.sub(U32.sub(U32.add(x, 65536), y), w)"
    # v(2^16 as a word) = 2^16, each step of exactly the type the next takes
    L1 = f"U.U32Nat.low(32n, U.U32Nat.dbl(16n, U32.to_nat(1)))"
    L2 = f"U.U32Nat.low(32n, {W16})"
    E65 = (f"Equal.trans(Nat, U32.to_nat({SH1}), {L1}, {W16}, UL.u32_shln_low(1, 16n), "
           f"Equal.trans(Nat, {L1}, {L2}, {W16}, Equal.cong(Nat, Nat, zz => U.U32Nat.low(32n, U.U32Nat.dbl(16n, zz)), U32.to_nat(1), 1n, {{==}}), "
           f"UL.low_small(32n, {W16}, {lt_rw(f'Nat.add(0n, {W16})', W32, W16, W32, f'bq.a0({W16})', None, 'bq.k2w(16n, 14n, 32n, 0n, {==}, {==}, {==})')})))")
    b1 = f"U.U32Nat.bit(U32.is_lt({A1}, x))"
    ea1 = calc(f"Nat.add({v(A1)}, {D('32n', b1)})",
               (f"Nat.add({v(x)}, U32.to_nat({SH1}))", hyp(f"UL.u32_add_wrap(x, {SH1})", f"Nat.add({v(A1)}, {D('32n', b1)})", f"Nat.add({v(x)}, U32.to_nat({SH1}))")),
               (f"Nat.add({v(x)}, WW)", hyp("e65", f"U32.to_nat({SH1})", "WW")))
    XW = f"Nat.add({v(x)}, WW)"
    k2 = "hk"
    va1 = f"UL.dbl_nowrap(32n, {b1}, {v(A1)}, {XW}, {XW}, {ea1.text}, UL.nat_le_refl({XW}), {k2})"
    # y <= x + 2^16
    hle2 = (f"bq.lt_le({v(y)}, {v(A1)}, {lt_rw(v(y), XW, v(y), v(A1), None, f'Equal.sym(Nat, {v(A1)}, {XW}, {va1})', f'bq.ltle({v(y)}, WW, {XW}, hy, UL.nat_le_add(WW, {v(x)}))')})")
    E2 = calc(f"Nat.add({v(A2)}, {v(y)})",
              (f"Nat.add(Nat.sub({v(A1)}, {v(y)}), {v(y)})", hyp(f"UL.u32_sub_value({A1}, y, hle2)", v(A2), f"Nat.sub({v(A1)}, {v(y)})")),
              (v(A1), hyp(f"UL.nat_le_witness({v(y)}, {v(A1)}, hle2)", f"Nat.add(Nat.sub({v(A1)}, {v(y)}), {v(y)})", v(A1))))
    # w <= a2: a2 + y = x + 2^16, y < 2^16
    gy, GY = wit_lt(v(y), "WW", "hy")
    p = calc(f"Nat.add({v(y)}, {v(A2)})",
             (f"Nat.add({v(A2)}, {v(y)})", "ring"),
             (v(A1), hyp("e2", f"Nat.add({v(A2)}, {v(y)})", v(A1))),
             (XW, hyp(va1, v(A1), XW)),
             (f"Nat.add({v(x)}, Nat.add({gy}, 1n+{v(y)}))", sym(GY)),
             (f"Nat.add({v(y)}, Nat.add(Nat.add({v(x)}, {gy}), 1n))", "ring"))
    a2e = hyp(f"UL.nat_add_cancel({v(y)}, {v(A2)}, Nat.add(Nat.add({v(x)}, {gy}), 1n), {p.text})", v(A2), f"Nat.add(Nat.add({v(x)}, {gy}), 1n)")
    one = le_from("1n", v(A2), f"Nat.add({v(x)}, {gy})", calc(f"Nat.add(Nat.add({v(x)}, {gy}), 1n)", (v(A2), sym(a2e))))
    hle3 = f"bq.le_trans({v(w)}, 1n, {v(A2)}, hw, {one})"
    E3 = calc(f"Nat.add({v(T)}, {v(w)})",
              (f"Nat.add(Nat.sub({v(A2)}, {v(w)}), {v(w)})", hyp(f"UL.u32_sub_value({A2}, w, hle3)", v(T), f"Nat.sub({v(A2)}, {v(w)})")),
              (v(A2), hyp(f"UL.nat_le_witness({v(w)}, {v(A2)}, hle3)", f"Nat.add(Nat.sub({v(A2)}, {v(w)}), {v(w)})", v(A2))))
    TEv = calc(f"Nat.add(Nat.add({v(T)}, {v(y)}), {v(w)})",
               (f"Nat.add(Nat.add({v(T)}, {v(w)}), {v(y)})", "ring"),
               (f"Nat.add({v(A2)}, {v(y)})", hyp("e3", f"Nat.add({v(T)}, {v(w)})", v(A2))),
               (v(A1), hyp("e2", f"Nat.add({v(A2)}, {v(y)})", v(A1))),
               (XW, hyp(va1, v(A1), XW)))
    sig = f"(+x: U32, +y: U32, +w: U32, +hx: {LT16('x')}, +hy: {LT16('y')}, +hw: {btrue(f'Nat.is_le({v(w)}, 1n)')})"
    sig1 = (f"(+WW: Nat, +x: U32, +y: U32, +w: U32, +e65: {{U32.to_nat({SH1}) == WW : Nat}}, +hx: {btrue(f'Nat.is_lt({v(x)}, WW)')}, "
            f"+hy: {btrue(f'Nat.is_lt({v(y)}, WW)')}, +hw: {btrue(f'Nat.is_le({v(w)}, 1n)')}, +hk: {btrue(f'Nat.is_lt(Nat.add({v(x)}, WW), {W32})')})")
    XW16 = f"Nat.add({v(x)}, {W16})"
    put(f"""def bq.te1{sig1} -> {{Nat.add(Nat.add({v(T)}, {v(y)}), {v(w)}) == {XW} : Nat}}:
  +hle2 = {hle2}
  +e2 = {E2.text}
  +hle3 = {hle3}
  +e3 = {E3.text}
  {TEv.text}

def bq.te{sig} -> {{Nat.add(Nat.add({v(Tst)}, {v(y)}), {v(w)}) == {XW16} : Nat}}:
  %Equal.cong(U32, U32, zz => U32.add(x, zz), {SH1}, 65536, {{==}}) : {{Nat.add(Nat.add({v("U32.sub(U32.sub(_, y), w)")}, {v(y)}), {v(w)}) == {XW16} : Nat}}
  bq.te1({W16}, x, y, w, {E65}, hx, hy, hw, bq.k2w(16n, 14n, 32n, {v(x)}, {{==}}, {{==}}, hx))
""")
    # the borrow word: v(1 - (t >> 16)) = 1 - high16(t)
    sh = SH("t")
    hi = f"U.U32Nat.high(16n, {v('t')})"
    ltsh = lt_rw(hi, "2n", v(sh), "2n", f"Equal.sym(Nat, {v(sh)}, {hi}, UL.u32_shrn_value(t, 16n))", None, "h2")
    put(f"""def bq.bw(+t: U32, h2: {btrue(f'Nat.is_lt({hi}, 2n)')}) -> {{{v(f'U32.sub(1, {sh})')} == Nat.sub(1n, {hi}) : Nat}}:
  %UL.u32_shrn_value(t, 16n) : {{{v(f'U32.sub(1, {sh})')} == Nat.sub(1n, _) : Nat}}
  UL.u32_sub_value(1, {sh}, bq.le1({v(sh)}, {ltsh}))
""")
    sub_rec(Tst)


def sub_rec(Tw):
    T = v(Tw)
    W1 = f"U32.sub(1, {SH(Tw)})"
    hi = f"U.U32Nat.high(16n, {T})"
    sh = SH(Tw)
    VXS, VYS = V("xs"), V("ys")
    X, Y, Wv = v("x"), v("y"), v("w")
    TE = f"bq.te(x, y, w, hx1, hy1, hw)"
    h2 = f"bq.h2(16n, {T}, {X}, {Y}, {Wv}, {TE}, hx1)"
    bw = f"bq.bw({Tw}, {h2})"
    pre = f"bq.pre(16n, {T}, {X}, {Y}, {Wv}, {VXS}, {VYS}, {TE}, hx1, hl, {hi}, {{==}}, Nat.is_le(Nat.add({VYS}, Nat.sub(1n, {hi})), {VXS}), {{==}})"
    hle2 = (f"Equal.trans(Bool, Nat.is_le(Nat.add({VYS}, {v(W1)}), {VXS}), Nat.is_le(Nat.add({VYS}, Nat.sub(1n, {hi})), {VXS}), True{{}}, "
            f"Equal.cong(Nat, Bool, zz => Nat.is_le(Nat.add({VYS}, zz), {VXS}), {v(W1)}, Nat.sub(1n, {hi}), {bw}), {pre})")
    hw2 = (f"Equal.trans(Bool, Nat.is_le({v(W1)}, 1n), Nat.is_le(Nat.sub(1n, {hi}), 1n), True{{}}, "
           f"Equal.cong(Nat, Bool, zz => Nat.is_le(zz, 1n), {v(W1)}, Nat.sub(1n, {hi}), {bw}), bq.s1le({hi}))")
    VS = V(f"N.bn.sub(xs, ys, {W1})")
    ih2 = (f"Equal.trans(Nat, Nat.add(Nat.add({VS}, {VYS}), Nat.sub(1n, {hi})), Nat.add(Nat.add({VS}, {VYS}), {v(W1)}), {VXS}, "
           f"Equal.cong(Nat, Nat, zz => Nat.add(Nat.add({VS}, {VYS}), zz), Nat.sub(1n, {hi}), {v(W1)}, Equal.sym(Nat, {v(W1)}, Nat.sub(1n, {hi}), {bw})), ih)")
    post = f"bq.post(16n, {T}, {X}, {Y}, {Wv}, {VXS}, {VYS}, {VS}, {TE}, hx1, {hi}, {{==}}, {ih2})"
    LOT = f"U.U32Nat.low(16n, {T})"
    G0 = f"Nat.add(Nat.add(Nat.add({v(AND(Tw))}, {D16(VS)}), Nat.add({Y}, {D16(VYS)})), {Wv})"
    G1 = f"Nat.add(Nat.add(Nat.add({LOT}, {D16(VS)}), Nat.add({Y}, {D16(VYS)})), {Wv})"
    fin = (f"Equal.trans(Nat, {G0}, {G1}, Nat.add({X}, {D16(VXS)}), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(Nat.add(zz, {D16(VS)}), Nat.add({Y}, {D16(VYS)})), {Wv}), {v(AND(Tw))}, {LOT}, bq.lo({Tw})), {post})")
    hx1 = f"bq.lv(x, bq.and1(U32.is_zero({SH('x')}), {OK('xs')}, hx))"
    hy1 = f"bq.lv(y, bq.and1(U32.is_zero({SH('y')}), {OK('ys')}, hy))"
    hxs = f"bq.and2(U32.is_zero({SH('x')}), {OK('xs')}, hx)"
    hys = f"bq.and2(U32.is_zero({SH('y')}), {OK('ys')}, hy)"
    body = f"""      +hx1 = {hx1}
      +ih = bq.sv(xs, ys, {W1}, {hxs}, YS_OK, {hw2}, {hle2})
      {fin}"""
    # the Nil-limb case: as y = 0, ys = Nil
    T0 = Tw.replace("U32.sub(U32.add(x, 65536), y)", "U32.sub(U32.add(x, 65536), 0)")
    sub0 = (f"Equal.cong(U32, {LIST}, zz => Con{{{AND('U32.sub(zz, w)')}, N.bn.sub(xs, Nil{{}}, U32.sub(1, {SH('U32.sub(zz, w)')}))}}, U32.add(x, 65536), U32.sub(U32.add(x, 65536), 0), "
            f"Equal.sym(U32, U32.sub(U32.add(x, 65536), 0), U32.add(x, 65536), bq.w0(U32.add(x, 65536))))")
    hle_full = btrue(f"Nat.is_le(Nat.add({V('ys')}, {Wv}), {V('xs')})")
    put(f"""def bq.z16() -> {LT16('0')}:
  {{==}}

def bq.w0(+a: U32) -> {{U32.sub(a, 0) == a : U32}}:
  UL.u32_value_eq(U32.sub(a, 0), a, Equal.trans(Nat, U32.to_nat(U32.sub(a, 0)), Nat.sub(U32.to_nat(a), 0n), U32.to_nat(a), UL.u32_sub_value(a, 0, bq.le0(U32.to_nat(a))), bq.sub0(U32.to_nat(a))))

def bq.sv(xs: {LIST}, ys: {LIST}, +w: U32, +hx: {{{OK('xs')} == True{{}} : Bool}}, +hy: {{{OK('ys')} == True{{}} : Bool}}, +hw: {btrue(f'Nat.is_le({Wv}, 1n)')}, +hl: {hle_full}) -> {{Nat.add(Nat.add({V('N.bn.sub(xs, ys, w)')}, {V('ys')}), {Wv}) == {V('xs')} : Nat}}:
  match xs ys:
    case Con{{+x, +xs}} Con{{+y, +ys}}:
      +hy1 = {hy1}
{body.replace('YS_OK', hys)}
    case Con{{+x, +xs}} Nil{{}}:
      %Equal.sym({LIST}, N.bn.sub(Con{{x, xs}}, Nil{{}}, w), N.bn.sub(Con{{x, xs}}, Con{{0, Nil{{}}}}, w), {sub0}) : {{Nat.add(Nat.add({V('_')}, 0n), {Wv}) == {V('Con{x, xs}')} : Nat}}
      +hy1 = bq.z16()
{body.replace('YS_OK', '{==}').replace(VYS, V('Nil{}')).replace('N.bn.sub(xs, ys, ', 'N.bn.sub(xs, Nil{}, ').replace('bq.sv(xs, ys, ', 'bq.sv(xs, Nil{}, ').replace('U32.sub(U32.add(x, 65536), y)', 'U32.sub(U32.add(x, 65536), 0)').replace('bq.te(x, y, w', 'bq.te(x, 0, w').replace(v('y'), 'U32.to_nat(0)')}
    case Nil{{}} Con{{+y, +ys}}:
      bq.le00(Nat.add({V('Con{y, ys}')}, {Wv}), hl)
    case Nil{{}} Nil{{}}:
      bq.le00(Nat.add(0n, {Wv}), hl)

def bq.sk(xs: {LIST}, ys: {LIST}, +w: U32) -> {{{OK('N.bn.sub(xs, ys, w)')} == True{{}} : Bool}}:
  match xs ys:
    case Con{{+x, +xs}} Con{{+y, +ys}}:
      bq.and3(U32.is_zero({SH(AND(Tw))}), {OK(f'N.bn.sub(xs, ys, {W1})')}, bq.mk({Tw}), bq.sk(xs, ys, {W1}))
    case Con{{+x, +xs}} Nil{{}}:
      bq.and3(U32.is_zero({SH(AND('U32.sub(U32.add(x, 65536), w)'))}), {OK('N.bn.sub(xs, Nil{}, U32.sub(1, ' + SH('U32.sub(U32.add(x, 65536), w)') + '))')}, bq.mk(U32.sub(U32.add(x, 65536), w)), bq.sk(xs, Nil{{}}, U32.sub(1, {SH('U32.sub(U32.add(x, 65536), w)')})))
    case Nil{{}} Con{{+y, +ys}}:
      {{==}}
    case Nil{{}} Nil{{}}:
      {{==}}
""")
    _ = (T0, sh)
    norm_and_laws()


def norm_and_laws():
    put(f"""# norm keeps the value and the limbs

def bq.consv(+x: U32, r: {LIST}) -> {{{V('N.bn.cons(x, r)')} == Nat.add({v('x')}, {D16(V('r'))}) : Nat}}:
  match r:
    case Nil{{}}:
      Equal.trans(Nat, {V('N.bn.lone(U32.is_zero(x), x)')}, {v('x')}, Nat.add({v('x')}, {D16('0n')}), bq.lone(x, U32.is_zero(x), {{==}}), Equal.sym(Nat, Nat.add({v('x')}, 0n), {v('x')}, UL.nat_add_zero({v('x')})))
    case Con{{a, t}}:
      {{==}}

def bq.consk(+x: U32, r: {LIST}, +hx: {VALID('x')}, hr: {{{OK('r')} == True{{}} : Bool}}) -> {{{OK('N.bn.cons(x, r)')} == True{{}} : Bool}}:
  match r:
    case Nil{{}}:
      bq.okl(x, U32.is_zero(x), {{==}}, bq.lv(x, hx))
    case Con{{a, t}}:
      bq.and3(U32.is_zero({SH('x')}), {OK('Con{a, t}')}, hx, hr)

def bq.nv(xs: {LIST}) -> {{{V('N.bn.norm(xs)')} == {V('xs')} : Nat}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      Equal.trans(Nat, {V('N.bn.cons(x, N.bn.norm(t))')}, Nat.add({v('x')}, {D16(V('N.bn.norm(t)'))}), Nat.add({v('x')}, {D16(V('t'))}), bq.consv(x, N.bn.norm(t)), Equal.cong(Nat, Nat, zz => Nat.add({v('x')}, {D16('zz')}), {V('N.bn.norm(t)')}, {V('t')}, bq.nv(t)))

def bq.nk(xs: {LIST}, +hx: {{{OK('xs')} == True{{}} : Bool}}) -> {{{OK('N.bn.norm(xs)')} == True{{}} : Bool}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      bq.consk(x, N.bn.norm(t), bq.and1(U32.is_zero({SH('x')}), {OK('t')}, hx), bq.nk(t, bq.and2(U32.is_zero({SH('x')}), {OK('t')}, hx)))
""")
    vx, vy = V("x"), V("y")
    S = V("N.bn.sub(x, y, 0)")
    sv = f"bq.sv(x, y, 0, ha, hb, {{==}}, hle)"
    e = calc(f"Nat.add({vy}, {S})", (f"Nat.add({S}, {vy})", "ring"),
             (f"Nat.add(Nat.add({S}, {vy}), 0n)", sym(hyp(f"UL.nat_add_zero(Nat.add({S}, {vy}))", f"Nat.add(Nat.add({S}, {vy}), 0n)", f"Nat.add({S}, {vy})"))),
             (vx, hyp(sv, f"Nat.add(Nat.add({S}, {vy}), 0n)", vx)))
    hle = (f"Equal.trans(Bool, Nat.is_le(Nat.add({vy}, U32.to_nat(0)), {vx}), Nat.is_le({vy}, {vx}), True{{}}, "
           f"Equal.cong(Nat, Bool, zz => Nat.is_le(zz, {vx}), Nat.add({vy}, U32.to_nat(0)), {vy}, UL.nat_add_zero({vy})), bq.nlt_le({vx}, {vy}, Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Nat.cmp({vx}, {vy}), C, ec)))")
    ge_case = (f"      +hle = {hle.replace('C, ec', 'CC, ec')}\n"
               f"      Equal.trans(Nat, {V('N.bn.norm(N.bn.sub(x, y, 0))')}, {S}, Nat.sub({vx}, {vy}), bq.nv(N.bn.sub(x, y, 0)), "
               f"Equal.sym(Nat, Nat.sub({vx}, {vy}), {S}, Equal.trans(Nat, Nat.sub({vx}, {vy}), Nat.sub(Nat.add({vy}, {S}), {vy}), {S}, Equal.cong(Nat, Nat, zz => Nat.sub(zz, {vy}), {vx}, Nat.add({vy}, {S}), Equal.sym(Nat, Nat.add({vy}, {S}), {vx}, {e.text})), bq.subk({vy}, {S}))))")
    put(f"""def bq.sg(+x: {LIST}, +y: {LIST}, +ha: {{{OK('x')} == True{{}} : Bool}}, +hb: {{{OK('y')} == True{{}} : Bool}}, c: Cmp, ec: {{Nat.cmp({vx}, {vy}) == c : Cmp}}) -> {{Laws.bnlaw.value(N.bn.sub.go(N.bn.ge(c), x, y)) == Nat.sub({vx}, {vy}) : Nat}}:
  match c:
    case LT{{}}:
      Equal.sym(Nat, Nat.sub({vx}, {vy}), 0n, bq.sl({vx}, {vy}, Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Nat.cmp({vx}, {vy}), LT{{}}, ec)))
    case EQ{{}}:
{ge_case.replace('CC', 'EQ{}')}
    case GT{{}}:
{ge_case.replace('CC', 'GT{}')}

def bq.sgk(+x: {LIST}, +y: {LIST}, z: Bool) -> {{Laws.bnlaw.valid(N.bn.sub.go(z, x, y)) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      bq.nk(N.bn.sub(x, y, 0), bq.sk(x, y, 0))
    case False{{}}:
      {{==}}

def Laws.sub_value(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      +ha2 = ha
      +hb2 = hb
      %Equal.sym(Cmp, N.bn.cmp(x, y, EQ{{}}), Nat.cmp({vx}, {vy}), Equal.trans(Cmp, N.bn.cmp(x, y, EQ{{}}), N.bn.step(Nat.cmp({vx}, {vy}), EQ{{}}), Nat.cmp({vx}, {vy}), bq.cm(x, y, EQ{{}}, ha2, hb2), bq.st(Nat.cmp({vx}, {vy})))) : {{Laws.bnlaw.value(N.bn.sub.go(N.bn.ge(_), x, y)) == Nat.sub({vx}, {vy}) : Nat}}
      bq.sg(x, y, ha2, hb2, Nat.cmp({vx}, {vy}), {{==}})

def Laws.sub_valid(a, b):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bq.sgk(x, y, N.bn.ge(N.bn.cmp(x, y, EQ{{}})))
""")


def main():
    put("# The limbs: the values of add, cmp and sub, and their limbs stay 16-bit\n")
    basics()
    klemmas()
    sums()
    adds()
    cmps()
    subs()
    put("")
    text = "\n".join(out)
    hdr = ("# Generated by gen/proof_limbs.py; do not edit by hand. The proofs of LAWS_limbs.bend.\n"
           "import Base\nimport ../u32/u32.bend as U\nimport ../u32/LAWS.bend as UL\nimport ../u32/PROOF.bend as UP\n"
           "import ./bignum.bend as N\nimport ./LAWS_limbs.bend as Laws\n\n")
    with open(PROOF, "w", newline="\n") as f:
        f.write(hdr + text)

if __name__ == "__main__":
    main()
