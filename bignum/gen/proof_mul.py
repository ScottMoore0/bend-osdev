#!/usr/bin/env python3
"""Writes bignum/PROOF_mul.bend: the proofs of the multiplication laws
(mul_value, mul_valid).

  python3 gen/proof_mul.py

bn.mul is the schoolbook product: a row bn.mac(b, x, acc, c) adds x times
the number b, and a carry c, to acc, a limb at a time. One step takes
t = z + x y + c; with x, y, z and c below 2^16 that is at most
(2^16 - 1)^2 + 2 (2^16 - 1) = 2^32 - 1, so no 32-bit wrap (bm.km, for a
bound X that is a variable: z + x y + c < X X), and the step puts down
t & 65535 = low16(t) with the carry t >> 16 = high16(t) < 2^16. So by
induction on b a row is acc + x b + c (bm.mv), and by induction on a the
rows add up to a b (bm.mlv). Every limb the rows put down is masked, and
every carry is a word's high 16 bits, so the product is valid for every
input (bm.mok, bm.mlk). The lemmas on limbs come from PROOF_limbs.bend
(bq.*), the ring identities from scripts/natproof.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "scripts"))
import natproof as N  # noqa: E402
from natproof import btrue, calc, hyp, le_from, lt_from, lt_rw, sym, wit_lt  # noqa: E402

N.CFG["law"] = "UL."
N.OUT.prefix = "bm.r"
PROOF = os.path.join(HERE, "..", "PROOF_mul.bend")

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
    return f"LL.bnlaw.val({xs})"


def OK(xs):
    return f"LL.bnlaw.ok({xs})"


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


def D16(x):
    return D("16n", x)


W16 = D("16n", "1n")
W32 = D("32n", "1n")
LIST = "List<&2, U32>"


def SH(x):
    return f"U32.shrn({x}, 16n)"


def LT16(x):
    return btrue(f"Nat.is_lt({v(x)}, {W16})")


def AND(x):
    return f"U32.and(65535, {x})"


def OKT(xs):
    return f"{{{OK(xs)} == True{{}} : Bool}}"


def bounds():
    put("# A step does not wrap: z + x y + c < X X for x, y, z, c < X\n")
    ax, AX = wit_lt("x", "X", "hx")
    ay, AY = wit_lt("y", "X", "hy")
    az, AZ = wit_lt("z", "X", "hz")
    ac, AC = wit_lt("c", "X", "hc")
    S = "Nat.add(Nat.add(z, Nat.mul(x, y)), c)"
    # ac + c = ay + y: both are X - 1
    ce = calc(f"Nat.add(1n, Nat.add({ac}, c))",
              (f"Nat.add({ac}, 1n+c)", "ring"),
              ("X", AC),
              (f"Nat.add({ay}, 1n+y)", sym(AY)),
              (f"Nat.add(1n, Nat.add({ay}, y))", "ring"))
    E = hyp("ce", f"Nat.add({ac}, c)", f"Nat.add({ay}, y)")
    w = f"Nat.add(Nat.add(Nat.add(Nat.mul({ax}, {ay}), Nat.mul(x, {ay})), Nat.mul({ax}, y)), Nat.add({az}, {ac}))"
    pf = calc(f"Nat.add({w}, 1n+{S})",
              (f"Nat.add(Nat.add(Nat.mul(Nat.add({ax}, x), {ay}), Nat.mul(Nat.add({ax}, x), y)), Nat.add(Nat.add({az}, 1n+z), Nat.add({ac}, c)))", "ring"),
              (f"Nat.add(Nat.add(Nat.mul(Nat.add({ax}, x), {ay}), Nat.mul(Nat.add({ax}, x), y)), Nat.add(Nat.add({az}, 1n+z), Nat.add({ay}, y)))", E),
              (f"Nat.add(Nat.add(Nat.mul(Nat.add({ax}, x), {ay}), Nat.mul(Nat.add({ax}, x), y)), Nat.add(X, Nat.add({ay}, y)))", AZ),
              (f"Nat.add(Nat.mul(Nat.add({ax}, 1n+x), Nat.add({ay}, y)), X)", "ring"),
              (f"Nat.add(Nat.mul(X, Nat.add({ay}, y)), X)", AX),
              (f"Nat.mul(X, Nat.add({ay}, 1n+y))", "ring"),
              ("Nat.mul(X, X)", AY))
    put(f"""def bm.km(+X: Nat, +x: Nat, +y: Nat, +z: Nat, +c: Nat, +hx: {btrue('Nat.is_lt(x, X)')}, +hy: {btrue('Nat.is_lt(y, X)')}, +hz: {btrue('Nat.is_lt(z, X)')}, +hc: {btrue('Nat.is_lt(c, X)')}) -> {btrue(f'Nat.is_lt({S}, Nat.mul(X, X))')}:
  +ce = UL.nat_add_cancel(1n, Nat.add({ac}, c), Nat.add({ay}, y), {ce.text})
  {lt_from(S, "Nat.mul(X, X)", w, pf)}

def bm.sq(+h: Nat, +m: Nat, e: {{Nat.add(h, h) == m : Nat}}) -> {{Nat.mul({D('h', '1n')}, {D('h', '1n')}) == {D('m', '1n')} : Nat}}:
  %e : {{Nat.mul({D('h', '1n')}, {D('h', '1n')}) == {D('_', '1n')} : Nat}}
  %UL.dbl_dbl(h, h, 1n) : {{Nat.mul({D('h', '1n')}, {D('h', '1n')}) == _ : Nat}}
  Equal.trans(Nat, Nat.mul({D('h', '1n')}, {D('h', '1n')}), {D('h', f"Nat.mul(1n, {D('h', '1n')})")}, {D('h', D('h', '1n'))}, UL.dbl_mul_l(h, 1n, {D('h', '1n')}), Equal.cong(Nat, Nat, zz => {D('h', 'zz')}, Nat.mul(1n, {D('h', '1n')}), {D('h', '1n')}, UL.nat_one_mul({D('h', '1n')})))
""")
    N.bend_u32(put, "bm")


def sums():
    put("# The 32-bit sums of a row step: z + x y + c, and x y + c\n")
    x, y, z, c = "x", "y", "z", "c"
    P = f"Nat.mul({v(x)}, {v(y)})"
    S = f"Nat.add(Nat.add({v(z)}, {P}), {v(c)})"
    MUL = "U32.mul(x, y)"
    km = f"bm.km({W16}, {v(x)}, {v(y)}, {v(z)}, {v(c)}, hx, hy, hz, hc)"
    bs = lt_rw(S, f"Nat.mul({W16}, {W16})", S, W32, None, "bm.sq(16n, 32n, {==})", km)
    leP = le_from(P, S, f"Nat.add({v(z)}, {v(c)})", calc(f"Nat.add(Nat.add({v(z)}, {v(c)}), {P})", (S, "ring")))
    ZP = f"Nat.add({v(z)}, {P})"
    leZP = le_from(ZP, S, v(c), calc(f"Nat.add({v(c)}, {ZP})", (S, "ring")))
    A2 = f"U32.add(z, {MUL})"
    T = f"U32.add({A2}, c)"
    b2 = f"U.U32Nat.bit(U32.is_lt({A2}, z))"
    b3 = f"U.U32Nat.bit(U32.is_lt({T}, {A2}))"
    e2 = calc(f"Nat.add({v(A2)}, {D('32n', b2)})",
              (f"Nat.add({v(z)}, {v(MUL)})", hyp(f"UL.u32_add_wrap(z, {MUL})", f"Nat.add({v(A2)}, {D('32n', b2)})", f"Nat.add({v(z)}, {v(MUL)})")),
              (ZP, hyp("m1", v(MUL), P)))
    e3 = calc(f"Nat.add({v(T)}, {D('32n', b3)})",
              (f"Nat.add({v(A2)}, {v(c)})", hyp(f"UL.u32_add_wrap({A2}, c)", f"Nat.add({v(T)}, {D('32n', b3)})", f"Nat.add({v(A2)}, {v(c)})")),
              (S, hyp("a2", v(A2), ZP)))
    hyps = f"+hx: {LT16('x')}, +hy: {LT16('y')}, +hz: {LT16('z')}, +hc: {LT16('c')}"
    put(f"""def bm.b4(+x: U32, +y: U32, +z: U32, +c: U32, {hyps}) -> {btrue(f'Nat.is_lt({S}, {W32})')}:
  {bs}

def bm.s4(+x: U32, +y: U32, +z: U32, +c: U32, {hyps}) -> {{{v(T)} == {S} : Nat}}:
  +bs = bm.b4(x, y, z, c, hx, hy, hz, hc)
  +m1 = UL.dbl_nowrap(32n, U.U32Nat.high(32n, {P}), {v(MUL)}, {P}, {P}, UL.u32_mul_wrap(x, y), UL.nat_le_refl({P}), PL.bq.lelt({P}, {S}, {W32}, {leP}, bs))
  +a2 = UL.dbl_nowrap(32n, {b2}, {v(A2)}, {ZP}, {ZP}, {e2.text}, UL.nat_le_refl({ZP}), PL.bq.lelt({ZP}, {S}, {W32}, {leZP}, bs))
  UL.dbl_nowrap(32n, {b3}, {v(T)}, {S}, {S}, {e3.text}, UL.nat_le_refl({S}), bs)
""")
    # no limb of acc: x y + c, as 0 + x y + c
    S0 = f"Nat.add({P}, {v(c)})"
    km0 = f"bm.km({W16}, {v(x)}, {v(y)}, 0n, {v(c)}, hx, hy, {{==}}, hc)"
    bs0 = lt_rw(f"Nat.add(Nat.add(0n, {P}), {v(c)})", f"Nat.mul({W16}, {W16})", S0, W32, "{==}", "bm.sq(16n, 32n, {==})", km0)
    leP0 = le_from(P, S0, v(c), calc(f"Nat.add({v(c)}, {P})", (S0, "ring")))
    T0 = f"U32.add({MUL}, c)"
    b0 = f"U.U32Nat.bit(U32.is_lt({T0}, {MUL}))"
    e0 = calc(f"Nat.add({v(T0)}, {D('32n', b0)})",
              (f"Nat.add({v(MUL)}, {v(c)})", hyp(f"UL.u32_add_wrap({MUL}, c)", f"Nat.add({v(T0)}, {D('32n', b0)})", f"Nat.add({v(MUL)}, {v(c)})")),
              (S0, hyp("m1", v(MUL), P)))
    hyps0 = f"+hx: {LT16('x')}, +hy: {LT16('y')}, +hc: {LT16('c')}"
    put(f"""def bm.b3(+x: U32, +y: U32, +c: U32, {hyps0}) -> {btrue(f'Nat.is_lt({S0}, {W32})')}:
  {bs0}

def bm.s3(+x: U32, +y: U32, +c: U32, {hyps0}) -> {{{v(T0)} == {S0} : Nat}}:
  +bs = bm.b3(x, y, c, hx, hy, hc)
  +m1 = UL.dbl_nowrap(32n, U.U32Nat.high(32n, {P}), {v(MUL)}, {P}, {P}, UL.u32_mul_wrap(x, y), UL.nat_le_refl({P}), PL.bq.lelt({P}, {S0}, {W32}, {leP0}, bs))
  UL.dbl_nowrap(32n, {b0}, {v(T0)}, {S0}, {S0}, {e0.text}, UL.nat_le_refl({S0}), bs)
""")
    # the carry of any word is below 2^16
    put(f"""def bm.hc(+t: U32) -> {LT16(SH('t'))}:
  {lt_rw(f"U.U32Nat.high(16n, {v('t')})", W16, v(SH('t')), W16, f"Equal.sym(Nat, {v(SH('t'))}, U.U32Nat.high(16n, {v('t')}), UL.u32_shrn_value(t, 16n))", None, f"UL.high_lt(16n, 16n, 32n, {v('t')}, {{==}}, bm.lt32(t))")}
""")


def rows():
    put("# A row: acc + x b + c, and its limbs are 16-bit\n")
    T = "U32.add(U32.add(z, U32.mul(x, y)), c)"
    T0 = "U32.add(U32.mul(x, y), c)"
    P = f"Nat.mul({v('x')}, {v('y')})"
    S = f"Nat.add(Nat.add({v('z')}, {P}), {v('c')})"
    S0 = f"Nat.add({P}, {v('c')})"

    def chain(t, s, rest, ihr, rhs):
        tt = v(t)
        lo, hi = f"U.U32Nat.low(16n, {tt})", f"U.U32Nat.high(16n, {tt})"
        return calc(f"Nat.add({v(AND(t))}, {D16(V(rest))})",
                    (f"Nat.add({lo}, {D16(V(rest))})", hyp(f"PL.bq.lo({t})", v(AND(t)), lo)),
                    (f"Nat.add({lo}, {D16(f'Nat.add({ihr}, {v(SH(t))})')})", hyp("ih", V(rest), f"Nat.add({ihr}, {v(SH(t))})")),
                    (f"Nat.add({lo}, {D16(f'Nat.add({ihr}, {hi})')})", hyp(f"UL.u32_shrn_value({t}, 16n)", v(SH(t)), hi)),
                    (f"Nat.add(Nat.add({lo}, {D16(hi)}), {D16(ihr)})", "ring"),
                    (f"Nat.add({tt}, {D16(ihr)})", hyp(f"UL.low_high(16n, {tt})", f"Nat.add({lo}, {D16(hi)})", tt)),
                    (f"Nat.add({s}, {D16(ihr)})", hyp("st", tt, s)),
                    (rhs, "ring"))
    rest = f"N.bn.mac(ys, x, zs, {SH(T)})"
    rhs = f"Nat.add(Nat.add(Nat.add({v('z')}, {D16(V('zs'))}), Nat.mul({v('x')}, Nat.add({v('y')}, {D16(V('ys'))}))), {v('c')})"
    c1 = chain(T, S, rest, f"Nat.add({V('zs')}, Nat.mul({v('x')}, {V('ys')}))", rhs)
    rest0 = f"N.bn.mac(ys, x, Nil{{}}, {SH(T0)})"
    rhs0 = f"Nat.add(Nat.mul({v('x')}, Nat.add({v('y')}, {D16(V('ys'))})), {v('c')})"
    c0 = chain(T0, S0, rest0, f"Nat.mul({v('x')}, {V('ys')})", rhs0)

    def nil_case(acc):
        R = f"Nat.add(Nat.add({acc}, Nat.mul({v('x')}, 0n)), {v('c')})"
        e = calc(R, (f"Nat.add(Nat.add({acc}, 0n), {v('c')})", hyp(f"UL.nat_mul_zero({v('x')})", f"Nat.mul({v('x')}, 0n)", "0n")),
                 (f"Nat.add({acc}, {v('c')})", hyp(f"UL.nat_add_zero({acc})", f"Nat.add({acc}, 0n)", acc)))
        return R, e
    Rn, en = nil_case("0n")
    Rc, ec = nil_case(V("Con{z, zs}"))
    hy1 = f"PL.bq.lv(y, PL.bq.and1(U32.is_zero({SH('y')}), {OK('ys')}, hb))"
    hys = f"PL.bq.and2(U32.is_zero({SH('y')}), {OK('ys')}, hb)"
    hz1 = f"PL.bq.lv(z, PL.bq.and1(U32.is_zero({SH('z')}), {OK('zs')}, ha))"
    hzs = f"PL.bq.and2(U32.is_zero({SH('z')}), {OK('zs')}, ha)"
    goal = f"{{{V('N.bn.mac(b, x, acc, c)')} == Nat.add(Nat.add({V('acc')}, Nat.mul({v('x')}, {V('b')})), {v('c')}) : Nat}}"
    put(f"""def bm.mv(b: {LIST}, +x: U32, acc: {LIST}, +c: U32, +hb: {OKT('b')}, +hx: {LT16('x')}, +ha: {OKT('acc')}, +hc: {LT16('c')}) -> {goal}:
  match b acc:
    case Con{{+y, +ys}} Con{{+z, +zs}}:
      +hy1 = {hy1}
      +hz1 = {hz1}
      +st = bm.s4(x, y, z, c, hx, hy1, hz1, hc)
      +ih = bm.mv(ys, x, zs, {SH(T)}, {hys}, hx, {hzs}, bm.hc({T}))
      {c1.text}
    case Con{{+y, +ys}} Nil{{}}:
      +hy1 = {hy1}
      +st = bm.s3(x, y, c, hx, hy1, hc)
      +ih = bm.mv(ys, x, Nil{{}}, {SH(T0)}, {hys}, hx, {{==}}, bm.hc({T0}))
      {c0.text}
    case Nil{{}} Nil{{}}:
      Equal.trans(Nat, {V('N.bn.carry(Nil{}, c)')}, Nat.add(0n, {v('c')}), {Rn}, PL.bq.cv(Nil{{}}, c, {{==}}, hc), Equal.sym(Nat, {Rn}, Nat.add(0n, {v('c')}), {en.text}))
    case Nil{{}} Con{{+z, +zs}}:
      Equal.trans(Nat, {V('N.bn.carry(Con{z, zs}, c)')}, Nat.add({V('Con{z, zs}')}, {v('c')}), {Rc}, PL.bq.cv(Con{{z, zs}}, c, ha, hc), Equal.sym(Nat, {Rc}, Nat.add({V('Con{z, zs}')}, {v('c')}), {ec.text}))

def bm.mok(b: {LIST}, +x: U32, acc: {LIST}, +c: U32, +ha: {OKT('acc')}, +hc: {LT16('c')}) -> {{{OK('N.bn.mac(b, x, acc, c)')} == True{{}} : Bool}}:
  match b acc:
    case Con{{+y, +ys}} Con{{+z, +zs}}:
      PL.bq.and3(U32.is_zero({SH(AND(T))}), {OK(rest)}, PL.bq.mk({T}), bm.mok(ys, x, zs, {SH(T)}, {hzs}, bm.hc({T})))
    case Con{{+y, +ys}} Nil{{}}:
      PL.bq.and3(U32.is_zero({SH(AND(T0))}), {OK(rest0)}, PL.bq.mk({T0}), bm.mok(ys, x, Nil{{}}, {SH(T0)}, {{==}}, bm.hc({T0})))
    case Nil{{}} Nil{{}}:
      PL.bq.ck(Nil{{}}, c, {{==}}, hc)
    case Nil{{}} Con{{+z, +zs}}:
      PL.bq.ck(Con{{z, zs}}, c, ha, hc)
""")


def products():
    put("# The product: the rows add up to a b, and every limb is 16-bit\n")
    M = "N.bn.mul(t, b)"
    mid = f"Nat.add(Nat.add({D16(V(M))}, Nat.mul({v('x')}, {V('b')})), 0n)"
    rhs = f"Nat.mul(Nat.add({v('x')}, {D16(V('t'))}), {V('b')})"
    tb = f"Nat.mul({V('t')}, {V('b')})"
    e = calc(mid, (f"Nat.add(Nat.add({D16(tb)}, Nat.mul({v('x')}, {V('b')})), 0n)", hyp("ih", V(M), tb)),
             (rhs, "ring"))
    put(f"""def bm.mlk(xs: {LIST}, +b: {LIST}) -> {{{OK('N.bn.mul(xs, b)')} == True{{}} : Bool}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      bm.mok(b, x, Con{{0, {M}}}, 0, bm.mlk(t, b), PL.bq.z16())

def bm.mlv(xs: {LIST}, +b: {LIST}, +hx: {OKT('xs')}, +hb: {OKT('b')}) -> {{{V('N.bn.mul(xs, b)')} == Nat.mul({V('xs')}, {V('b')}) : Nat}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      +hx1 = PL.bq.lv(x, PL.bq.and1(U32.is_zero({SH('x')}), {OK('t')}, hx))
      +ih = bm.mlv(t, b, PL.bq.and2(U32.is_zero({SH('x')}), {OK('t')}, hx), hb)
      Equal.trans(Nat, {V(f'N.bn.mac(b, x, Con{{0, {M}}}, 0)')}, {mid}, {rhs}, bm.mv(b, x, Con{{0, {M}}}, 0, hb, hx1, bm.mlk(t, b), PL.bq.z16()), {e.text})

def Laws.mul_value(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bm.mlv(x, y, ha, hb)

def Laws.mul_valid(a, b):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bm.mlk(x, y)
""")


def main():
    put("# Multiplication: the schoolbook product is the product of the values\n")
    bounds()
    sums()
    rows()
    products()
    put("")
    text = "\n".join(out)
    hdr = ("# Generated by gen/proof_mul.py; do not edit by hand. The proofs of LAWS_mul.bend.\n"
           "import Base\nimport ../u32/u32.bend as U\nimport ../u32/LAWS.bend as UL\nimport ../u32/PROOF.bend as UP\n"
           "import ./bignum.bend as N\nimport ./LAWS_limbs.bend as LL\nimport ./PROOF_limbs.bend as PL\n"
           "import ./LAWS_mul.bend as Laws\n\n")
    with open(PROOF, "w", newline="\n") as f:
        f.write(hdr + text)


if __name__ == "__main__":
    main()
