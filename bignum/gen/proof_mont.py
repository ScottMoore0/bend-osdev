#!/usr/bin/env python3
"""Writes bignum/PROOF_mont.bend: the proofs of the Montgomery and
exponentiation laws (LAWS_mont.bend).

  python3 gen/proof_mont.py

Modulo an odd n of k limbs, R = 2^(16 k):

* bn.np: n0 n0 = 1 mod 8 for odd n0 (by.n8), and Newton's step i (2 - x i)
  doubles the correct low bits (by.nw: if x i = 1 + 2^J h then
  x i (2 - x i) + 2^(2J) h^2 = 1 mod 2^16), so four steps give
  n0 i = 1 mod 2^16 and np = 2^16 - i gives n0 np + 1 = 0 mod 2^16
  (by.np). The 32-bit wrap of the U32 arithmetic disappears modulo 2^16.
* A REDC step (by.s2): t1 = t + a_i b, m = t1_0 np mod 2^16, and the low
  limb of t1 + m n is 0 (t1_0 (1 + np n0) = 0 mod 2^16), so dropping it
  gives 2^16 t' = t + a_i b + m n. So t stays below 2 n (by.bd, by.gb), and
  after k steps 2^(16 k) t = a b mod n (by.gv); one conditional subtraction
  (by.csv) and the trim (k limbs hold any number below n) give a value
  below n with (mm R) mod n = (a b) mod n (by.mmc).
* R is cancelled modulo an odd n (by.cd: with n = 1 + 2 H, a = 2 a (1 + H)
  mod n), so forms x R mod n multiply to forms of products (by.mg2, by.mf);
  R^2 mod n is 1 doubled 32 k times (by.r2v).
* Montgomery exponentiation squares and multiplies over the bits of each
  limb (by.bits: the exponent so far doubles and takes the bit, low(1 + p,
  w) = low(p, w) + 2^p bit p) and over the limbs most significant first
  (by.mgo, with by.be the big-endian value of the reversed limbs, by.brv).
* BnMod.exp takes Montgomery's way when the context check passes (which
  gives n odd and above 1), exp_plain's otherwise; the Montgomery result
  is normalised, and valid normalised limbs of equal value are equal
  (by.can), so both orders of a double exponentiation give the same number.

The Nat lemmas on Nat.mod and Nat.pow come from PROOF_mod.bend (bx.*), the
limb lemmas from PROOF_limbs.bend (bq.*), PROOF_mul.bend (bm.*) and
PROOF_div.bend (bd.*), the ring identities from scripts/natproof.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "scripts"))
import natproof as NP  # noqa: E402
from natproof import btrue, calc, hyp, sym, lt_rw  # noqa: E402

NP.CFG["law"] = "UL."
NP.OUT.prefix = "by.r"
PROOF = os.path.join(HERE, "..", "PROOF_mont.bend")

out = []
_flushed = [0]


def put(s=""):
    defs = NP.OUT.defs[_flushed[0]:]
    if defs:
        out.append("\n".join(defs))
        _flushed[0] = len(NP.OUT.defs)
    out.append(s)


LIST = "List<&2, U32>"
ONE1 = "Con{1, Nil{}}"


def v(x):
    return f"U32.to_nat({x})"


def V(xs):
    return f"LL.bnlaw.val({xs})"


def VAL(a):
    return f"LL.bnlaw.value({a})"


def OKT(xs):
    return btrue(f"LL.bnlaw.ok({xs})")


def VT(a):
    return btrue(f"LL.bnlaw.valid({a})")


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


W16 = D("16n", "1n")
W32 = D("32n", "1n")


def LOW(k, x):
    return f"U.U32Nat.low({k}, {x})"


def HIGH(k, x):
    return f"U.U32Nat.high({k}, {x})"


def ODD(x):
    return f"U.U32Nat.odd({x})"


def MOD(a, b):
    return f"Nat.mod({a}, {b})"


def ADD(a, b):
    return f"Nat.add({a}, {b})"


def MUL(a, b):
    return f"Nat.mul({a}, {b})"


def POW(a, b):
    return f"Nat.pow({a}, {b})"


def DBL(x):
    return f"Nat.double({x})"


def EQ(a, b, ty="Nat"):
    return "{" + f"{a} == {b} : {ty}" + "}"


def TR(ty, a, b, c, ab, bc):
    return f"Equal.trans({ty}, {a}, {b}, {c}, {ab}, {bc})"


def SY(ty, a, b, e):
    return f"Equal.sym({ty}, {a}, {b}, {e})"


def CG(A, B, body, a, b, e):
    return f"Equal.cong({A}, {B}, zz => {body}, {a}, {b}, {e})"


def LTx(x, y):
    return btrue(f"Nat.is_lt({x}, {y})")


def H(name, lhs, rhs):
    return hyp(name, lhs, rhs)


def le_rw(x, y, x2, y2, ex, ey, h):
    cur, a, b = h, x, y
    if ex is not None:
        cur = (f"Equal.trans(Bool, Nat.is_le({x2}, {b}), Nat.is_le({a}, {b}), True{{}}, "
               f"Equal.cong(Nat, Bool, zz => Nat.is_le(zz, {b}), {x2}, {a}, Equal.sym(Nat, {a}, {x2}, {ex})), {cur})")
        a = x2
    if ey is not None:
        cur = (f"Equal.trans(Bool, Nat.is_le({a}, {y2}), Nat.is_le({a}, {b}), True{{}}, "
               f"Equal.cong(Nat, Bool, zz => Nat.is_le({a}, zz), {y2}, {b}, Equal.sym(Nat, {b}, {y2}, {ey})), {cur})")
    return cur


# the lemmas of PROOF_mod.bend as hypotheses
def la(k, a, b):
    return H(f"by.la({k}, {a}, {b})", LOW(k, ADD(a, b)), LOW(k, ADD(LOW(k, a), b)))


def lar(k, a, b):
    return H(f"by.lar({k}, {a}, {b})", LOW(k, ADD(a, b)), LOW(k, ADD(a, LOW(k, b))))


def lm(k, a, b):
    return H(f"by.lm({k}, {a}, {b})", LOW(k, MUL(a, b)), LOW(k, MUL(LOW(k, a), b)))


def lmr(k, a, b):
    return H(f"by.lmr({k}, {a}, {b})", LOW(k, MUL(a, b)), LOW(k, MUL(a, LOW(k, b))))


def ll(j, kk, m, x):
    return H(f"by.ll({j}, {kk}, {m}, {{==}}, {x})", LOW(j, LOW(m, x)), LOW(j, x))


def mml(a, b, B, h):
    return H(f"PX.bx.mml({a}, {b}, {B}, {h})", MOD(MUL(MOD(a, B), b), B), MOD(MUL(a, b), B))


def mmr(a, b, B, h):
    return H(f"PX.bx.mmr({a}, {b}, {B}, {h})", MOD(MUL(a, MOD(b, B)), B), MOD(MUL(a, b), B))


def mdl(K, y, B, h):
    return H(f"PX.bx.mdl({K}, {y}, {B}, {h})", MOD(D(K, MOD(y, B)), B), MOD(D(K, y), B))


def mam(A, q, B, h):
    return H(f"PX.bx.mam({A}, {q}, {B}, {h})", MOD(ADD(A, MUL(q, B)), B), MOD(A, B))


def lows():
    put("# Congruences modulo 2^k: reducing a summand or a factor first, and the\n"
        "# low j bits of the low m bits for j <= m\n")
    hk = HIGH("m", "x")
    c = calc(LOW("j", "x"),
             (LOW("j", ADD(LOW("m", "x"), D("m", hk))), sym(H("UL.low_high(m, x)", ADD(LOW("m", "x"), D("m", hk)), "x"))),
             (LOW("j", ADD(LOW("m", "x"), D("Nat.add(j, k)", hk))), sym(H("e", "Nat.add(j, k)", "m"))),
             (LOW("j", ADD(LOW("m", "x"), D("j", D("k", hk)))), sym(H(f"UL.dbl_dbl(j, k, {hk})", D("j", D("k", hk)), D("Nat.add(j, k)", hk)))),
             (LOW("j", LOW("m", "x")), H(f"UL.low_add_dbl(j, {LOW('m', 'x')}, {D('k', hk)})", LOW("j", ADD(LOW("m", "x"), D("j", D("k", hk)))), LOW("j", LOW("m", "x")))))
    put(f"""def by.ll(+j: Nat, +k: Nat, +m: Nat, +e: {EQ('Nat.add(j, k)', 'm')}, +x: Nat) -> {EQ(LOW('j', LOW('m', 'x')), LOW('j', 'x'))}:
  {sym(c).text}
""")
    ha = HIGH("k", "a")
    c = calc(LOW("k", ADD("a", "b")),
             (LOW("k", ADD(ADD(LOW("k", "a"), D("k", ha)), "b")), sym(H("UL.low_high(k, a)", ADD(LOW("k", "a"), D("k", ha)), "a"))),
             (LOW("k", ADD(ADD(LOW("k", "a"), "b"), D("k", ha))), "ring"),
             (LOW("k", ADD(LOW("k", "a"), "b")), H(f"UL.low_add_dbl(k, {ADD(LOW('k', 'a'), 'b')}, {ha})", LOW("k", ADD(ADD(LOW("k", "a"), "b"), D("k", ha))), LOW("k", ADD(LOW("k", "a"), "b")))))
    put(f"""def by.la(+k: Nat, +a: Nat, +b: Nat) -> {EQ(LOW('k', ADD('a', 'b')), LOW('k', ADD(LOW('k', 'a'), 'b')))}:
  {c.text}
""")
    c = calc(LOW("k", ADD("a", "b")), (LOW("k", ADD("b", "a")), "ring"), (LOW("k", ADD(LOW("k", "b"), "a")), la("k", "b", "a")),
             (LOW("k", ADD("a", LOW("k", "b"))), "ring"))
    put(f"""def by.lar(+k: Nat, +a: Nat, +b: Nat) -> {EQ(LOW('k', ADD('a', 'b')), LOW('k', ADD('a', LOW('k', 'b'))))}:
  {c.text}
""")
    c = calc(LOW("k", MUL("a", "b")),
             (LOW("k", MUL(ADD(LOW("k", "a"), D("k", ha)), "b")), sym(H("UL.low_high(k, a)", ADD(LOW("k", "a"), D("k", ha)), "a"))),
             (LOW("k", ADD(MUL(LOW("k", "a"), "b"), D("k", MUL(ha, "b")))), "ring"),
             (LOW("k", MUL(LOW("k", "a"), "b")), H(f"UL.low_add_dbl(k, {MUL(LOW('k', 'a'), 'b')}, {MUL(ha, 'b')})", LOW("k", ADD(MUL(LOW("k", "a"), "b"), D("k", MUL(ha, "b")))), LOW("k", MUL(LOW("k", "a"), "b")))))
    put(f"""def by.lm(+k: Nat, +a: Nat, +b: Nat) -> {EQ(LOW('k', MUL('a', 'b')), LOW('k', MUL(LOW('k', 'a'), 'b')))}:
  {c.text}
""")
    c = calc(LOW("k", MUL("a", "b")), (LOW("k", MUL("b", "a")), "ring"), (LOW("k", MUL(LOW("k", "b"), "a")), lm("k", "b", "a")),
             (LOW("k", MUL("a", LOW("k", "b"))), "ring"))
    put(f"""def by.lmr(+k: Nat, +a: Nat, +b: Nat) -> {EQ(LOW('k', MUL('a', 'b')), LOW('k', MUL('a', LOW('k', 'b'))))}:
  {c.text}
""")


def inverse():
    put("# bn.np: Newton's steps for n0^-1 mod 2^16, from n0 n0 = 1 mod 8\n")
    lt1632 = (f"Equal.trans(Bool, Nat.is_lt({W16}, {W32}), Nat.is_lt(Nat.add(0n, {W16}), {W32}), True{{}}, "
              f"Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, {W32}), {W16}, Nat.add(0n, {W16}), Equal.sym(Nat, Nat.add(0n, {W16}), {W16}, PL.bq.a0({W16}))), "
              f"PL.bq.k2w(16n, 14n, 32n, 0n, {{==}}, {{==}}, {{==}}))")
    put(f"""def by.w65() -> {EQ(v('65536'), W16)}:
  Equal.trans(Nat, U32.to_nat(65536), U32.to_nat(U32.shln(1, 16n)), {W16}, Equal.cong(U32, Nat, zz => U32.to_nat(zz), 65536, U32.shln(1, 16n), {{==}}), Equal.trans(Nat, U32.to_nat(U32.shln(1, 16n)), {LOW('32n', D('16n', v('1')))}, {W16}, UL.u32_shln_low(1, 16n), Equal.trans(Nat, {LOW('32n', D('16n', v('1')))}, {LOW('32n', W16)}, {W16}, Equal.cong(Nat, Nat, zz => {LOW('32n', D('16n', 'zz'))}, U32.to_nat(1), 1n, {{==}}), UL.low_small(32n, {W16}, {lt1632}))))
""")
    # n0 n0 = 1 mod 8: by cases on n0 mod 8
    def sq8(d, var):
        ind = "  " * (d + 1)
        lines = [f"{ind}match {var}:"]
        lines.append(f"{ind}  case 0n:")
        if d % 2 == 1:
            lines.append(f"{ind}    {{==}}")
        else:
            lines.append(f"{ind}    Empty.absurd({{U.U32Nat.low(3n, Nat.mul({d}n, {d}n)) == 1n : Nat}}, PL.bq.zs(0n, ho))")
        nv = f"r{d + 1}"
        lines.append(f"{ind}  case 1n+{nv}:")
        if d + 1 == 8:
            ind2 = ind + "    "
            lines.append(f"{ind2}match {nv}:")
            lines.append(f"{ind2}  case 0n:")
            lines.append(f"{ind2}    Empty.absurd({{U.U32Nat.low(3n, Nat.mul(8n, 8n)) == 1n : Nat}}, PL.bq.ft(hr))")
            lines.append(f"{ind2}  case 1n+r9:")
            lines.append(f"{ind2}    Empty.absurd({{U.U32Nat.low(3n, Nat.mul(9n+r9, 9n+r9)) == 1n : Nat}}, PL.bq.ft(hr))")
        else:
            lines.append(sq8(d + 1, nv))
        return "\n".join(lines)
    put(f"""def by.sq8(r: Nat, hr: {LTx('r', '8n')}, ho: {EQ(LOW('1n', 'r'), '1n')}) -> {EQ(LOW('3n', MUL('r', 'r')), '1n')}:
{sq8(0, 'r')}
""")
    vx = v("x")
    r = LOW("3n", vx)
    c = calc(LOW("3n", MUL(vx, vx)), (LOW("3n", MUL(r, vx)), lm("3n", vx, vx)), (LOW("3n", MUL(r, r)), lmr("3n", r, vx)))
    put(f"""def by.n8(+x: U32, +ho: {EQ(LOW('1n', vx), '1n')}) -> {EQ(LOW('3n', MUL(vx, vx)), '1n')}:
  Equal.trans(Nat, {LOW('3n', MUL(vx, vx))}, {LOW('3n', MUL(r, r))}, 1n, {c.text}, by.sq8({r}, UL.low_lt(3n, {vx}), Equal.trans(Nat, {LOW('1n', r)}, {LOW('1n', vx)}, 1n, by.ll(1n, 2n, 3n, {{==}}, {vx}), ho)))
""")
    # Newton's step
    vi = v("i")
    P = "U32.mul(x, i)"
    S = f"U32.sub(2, {P})"
    R = f"U32.and(65535, U32.mul(i, {S}))"
    vS, vR, vP = v(S), v(R), v(P)
    u = MUL(vx, vi)
    h = HIGH("J", u)
    DJh = D("J", h)
    beta = f"U.U32Nat.bit(U32.is_lt(2, {P}))"
    q1 = HIGH("16n", ADD(vS, u))
    Z = D("J", D("J", MUL(h, h)))
    f1 = calc(vR, (LOW("16n", v(f"U32.mul(i, {S})")), H(f"PL.bq.lo(U32.mul(i, {S}))", vR, LOW("16n", v(f"U32.mul(i, {S})")))),
              (LOW("16n", LOW("32n", MUL(vi, vS))), H(f"UL.u32_mul_low(i, {S})", v(f"U32.mul(i, {S})"), LOW("32n", MUL(vi, vS)))),
              (LOW("16n", MUL(vi, vS)), ll("16n", "16n", "32n", MUL(vi, vS))))
    f3 = calc(LOW("16n", ADD(vS, u)),
              (LOW("16n", ADD(u, vS)), "ring"),
              (LOW("16n", ADD(LOW("16n", u), vS)), la("16n", u, vS)),
              (LOW("16n", ADD(LOW("16n", LOW("32n", u)), vS)), sym(ll("16n", "16n", "32n", u))),
              (LOW("16n", ADD(LOW("32n", u), vS)), sym(la("16n", LOW("32n", u), vS))),
              (LOW("16n", ADD(vP, vS)), sym(H("UL.u32_mul_low(x, i)", vP, LOW("32n", u)))),
              (LOW("16n", ADD(vS, vP)), "ring"),
              (LOW("16n", ADD(v("2"), D("32n", beta))), H(f"UL.u32_sub_wrap(2, {P})", ADD(vS, vP), ADD(v("2"), D("32n", beta)))),
              (LOW("16n", ADD("2n", D("Nat.add(16n, 16n)", beta))), "="),
              (LOW("16n", ADD("2n", D("16n", D("16n", beta)))), sym(H(f"UL.dbl_dbl(16n, 16n, {beta})", D("16n", D("16n", beta)), D("Nat.add(16n, 16n)", beta)))),
              (LOW("16n", "2n"), H(f"UL.low_add_dbl(16n, 2n, {D('16n', beta)})", LOW("16n", ADD("2n", D("16n", D("16n", beta)))), LOW("16n", "2n"))),
              ("2n", "="))
    f5 = calc(ADD(vS, u), (ADD(LOW("16n", ADD(vS, u)), D("16n", q1)), sym(H(f"UL.low_high(16n, {ADD(vS, u)})", ADD(LOW("16n", ADD(vS, u)), D("16n", q1)), ADD(vS, u)))),
              (ADD("2n", D("16n", q1)), H("f3", LOW("16n", ADD(vS, u)), "2n")))
    f4 = calc(u, (ADD(LOW("J", u), DJh), sym(H(f"UL.low_high(J, {u})", ADD(LOW("J", u), DJh), u))), (ADD("1n", DJh), H("hJ", LOW("J", u), "1n")))
    F4 = H("f4", u, ADD("1n", DJh))
    eg = calc(ADD("1n", ADD(vS, DJh)), (ADD(vS, ADD("1n", DJh)), "ring"), (ADD(vS, u), sym(F4)), (ADD("2n", D("16n", q1)), H("f5", ADD(vS, u), ADD("2n", D("16n", q1)))),
              (ADD("1n", ADD("1n", D("16n", q1))), "="))
    G = H("g", ADD(vS, DJh), ADD("1n", D("16n", q1)))
    Y = MUL(vx, vR)
    key = calc(LOW("16n", ADD(Y, Z)),
               (LOW("16n", ADD(LOW("16n", Y), Z)), la("16n", Y, Z)),
               (LOW("16n", ADD(LOW("16n", MUL(vx, LOW("16n", MUL(vi, vS)))), Z)), H("f1", vR, LOW("16n", MUL(vi, vS)))),
               (LOW("16n", ADD(LOW("16n", MUL(vx, MUL(vi, vS))), Z)), sym(lmr("16n", vx, MUL(vi, vS)))),
               (LOW("16n", ADD(MUL(vx, MUL(vi, vS)), Z)), sym(la("16n", MUL(vx, MUL(vi, vS)), Z))),
               (LOW("16n", ADD(MUL(u, vS), Z)), "ring"),
               (LOW("16n", ADD(MUL(ADD("1n", DJh), vS), Z)), F4),
               (LOW("16n", ADD(vS, MUL(DJh, ADD(vS, DJh)))), "ring"),
               (LOW("16n", ADD(vS, MUL(DJh, ADD("1n", D("16n", q1))))), G),
               (LOW("16n", ADD(ADD(vS, DJh), D("16n", MUL(DJh, q1)))), "ring"),
               (LOW("16n", ADD(ADD("1n", D("16n", q1)), D("16n", MUL(DJh, q1)))), G),
               (LOW("16n", ADD("1n", D("16n", ADD(q1, MUL(DJh, q1))))), "ring"),
               (LOW("16n", "1n"), H(f"UL.low_add_dbl(16n, 1n, {ADD(q1, MUL(DJh, q1))})", LOW("16n", ADD("1n", D("16n", ADD(q1, MUL(DJh, q1))))), LOW("16n", "1n"))),
               ("1n", "="))
    hh = MUL(h, h)
    fin = calc(LOW("J2", Y),
               (LOW("J2", ADD(Y, D("J2", D("E", hh)))), sym(H(f"UL.low_add_dbl(J2, {Y}, {D('E', hh)})", LOW("J2", ADD(Y, D("J2", D("E", hh)))), LOW("J2", Y)))),
               (LOW("J2", ADD(Y, D("Nat.add(J2, E)", hh))), H(f"UL.dbl_dbl(J2, E, {hh})", D("J2", D("E", hh)), D("Nat.add(J2, E)", hh))),
               (LOW("J2", ADD(Y, D("Nat.add(J, J)", hh))), H("e1", "Nat.add(J2, E)", "Nat.add(J, J)")),
               (LOW("J2", ADD(Y, Z)), sym(H(f"UL.dbl_dbl(J, J, {hh})", Z, D("Nat.add(J, J)", hh)))),
               (LOW("J2", LOW("16n", ADD(Y, Z))), sym(H(f"by.ll(J2, F, 16n, e2, {ADD(Y, Z)})", LOW("J2", LOW("16n", ADD(Y, Z))), LOW("J2", ADD(Y, Z))))),
               (LOW("J2", "1n"), H("key", LOW("16n", ADD(Y, Z)), "1n")),
               ("1n", H("hJ2", LOW("J2", "1n"), "1n")))
    put(f"""def by.nw(+J: Nat, +J2: Nat, +E: Nat, +F: Nat, +x: U32, +i: U32, +hJ: {EQ(LOW('J', u), '1n')}, +e1: {EQ('Nat.add(J2, E)', 'Nat.add(J, J)')}, +e2: {EQ('Nat.add(J2, F)', '16n')}, +hJ2: {EQ(LOW('J2', '1n'), '1n')}) -> {EQ(LOW('J2', MUL(vx, v('Mt.bn.inv16(x, i)'))), '1n')}:
  +f1 = {f1.text}
  +f3 = {f3.text}
  +f5 = {f5.text}
  +f4 = {f4.text}
  +g = UL.nat_add_cancel(1n, {ADD(vS, DJh)}, {ADD('1n', D('16n', q1))}, {eg.text})
  +key = {key.text}
  {fin.text}
""")
    i1 = "Mt.bn.inv16(n0, n0)"
    i2 = f"Mt.bn.inv16(n0, {i1})"
    i3 = f"Mt.bn.inv16(n0, {i2})"
    i4 = f"Mt.bn.inv16(n0, {i3})"
    n0 = v("n0")
    vI = v(i4)
    T4 = f"U32.mul({i3}, U32.sub(2, U32.mul(n0, {i3})))"
    SB = f"U32.sub(65536, {i4})"
    vSB = v(SB)
    hI = lt_rw(LOW("16n", v(T4)), W16, vI, W16, SY("Nat", v(f"U32.and(65535, {T4})"), LOW("16n", v(T4)), f"PL.bq.lo({T4})"), None, f"UL.low_lt(16n, {v(T4)})")
    hle = f"PL.bq.lt_le({vI}, {v('65536')}, {lt_rw(vI, W16, vI, v('65536'), None, SY('Nat', v('65536'), W16, 'by.w65()'), 'hI')})"
    esb = calc(ADD(vSB, vI), (ADD(f"Nat.sub({v('65536')}, {vI})", vI), H(f"UL.u32_sub_value(65536, {i4}, hle)", vSB, f"Nat.sub({v('65536')}, {vI})")),
               (v("65536"), H(f"UL.nat_le_witness({vI}, {v('65536')}, hle)", ADD(f"Nat.sub({v('65536')}, {vI})", vI), v("65536"))),
               (W16, H("by.w65()", v("65536"), W16)))
    npv = v(f"U32.and(65535, {SB})")
    c = calc(LOW("16n", ADD(MUL(n0, npv), "1n")),
             (LOW("16n", ADD(MUL(n0, LOW("16n", vSB)), "1n")), H(f"PL.bq.lo({SB})", npv, LOW("16n", vSB))),
             (LOW("16n", ADD(LOW("16n", MUL(n0, LOW("16n", vSB))), "1n")), la("16n", MUL(n0, LOW("16n", vSB)), "1n")),
             (LOW("16n", ADD(LOW("16n", MUL(n0, vSB)), "1n")), sym(lmr("16n", n0, vSB))),
             (LOW("16n", ADD(MUL(n0, vSB), "1n")), sym(la("16n", MUL(n0, vSB), "1n"))),
             (LOW("16n", ADD(MUL(n0, vSB), LOW("16n", MUL(n0, vI)))), sym(H("h4", LOW("16n", MUL(n0, vI)), "1n"))),
             (LOW("16n", ADD(MUL(n0, vSB), MUL(n0, vI))), sym(lar("16n", MUL(n0, vSB), MUL(n0, vI)))),
             (LOW("16n", MUL(n0, ADD(vSB, vI))), "ring"),
             (LOW("16n", MUL(n0, W16)), H("esb", ADD(vSB, vI), W16)),
             (LOW("16n", ADD("0n", D("16n", n0))), "ring"),
             (LOW("16n", "0n"), H(f"UL.low_add_dbl(16n, 0n, {n0})", LOW("16n", ADD("0n", D("16n", n0))), LOW("16n", "0n"))),
             ("0n", "="))
    put(f"""def by.np(+n0: U32, +ho: {EQ(LOW('1n', n0), '1n')}) -> {EQ(LOW('16n', ADD(MUL(n0, v('Mt.bn.np(n0)')), '1n')), '0n')}:
  +h1 = by.nw(3n, 6n, 0n, 10n, n0, n0, by.n8(n0, ho), {{==}}, {{==}}, {{==}})
  +h2 = by.nw(6n, 12n, 0n, 4n, n0, {i1}, h1, {{==}}, {{==}}, {{==}})
  +h3 = by.nw(12n, 16n, 8n, 0n, n0, {i2}, h2, {{==}}, {{==}}, {{==}})
  +h4 = by.nw(16n, 16n, 16n, 0n, n0, {i3}, h3, {{==}}, {{==}}, {{==}})
  +hI = {hI}
  +hle = {hle}
  +esb = {esb.text}
  {c.text}
""")


# ---------------------------------------------------------------- REDC

VN = V("n")
HNP = EQ(LOW("16n", ADD(MUL(v("N.bn.hd(n)"), v("np")), "1n")), "0n")


def redc():
    put("# A REDC step: the low limb of t1 + m n is 0, so 2^16 t' = t1 + m n\n")
    M = "U32.and(65535, U32.mul(N.bn.hd(t1), np))"
    T2 = f"N.bn.mac(n, {M}, t1, 0)"
    vM = v(M)
    z = v("N.bn.hd(t1)")
    vnp = v("np")
    n0 = v("N.bn.hd(n)")
    Vt1 = V("t1")
    MULT = "U32.mul(N.bn.hd(t1), np)"
    hM = lt_rw(LOW("16n", v(MULT)), W16, vM, W16, SY("Nat", vM, LOW("16n", v(MULT)), f"PL.bq.lo({MULT})"), None, f"UL.low_lt(16n, {v(MULT)})")
    eT2 = calc(V(T2), (ADD(ADD(Vt1, MUL(vM, VN)), v("0")), H(f"PM.bm.mv(n, {M}, t1, 0, hn, hm, h1, PL.bq.z16())", V(T2), ADD(ADD(Vt1, MUL(vM, VN)), v("0")))),
               (ADD(ADD(Vt1, MUL(vM, VN)), "0n"), "="),
               (ADD(Vt1, MUL(vM, VN)), H(f"UL.nat_add_zero({ADD(Vt1, MUL(vM, VN))})", ADD(ADD(Vt1, MUL(vM, VN)), "0n"), ADD(Vt1, MUL(vM, VN)))))
    eM = calc(vM, (LOW("16n", v(MULT)), H(f"PL.bq.lo({MULT})", vM, LOW("16n", v(MULT)))),
              (LOW("16n", LOW("32n", MUL(z, vnp))), H(f"UL.u32_mul_low(N.bn.hd(t1), np)", v(MULT), LOW("32n", MUL(z, vnp)))),
              (LOW("16n", MUL(z, vnp)), ll("16n", "16n", "32n", MUL(z, vnp))))
    ez = H("PX.bx.hdl(t1, h1)", z, LOW("16n", Vt1))
    en0 = H("PX.bx.hdl(n, hn)", n0, LOW("16n", VN))
    key = calc(LOW("16n", V(T2)),
               (LOW("16n", ADD(Vt1, MUL(vM, VN))), H("eT2", V(T2), ADD(Vt1, MUL(vM, VN)))),
               (LOW("16n", ADD(LOW("16n", Vt1), MUL(vM, VN))), la("16n", Vt1, MUL(vM, VN))),
               (LOW("16n", ADD(z, MUL(vM, VN))), sym(ez)),
               (LOW("16n", ADD(z, LOW("16n", MUL(vM, VN)))), lar("16n", z, MUL(vM, VN))),
               (LOW("16n", ADD(z, LOW("16n", MUL(LOW("16n", MUL(z, vnp)), VN)))), H("eM", vM, LOW("16n", MUL(z, vnp)))),
               (LOW("16n", ADD(z, LOW("16n", MUL(MUL(z, vnp), VN)))), sym(lm("16n", MUL(z, vnp), VN))),
               (LOW("16n", ADD(z, LOW("16n", MUL(MUL(z, vnp), LOW("16n", VN))))), lmr("16n", MUL(z, vnp), VN)),
               (LOW("16n", ADD(z, LOW("16n", MUL(MUL(z, vnp), n0)))), sym(en0)),
               (LOW("16n", ADD(z, MUL(MUL(z, vnp), n0))), sym(lar("16n", z, MUL(MUL(z, vnp), n0)))),
               (LOW("16n", MUL(ADD(MUL(n0, vnp), "1n"), z)), "ring"),
               (LOW("16n", MUL(LOW("16n", ADD(MUL(n0, vnp), "1n")), z)), lm("16n", ADD(MUL(n0, vnp), "1n"), z)),
               (LOW("16n", MUL("0n", z)), H("hnp", LOW("16n", ADD(MUL(n0, vnp), "1n")), "0n")),
               ("0n", "="))
    TLT2 = V(f"N.bn.tl({T2})")
    fin = calc(D("16n", TLT2), (ADD("0n", D("16n", TLT2)), "="),
               (ADD(v(f"N.bn.hd({T2})"), D("16n", TLT2)), sym(H("ehd", v(f"N.bn.hd({T2})"), "0n"))),
               (V(T2), H(f"PX.bx.tlv({T2})", ADD(v(f"N.bn.hd({T2})"), D("16n", TLT2)), V(T2))),
               (ADD(Vt1, MUL(vM, VN)), H("eT2", V(T2), ADD(Vt1, MUL(vM, VN)))))
    put(f"""def by.s2(+t1: {LIST}, +n: {LIST}, +np: U32, +h1: {OKT('t1')}, +hn: {OKT('n')}, +hnp: {HNP}) -> {EQ(D('16n', TLT2), ADD(Vt1, MUL(vM, VN)))}:
  +hm = {hM}
  +ok2 = PM.bm.mok(n, {M}, t1, 0, h1, PL.bq.z16())
  +eT2 = {eT2.text}
  +eM = {eM.text}
  +key = {key.text}
  +ehd = Equal.trans(Nat, {v(f'N.bn.hd({T2})')}, {LOW('16n', V(T2))}, 0n, PX.bx.hdl({T2}, ok2), key)
  {fin.text}
""")
    # the bound
    wa, A = NP.wit_lt("a0", W16, "ha")
    wm, Mw = NP.wit_lt("m", W16, "hm")
    wt, Tw = NP.wit_lt("T", "Nat.double(Nv)", "ht")
    wb, Bw = NP.wit_lt("B", "Nv", "hB")
    S = ADD(ADD("T", MUL("a0", "B")), MUL("m", "Nv"))
    w = ADD(ADD(ADD("a0", MUL("a0", wb)), MUL(ADD(wa, wm), "Nv")), wt)
    pf = calc(ADD(w, f"1n+{S}"),
              (ADD(ADD(MUL("a0", ADD(wb, "1n+B")), MUL(ADD(wa, wm), "Nv")), ADD(MUL("m", "Nv"), ADD(wt, "1n+T"))), "ring"),
              (ADD(ADD(MUL("a0", "Nv"), MUL(ADD(wa, wm), "Nv")), ADD(MUL("m", "Nv"), ADD(wt, "1n+T"))), Bw),
              (ADD(ADD(MUL("a0", "Nv"), MUL(ADD(wa, wm), "Nv")), ADD(MUL("m", "Nv"), DBL("Nv"))), Tw),
              (ADD(MUL("Nv", ADD(wa, "1n+a0")), MUL("Nv", ADD(wm, "1n+m"))), "ring"),
              (ADD(MUL("Nv", W16), MUL("Nv", ADD(wm, "1n+m"))), A),
              (ADD(MUL("Nv", W16), MUL("Nv", W16)), Mw),
              (D("16n", DBL("Nv")), "ring"))
    put(f"""def by.bd(+T: Nat, +a0: Nat, +B: Nat, +m: Nat, +Nv: Nat, +ht: {LTx('T', DBL('Nv'))}, +ha: {LTx('a0', W16)}, +hB: {LTx('B', 'Nv')}, +hm: {LTx('m', W16)}) -> {LTx(S, D('16n', DBL('Nv')))}:
  {NP.lt_from(S, D('16n', DBL('Nv')), w, pf)}

def by.dlt(+a: Nat, +b: Nat, h: {LTx('a', 'b')}) -> {LTx(DBL('a'), DBL('b'))}:
  Equal.trans(Bool, Nat.is_lt(Nat.double(a), Nat.double(b)), Nat.is_lt(a, b), True{{}}, UL.dbl_lt(1n, a, b), h)

def by.p2(N0: Nat, h: {LTx('0n', 'N0')}) -> {LTx('0n', DBL('N0'))}:
  match N0:
    case 0n:
      Empty.absurd({LTx('0n', DBL('0n'))}, PL.bq.ft(h))
    case 1n+q:
      {{==}}
""")
    # the loop
    T1 = "N.bn.mac(b, N.bn.hd(a), t, 0)"
    Mm = f"U32.and(65535, U32.mul(N.bn.hd({T1}), np))"
    T2l = f"N.bn.mac(n, {Mm}, {T1}, 0)"
    TL = f"N.bn.tl({T2l})"
    a0 = v("N.bn.hd(a)")
    okT1 = f"PM.bm.mok(b, N.bn.hd(a), t, 0, ht, PL.bq.z16())"
    okT2 = f"PM.bm.mok(n, {Mm}, {T1}, 0, {okT1}, PL.bq.z16())"
    okTL = f"PX.bx.tlk({T2l}, {okT2})"
    GO = lambda i, a, t: f"Mt.bn.mm.go({i}, {a}, b, n, np, {t})"
    put(f"""def by.gk(i: Nat, +a: {LIST}, +b: {LIST}, +n: {LIST}, +np: U32, +t: {LIST}, +ht: {OKT('t')}) -> {OKT(GO('i', 'a', 't'))}:
  match i:
    case 0n:
      ht
    case 1n+ +p:
      by.gk(p, N.bn.tl(a), b, n, np, {TL}, {okTL})
""")
    s1 = calc(V(T1), (ADD(ADD(V("t"), MUL(a0, V("b"))), v("0")), H(f"PM.bm.mv(b, N.bn.hd(a), t, 0, hb, PX.bx.hdlt(a, ha), ht, PL.bq.z16())", V(T1), ADD(ADD(V("t"), MUL(a0, V("b"))), v("0")))),
              (ADD(ADD(V("t"), MUL(a0, V("b"))), "0n"), "="),
              (ADD(V("t"), MUL(a0, V("b"))), H(f"UL.nat_add_zero({ADD(V('t'), MUL(a0, V('b')))})", ADD(ADD(V("t"), MUL(a0, V("b"))), "0n"), ADD(V("t"), MUL(a0, V("b"))))))
    vMm = v(Mm)
    MULm = f"U32.mul(N.bn.hd({T1}), np)"
    hMm = lt_rw(LOW("16n", v(MULm)), W16, vMm, W16, SY("Nat", vMm, LOW("16n", v(MULm)), f"PL.bq.lo({MULm})"), None, f"UL.low_lt(16n, {v(MULm)})")
    S2 = H(f"by.s2({T1}, n, np, {okT1}, hn, hnp)", D("16n", V(TL)), ADD(V(T1), MUL(vMm, VN)))
    S1 = H("s1", V(T1), ADD(V("t"), MUL(a0, V("b"))))
    efull = calc(D("16n", V(TL)), (ADD(V(T1), MUL(vMm, VN)), S2), (ADD(ADD(V("t"), MUL(a0, V("b"))), MUL(vMm, VN)), S1))
    SS = ADD(ADD(V("t"), MUL(a0, V("b"))), MUL(vMm, VN))
    hT = lt_rw(SS, D("16n", DBL(VN)), D("16n", V(TL)), D("16n", DBL(VN)), sym(efull).text, None,
               f"by.bd({V('t')}, {a0}, {V('b')}, {vMm}, {VN}, htl, PX.bx.hdlt(a, ha), hbl, {hMm})")
    htl2 = f"Equal.trans(Bool, Nat.is_lt({V(TL)}, {DBL(VN)}), Nat.is_lt({D('16n', V(TL))}, {D('16n', DBL(VN))}), True{{}}, Equal.sym(Bool, Nat.is_lt({D('16n', V(TL))}, {D('16n', DBL(VN))}), Nat.is_lt({V(TL)}, {DBL(VN)}), UL.dbl_lt(16n, {V(TL)}, {DBL(VN)})), {hT})"
    common = f"+a: {LIST}, +b: {LIST}, +n: {LIST}, +np: U32, +t: {LIST}, +ha: {OKT('a')}, +hb: {OKT('b')}, +hn: {OKT('n')}, +ht: {OKT('t')}, +hnp: {HNP}"
    put(f"""def by.gb(i: Nat, {common}, +hbl: {LTx(V('b'), VN)}, +htl: {LTx(V('t'), DBL(VN))}) -> {LTx(V(GO('i', 'a', 't')), DBL(VN))}:
  match i:
    case 0n:
      htl
    case 1n+ +p:
      +s1 = {s1.text}
      by.gb(p, N.bn.tl(a), b, n, np, {TL}, PX.bx.tlk(a, ha), hb, hn, {okTL}, hnp, hbl, {htl2})
""")
    Mp = "Nat.mul(p, 16n)"
    R = V(GO("p", "N.bn.tl(a)", TL))
    Vtla = V("N.bn.tl(a)")
    hal16 = lt_rw(V("a"), D(ADD("16n", Mp), "1n"), V("a"), D("16n", D(Mp, "1n")), None, f"Equal.sym(Nat, {D('16n', D(Mp, '1n'))}, {D(ADD('16n', Mp), '1n')}, UL.dbl_dbl(16n, {Mp}, 1n))", "hal")
    le16 = NP.le_from(D("16n", Vtla), V("a"), a0, H("PX.bx.tlv(a)", ADD(a0, D("16n", Vtla)), V("a")))
    lt16 = f"PL.bq.lelt({D('16n', Vtla)}, {V('a')}, {D('16n', D(Mp, '1n'))}, {le16}, {hal16})"
    hal2 = f"Equal.trans(Bool, Nat.is_lt({Vtla}, {D(Mp, '1n')}), Nat.is_lt({D('16n', Vtla)}, {D('16n', D(Mp, '1n'))}), True{{}}, Equal.sym(Bool, Nat.is_lt({D('16n', Vtla)}, {D('16n', D(Mp, '1n'))}), Nat.is_lt({Vtla}, {D(Mp, '1n')}), UL.dbl_lt(16n, {Vtla}, {D(Mp, '1n')})), {lt16})"
    IH = H(f"by.gv(p, N.bn.tl(a), b, n, np, {TL}, PX.bx.tlk(a, ha), hb, hn, {okTL}, hnp, hn0, {hal2})", MOD(D(Mp, R), VN), MOD(ADD(V(TL), MUL(Vtla, V("b"))), VN))
    Vb = V("b")
    inner = ADD(V("t"), MUL(ADD(a0, D("16n", Vtla)), Vb))
    c = calc(MOD(D(ADD("16n", Mp), R), VN),
             (MOD(D("16n", D(Mp, R)), VN), sym(H(f"UL.dbl_dbl(16n, {Mp}, {R})", D("16n", D(Mp, R)), D(ADD("16n", Mp), R)))),
             (MOD(D("16n", MOD(D(Mp, R), VN)), VN), sym(mdl("16n", D(Mp, R), VN, "hn0"))),
             (MOD(D("16n", MOD(ADD(V(TL), MUL(Vtla, Vb)), VN)), VN), IH),
             (MOD(D("16n", ADD(V(TL), MUL(Vtla, Vb))), VN), mdl("16n", ADD(V(TL), MUL(Vtla, Vb)), VN, "hn0")),
             (MOD(ADD(D("16n", V(TL)), D("16n", MUL(Vtla, Vb))), VN), "ring"),
             (MOD(ADD(ADD(V(T1), MUL(vMm, VN)), D("16n", MUL(Vtla, Vb))), VN), S2),
             (MOD(ADD(ADD(ADD(V("t"), MUL(a0, Vb)), MUL(vMm, VN)), D("16n", MUL(Vtla, Vb))), VN), S1),
             (MOD(ADD(inner, MUL(vMm, VN)), VN), "ring"),
             (MOD(inner, VN), mam(inner, vMm, VN, "hn0")),
             (MOD(ADD(V("t"), MUL(V("a"), Vb)), VN), H("PX.bx.tlv(a)", ADD(a0, D("16n", Vtla)), V("a"))))
    c0 = calc(MOD(ADD(V("t"), MUL(V("a"), Vb)), VN), (MOD(ADD(V("t"), MUL("0n", Vb)), VN), H(f"PL.bq.lt1({V('a')}, hal)", V("a"), "0n")),
              (MOD(ADD(V("t"), "0n"), VN), "="), (MOD(V("t"), VN), H(f"UL.nat_add_zero({V('t')})", ADD(V("t"), "0n"), V("t"))))
    put(f"""def by.gv(i: Nat, {common}, +hn0: {LTx('0n', VN)}, +hal: {LTx(V('a'), D('Nat.mul(i, 16n)', '1n'))}) -> {EQ(MOD(D('Nat.mul(i, 16n)', V(GO('i', 'a', 't'))), VN), MOD(ADD(V('t'), MUL(V('a'), Vb)), VN))}:
  match i:
    case 0n:
      {sym(c0).text}
    case 1n+ +p:
      +s1 = {s1.text}
      {c.text}
""")


def csub():
    put("# The conditional subtraction: t mod n, for t below 2 n\n")
    Vt = V("t")
    Sv = V("N.bn.sub(t, n, 0)")
    hl = le_rw(VN, Vt, ADD(VN, v("0")), Vt, SY("Nat", ADD(VN, "0n"), VN, f"UL.nat_add_zero({VN})"), None, "hle")
    e1 = calc(ADD(MUL("1n", VN), Sv), (ADD(ADD(Sv, VN), "0n"), "ring"), (ADD(ADD(Sv, VN), v("0")), "="), (Vt, H("sv", ADD(ADD(Sv, VN), v("0")), Vt)))
    e2 = calc(ADD(Sv, VN), (ADD(ADD(Sv, VN), "0n"), sym(H(f"UL.nat_add_zero({ADD(Sv, VN)})", ADD(ADD(Sv, VN), "0n"), ADD(Sv, VN)))),
              (ADD(ADD(Sv, VN), v("0")), "="), (Vt, H("sv", ADD(ADD(Sv, VN), v("0")), Vt)))
    hlt2 = lt_rw(Vt, DBL(VN), ADD(Sv, VN), ADD(VN, VN), sym(e2).text, f"UL.nat_double({VN})", "hlt")
    lt = (f"Equal.trans(Bool, Nat.is_lt({Sv}, {VN}), Nat.is_lt({ADD(Sv, VN)}, {ADD(VN, VN)}), True{{}}, "
          f"Equal.sym(Bool, Nat.is_lt({ADD(Sv, VN)}, {ADD(VN, VN)}), Nat.is_lt({Sv}, {VN}), Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Nat.cmp({ADD(Sv, VN)}, {ADD(VN, VN)}), Nat.cmp({Sv}, {VN}), PL.bq.ca({Sv}, {VN}, {VN}))), {hlt2})")
    base = f"+t: {LIST}, +n: {LIST}, +ht: {OKT('t')}, +hn: {OKT('n')}, +hlt: {LTx(Vt, DBL(VN))}"
    cmp = f"Nat.cmp({Vt}, {VN})"
    put(f"""def by.csgk(z: Bool, +t: {LIST}, +n: {LIST}, +ht: {OKT('t')}) -> {OKT('Mt.bn.csub.go(z, t, n)')}:
  match z:
    case True{{}}:
      PL.bq.sk(t, n, 0)
    case False{{}}:
      ht

def by.csk(+t: {LIST}, +n: {LIST}, +ht: {OKT('t')}) -> {OKT('Mt.bn.csub(t, n)')}:
  by.csgk(N.bn.ge(N.bn.cmp(t, n, EQ{{}})), t, n, ht)

def by.csge({base}, +hle: {btrue(f'Nat.is_le({VN}, {Vt})')}) -> {EQ(Sv, MOD(Vt, VN))}:
  +sv = PL.bq.sv(t, n, 0, ht, hn, {{==}}, {hl})
  Equal.sym(Nat, {MOD(Vt, VN)}, {Sv}, PX.bx.mu({Vt}, {VN}, 1n, {Sv}, {e1.text}, {lt}))

def by.csg(c: Cmp, {base}, ec: {EQ(cmp, 'c', 'Cmp')}) -> {EQ(V('Mt.bn.csub.go(N.bn.ge(c), t, n)'), MOD(Vt, VN))}:
  match c:
    case LT{{}}:
      Equal.sym(Nat, {MOD(Vt, VN)}, {Vt}, PX.bx.msm({Vt}, {VN}, Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), {cmp}, LT{{}}, ec)))
    case EQ{{}}:
      by.csge(t, n, ht, hn, hlt, {le_rw(VN, VN, VN, Vt, None, SY('Nat', Vt, VN, f'PL.bq.ceq({Vt}, {VN}, ec)'), f'UL.nat_le_refl({VN})')})
    case GT{{}}:
      by.csge(t, n, ht, hn, hlt, PL.bq.lt_le({VN}, {Vt}, PL.bq.gl({Vt}, {VN}, ec)))

def by.csv({base}) -> {EQ(V('Mt.bn.csub(t, n)'), MOD(Vt, VN))}:
  %Equal.sym(Cmp, N.bn.cmp(t, n, EQ{{}}), {cmp}, Equal.trans(Cmp, N.bn.cmp(t, n, EQ{{}}), N.bn.step({cmp}, EQ{{}}), {cmp}, PL.bq.cm(t, n, EQ{{}}, ht, hn), PL.bq.st({cmp}))) : {EQ(V('Mt.bn.csub.go(N.bn.ge(_), t, n)'), MOD(Vt, VN))}
  by.csg({cmp}, t, n, ht, hn, hlt, {{==}})

def by.trv(+xs: {LIST}, +k: Nat, +hx: {OKT('xs')}) -> {EQ(V('Mt.bn.trim(k, xs)'), LOW('Nat.mul(k, 16n)', V('xs')))}:
  PX.bx.tkv(xs, k, hx)

def by.trk(+xs: {LIST}, +k: Nat, +hx: {OKT('xs')}) -> {OKT('Mt.bn.trim(k, xs)')}:
  PX.bx.tkk(xs, k, hx)
""")


K = "Nat.mul(N.bn.len(n), 16n)"
KL = "N.bn.len(n)"


def MM(a, b, np="np", k=KL):
    return f"Mt.bn.mm({a}, {b}, n, {np}, {k})"


def F(u):
    return MOD(D(K, u), VN)


def mmlemmas():
    put("# Montgomery multiplication: (mm R) mod n = (a b) mod n, below n\n")
    G = f"Mt.bn.mm.go({KL}, a, b, n, np, N.bn.zeros({KL}))"
    C = f"Mt.bn.csub({G}, n)"
    put(f"""def by.mmk(+a: {LIST}, +b: {LIST}, +n: {LIST}, +np: U32, +k: Nat) -> {OKT('Mt.bn.mm(a, b, n, np, k)')}:
  PX.bx.tkk(Mt.bn.csub(Mt.bn.mm.go(k, a, b, n, np, N.bn.zeros(k)), n), k, by.csk(Mt.bn.mm.go(k, a, b, n, np, N.bn.zeros(k)), n, by.gk(k, a, b, n, np, N.bn.zeros(k), PX.bx.zk(k))))
""")
    okG = f"by.gk({KL}, a, b, n, np, N.bn.zeros({KL}), PX.bx.zk({KL}))"
    htl0 = lt_rw("0n", DBL(VN), V(f"N.bn.zeros({KL})"), DBL(VN), SY("Nat", V(f"N.bn.zeros({KL})"), "0n", f"PX.bx.zv({KL})"), None, f"by.p2({VN}, hn0)")
    hG = f"by.gb({KL}, a, b, n, np, N.bn.zeros({KL}), ha, hb, hn, PX.bx.zk({KL}), hnp, hbl, {htl0})"
    eC = H(f"by.csv({G}, n, {okG}, hn, {hG})", V(C), MOD(V(G), VN))
    okC = f"by.csk({G}, n, {okG})"
    hCn = lt_rw(MOD(V(G), VN), VN, V(C), VN, sym(eC).text, None, f"PD.bd.nml({V(G)}, {VN}, hn0)")
    hCl = f"PL.bq.lt_trans({V(C)}, {VN}, {D(K, '1n')}, {hCn}, PX.bx.vlt(n, hn))"
    eT = calc(V(f"Mt.bn.trim({KL}, {C})"), (LOW(K, V(C)), H(f"by.trv({C}, {KL}, {okC})", V(f"Mt.bn.trim({KL}, {C})"), LOW(K, V(C)))),
              (V(C), H(f"UL.low_small({K}, {V(C)}, {hCl})", LOW(K, V(C)), V(C))), (MOD(V(G), VN), eC))
    hyps = f"+a: {LIST}, +b: {LIST}, +n: {LIST}, +np: U32, +ha: {OKT('a')}, +hb: {OKT('b')}, +hn: {OKT('n')}, +hnp: {HNP}, +hn0: {LTx('0n', VN)}, +hbl: {LTx(V('b'), VN)}"
    put(f"""def by.mmv({hyps}) -> {EQ(V(MM('a', 'b')), MOD(V(G), VN))}:
  {eT.text}

def by.mml({hyps}) -> {LTx(V(MM('a', 'b')), VN)}:
  {lt_rw(MOD(V(G), VN), VN, V(MM('a', 'b')), VN, SY('Nat', V(MM('a', 'b')), MOD(V(G), VN), 'by.mmv(a, b, n, np, ha, hb, hn, hnp, hn0, hbl)'), None, f'PD.bd.nml({V(G)}, {VN}, hn0)')}
""")
    Va, Vb = V("a"), V("b")
    hal2 = f"PL.bq.lt_trans({Va}, {VN}, {D(K, '1n')}, hal, PX.bx.vlt(n, hn))"
    gv = H(f"by.gv({KL}, a, b, n, np, N.bn.zeros({KL}), ha, hb, hn, PX.bx.zk({KL}), hnp, hn0, {hal2})", MOD(D(K, V(G)), VN), MOD(ADD(V(f"N.bn.zeros({KL})"), MUL(Va, Vb)), VN))
    c = calc(MOD(D(K, V(MM("a", "b"))), VN),
             (MOD(D(K, MOD(V(G), VN)), VN), H("by.mmv(a, b, n, np, ha, hb, hn, hnp, hn0, hbl)", V(MM("a", "b")), MOD(V(G), VN))),
             (MOD(D(K, V(G)), VN), mdl(K, V(G), VN, "hn0")),
             (MOD(ADD(V(f"N.bn.zeros({KL})"), MUL(Va, Vb)), VN), gv),
             (MOD(ADD("0n", MUL(Va, Vb)), VN), H(f"PX.bx.zv({KL})", V(f"N.bn.zeros({KL})"), "0n")),
             (MOD(MUL(Va, Vb), VN), "="))
    put(f"""def by.mmc({hyps}, +hal: {LTx(Va, VN)}) -> {EQ(MOD(D(K, V(MM('a', 'b'))), VN), MOD(MUL(Va, Vb), VN))}:
  {c.text}
""")


CTXP = f"+n: {LIST}, +np: U32, +hn: {OKT('n')}, +hnp: {HNP}, +H: Nat, +hodd: {EQ(ADD('1n', DBL('H')), VN)}, +hn0: {LTx('0n', VN)}"
CTXA = "n, np, hn, hnp, H, hodd, hn0"
NPm = "Mt.bn.np(N.bn.hd(n))"
R2 = f"Mt.bn.mont.r2(Nat.mul(32n, {KL}), {ONE1}, n, {KL})"
ONEm = MM(R2, ONE1, NPm)
MKP = f"+n: {LIST}, +hn: {OKT('n')}, +ho: {EQ(LOW('1n', v('N.bn.hd(n)')), '1n')}, +hn1: {LTx('1n', VN)}"
CTXM = f"n, {NPm}, hn, by.np(N.bn.hd(n), ho), {HIGH('1n', VN)}, by.hodd(n, hn, ho), by.hn0(n, hn1)"
MK = "Mt.bn.mont.mk(n)"


def nml(a, b, h):
    return f"PD.bd.nml({a}, {b}, {h})"


def msm(a, b, h):
    return f"PX.bx.msm({a}, {b}, {h})"


def cancel():
    put("# R is cancelled modulo an odd n = 1 + 2 H: a = 2 a (1 + H) mod n\n")
    HB = "hB"

    def one(x):
        return calc(MOD(x, "B"),
                    (MOD(ADD(x, MUL(x, "B")), "B"), sym(mam(x, x, "B", HB))),
                    (MOD(ADD(x, MUL(x, ADD("1n", DBL("H")))), "B"), sym(H("eB", ADD("1n", DBL("H")), "B"))),
                    (MOD(MUL(DBL(x), ADD("1n", "H")), "B"), "ring"))
    c = calc(MOD("a", "B"),
             (MOD(MUL(DBL("a"), ADD("1n", "H")), "B"), one("a")),
             (MOD(MUL(MOD(DBL("a"), "B"), ADD("1n", "H")), "B"), sym(mml(DBL("a"), ADD("1n", "H"), "B", HB))),
             (MOD(MUL(MOD(DBL("b"), "B"), ADD("1n", "H")), "B"), H("e", MOD(DBL("a"), "B"), MOD(DBL("b"), "B"))),
             (MOD(MUL(DBL("b"), ADD("1n", "H")), "B"), mml(DBL("b"), ADD("1n", "H"), "B", HB)),
             (MOD("b", "B"), sym(one("b"))))
    put(f"""def by.c2(+a: Nat, +b: Nat, +B: Nat, +H: Nat, +eB: {EQ(ADD('1n', DBL('H')), 'B')}, +e: {EQ(MOD(DBL('a'), 'B'), MOD(DBL('b'), 'B'))}) -> {EQ(MOD('a', 'B'), MOD('b', 'B'))}:
  +hB = Equal.trans(Bool, Nat.is_lt(0n, B), Nat.is_lt(0n, {ADD('1n', DBL('H'))}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(0n, zz), B, {ADD('1n', DBL('H'))}, Equal.sym(Nat, {ADD('1n', DBL('H'))}, B, eB)), {{==}})
  {c.text}

def by.cd(K: Nat, +a: Nat, +b: Nat, +B: Nat, +H: Nat, +eB: {EQ(ADD('1n', DBL('H')), 'B')}, e: {EQ(MOD(D('K', 'a'), 'B'), MOD(D('K', 'b'), 'B'))}) -> {EQ(MOD('a', 'B'), MOD('b', 'B'))}:
  match K:
    case 0n:
      e
    case 1n+ +p:
      by.cd(p, a, b, B, H, eB, by.c2({D('p', 'a')}, {D('p', 'b')}, B, H, eB, e))
""")


def forms():
    put("# Montgomery forms: from (mm R) mod n = (a b) mod n with R cancelled\n")
    Va, Vb = V("a"), V("b")
    C = V(MM("a", "b"))
    hal = lt_rw(MOD("A", VN), VN, Va, VN, SY("Nat", Va, MOD("A", VN), "ea"), None, nml("A", VN, "hn0"))
    hbl = lt_rw(MOD("Bq", VN), VN, Vb, VN, SY("Nat", Vb, MOD("Bq", VN), "eb"), None, nml("Bq", VN, "hn0"))
    e1 = calc(MOD(D(K, C), VN),
              (MOD(MUL(Va, Vb), VN), H("by.mmc(a, b, n, np, ha, hb, hn, hnp, hn0, hbl, hal)", MOD(D(K, C), VN), MOD(MUL(Va, Vb), VN))),
              (MOD(MUL(MOD("A", VN), Vb), VN), H("ea", Va, MOD("A", VN))),
              (MOD(MUL(MOD("A", VN), MOD("Bq", VN)), VN), H("eb", Vb, MOD("Bq", VN))),
              (MOD(MUL("A", MOD("Bq", VN)), VN), mml("A", MOD("Bq", VN), VN, "hn0")),
              (MOD(MUL("A", "Bq"), VN), mmr("A", "Bq", VN, "hn0")),
              (MOD(D(K, "W"), VN), H("eAB", MUL("A", "Bq"), D(K, "W"))))
    put(f"""def by.mg2(+a: {LIST}, +b: {LIST}, +A: Nat, +Bq: Nat, +W: Nat, {CTXP}, +ha: {OKT('a')}, +hb: {OKT('b')}, +ea: {EQ(Va, MOD('A', VN))}, +eb: {EQ(Vb, MOD('Bq', VN))}, +eAB: {EQ(MUL('A', 'Bq'), D(K, 'W'))}) -> {EQ(C, MOD('W', VN))}:
  +hal = {hal}
  +hbl = {hbl}
  Equal.trans(Nat, {C}, {MOD(C, VN)}, {MOD('W', VN)}, Equal.sym(Nat, {MOD(C, VN)}, {C}, {msm(C, VN, 'by.mml(a, b, n, np, ha, hb, hn, hnp, hn0, hbl)')}), by.cd({K}, {C}, W, {VN}, H, hodd, {e1.text}))
""")
    put(f"""def by.mf(+a: {LIST}, +b: {LIST}, +u: Nat, +w: Nat, {CTXP}, +ha: {OKT('a')}, +hb: {OKT('b')}, +ea: {EQ(Va, F('u'))}, +eb: {EQ(Vb, F('w'))}) -> {EQ(C, F(MUL('u', 'w')))}:
  by.mg2(a, b, {D(K, 'u')}, {D(K, 'w')}, {D(K, MUL('u', 'w'))}, {CTXA}, ha, hb, ea, eb, {NP.ring(MUL(D(K, 'u'), D(K, 'w')), D(K, D(K, MUL('u', 'w')))).text})
""")


def rsq():
    put("# R^2 mod n: 1 doubled 32 k times, reduced at each step\n")
    SH = "N.bn.shl1(x, 0)"
    CS = f"Mt.bn.csub({SH}, n)"
    put(f"""def by.r2k(f: Nat, +x: {LIST}, +n: {LIST}, +k: Nat, +hx: {OKT('x')}) -> {OKT('Mt.bn.mont.r2(f, x, n, k)')}:
  match f:
    case 0n:
      hx
    case 1n+ +p:
      by.r2k(p, Mt.bn.trim(k, {CS}), n, k, by.trk({CS}, k, by.csk({SH}, n, PD.bd.s1k(x, 0, hx, {{==}}))))
""")
    Vx = V("x")
    VSH, VCS = V(SH), V(CS)
    X1 = f"Mt.bn.trim({KL}, {CS})"
    VX1 = V(X1)
    okSH = "PD.bd.s1k(x, 0, hx, {==})"
    eSH = calc(VSH, (ADD(DBL(Vx), v("0")), H(f"PD.bd.s1v(x, 0, hx, {{==}})", VSH, ADD(DBL(Vx), v("0")))), (ADD(DBL(Vx), "0n"), "="),
               (DBL(Vx), H(f"UL.nat_add_zero({DBL(Vx)})", ADD(DBL(Vx), "0n"), DBL(Vx))))
    hSH = lt_rw(DBL(Vx), DBL(VN), VSH, DBL(VN), sym(eSH).text, None, f"by.dlt({Vx}, {VN}, hxl)")
    eCS = H(f"by.csv({SH}, n, {okSH}, hn, {hSH})", VCS, MOD(VSH, VN))
    okCS = f"by.csk({SH}, n, {okSH})"
    hCSl = lt_rw(MOD(VSH, VN), VN, VCS, VN, sym(eCS).text, None, nml(VSH, VN, "hn0"))
    eX1 = calc(VX1, (LOW(K, VCS), H(f"by.trv({CS}, {KL}, {okCS})", VX1, LOW(K, VCS))),
               (VCS, H(f"UL.low_small({K}, {VCS}, PL.bq.lt_trans({VCS}, {VN}, {D(K, '1n')}, {hCSl}, PX.bx.vlt(n, hn)))", LOW(K, VCS), VCS)),
               (MOD(VSH, VN), eCS), (MOD(DBL(Vx), VN), eSH))
    hX1l = lt_rw(MOD(DBL(Vx), VN), VN, VX1, VN, sym(eX1).text, None, nml(DBL(Vx), VN, "hn0"))
    okX1 = f"by.trk({CS}, {KL}, {okCS})"
    R2p = f"Mt.bn.mont.r2(p, {X1}, n, {KL})"
    c = calc(V(R2p), (MOD(D("p", VX1), VN), H(f"by.r2v(p, {X1}, n, {okX1}, hn, hn0, {hX1l})", V(R2p), MOD(D("p", VX1), VN))),
             (MOD(D("p", MOD(DBL(Vx), VN)), VN), eX1),
             (MOD(D("p", DBL(Vx)), VN), mdl("p", DBL(Vx), VN, "hn0")),
             (MOD(D("p", D("1n", Vx)), VN), "="),
             (MOD(D("1n", D("p", Vx)), VN), H(f"UL.dbl_comm(p, 1n, {Vx})", D("p", D("1n", Vx)), D("1n", D("p", Vx)))),
             (MOD(D("1n+p", Vx), VN), "="))
    put(f"""def by.r2v(f: Nat, +x: {LIST}, +n: {LIST}, +hx: {OKT('x')}, +hn: {OKT('n')}, +hn0: {LTx('0n', VN)}, +hxl: {LTx(Vx, VN)}) -> {EQ(V(f'Mt.bn.mont.r2(f, x, n, {KL})'), MOD(D('f', Vx), VN))}:
  match f:
    case 0n:
      Equal.sym(Nat, {MOD(Vx, VN)}, {Vx}, {msm(Vx, VN, 'hxl')})
    case 1n+ +p:
      {c.text}
""")
    c = calc(V(R2), (MOD(D(MUL("32n", KL), V(ONE1)), VN), H(f"by.r2v(Nat.mul(32n, {KL}), {ONE1}, n, {{==}}, hn, hn0, hn1)", V(R2), MOD(D(MUL("32n", KL), V(ONE1)), VN))),
             (MOD(D(MUL("32n", KL), "1n"), VN), "="),
             (MOD(D(ADD(K, K), "1n"), VN), "ring"),
             (MOD(D(K, D(K, "1n")), VN), sym(H(f"UL.dbl_dbl({K}, {K}, 1n)", D(K, D(K, "1n")), D(ADD(K, K), "1n")))))
    put(f"""def by.r2f(+n: {LIST}, +hn: {OKT('n')}, +hn0: {LTx('0n', VN)}, +hn1: {LTx('1n', VN)}) -> {EQ(V(R2), MOD(D(K, D(K, '1n')), VN))}:
  {c.text}
""")


def mexp():
    put("# Montgomery exponentiation: square, and multiply where the bit is set,\n"
        "# over the bits of each limb and the limbs most significant first\n")
    vw = v("w")
    BIT = "U32.and(1, U32.shrn(w, p))"
    vB = v(BIT)
    O = ODD(HIGH("p", vw))
    DP = DBL("P")
    PX_ = POW("X", DP)
    eb = calc(vB, (ODD(v("U32.shrn(w, p)")), H("PX.bx.b1(U32.shrn(w, p))", vB, ODD(v("U32.shrn(w, p)")))),
              (O, H("UL.u32_shrn_value(w, p)", v("U32.shrn(w, p)"), HIGH("p", vw))))
    ct = calc(V("sq"), (F(PX_), H("esq", V("sq"), F(PX_))), (F(POW("X", ADD(DP, "0n"))), sym(H(f"UL.nat_add_zero({DP})", ADD(DP, "0n"), DP))),
              (F(POW("X", ADD(DP, O))), sym(H("eO", O, "0n"))))
    cf = calc(V(MM("sq", "x")), (F(MUL(PX_, "X")), H("emm", V(MM("sq", "x")), F(MUL(PX_, "X")))),
              (F(MUL(PX_, MUL("X", "1n"))), "ring"),
              (F(MUL(PX_, POW("X", "1n"))), "="),
              (F(POW("X", ADD(DP, "1n"))), sym(H(f"PX.bx.pa(X, {DP}, 1n)", POW("X", ADD(DP, "1n")), MUL(PX_, POW("X", "1n"))))),
              (F(POW("X", ADD(DP, O))), sym(H("eO1", O, "1n"))))
    eqb = (f"Equal.trans(Bool, Nat.is_eq({vB}, 0n), U32.is_eq({BIT}, 0), ZZ, Equal.sym(Bool, U32.is_eq({BIT}, 0), Nat.is_eq({vB}, U32.to_nat(0)), UL.u32_eq_value({BIT}, 0)), ez)")
    put(f"""def by.mpk(z: Bool, +w: U32, +p: Nat, +sq: {LIST}, +x: {LIST}, +X: Nat, +P: Nat, {CTXP}, +hsq: {OKT('sq')}, +hx: {OKT('x')}, +esq: {EQ(V('sq'), F(PX_))}, +ex: {EQ(V('x'), F('X'))}, +ez: {EQ(f'U32.is_zero({BIT})', 'z', 'Bool')}) -> {EQ(V(f'Mt.bn.mexp.pick(z, sq, x, n, np, {KL})'), F(POW('X', ADD(DP, O))))}:
  match z:
    case True{{}}:
      +e0 = PL.bq.z0({vB}, {eqb.replace('ZZ', 'True{}')})
      +eO = Equal.trans(Nat, {O}, {vB}, 0n, {sym(eb).text}, e0)
      {ct.text}
    case False{{}}:
      +pos = PL.bq.nz({vB}, {eqb.replace('ZZ', 'False{}')})
      +eO1 = PL.bq.one({O}, UL.nat_odd_le({HIGH('p', vw)}), {lt_rw('0n', vB, '0n', O, None, eb.text, 'pos')})
      +emm = by.mf(sq, x, {PX_}, X, {CTXA}, hsq, hx, esq, ex)
      {cf.text}

def by.mpkk(z: Bool, +sq: {LIST}, +x: {LIST}, +n: {LIST}, +np: U32, +k: Nat, +hsq: {OKT('sq')}) -> {OKT('Mt.bn.mexp.pick(z, sq, x, n, np, k)')}:
  match z:
    case True{{}}:
      hsq
    case False{{}}:
      by.mmk(sq, x, n, np, k)
""")
    PP = POW("X", "P")
    SQ = MM("acc", "acc")
    Z = "U32.is_zero(U32.and(1, U32.shrn(w, p)))"
    ACC2 = f"Mt.bn.mexp.pick({Z}, {SQ}, x, n, np, {KL})"
    P2 = ADD(DP, O)
    esq = calc(V(SQ), (F(MUL(PP, PP)), H(f"by.mf(acc, acc, {PP}, {PP}, {CTXA}, hacc, hacc, eacc, eacc)", V(SQ), F(MUL(PP, PP)))),
               (F(POW("X", ADD("P", "P"))), sym(H("PX.bx.pa(X, P, P)", POW("X", ADD("P", "P")), MUL(PP, PP)))),
               (F(POW("X", DP)), sym(H("UL.nat_double(P)", DP, ADD("P", "P")))))
    ee = calc(ADD(D("p", P2), LOW("p", vw)),
              (ADD(DBL(D("p", "P")), ADD(LOW("p", vw), D("p", O))), "ring"),
              (ADD(DBL(D("p", "P")), LOW("1n+p", vw)), sym(H(f"PX.bx.lo1(p, {vw})", LOW("1n+p", vw), ADD(LOW("p", vw), D("p", O))))),
              (ADD(D("1n+p", "P"), LOW("1n+p", vw)), "="))
    BITS = lambda b, acc, P_: f"Mt.bn.mexp.bits({b}, w, {acc}, x, n, np, {KL})"
    fin = calc(V(BITS("p", ACC2, P2)), (F(POW("X", ADD(D("p", P2), LOW("p", vw)))), H("ih", V(BITS("p", ACC2, P2)), F(POW("X", ADD(D("p", P2), LOW("p", vw)))))),
               (F(POW("X", ADD(D("1n+p", "P"), LOW("1n+p", vw)))), ee))
    c0 = calc(V("acc"), (F(PP), H("eacc", V("acc"), F(PP))), (F(POW("X", ADD("P", "0n"))), sym(H("UL.nat_add_zero(P)", ADD("P", "0n"), "P"))),
              (F(POW("X", ADD(D("0n", "P"), LOW("0n", vw)))), "="))
    put(f"""def by.bits(b: Nat, +w: U32, +acc: {LIST}, +x: {LIST}, +X: Nat, +P: Nat, {CTXP}, +hacc: {OKT('acc')}, +hx: {OKT('x')}, +eacc: {EQ(V('acc'), F(PP))}, +ex: {EQ(V('x'), F('X'))}) -> {EQ(V(BITS('b', 'acc', 'P')), F(POW('X', ADD(D('b', 'P'), LOW('b', vw)))))}:
  match b:
    case 0n:
      {c0.text}
    case 1n+ +p:
      +esq = {esq.text}
      +hsq = by.mmk(acc, acc, n, np, {KL})
      +eacc2 = by.mpk({Z}, w, p, {SQ}, x, X, P, {CTXA}, hsq, hx, esq, ex, {{==}})
      +ih = by.bits(p, w, {ACC2}, x, X, {P2}, {CTXA}, by.mpkk({Z}, {SQ}, x, n, np, {KL}, hsq), hx, eacc2, ex)
      {fin.text}

def by.bitk(b: Nat, +w: U32, +acc: {LIST}, +x: {LIST}, +n: {LIST}, +np: U32, +k: Nat, +hacc: {OKT('acc')}) -> {OKT('Mt.bn.mexp.bits(b, w, acc, x, n, np, k)')}:
  match b:
    case 0n:
      hacc
    case 1n+ +p:
      by.bitk(p, w, Mt.bn.mexp.pick({Z}, Mt.bn.mm(acc, acc, n, np, k), x, n, np, k), x, n, np, k, by.mpkk({Z}, Mt.bn.mm(acc, acc, n, np, k), x, n, np, k, by.mmk(acc, acc, n, np, k)))

def by.be(es: {LIST}, P: Nat) -> Nat:
  match es:
    case Nil{{}}:
      P
    case Con{{e, t}}:
      by.be(t, Nat.add(U.U32Nat.dbl(16n, P), U.U32Nat.low(16n, U32.to_nat(e))))
""")
    B16 = f"Mt.bn.mexp.bits(16n, e, acc, x, n, np, {KL})"
    P16 = ADD(D("16n", "P"), LOW("16n", v("e")))
    put(f"""def by.mgo(es: {LIST}, +acc: {LIST}, +x: {LIST}, +X: Nat, +P: Nat, {CTXP}, +hacc: {OKT('acc')}, +hx: {OKT('x')}, +eacc: {EQ(V('acc'), F(PP))}, +ex: {EQ(V('x'), F('X'))}) -> {EQ(V(f'Mt.bn.mexp.go(es, acc, x, n, np, {KL})'), F(POW('X', 'by.be(es, P)')))}:
  match es:
    case Nil{{}}:
      eacc
    case Con{{+e, +t}}:
      by.mgo(t, {B16}, x, X, {P16}, {CTXA}, by.bitk(16n, e, acc, x, n, np, {KL}, hacc), hx, by.bits(16n, e, acc, x, X, P, {CTXA}, hacc, hx, eacc, ex), ex)

def by.mgk(es: {LIST}, +acc: {LIST}, +x: {LIST}, +n: {LIST}, +np: U32, +k: Nat, +hacc: {OKT('acc')}) -> {OKT('Mt.bn.mexp.go(es, acc, x, n, np, k)')}:
  match es:
    case Nil{{}}:
      hacc
    case Con{{+e, +t}}:
      by.mgk(t, Mt.bn.mexp.bits(16n, e, acc, x, n, np, k), x, n, np, k, by.bitk(16n, e, acc, x, n, np, k, hacc))
""")
    M = "Nat.mul(N.bn.len(t), 16n)"
    vx, Vt = v("x"), V("t")
    hx1 = "PL.bq.lv(x, PL.bq.and1(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx))"
    hxs = "PL.bq.and2(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx)"
    E0 = ADD(D("16n", ADD(D(M, "P"), Vt)), LOW("16n", vx))
    E1 = ADD(D(ADD("16n", M), "P"), ADD(vx, D("16n", Vt)))
    ee = calc(E0, (ADD(D("16n", ADD(D(M, "P"), Vt)), vx), H(f"UL.low_small(16n, {vx}, {hx1})", LOW("16n", vx), vx)),
              (ADD(D("16n", D(M, "P")), ADD(vx, D("16n", Vt))), "ring"),
              (E1, H(f"UL.dbl_dbl(16n, {M}, P)", D("16n", D(M, "P")), D(ADD("16n", M), "P"))))
    NE = "N.bn.norm(es)"
    M2 = f"Nat.mul(N.bn.len({NE}), 16n)"
    cb = calc(ADD(D(M2, "0n"), V(NE)), (ADD("0n", V(NE)), H(f"UL.dbl_zero({M2})", D(M2, "0n"), "0n")), (V(NE), "="),
              (V("es"), H("PL.bq.nv(es)", V(NE), V("es"))))
    put(f"""def by.brv(xs: {LIST}, +acc: {LIST}, +P: Nat, +hx: {OKT('xs')}) -> {EQ('by.be(List.reverse.go(&2, U32, xs, acc), P)', f"by.be(acc, {ADD(D('Nat.mul(N.bn.len(xs), 16n)', 'P'), V('xs'))})")}:
  match xs:
    case Nil{{}}:
      Equal.sym(Nat, by.be(acc, Nat.add(P, 0n)), by.be(acc, P), Equal.cong(Nat, Nat, zz => by.be(acc, zz), Nat.add(P, 0n), P, UL.nat_add_zero(P)))
    case Con{{+x, +t}}:
      Equal.trans(Nat, by.be(List.reverse.go(&2, U32, t, Con{{x, acc}}), P), by.be(Con{{x, acc}}, {ADD(D(M, 'P'), Vt)}), by.be(acc, {E1}), by.brv(t, Con{{x, acc}}, P, {hxs}), Equal.cong(Nat, Nat, zz => by.be(acc, zz), {E0}, {E1}, {ee.text}))

def by.bev(+es: {LIST}, +he: {OKT('es')}) -> {EQ(f'by.be(List.reverse(&2, U32, {NE}), 0n)', V('es'))}:
  Equal.trans(Nat, by.be(List.reverse(&2, U32, {NE}), 0n), {ADD(D(M2, '0n'), V(NE))}, {V('es')}, by.brv({NE}, Nil{{}}, 0n, PL.bq.nk(es, he)), {cb.text})
""")


def canon():
    put("# Valid limbs without zeros on top are determined by their value\n")
    VX, VY = V("Con{x, t}"), V("Con{y, s}")
    hx1 = "PL.bq.lv(x, PL.bq.and1(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx))"
    hxs = "PL.bq.and2(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx)"
    hy1 = "PL.bq.lv(y, PL.bq.and1(U32.is_zero(U32.shrn(y, 16n)), LL.bnlaw.ok(s), hy))"
    hys = "PL.bq.and2(U32.is_zero(U32.shrn(y, 16n)), LL.bnlaw.ok(s), hy)"
    ex = TR("Nat", v("x"), LOW("16n", VX), v("y"), f"UL.low_unique(16n, {VX}, {v('x')}, {V('t')}, {{==}}, {hx1})",
            TR("Nat", LOW("16n", VX), LOW("16n", VY), v("y"), CG("Nat", "Nat", LOW("16n", "zz"), VX, VY, "e"),
               SY("Nat", v("y"), LOW("16n", VY), f"UL.low_unique(16n, {VY}, {v('y')}, {V('s')}, {{==}}, {hy1})")))
    et = TR("Nat", V("t"), HIGH("16n", VX), V("s"), f"UL.high_unique(16n, {VX}, {v('x')}, {V('t')}, {{==}}, {hx1})",
            TR("Nat", HIGH("16n", VX), HIGH("16n", VY), V("s"), CG("Nat", "Nat", HIGH("16n", "zz"), VX, VY, "e"),
               SY("Nat", V("s"), HIGH("16n", VY), f"UL.high_unique(16n, {VY}, {v('y')}, {V('s')}, {{==}}, {hy1})")))
    vy, Vs = v("y"), V("s")
    put(f"""def by.nc0(z: Bool, +x: U32, ez: {EQ('U32.is_zero(x)', 'z', 'Bool')}) -> {EQ('N.bn.norm(N.bn.lone(z, x))', 'N.bn.lone(z, x)', LIST)}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      Equal.cong(Bool, {LIST}, zz => N.bn.lone(zz, x), U32.is_zero(x), False{{}}, ez)

def by.nc(r: {LIST}, +x: U32, ih: {EQ('N.bn.norm(r)', 'r', LIST)}) -> {EQ('N.bn.norm(N.bn.cons(x, r))', 'N.bn.cons(x, r)', LIST)}:
  match r:
    case Nil{{}}:
      by.nc0(U32.is_zero(x), x, {{==}})
    case Con{{+y, +s}}:
      Equal.cong({LIST}, {LIST}, zz => N.bn.cons(x, zz), N.bn.norm(Con{{y, s}}), Con{{y, s}}, ih)

def by.nn(xs: {LIST}) -> {EQ('N.bn.norm(N.bn.norm(xs))', 'N.bn.norm(xs)', LIST)}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      by.nc(N.bn.norm(t), x, by.nn(t))

def by.nz0(ys: {LIST}, e: {EQ(V('ys'), '0n')}) -> {EQ('N.bn.norm(ys)', 'Nil{}', LIST)}:
  match ys:
    case Nil{{}}:
      {{==}}
    case Con{{+y, +s}}:
      +band = Equal.trans(Bool, Bool.and(Nat.is_eq({vy}, 0n), Nat.is_eq({Vs}, 0n)), Nat.is_eq({ADD(vy, D('16n', Vs))}, 0n), True{{}}, Equal.sym(Bool, Nat.is_eq({ADD(vy, D('16n', Vs))}, 0n), Bool.and(Nat.is_eq({vy}, 0n), Nat.is_eq({Vs}, 0n)), PL.bq.ez(16n, {vy}, {Vs})), Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 0n), {ADD(vy, D('16n', Vs))}, 0n, e))
      +yz = UL.u32_value_eq(y, 0, PL.bq.z0({vy}, PL.bq.and1(Nat.is_eq({vy}, 0n), Nat.is_eq({Vs}, 0n), band)))
      +ns = by.nz0(s, PL.bq.z0({Vs}, PL.bq.and2(Nat.is_eq({vy}, 0n), Nat.is_eq({Vs}, 0n), band)))
      Equal.trans({LIST}, N.bn.cons(y, N.bn.norm(s)), N.bn.cons(y, Nil{{}}), Nil{{}}, Equal.cong({LIST}, {LIST}, zz => N.bn.cons(y, zz), N.bn.norm(s), Nil{{}}, ns), Equal.trans({LIST}, N.bn.cons(y, Nil{{}}), N.bn.cons(0, Nil{{}}), Nil{{}}, Equal.cong(U32, {LIST}, zz => N.bn.cons(zz, Nil{{}}), y, 0, yz), {{==}}))

def by.can(xs: {LIST}, ys: {LIST}, +hx: {OKT('xs')}, +hy: {OKT('ys')}, +e: {EQ(V('xs'), V('ys'))}) -> {EQ('N.bn.norm(xs)', 'N.bn.norm(ys)', LIST)}:
  match xs ys:
    case Nil{{}} Nil{{}}:
      {{==}}
    case Nil{{}} Con{{+y, +s}}:
      Equal.sym({LIST}, N.bn.norm(Con{{y, s}}), Nil{{}}, by.nz0(Con{{y, s}}, Equal.sym(Nat, 0n, {VY}, e)))
    case Con{{+x, +t}} Nil{{}}:
      by.nz0(Con{{x, t}}, e)
    case Con{{+x, +t}} Con{{+y, +s}}:
      +xy = UL.u32_value_eq(x, y, {ex})
      +ih = by.can(t, s, {hxs}, {hys}, {et})
      Equal.trans({LIST}, N.bn.cons(x, N.bn.norm(t)), N.bn.cons(y, N.bn.norm(t)), N.bn.cons(y, N.bn.norm(s)), Equal.cong(U32, {LIST}, zz => N.bn.cons(zz, N.bn.norm(t)), x, y, xy), Equal.cong({LIST}, {LIST}, zz => N.bn.cons(y, zz), N.bn.norm(t), N.bn.norm(s), ih))

def by.lim(u: N.BnNat) -> {LIST}:
  match u:
    case N.BnNat{{ls}}:
      ls

def by.vl(u: N.BnNat) -> {EQ(VAL('u'), V('by.lim(u)'))}:
  match u:
    case N.BnNat{{+ls}}:
      {{==}}

def by.kl(u: N.BnNat, h: {VT('u')}) -> {OKT('by.lim(u)')}:
  match u:
    case N.BnNat{{+ls}}:
      h

def by.ofn(c: Mt.BnMont, y: N.BnNat) -> {EQ('Mt.BnMont.of(c, y)', 'N.BnNat{N.bn.norm(by.lim(Mt.BnMont.of(c, y)))}', 'N.BnNat')}:
  match c y:
    case Mt.BnMont{{+n, +np, +k, +r2, +one}} N.BnNat{{+ls}}:
      Equal.cong({LIST}, N.BnNat, zz => N.BnNat{{zz}}, N.bn.norm(Mt.bn.mm(ls, {ONE1}, n, np, k)), N.bn.norm(N.bn.norm(Mt.bn.mm(ls, {ONE1}, n, np, k))), Equal.sym({LIST}, N.bn.norm(N.bn.norm(Mt.bn.mm(ls, {ONE1}, n, np, k))), N.bn.norm(Mt.bn.mm(ls, {ONE1}, n, np, k)), by.nn(Mt.bn.mm(ls, {ONE1}, n, np, k))))

def by.hc0(z: Bool, +x: U32, ez: {EQ('U32.is_zero(x)', 'z', 'Bool')}) -> {EQ('N.bn.hd(N.bn.lone(z, x))', 'x', 'U32')}:
  match z:
    case True{{}}:
      Equal.sym(U32, x, 0, UL.u32_value_eq(x, 0, PL.bq.z0({v('x')}, Equal.trans(Bool, Nat.is_eq({v('x')}, 0n), U32.is_eq(x, 0), True{{}}, Equal.sym(Bool, U32.is_eq(x, 0), Nat.is_eq({v('x')}, U32.to_nat(0)), UL.u32_eq_value(x, 0)), ez))))
    case False{{}}:
      {{==}}

def by.hc(r: {LIST}, +x: U32) -> {EQ('N.bn.hd(N.bn.cons(x, r))', 'x', 'U32')}:
  match r:
    case Nil{{}}:
      by.hc0(U32.is_zero(x), x, {{==}})
    case Con{{+y, +s}}:
      {{==}}

def by.hn(xs: {LIST}) -> {EQ('N.bn.hd(N.bn.norm(xs))', 'N.bn.hd(xs)', 'U32')}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      by.hc(N.bn.norm(t), x)
""")


def CHK(n):
    return f"Bool.and(U32.is_eq(U32.and(1, N.bn.hd({n})), 1), Cmp.is_gt(N.bn.cmp({n}, {ONE1}, EQ{{}})))"


def context():
    put("# A Montgomery context: n valid, odd and above 1\n")
    hdn = v("N.bn.hd(n)")
    l1 = calc(LOW("1n", VN), (LOW("1n", LOW("16n", VN)), sym(ll("1n", "15n", "16n", VN))),
              (LOW("1n", hdn), sym(H("PX.bx.hdl(n, hn)", hdn, LOW("16n", VN)))), ("1n", H("ho", LOW("1n", hdn), "1n")))
    c = calc(ADD("1n", DBL(HIGH("1n", VN))), (ADD("1n", D("1n", HIGH("1n", VN))), "="),
             (ADD(LOW("1n", VN), D("1n", HIGH("1n", VN))), sym(l1)),
             (VN, H(f"UL.low_high(1n, {VN})", ADD(LOW("1n", VN), D("1n", HIGH("1n", VN))), VN)))
    eb1 = SY("Nat", MOD("1n", VN), "1n", msm("1n", VN, "hn1"))
    HN0 = "by.hn0(n, hn1)"
    vx = VAL("x")
    TO = f"Mt.BnMont.to({MK}, x)"
    RV = "List.reverse(&2, U32, N.bn.norm(es))"
    put(f"""def by.hodd(+n: {LIST}, +hn: {OKT('n')}, +ho: {EQ(LOW('1n', hdn), '1n')}) -> {EQ(ADD('1n', DBL(HIGH('1n', VN))), VN)}:
  {c.text}

def by.hn0(+n: {LIST}, +hn1: {LTx('1n', VN)}) -> {LTx('0n', VN)}:
  PL.bq.lt_trans(0n, 1n, {VN}, {{==}}, hn1)

def by.one({MKP}) -> {EQ(V(ONEm), F('1n'))}:
  by.mg2({R2}, {ONE1}, {D(K, D(K, '1n'))}, 1n, {D(K, '1n')}, {CTXM}, by.r2k(Nat.mul(32n, {KL}), {ONE1}, n, {KL}, {{==}}), {{==}}, by.r2f(n, hn, {HN0}, hn1), {eb1}, UL.nat_mul_one({D(K, D(K, '1n'))}))

def by.mto(u: N.BnNat, +n: {LIST}, +A: Nat, +hn: {OKT('n')}, +ho: {EQ(LOW('1n', hdn), '1n')}, +hn1: {LTx('1n', VN)}, +hu: {VT('u')}, +eu: {EQ(VAL('u'), MOD('A', VN))}) -> {EQ(VAL(f'Mt.bn.mont.to(u, {R2}, n, {NPm}, {KL})'), F('A'))}:
  match u:
    case N.BnNat{{+ls}}:
      by.mg2(ls, {R2}, A, {D(K, D(K, '1n'))}, {D(K, 'A')}, {CTXM}, hu, by.r2k(Nat.mul(32n, {KL}), {ONE1}, n, {KL}, {{==}}), eu, by.r2f(n, hn, {HN0}, hn1), {NP.ring(MUL('A', D(K, D(K, '1n'))), D(K, D(K, 'A'))).text})

def by.mtk(u: N.BnNat, +r2: {LIST}, +n: {LIST}, +np: U32, +k: Nat) -> {VT('Mt.bn.mont.to(u, r2, n, np, k)')}:
  match u:
    case N.BnNat{{+ls}}:
      by.mmk(ls, r2, n, np, k)

def by.tov(+x: N.BnNat, {MKP}, +hx: {VT('x')}) -> {EQ(VAL(TO), F(vx))}:
  by.mto(N.BnNat.mod(x, N.BnNat{{n}}), n, {vx}, hn, ho, hn1, LD.mod_valid(x, N.BnNat{{n}}, hx), LD.mod_value(x, N.BnNat{{n}}, hx, hn))

def by.tok(+x: N.BnNat, +n: {LIST}) -> {VT(TO)}:
  by.mtk(N.BnNat.mod(x, N.BnNat{{n}}), {R2}, n, {NPm}, {KL})

def by.mev(w: N.BnNat, e: N.BnNat, {MKP}, +X: Nat, +hw: {VT('w')}, +he: {VT('e')}, +ew: {EQ(VAL('w'), F('X'))}) -> {EQ(VAL(f'Mt.BnMont.exp({MK}, w, e)'), F(POW('X', VAL('e'))))}:
  match w e:
    case N.BnNat{{+xs}} N.BnNat{{+es}}:
      Equal.trans(Nat, {V(f'Mt.bn.mexp.go({RV}, {ONEm}, xs, n, {NPm}, {KL})')}, {F(POW('X', f'by.be({RV}, 0n)'))}, {F(POW('X', V('es')))}, by.mgo({RV}, {ONEm}, xs, X, 0n, {CTXM}, by.mmk({R2}, {ONE1}, n, {NPm}, {KL}), hw, by.one(n, hn, ho, hn1), ew), Equal.cong(Nat, Nat, zz => {F(POW('X', 'zz'))}, by.be({RV}, 0n), {V('es')}, by.bev(es, he)))

def by.mek(w: N.BnNat, e: N.BnNat, +n: {LIST}) -> {VT(f'Mt.BnMont.exp({MK}, w, e)')}:
  match w e:
    case N.BnNat{{+xs}} N.BnNat{{+es}}:
      by.mgk({RV}, {ONEm}, xs, n, {NPm}, {KL}, by.mmk({R2}, {ONE1}, n, {NPm}, {KL}))

def by.mof(y: N.BnNat, {MKP}, +u: Nat, +hy: {VT('y')}, +ey: {EQ(VAL('y'), F('u'))}) -> {EQ(VAL(f'Mt.BnMont.of({MK}, y)'), MOD('u', VN))}:
  match y:
    case N.BnNat{{+ls}}:
      Equal.trans(Nat, {V(f'N.bn.norm({MM("ls", ONE1, NPm)})')}, {V(MM('ls', ONE1, NPm))}, {MOD('u', VN)}, PL.bq.nv({MM('ls', ONE1, NPm)}), by.mg2(ls, {ONE1}, {D(K, 'u')}, 1n, u, {CTXM}, hy, {{==}}, ey, {eb1}, UL.nat_mul_one({D(K, 'u')})))

def by.ofk(y: N.BnNat, +n: {LIST}) -> {VT(f'Mt.BnMont.of({MK}, y)')}:
  match y:
    case N.BnNat{{+ls}}:
      PL.bq.nk({MM('ls', ONE1, NPm)}, by.mmk(ls, {ONE1}, n, {NPm}, {KL}))

def by.mxv(+x: N.BnNat, +e: N.BnNat, {MKP}, +hx: {VT('x')}, +he: {VT('e')}) -> {EQ(VAL(f'Mt.BnMont.modexp({MK}, x, e)'), MOD(POW(vx, VAL('e')), VN))}:
  by.mof(Mt.BnMont.exp({MK}, {TO}, e), n, hn, ho, hn1, {POW(vx, VAL('e'))}, by.mek({TO}, e, n), by.mev({TO}, e, n, hn, ho, hn1, {vx}, by.tok(x, n), he, by.tov(x, n, hn, ho, hn1, hx)))

def by.mxk(+x: N.BnNat, +e: N.BnNat, +n: {LIST}) -> {VT(f'Mt.BnMont.modexp({MK}, x, e)')}:
  by.ofk(Mt.BnMont.exp({MK}, {TO}, e), n)
""")
    NL = "N.bn.norm(ls)"
    VNL, Vls = V(NL), V("ls")
    A = f"U32.is_eq(U32.and(1, N.bn.hd(n)), 1)"
    B = f"Cmp.is_gt(N.bn.cmp(n, {ONE1}, EQ{{}}))"
    ANL, BNL = A.replace("(n)", f"({NL})"), f"Cmp.is_gt(N.bn.cmp({NL}, {ONE1}, EQ{{}}))"
    cmpn = f"N.bn.cmp(n, {ONE1}, EQ{{}})"
    cmpl = f"N.bn.cmp({NL}, {ONE1}, EQ{{}})"
    a_ = TR("Bool", ANL, f"U32.is_eq(U32.and(1, N.bn.hd(ls)), 1)", "True{}", CG("U32", "Bool", "U32.is_eq(U32.and(1, zz), 1)", f"N.bn.hd({NL})", "N.bn.hd(ls)", "by.hn(ls)"), "hmo")
    ecc = TR("Cmp", cmpl, f"Nat.cmp({VNL}, 1n)", "GT{}", TR("Cmp", cmpl, f"N.bn.step(Nat.cmp({VNL}, 1n), EQ{{}})", f"Nat.cmp({VNL}, 1n)", f"PL.bq.cm({NL}, {ONE1}, EQ{{}}, PL.bq.nk(ls, hm), {{==}})", f"PL.bq.st(Nat.cmp({VNL}, 1n))"),
             f"PL.bq.lg({VNL}, 1n, by.lift(ls, 1n, hm1))")
    b_ = TR("Bool", BNL, "Cmp.is_gt(GT{})", "True{}", CG("Cmp", "Bool", "Cmp.is_gt(zz)", cmpl, "GT{}", ecc), "{==}")
    PW = POW(VAL("x"), VAL("e"))
    put(f"""def by.cg(c: Cmp, e: {btrue('Cmp.is_gt(c)')}) -> {EQ('c', 'GT{}', 'Cmp')}:
  match c:
    case LT{{}}:
      Empty.absurd({{LT{{}} == GT{{}} : Cmp}}, PL.bq.ft(e))
    case EQ{{}}:
      Empty.absurd({{EQ{{}} == GT{{}} : Cmp}}, PL.bq.ft(e))
    case GT{{}}:
      {{==}}

def by.ho2(+x: U32, +h: {btrue('U32.is_eq(U32.and(1, x), 1)')}) -> {EQ(LOW('1n', v('x')), '1n')}:
  +e1 = Equal.trans(Bool, Nat.is_eq({v('U32.and(1, x)')}, 1n), U32.is_eq(U32.and(1, x), 1), True{{}}, Equal.sym(Bool, U32.is_eq(U32.and(1, x), 1), Nat.is_eq({v('U32.and(1, x)')}, U32.to_nat(1)), UL.u32_eq_value(U32.and(1, x), 1)), h)
  Equal.trans(Nat, {LOW('1n', v('x'))}, {ODD(v('x'))}, 1n, PX.bx.l1o({v('x')}), Equal.trans(Nat, {ODD(v('x'))}, {v('U32.and(1, x)')}, 1n, Equal.sym(Nat, {v('U32.and(1, x)')}, {ODD(v('x'))}, PX.bx.b1(x)), PX.bx.eqt({v('U32.and(1, x)')}, 1n, e1)))

def by.ck1(+n: {LIST}, +h: {btrue(CHK('n'))}) -> {EQ(LOW('1n', hdn), '1n')}:
  by.ho2(N.bn.hd(n), PL.bq.and1({A}, {B}, h))

def by.ck2(+n: {LIST}, +hn: {OKT('n')}, +h: {btrue(CHK('n'))}) -> {LTx('1n', VN)}:
  +g = by.cg({cmpn}, PL.bq.and2({A}, {B}, h))
  PL.bq.gl({VN}, 1n, Equal.trans(Cmp, Nat.cmp({VN}, 1n), {cmpn}, GT{{}}, Equal.sym(Cmp, {cmpn}, Nat.cmp({VN}, 1n), Equal.trans(Cmp, {cmpn}, N.bn.step(Nat.cmp({VN}, 1n), EQ{{}}), Nat.cmp({VN}, 1n), PL.bq.cm(n, {ONE1}, EQ{{}}, hn, {{==}}), PL.bq.st(Nat.cmp({VN}, 1n)))), g))

def by.lift(+ls: {LIST}, +a: Nat, +h: {LTx('a', Vls)}) -> {LTx('a', VNL)}:
  {lt_rw('a', Vls, 'a', VNL, None, SY('Nat', VNL, Vls, 'PL.bq.nv(ls)'), 'h')}

def by.ck0(+ls: {LIST}, +hm: {OKT('ls')}, +hmo: {btrue('N.BnNat.is_odd(N.BnNat{ls})')}, +hm1: {LTx('1n', Vls)}) -> {btrue(CHK(NL))}:
  PL.bq.and3({ANL}, {BNL}, {a_}, {b_})

def by.hof(+ls: {LIST}, +hmo: {btrue('N.BnNat.is_odd(N.BnNat{ls})')}) -> {EQ(LOW('1n', v(f'N.bn.hd({NL})')), '1n')}:
  by.ho2(N.bn.hd({NL}), {a_})

def by.exw(z: Bool, +ls: {LIST}, +x: N.BnNat, +e: N.BnNat, +hx: {VT('x')}, +he: {VT('e')}, +hm: {OKT('ls')}, +hm0: {LTx('0n', Vls)}, +ez: {EQ(CHK(NL), 'z', 'Bool')}) -> {EQ(VAL(f'Md.bn.exp.with(Mt.bn.mont.ok(z, {NL}), x, e, N.BnNat{{ls}})'), MOD(PW, Vls))}:
  match z:
    case True{{}}:
      Equal.trans(Nat, {VAL(f'Mt.BnMont.modexp(Mt.bn.mont.mk({NL}), x, e)')}, {MOD(PW, VNL)}, {MOD(PW, Vls)}, by.mxv(x, e, {NL}, PL.bq.nk(ls, hm), by.ck1({NL}, ez), by.ck2({NL}, PL.bq.nk(ls, hm), ez), hx, he), Equal.cong(Nat, Nat, zz => {MOD(PW, 'zz')}, {VNL}, {Vls}, PL.bq.nv(ls)))
    case False{{}}:
      LX.exp_plain_value(x, e, N.BnNat{{ls}}, hx, he, hm, hm0)

def by.exk(z: Bool, +ls: {LIST}, +x: N.BnNat, +e: N.BnNat) -> {VT(f'Md.bn.exp.with(Mt.bn.mont.ok(z, {NL}), x, e, N.BnNat{{ls}})')}:
  match z:
    case True{{}}:
      by.mxk(x, e, {NL})
    case False{{}}:
      LX.exp_plain_valid(x, e, N.BnNat{{ls}})

def by.em(+z: N.BnNat, +e: N.BnNat, +m: N.BnNat, +c: Mt.BnMont, +hc: {EQ('Mt.BnMont.ctx(m)', 'Some{c}', 'Maybe<&2, Mt.BnMont>')}) -> {EQ('Md.BnMod.exp(z, e, m)', 'Mt.BnMont.modexp(c, z, e)', 'N.BnNat')}:
  %Equal.sym(Maybe<&2, Mt.BnMont>, Mt.BnMont.ctx(m), Some{{c}}, hc) : {{Md.bn.exp.with(_, z, e, m) == Mt.BnMont.modexp(c, z, e) : N.BnNat}}
  {{==}}
""")


def laws():
    put("# The laws\n")
    NL = "N.bn.norm(ls)"
    VNL, Vls = V(NL), V("ls")
    NPn = f"Mt.bn.np(N.bn.hd({NL}))"
    KM = f"Nat.mul(N.bn.len({NL}), 16n)"
    MKn = f"Mt.bn.mont.mk({NL})"
    pre = """      +hn = PL.bq.nk(ls, hm)
      +ho = by.hof(ls, hmo)
      +hn1 = by.lift(ls, 1n, hm1)"""
    HNPn = f"by.np(N.bn.hd({NL}), ho)"
    HN0n = f"by.hn0({NL}, hn1)"

    def MMn(a, b):
        return f"Mt.bn.mm({a}, {b}, {NL}, {NPn}, N.bn.len({NL}))"
    R2n = f"Mt.bn.mont.r2(Nat.mul(32n, N.bn.len({NL})), {ONE1}, {NL}, N.bn.len({NL}))"
    ONEn = MMn(R2n, ONE1)
    NV = "PL.bq.nv(ls)"
    cof = calc(MOD(D(KM, V(f"N.bn.norm({MMn('ys', ONE1)})")), VNL),
               (MOD(D(KM, V(MMn("ys", ONE1))), VNL), H(f"PL.bq.nv({MMn('ys', ONE1)})", V(f"N.bn.norm({MMn('ys', ONE1)})"), V(MMn("ys", ONE1)))),
               (MOD(MUL(V("ys"), V(ONE1)), VNL), H(f"by.mmc(ys, {ONE1}, {NL}, {NPn}, hy, {{==}}, hn, {HNPn}, {HN0n}, hn1, by.lift(ls, {V('ys')}, hyl))", MOD(D(KM, V(MMn("ys", ONE1))), VNL), MOD(MUL(V("ys"), V(ONE1)), VNL))),
               (MOD(MUL(V("ys"), "1n"), VNL), "="),
               (MOD(V("ys"), VNL), H(f"UL.nat_mul_one({V('ys')})", MUL(V("ys"), "1n"), V("ys"))))
    TOn = f"Mt.BnMont.to({MKn}, x)"
    vx, va, vb, vm = VAL("x"), VAL("a"), VAL("b"), VAL("m")
    I1, I2 = "Md.BnMod.exp(x, a, m)", "Md.BnMod.exp(x, b, m)"
    E1, E2 = f"Md.BnMod.exp({I1}, b, m)", f"Md.BnMod.exp({I2}, a, m)"
    Cc = "Mt.BnMont.of_odd(m)"
    M1, M2 = f"Mt.BnMont.modexp({Cc}, {I1}, b)", f"Mt.BnMont.modexp({Cc}, {I2}, a)"
    cee = calc(VAL(E1), (MOD(POW(VAL(I1), vb), vm), H(f"Laws.exp_value({I1}, b, m, Laws.exp_valid(x, a, m), hb, hm, hm0)", VAL(E1), MOD(POW(VAL(I1), vb), vm))),
               (MOD(POW(MOD(POW(vx, va), vm), vb), vm), H("Laws.exp_value(x, a, m, hx, ha, hm, hm0)", VAL(I1), MOD(POW(vx, va), vm))),
               (MOD(POW(POW(vx, va), vb), vm), H(f"PX.bx.pmod({POW(vx, va)}, {vb}, {vm}, hm0)", MOD(POW(MOD(POW(vx, va), vm), vb), vm), MOD(POW(POW(vx, va), vb), vm))),
               (MOD(POW(vx, MUL(va, vb)), vm), H(f"PX.bx.pm({vx}, {va}, {vb})", POW(POW(vx, va), vb), POW(vx, MUL(va, vb)))))
    em1 = f"by.em({I1}, b, m, {Cc}, hc)"
    em2 = f"by.em({I2}, a, m, {Cc}, hc)"
    PAB, PBA = MOD(POW(vx, MUL(va, vb)), vm), MOD(POW(vx, MUL(vb, va)), vm)
    LM1, LM2 = V(f"by.lim({M1})"), V(f"by.lim({M2})")
    ts = [LM1, VAL(M1), VAL(E1), PAB, PBA, VAL(E2), VAL(M2), LM2]
    ps = [SY("Nat", VAL(M1), LM1, f"by.vl({M1})"),
          SY("Nat", VAL(E1), VAL(M1), CG("N.BnNat", "Nat", "LL.bnlaw.value(zz)", E1, M1, em1)),
          f"Laws.exp_exp_value(x, a, b, m, hx, ha, hb, hm, hm0)",
          CG("Nat", "Nat", MOD(POW(vx, "zz"), vm), MUL(va, vb), MUL(vb, va), f"UL.nat_mul_comm({va}, {vb})"),
          SY("Nat", VAL(E2), PBA, "Laws.exp_exp_value(x, b, a, m, hx, hb, ha, hm, hm0)"),
          CG("N.BnNat", "Nat", "LL.bnlaw.value(zz)", E2, M2, em2),
          f"by.vl({M2})"]
    eV = ps[0]
    for i in range(1, len(ps)):
        eV = TR("Nat", ts[0], ts[i], ts[i + 1], eV, ps[i])

    def okm(E, M, em, ex):
        return f"by.kl({M}, Equal.trans(Bool, LL.bnlaw.valid({M}), LL.bnlaw.valid({E}), True{{}}, Equal.sym(Bool, LL.bnlaw.valid({E}), LL.bnlaw.valid({M}), Equal.cong(N.BnNat, Bool, zz => LL.bnlaw.valid(zz), {E}, {M}, {em})), {ex}))"
    N1 = f"N.BnNat{{N.bn.norm(by.lim({M1}))}}"
    N2 = f"N.BnNat{{N.bn.norm(by.lim({M2}))}}"
    en1 = f"by.ofn({Cc}, Mt.BnMont.exp({Cc}, Mt.BnMont.to({Cc}, {I1}), b))"
    en2 = f"by.ofn({Cc}, Mt.BnMont.exp({Cc}, Mt.BnMont.to({Cc}, {I2}), a))"
    cn = f"by.can(by.lim({M1}), by.lim({M2}), {okm(E1, M1, em1, f'Laws.exp_valid({I1}, b, m)')}, {okm(E2, M2, em2, f'Laws.exp_valid({I2}, a, m)')}, {eV})"
    BN = "N.BnNat"
    comm = TR(BN, E1, M1, E2, em1, TR(BN, M1, N1, E2, en1, TR(BN, N1, N2, E2, CG(LIST, BN, "N.BnNat{zz}", f"N.bn.norm(by.lim({M1}))", f"N.bn.norm(by.lim({M2}))", cn),
                                                                TR(BN, N2, M2, E2, SY(BN, M2, N2, en2), SY(BN, E2, M2, em2)))))
    put(f"""def Laws.ctx_of_odd(m, hm, hmo, hm1):
  match m:
    case N.BnNat{{+ls}}:
      %Equal.sym(Bool, {CHK(NL)}, True{{}}, by.ck0(ls, hm, hmo, hm1)) : {{Mt.bn.mont.ok(_, {NL}) == Some{{{MKn}}} : Maybe<&2, Mt.BnMont>}}
      {{==}}

def Laws.mont_mul_value(m, a, b, hm, hmo, hm1, ha, hb, hal, hbl):
  match m a b:
    case N.BnNat{{+ls}} N.BnNat{{+xs}} N.BnNat{{+ys}}:
{pre}
      %{NV} : {EQ(MOD(D(KM, V(MMn('xs', 'ys'))), '_'), MOD(MUL(V('xs'), V('ys')), '_'))}
      by.mmc(xs, ys, {NL}, {NPn}, ha, hb, hn, {HNPn}, {HN0n}, by.lift(ls, {V('ys')}, hbl), by.lift(ls, {V('xs')}, hal))

def Laws.mont_mul_lt(m, a, b, hm, hmo, hm1, ha, hb, hal, hbl):
  match m a b:
    case N.BnNat{{+ls}} N.BnNat{{+xs}} N.BnNat{{+ys}}:
{pre}
      %{NV} : {LTx(V(MMn('xs', 'ys')), '_')}
      by.mml(xs, ys, {NL}, {NPn}, ha, hb, hn, {HNPn}, {HN0n}, by.lift(ls, {V('ys')}, hbl))

def Laws.mont_mul_valid(m, a, b):
  match m a b:
    case N.BnNat{{+ls}} N.BnNat{{+xs}} N.BnNat{{+ys}}:
      by.mmk(xs, ys, {NL}, {NPn}, N.bn.len({NL}))

def Laws.mont_to_value(m, x, hm, hmo, hm1, hx):
  match m:
    case N.BnNat{{+ls}}:
{pre}
      %{NV} : {EQ(VAL(TOn), MOD(D(KM, vx), '_'))}
      by.tov(x, {NL}, hn, ho, hn1, hx)

def Laws.mont_one_value(m, hm, hmo, hm1):
  match m:
    case N.BnNat{{+ls}}:
{pre}
      %{NV} : {EQ(V(ONEn), MOD(D(KM, '1n'), '_'))}
      by.one({NL}, hn, ho, hn1)

def Laws.mont_of_value(m, y, hm, hmo, hm1, hy, hyl):
  match m y:
    case N.BnNat{{+ls}} N.BnNat{{+ys}}:
{pre}
      %{NV} : {EQ(MOD(D(KM, V(f"N.bn.norm({MMn('ys', ONE1)})")), '_'), MOD(V('ys'), '_'))}
      {cof.text}

def Laws.mont_of_to(m, x, hm, hmo, hm1, hx):
  match m:
    case N.BnNat{{+ls}}:
{pre}
      %{NV} : {EQ(VAL(f'Mt.BnMont.of({MKn}, {TOn})'), MOD(vx, '_'))}
      by.mof({TOn}, {NL}, hn, ho, hn1, {vx}, by.tok(x, {NL}), by.tov(x, {NL}, hn, ho, hn1, hx))

def Laws.modexp_value(m, x, e, hm, hmo, hm1, hx, he):
  match m:
    case N.BnNat{{+ls}}:
{pre}
      %{NV} : {EQ(VAL(f'Mt.BnMont.modexp({MKn}, x, e)'), MOD(POW(vx, VAL('e')), '_'))}
      by.mxv(x, e, {NL}, hn, ho, hn1, hx, he)

def Laws.exp_value(x, e, m, hx, he, hm, hm0):
  match m:
    case N.BnNat{{+ls}}:
      by.exw({CHK(NL)}, ls, x, e, hx, he, hm, hm0, {{==}})

def Laws.exp_eq_plain(x, e, m, hx, he, hm, hm0):
  Equal.trans(Nat, {VAL('Md.BnMod.exp(x, e, m)')}, {MOD(POW(vx, VAL('e')), vm)}, {VAL('Md.BnMod.exp_plain(x, e, m)')}, Laws.exp_value(x, e, m, hx, he, hm, hm0), Equal.sym(Nat, {VAL('Md.BnMod.exp_plain(x, e, m)')}, {MOD(POW(vx, VAL('e')), vm)}, LX.exp_plain_value(x, e, m, hx, he, hm, hm0)))

def Laws.exp_valid(x, e, m):
  match m:
    case N.BnNat{{+ls}}:
      by.exk({CHK(NL)}, ls, x, e)

def Laws.exp_exp_value(x, a, b, m, hx, ha, hb, hm, hm0):
  {cee.text}

def Laws.exp_exp_comm(x, a, b, m, hx, ha, hb, hm, hmo, hm1):
  +hc = Laws.ctx_of_odd(m, hm, hmo, hm1)
  +hm0 = PL.bq.lt_trans(0n, 1n, {vm}, {{==}}, hm1)
  {comm}
""")


def main():
    put("# Montgomery multiplication, its contexts, and the exponentiations\n")
    lows()
    inverse()
    redc()
    csub()
    mmlemmas()
    cancel()
    forms()
    rsq()
    mexp()
    canon()
    context()
    laws()
    put("")
    text = "\n".join(out)
    hdr = ("# Generated by gen/proof_mont.py; do not edit by hand. The proofs of LAWS_mont.bend.\n"
           "import Base\nimport ../u32/u32.bend as U\nimport ../u32/LAWS.bend as UL\nimport ../u32/PROOF.bend as UP\n"
           "import ./bignum.bend as N\nimport ./modular.bend as Md\nimport ./mont.bend as Mt\n"
           "import ./LAWS_limbs.bend as LL\nimport ./PROOF_limbs.bend as PL\n"
           "import ./LAWS_mul.bend as LM\nimport ./PROOF_mul.bend as PM\nimport ./LAWS_div.bend as LD\nimport ./PROOF_div.bend as PD\n"
           "import ./LAWS_mod.bend as LX\nimport ./PROOF_mod.bend as PX\n"
           "import ./LAWS_mont.bend as Laws\n\n")
    with open(PROOF, "w", newline="\n") as f:
        f.write(hdr + text)


if __name__ == "__main__":
    main()
