#!/usr/bin/env python3
"""Writes bignum/PROOF_div.bend: the proofs of the division laws
(LAWS_div.bend).

  python3 gen/proof_div.py

bn.divmod is long division by shift and subtract. With A = value(a) and
B = value(b) > 0, la and lb their bit lengths: if la < lb, A < B and the
quotient is 0; otherwise d = la - lb, r = A, s = B 2^d, q = 0, and
bn.div.go steps i from d down to 0 keeping

  q B 2^(i+1) + r = A,   r < B 2^(i+1),   s = B 2^i:

a step compares r with s, subtracts s when r >= s and puts that bit on q
(bd.st), then halves s. At the start r = A < 2^la <= B 2^(d+1), since
2^lb <= 2 B (bd.fa, bd.fb: the bit length's bounds, from bn.wbits on the
top limb of the normalised number); at the end (i = 0) q B + r = A with
r < B. The shifts' values: bn.shl(x, n) is x 2^n (bd.sl: n = 16 (n / 16) +
n mod 16 by Base's Nat.divmod, bd.dg), bn.shr1 halves (bd.sr), bn.shl1
doubles and adds a bit (bd.s1). BnNat.mod and BnNat.div are then Base's
Nat.mod and Nat.div of the values (u32's nat_mod_unique, nat_div_unique).
The lemmas on limbs come from PROOF_limbs.bend (bq.*), the ring
identities from scripts/natproof.py.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "scripts"))
import natproof as N  # noqa: E402
from natproof import btrue, calc, hyp, le_from, lt_from, lt_rw, sym, wit_le, wit_lt  # noqa: E402

N.CFG["law"] = "UL."
N.OUT.prefix = "bd.r"
PROOF = os.path.join(HERE, "..", "PROOF_div.bend")

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


def OKT(xs):
    return f"{{{OK(xs)} == True{{}} : Bool}}"


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


def D16(x):
    return D("16n", x)


W16 = D("16n", "1n")
W32 = D("32n", "1n")
LIST = "List<&2, U32>"


def SH(x, k="16n"):
    return f"U32.shrn({x}, {k})"


def LT16(x):
    return btrue(f"Nat.is_lt({v(x)}, {W16})")


def AND(x):
    return f"U32.and(65535, {x})"


def le_rw(x, y, x2, y2, ex, ey, h):
    """{is_le(x2, y2) == True} from h : {is_le(x, y) == True}, with ex : x == x2
    and ey : y == y2 (or None)."""
    cur, a, b = h, x, y
    if ex is not None:
        cur = (f"Equal.trans(Bool, Nat.is_le({x2}, {b}), Nat.is_le({a}, {b}), True{{}}, "
               f"Equal.cong(Nat, Bool, zz => Nat.is_le(zz, {b}), {x2}, {a}, Equal.sym(Nat, {a}, {x2}, {ex})), {cur})")
        a = x2
    if ey is not None:
        cur = (f"Equal.trans(Bool, Nat.is_le({a}, {y2}), Nat.is_le({a}, {b}), True{{}}, "
               f"Equal.cong(Nat, Bool, zz => Nat.is_le({a}, zz), {y2}, {b}, Equal.sym(Nat, {b}, {y2}, {ey})), {cur})")
    return cur


def tr(a, b, c, ab, bc, ty="Nat"):
    return f"Equal.trans({ty}, {a}, {b}, {c}, {ab}, {bc})"


def bt(a, c, ab, bc):
    """{a == True} from ab : {a == c} and bc : {c == True}"""
    return f"Equal.trans(Bool, {a}, {c}, True{{}}, {ab}, {bc})"


def zero_of(sh):
    """{v(sh) == 0n} from ez : {U32.is_zero(sh) == True}"""
    return (f"PL.bq.z0({v(sh)}, Equal.trans(Bool, Nat.is_eq({v(sh)}, 0n), U32.is_eq({sh}, 0), True{{}}, "
            f"Equal.sym(Bool, U32.is_eq({sh}, 0), Nat.is_eq({v(sh)}, 0n), UL.u32_eq_value({sh}, 0)), ez))")


def pos_of(sh, e="ez"):
    """{is_lt(0n, v(sh)) == True} from ez : {U32.is_zero(sh) == False}"""
    return (f"PL.bq.nz({v(sh)}, Equal.trans(Bool, Nat.is_eq({v(sh)}, 0n), U32.is_eq({sh}, 0), False{{}}, "
            f"Equal.sym(Bool, U32.is_eq({sh}, 0), Nat.is_eq({v(sh)}, 0n), UL.u32_eq_value({sh}, 0)), {e}))")


# ---------------------------------------------------------------- Base's Nat.divmod

def natdiv():
    put("# Base's Nat.divmod: q (1 + bp) + r = n with r <= bp, and the parts of n by 16\n")
    FST = "Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))"
    SND = "Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))"
    goal = f"{{Nat.add(Nat.mul({FST}, 1n+bp), {SND}) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}}"
    hb = hyp("hb", "bp", "r")
    e0 = calc("Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+bp), 0n))",
              ("Nat.add(Nat.add(np, Nat.mul(d, 1n+bp)), 1n+bp)", "ring"),
              ("Nat.add(Nat.add(np, Nat.mul(d, 1n+bp)), 1n+r)", hb),
              ("Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r))", "ring"))
    e1 = calc("Nat.add(np, Nat.add(Nat.mul(d, 1n+bp), 1n+r))", ("Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r))", "ring"))
    LHS = "Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np, M, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(1n+np, M, d, r)))"
    put(f"""def bd.dg(n: Nat, m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {{bp == Nat.add(r, m) : Nat}}) -> {goal}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +np:
      match m:
        case 0n:
          +hb = Equal.trans(Nat, bp, Nat.add(r, 0n), r, h, UL.nat_add_zero(r))
          +ih = bd.dg(np, r, 1n+d, 0n, bp, hb)
          Equal.trans(Nat, {LHS.replace('M', '0n')}, Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+bp), 0n)), Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)), ih, {e0.text})
        case 1n+ +mp:
          +ih = bd.dg(np, mp, d, 1n+r, bp, Equal.trans(Nat, bp, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), h, UL.nat_add_succ(r, mp)))
          Equal.trans(Nat, {LHS.replace('M', '1n+mp')}, Nat.add(np, Nat.add(Nat.mul(d, 1n+bp), 1n+r)), Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)), ih, {e1.text})

def bd.db(n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {{bp == Nat.add(r, m) : Nat}}) -> {btrue(f'Nat.is_le({SND}, bp)')}:
  match n:
    case 0n:
      {le_from("r", "bp", "m", calc("Nat.add(m, r)", ("Nat.add(r, m)", "ring"), ("bp", sym(hyp("h", "bp", "Nat.add(r, m)")))))}
    case 1n+np:
      match m:
        case 0n:
          bd.db(np, r, 1n+d, 0n, bp, Equal.trans(Nat, bp, Nat.add(r, 0n), r, h, UL.nat_add_zero(r)))
        case 1n+mp:
          bd.db(np, mp, d, 1n+r, bp, Equal.trans(Nat, bp, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), h, UL.nat_add_succ(r, mp)))

def bd.d16(+n: Nat) -> {{Nat.add(Nat.mul(Nat.div(n, 16n), 16n), Nat.mod(n, 16n)) == n : Nat}}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(n, 16n), 16n), Nat.mod(n, 16n)), Nat.add(n, 0n), n, bd.dg(n, 15n, 0n, 0n, 15n, {{==}}), UL.nat_add_zero(n))

def bd.m16(+n: Nat) -> {btrue('Nat.is_le(Nat.mod(n, 16n), 15n)')}:
  bd.db(n, 15n, 0n, 0n, 15n, {{==}})

def bd.ndm(+A: Nat, B: Nat, hB: {btrue('Nat.is_lt(0n, B)')}) -> {{Nat.add(Nat.mul(Nat.div(A, B), B), Nat.mod(A, B)) == A : Nat}}:
  match B:
    case 0n:
      Empty.absurd({{Nat.add(Nat.mul(Nat.div(A, 0n), 0n), Nat.mod(A, 0n)) == A : Nat}}, PL.bq.ft(hB))
    case 1n+bp:
      Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(A, 1n+bp), 1n+bp), Nat.mod(A, 1n+bp)), Nat.add(A, 0n), A, bd.dg(A, bp, 0n, 0n, bp, {{==}}), UL.nat_add_zero(A))

def bd.nml(+A: Nat, B: Nat, hB: {btrue('Nat.is_lt(0n, B)')}) -> {btrue('Nat.is_lt(Nat.mod(A, B), B)')}:
  match B:
    case 0n:
      Empty.absurd({btrue('Nat.is_lt(Nat.mod(A, 0n), 0n)')}, PL.bq.ft(hB))
    case 1n+bp:
      PL.bq.le_lt(Nat.mod(A, 1n+bp), 1n+bp, bd.db(A, bp, 0n, 0n, bp, {{==}}))
""")


# ---------------------------------------------------------------- bit lengths

def bits():
    put("# The bits of a limb: 2^(wbits - 1) <= x < 2^wbits\n")
    X = v("x")
    sh = SH("x", "p")
    hi = f"U.U32Nat.high(p, {X})"
    lo = f"U.U32Nat.low(p, {X})"
    hz = tr(hi, v(sh), "0n", f"Equal.sym(Nat, {v(sh)}, {hi}, UL.u32_shrn_value(x, p))", zero_of(sh))
    lox = calc(lo, (f"Nat.add({lo}, 0n)", sym(hyp(f"UL.nat_add_zero({lo})", f"Nat.add({lo}, 0n)", lo))),
               (f"Nat.add({lo}, {D('p', '0n')})", sym(hyp("UL.dbl_zero(p)", D("p", "0n"), "0n"))),
               (f"Nat.add({lo}, {D('p', hi)})", sym(hyp("hz", hi, "0n"))),
               (X, hyp(f"UL.low_high(p, {X})", f"Nat.add({lo}, {D('p', hi)})", X)))
    ltp = lt_rw(lo, D("p", "1n"), X, D("p", "1n"), lox.text, None, f"UL.low_lt(p, {X})")
    lep = f"UL.dbl_le_exp(p, 1n+p, 1n, PL.bq.le_succ(p, p, UL.nat_le_refl(p)))"
    WB = f"N.bn.wbits(p, x)"
    hp = (f"Equal.trans(Bool, Nat.is_lt(0n, {hi}), Nat.is_lt(0n, {v(sh)}), True{{}}, "
          f"Equal.cong(Nat, Bool, zz => Nat.is_lt(0n, zz), {hi}, {v(sh)}, Equal.sym(Nat, {v(sh)}, {hi}, UL.u32_shrn_value(x, p))), {pos_of(sh)})")
    le1 = (f"PL.bq.le_trans({D('p', '1n')}, {D('p', hi)}, {X}, "
           f"{bt(f'Nat.is_le({D(chr(112), "1n")}, {D(chr(112), hi)})', f'Nat.is_le(1n, {hi})', f'UL.dbl_le(p, 1n, {hi})', f'PL.bq.lt_sle(0n, {hi}, hp)')}, "
           f"{le_from(D('p', hi), X, lo, hyp(f'UL.low_high(p, {X})', f'Nat.add({lo}, {D(chr(112), hi)})', X))})")
    put(f"""def bd.dp(+p: Nat) -> {btrue(f"Nat.is_lt(0n, {D('p', '1n')})")}:
  Equal.trans(Bool, Nat.is_lt(0n, {D('p', '1n')}), Nat.is_lt({D('p', '0n')}, {D('p', '1n')}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, {D('p', '1n')}), 0n, {D('p', '0n')}, Equal.sym(Nat, {D('p', '0n')}, 0n, UL.dbl_zero(p))), UL.dbl_lt(p, 0n, 1n))

def bd.pz(+k: Nat, +t: Nat, h: {btrue('Nat.is_lt(0n, t)')}) -> {btrue(f"Nat.is_lt(0n, {D('k', 't')})")}:
  Equal.trans(Bool, Nat.is_lt(0n, {D('k', 't')}), Nat.is_lt({D('k', '0n')}, {D('k', 't')}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, {D('k', 't')}), 0n, {D('k', '0n')}, Equal.sym(Nat, {D('k', '0n')}, 0n, UL.dbl_zero(k))), Equal.trans(Bool, Nat.is_lt({D('k', '0n')}, {D('k', 't')}), Nat.is_lt(0n, t), True{{}}, UL.dbl_lt(k, 0n, t), h))

def bd.w0(X: Nat) -> {{Nat.is_le(1n, Nat.double(X)) == Nat.is_lt(0n, X) : Bool}}:
  match X:
    case 0n:
      {{==}}
    case 1n+q:
      {{==}}

def bd.wu.go(+p: Nat, +x: U32, z: Bool, ez: {{U32.is_zero({sh}) == z : Bool}}, ih: {{Nat.is_lt({X}, {D(WB, '1n')}) == Nat.is_lt({X}, {D('p', '1n')}) : Bool}}) -> {{Nat.is_lt({X}, {D(f'N.bn.wbits.pick(z, 1n+p, {WB})', '1n')}) == Nat.is_lt({X}, {D('1n+p', '1n')}) : Bool}}:
  match z:
    case True{{}}:
      +hz = {hz}
      +lt = {ltp}
      +lt2 = PL.bq.ltle({X}, {D('p', '1n')}, {D('1n+p', '1n')}, lt, {lep})
      Equal.trans(Bool, Nat.is_lt({X}, {D(WB, '1n')}), Nat.is_lt({X}, {D('p', '1n')}), Nat.is_lt({X}, {D('1n+p', '1n')}), ih, Equal.trans(Bool, Nat.is_lt({X}, {D('p', '1n')}), True{{}}, Nat.is_lt({X}, {D('1n+p', '1n')}), lt, Equal.sym(Bool, Nat.is_lt({X}, {D('1n+p', '1n')}), True{{}}, lt2)))
    case False{{}}:
      {{==}}

def bd.wu(i: Nat, +x: U32) -> {{Nat.is_lt({X}, {D('N.bn.wbits(i, x)', '1n')}) == Nat.is_lt({X}, {D('i', '1n')}) : Bool}}:
  match i:
    case 0n:
      {{==}}
    case 1n+p:
      bd.wu.go(p, x, U32.is_zero({sh}), {{==}}, bd.wu(p, x))

def bd.wl.go(+p: Nat, +x: U32, z: Bool, ez: {{U32.is_zero({sh}) == z : Bool}}, ih: {{Nat.is_le({D(WB, '1n')}, Nat.double({X})) == Nat.is_lt(0n, {X}) : Bool}}) -> {{Nat.is_le({D(f'N.bn.wbits.pick(z, 1n+p, {WB})', '1n')}, Nat.double({X})) == Nat.is_lt(0n, {X}) : Bool}}:
  match z:
    case True{{}}:
      ih
    case False{{}}:
      +hp = {hp}
      +le1 = {le1}
      +l = {bt(f"Nat.is_le({D('1n+p', '1n')}, Nat.double({X}))", f"Nat.is_le({D('p', '1n')}, {X})", f"UL.dbl_le(1n, {D('p', '1n')}, {X})", 'le1')}
      +r = PL.bq.ltle(0n, {D('p', '1n')}, {X}, bd.dp(p), le1)
      Equal.trans(Bool, Nat.is_le({D('1n+p', '1n')}, Nat.double({X})), True{{}}, Nat.is_lt(0n, {X}), l, Equal.sym(Bool, Nat.is_lt(0n, {X}), True{{}}, r))

def bd.wl(i: Nat, +x: U32) -> {{Nat.is_le({D('N.bn.wbits(i, x)', '1n')}, Nat.double({X})) == Nat.is_lt(0n, {X}) : Bool}}:
  match i:
    case 0n:
      bd.w0({X})
    case 1n+p:
      bd.wl.go(p, x, U32.is_zero({sh}), {{==}}, bd.wl(p, x))
""")


def tops():
    put("# The top limb of a list of limbs, and of a normalised one (bd.lnz: the top limb is not 0)\n")
    LG = "LASTGO(rest, y)"
    T = v(LG)
    K = "Nat.mul(N.bn.len(rest), 16n)"
    Y = v("y")
    # step: rest = Con{a, s}
    LG2 = "LASTGO(s, a)"
    T2 = v(LG2)
    K2 = "Nat.mul(N.bn.len(s), 16n)"
    V1 = V("Con{a, s}")
    M = D(K2, f"1n+{T2}")
    S = f"Nat.add({Y}, {D16(V1)})"
    g, G = wit_lt(V1, M, "ih")
    gy, GY = wit_lt(Y, W16, "hy")
    w = f"Nat.add({D16(g)}, {gy})"
    EXP = f"Nat.add(16n, {K2})"
    pfa = calc(f"Nat.add({w}, 1n+{S})",
               (f"Nat.add(Nat.add({D16(g)}, {D16(V1)}), Nat.add({gy}, 1n+{Y}))", "ring"),
               (f"Nat.add(Nat.add({D16(g)}, {D16(V1)}), {W16})", GY),
               (D16(f"Nat.add({g}, 1n+{V1})"), "ring"),
               (D16(M), G),
               (D(EXP, f"1n+{T2}"), hyp(f"UL.dbl_dbl(16n, {K2}, 1n+{T2})", D16(M), D(EXP, f"1n+{T2}"))))
    e, E = wit_le(D(K2, T2), V1, "ih")
    pfb = calc(f"Nat.add(Nat.add({Y}, {D16(e)}), {D(EXP, T2)})",
               (f"Nat.add(Nat.add({Y}, {D16(e)}), {D16(D(K2, T2))})", sym(hyp(f"UL.dbl_dbl(16n, {K2}, {T2})", D16(D(K2, T2)), D(EXP, T2)))),
               (f"Nat.add({Y}, {D16(f'Nat.add({e}, {D(K2, T2)})')})", "ring"),
               (S, E))
    hy = f"PL.bq.lv(y, PL.bq.and1(U32.is_zero({SH('y')}), {OK('Con{a, s}')}, h))"
    hs = f"PL.bq.and2(U32.is_zero({SH('y')}), {OK('Con{a, s}')}, h)"
    put(f"""def bd.lnz(ys: {LIST}) -> Bool:
  match ys:
    case Nil{{}}:
      True{{}}
    case Con{{y, t}}:
      Bool.not(U32.is_zero(LASTGO(t, y)))

def bd.nt(b: Bool, h: {{Bool.not(b) == True{{}} : Bool}}) -> {{b == False{{}} : Bool}}:
  match b:
    case True{{}}:
      Empty.absurd({{True{{}} == False{{}} : Bool}}, PL.bq.ft(h))
    case False{{}}:
      {{==}}

def bd.cz1(+x: U32, z: Bool, ez: {{U32.is_zero(x) == z : Bool}}) -> {{bd.lnz(N.bn.lone(z, x)) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      Equal.cong(Bool, Bool, zz => Bool.not(zz), U32.is_zero(x), False{{}}, ez)

def bd.cz(+x: U32, r: {LIST}, hr: {{bd.lnz(r) == True{{}} : Bool}}) -> {{bd.lnz(N.bn.cons(x, r)) == True{{}} : Bool}}:
  match r:
    case Nil{{}}:
      bd.cz1(x, U32.is_zero(x), {{==}})
    case Con{{a, s}}:
      hr

def bd.nz(xs: {LIST}) -> {{bd.lnz(N.bn.norm(xs)) == True{{}} : Bool}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      bd.cz(x, N.bn.norm(t), bd.nz(t))

def bd.tv(rest: {LIST}, +y: U32, h: {OKT('Con{y, rest}')}) -> {{U32.is_zero({SH(LG)}) == True{{}} : Bool}}:
  match rest:
    case Nil{{}}:
      PL.bq.and1(U32.is_zero({SH('y')}), True{{}}, h)
    case Con{{+a, +s}}:
      bd.tv(s, a, PL.bq.and2(U32.is_zero({SH('y')}), {OK('Con{a, s}')}, h))

def bd.ta(rest: {LIST}, +y: U32, +h: {OKT('Con{y, rest}')}) -> {btrue(f"Nat.is_lt({V('Con{y, rest}')}, {D(K, '1n+' + T)})")}:
  match rest:
    case Nil{{}}:
      {lt_rw(Y, f'1n+{Y}', f'Nat.add({Y}, 0n)', f'1n+{Y}', f'Equal.sym(Nat, Nat.add({Y}, 0n), {Y}, UL.nat_add_zero({Y}))', None, f'UL.nat_lt_add({Y}, 0n)')}
    case Con{{+a, +s}}:
      +hy = {hy}
      +ih = bd.ta(s, a, {hs})
      {lt_from(S, D(EXP, '1n+' + T2), w, pfa)}

def bd.tb(rest: {LIST}, +y: U32, +h: {OKT('Con{y, rest}')}) -> {btrue(f"Nat.is_le({D(K, T)}, {V('Con{y, rest}')})")}:
  match rest:
    case Nil{{}}:
      Equal.trans(Bool, Nat.is_le({Y}, Nat.add({Y}, 0n)), Nat.is_le({Y}, {Y}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_le({Y}, zz), Nat.add({Y}, 0n), {Y}, UL.nat_add_zero({Y})), UL.nat_le_refl({Y}))
    case Con{{+a, +s}}:
      +ih = bd.tb(s, a, {hs})
      {le_from(D(EXP, T2), S, f'Nat.add({Y}, {D16(e)})', pfb)}
""")
    # the bit length of a normalised list
    n = "Con{y0, rest}"
    LG0 = "LASTGO(rest, y0)"
    T0 = v(LG0)
    WB = f"N.bn.wbits(16n, {LG0})"
    L = "N.bn.len(rest)"
    K0 = f"Nat.mul({L}, 16n)"
    BLXc = f"Nat.add(Nat.mul(16n, Nat.sub({L}, 0n)), {WB})"
    BLX = "Nat.add(Nat.mul(16n, Nat.sub(N.bn.len(n), 1n)), N.bn.wbits(16n, N.bn.top(n)))"
    EKK = tr(K0, f"Nat.mul(16n, {L})", f"Nat.mul(16n, Nat.sub({L}, 0n))", f"UL.nat_mul_comm({L}, 16n)",
             f"Equal.cong(Nat, Nat, zz => Nat.mul(16n, zz), {L}, Nat.sub({L}, 0n), Equal.sym(Nat, Nat.sub({L}, 0n), {L}, PL.bq.sub0({L})))")
    ey = tr(D(K0, D(WB, "1n")), D(f"Nat.add({K0}, {WB})", "1n"), D(BLXc, "1n"), f"UL.dbl_dbl({K0}, {WB}, 1n)",
            f"Equal.cong(Nat, Nat, zz => {D(f'Nat.add(zz, {WB})', '1n')}, {K0}, Nat.mul(16n, Nat.sub({L}, 0n)), {EKK})")
    VN = V(n)
    tw = bt(f"Nat.is_lt({T0}, {D(WB, '1n')})", f"Nat.is_lt({T0}, {W16})", f"bd.wu(16n, {LG0})", "ht")
    lea = bt(f"Nat.is_le({D(K0, '1n+' + T0)}, {D(K0, D(WB, '1n'))})", f"Nat.is_le(1n+{T0}, {D(WB, '1n')})", f"UL.dbl_le({K0}, 1n+{T0}, {D(WB, '1n')})", f"PL.bq.lt_sle({T0}, {D(WB, '1n')}, tw)")
    lt1 = f"PL.bq.ltle({VN}, {D(K0, '1n+' + T0)}, {D(K0, D(WB, '1n'))}, bd.ta(rest, y0, hok), {lea})"
    bla = lt_rw(VN, D(K0, D(WB, "1n")), VN, D(BLXc, "1n"), None, ey, lt1)
    # lower
    w2 = bt(f"Nat.is_le({D(WB, '1n')}, Nat.double({T0}))", f"Nat.is_lt(0n, {T0})", f"bd.wl(16n, {LG0})", "tp0")
    A1 = bt(f"Nat.is_le({D(K0, D(WB, '1n'))}, {D(K0, f'Nat.double({T0})')})", f"Nat.is_le({D(WB, '1n')}, Nat.double({T0}))", f"UL.dbl_le({K0}, {D(WB, '1n')}, Nat.double({T0}))", "w2")
    A = le_rw(D(K0, D(WB, "1n")), D(K0, f"Nat.double({T0})"), D(BLXc, "1n"), D(K0, f"Nat.double({T0})"), ey, None, A1)
    B1 = bt(f"Nat.is_le(Nat.double({D(K0, T0)}), Nat.double({VN}))", f"Nat.is_le({D(K0, T0)}, {VN})", f"UL.dbl_le(1n, {D(K0, T0)}, {VN})", "tb")
    B = le_rw(f"Nat.double({D(K0, T0)})", f"Nat.double({VN})", D(K0, f"Nat.double({T0})"), f"Nat.double({VN})", f"Equal.sym(Nat, {D(K0, D('1n', T0))}, {D('1n', D(K0, T0))}, UL.dbl_comm({K0}, 1n, {T0}))", None, B1)
    le = f"PL.bq.le_trans({D(BLXc, '1n')}, {D(K0, f'Nat.double({T0})')}, Nat.double({VN}), {A}, {B})"
    put(f"""def bd.bla(n: {LIST}, +hok: {OKT('n')}, +hz: {{bd.lnz(n) == True{{}} : Bool}}) -> {btrue(f"Nat.is_lt({V('n')}, {D(BLX, '1n')})")}:
  match n:
    case Nil{{}}:
      {{==}}
    case Con{{+y0, +rest}}:
      +ht = PL.bq.lv({LG0}, bd.tv(rest, y0, hok))
      +tw = {tw}
      {bla}

def bd.blb(n: {LIST}, +hok: {OKT('n')}, +hz: {{bd.lnz(n) == True{{}} : Bool}}) -> {{Nat.is_le({D(BLX, '1n')}, Nat.double({V('n')})) == Nat.is_lt(0n, {V('n')}) : Bool}}:
  match n:
    case Nil{{}}:
      {{==}}
    case Con{{+y0, +rest}}:
      +ez = bd.nt(U32.is_zero({LG0}), hz)
      +tp0 = {pos_of(LG0)}
      +w2 = {w2}
      +tb = bd.tb(rest, y0, hok)
      +pos = PL.bq.ltle(0n, {D(K0, T0)}, {VN}, bd.pz({K0}, {T0}, tp0), tb)
      Equal.trans(Bool, Nat.is_le({D(BLXc, '1n')}, Nat.double({VN})), True{{}}, Nat.is_lt(0n, {VN}), {le}, Equal.sym(Bool, Nat.is_lt(0n, {VN}), True{{}}, pos))

def bd.fa(+xs: {LIST}, +hx: {OKT('xs')}) -> {btrue(f"Nat.is_lt({V('xs')}, {D('N.bn.bitlen(xs)', '1n')})")}:
  Equal.trans(Bool, Nat.is_lt({V('xs')}, {D('N.bn.bitlen(xs)', '1n')}), Nat.is_lt({V('N.bn.norm(xs)')}, {D('N.bn.bitlen(xs)', '1n')}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, {D('N.bn.bitlen(xs)', '1n')}), {V('xs')}, {V('N.bn.norm(xs)')}, Equal.sym(Nat, {V('N.bn.norm(xs)')}, {V('xs')}, PL.bq.nv(xs))), bd.bla(N.bn.norm(xs), PL.bq.nk(xs, hx), bd.nz(xs)))

def bd.fb(+xs: {LIST}, +hx: {OKT('xs')}) -> {{Nat.is_le({D('N.bn.bitlen(xs)', '1n')}, Nat.double({V('xs')})) == Nat.is_lt(0n, {V('xs')}) : Bool}}:
  %PL.bq.nv(xs) : {{Nat.is_le({D('N.bn.bitlen(xs)', '1n')}, Nat.double(_)) == Nat.is_lt(0n, _) : Bool}}
  bd.blb(N.bn.norm(xs), PL.bq.nk(xs, hx), bd.nz(xs))
""")


def shifts():
    put("# The shifts: zeros below, shlb, shl, shl1 and shr1\n")
    put(f"""# powers of two in the exact form the next step takes them (a closed one is
# never compared by computation)
def bd.d17(+h: Nat, +m: Nat, e: {{1n+h == m : Nat}}) -> {{Nat.double({D('h', '1n')}) == {D('m', '1n')} : Nat}}:
  %e : {{Nat.double({D('h', '1n')}) == {D('_', '1n')} : Nat}}
  {{==}}

def bd.d2(+h: Nat, +m: Nat, e: {{Nat.add(h, 1n) == m : Nat}}) -> {{{D('h', '2n')} == {D('m', '1n')} : Nat}}:
  %e : {{{D('h', '2n')} == {D('_', '1n')} : Nat}}
  UL.dbl_dbl(h, 1n, 1n)

def bd.dlt(+h: Nat, +m: Nat, e: {{1n+h == m : Nat}}, +x: Nat, hx: {btrue(f"Nat.is_lt(x, {D('h', '1n')})")}) -> {btrue(f"Nat.is_lt({D('1n', 'x')}, {D('m', '1n')})")}:
  %e : {btrue(f"Nat.is_lt({D('1n', 'x')}, {D('_', '1n')})")}
  Equal.trans(Bool, Nat.is_lt({D('1n', 'x')}, {D('1n+h', '1n')}), Nat.is_lt(x, {D('h', '1n')}), True{{}}, UL.dbl_lt(1n, x, {D('h', '1n')}), hx)
""")
    p1 = "1n"
    put(f"""def bd.za(k: Nat, +ys: {LIST}) -> {{{V('APPEND(N.bn.zeros(k), ys)')} == {D('Nat.mul(k, 16n)', V('ys'))} : Nat}}:
  match k:
    case 0n:
      {{==}}
    case 1n+p:
      Equal.trans(Nat, {D16(V('APPEND(N.bn.zeros(p), ys)'))}, {D16(D('Nat.mul(p, 16n)', V('ys')))}, {D('Nat.add(16n, Nat.mul(p, 16n))', V('ys'))}, Equal.cong(Nat, Nat, zz => {D16('zz')}, {V('APPEND(N.bn.zeros(p), ys)')}, {D('Nat.mul(p, 16n)', V('ys'))}, bd.za(p, ys)), UL.dbl_dbl(16n, Nat.mul(p, 16n), {V('ys')}))

def bd.zk(k: Nat, +ys: {LIST}, h: {OKT('ys')}) -> {OKT('APPEND(N.bn.zeros(k), ys)')}:
  match k:
    case 0n:
      h
    case 1n+p:
      bd.zk(p, ys, h)
""")
    # shlb: one step
    X = v("x")
    SL = "U32.shln(x, s)"
    VV = f"U32.or({SL}, c)"
    VC = v("c")
    E = "Nat.add(s, 16n)"
    VT = V("t")
    hx1 = f"PL.bq.lv(x, PL.bq.and1(U32.is_zero({SH('x')}), {OK('t')}, hx))"
    hts = f"PL.bq.and2(U32.is_zero({SH('x')}), {OK('t')}, hx)"
    B1 = lt_rw(D("s", X), D("s", W16), D("s", X), D(E, "1n"), None, "UL.dbl_dbl(s, 16n, 1n)",
               bt(f"Nat.is_lt({D('s', X)}, {D('s', W16)})", f"Nat.is_lt({X}, {W16})", f"UL.dbl_lt(s, {X}, {W16})", "hx1"))
    ws, WS = wit_le("s", "16n", "hs")
    e32 = le_from(E, "32n", ws, calc(f"Nat.add({ws}, {E})", (f"Nat.add(Nat.add({ws}, s), 16n)", "ring"), ("Nat.add(16n, 16n)", WS), ("32n", "=")))
    B2 = f"PL.bq.ltle({D('s', X)}, {D(E, '1n')}, {W32}, {B1}, UL.dbl_le_exp({E}, 32n, 1n, {e32}))"
    esl = tr(v(SL), f"U.U32Nat.low(32n, {D('s', X)})", D("s", X), "UL.u32_shln_low(x, s)", f"UL.low_small(32n, {D('s', X)}, {B2})")
    S = f"Nat.add({D('s', X)}, {VC})"
    vvv = tr(v(VV), f"Nat.add({v(SL)}, {VC})", S, f"UL.u32_or_split({SL}, c, s, {X}, {esl}, hc)",
             f"Equal.cong(Nat, Nat, zz => Nat.add(zz, {VC}), {v(SL)}, {D('s', X)}, {esl})")
    gx, GX = wit_lt(X, W16, "hx1")
    gc, GC = wit_lt(VC, D("s", "1n"), "hc")
    w = f"Nat.add({D('s', gx)}, {gc})"
    pf = calc(f"Nat.add({w}, 1n+{S})",
              (f"Nat.add({D('s', gx)}, Nat.add({D('s', X)}, Nat.add({gc}, 1n+{VC})))", "ring"),
              (f"Nat.add({D('s', gx)}, Nat.add({D('s', X)}, {D('s', '1n')}))", GC),
              (D("s", f"Nat.add({gx}, 1n+{X})"), "ring"),
              (D("s", W16), GX),
              (D(E, "1n"), hyp("UL.dbl_dbl(s, 16n, 1n)", D("s", W16), D(E, "1n"))))
    BV = lt_from(S, D(E, "1n"), w, pf)
    BVV = lt_rw(S, D(E, "1n"), v(VV), D(E, "1n"), f"Equal.sym(Nat, {v(VV)}, {S}, vvv)", None, "bv")
    hi = f"U.U32Nat.high(16n, {v(VV)})"
    hcp = lt_rw(hi, D("s", "1n"), v(SH(VV)), D("s", "1n"), f"Equal.sym(Nat, {v(SH(VV))}, {hi}, UL.u32_shrn_value({VV}, 16n))", None,
                f"UL.high_lt(16n, s, {E}, {v(VV)}, UL.nat_add_comm(16n, s), {BVV})")
    pre = f"""      +hx1 = {hx1}
      +vvv = {vvv}
      +bv = {BV}
      +hcp = {hcp}
"""
    lo = f"U.U32Nat.low(16n, {v(VV)})"
    REST = f"N.bn.shlb(t, s, {SH(VV)})"
    IHR = f"Nat.add({D('s', VT)}, {v(SH(VV))})"
    IHH = f"Nat.add({D('s', VT)}, {hi})"
    chain = calc(f"Nat.add({v(AND(VV))}, {D16(V(REST))})",
                 (f"Nat.add({lo}, {D16(V(REST))})", hyp(f"PL.bq.lo({VV})", v(AND(VV)), lo)),
                 (f"Nat.add({lo}, {D16(IHR)})", hyp("ih", V(REST), IHR)),
                 (f"Nat.add({lo}, {D16(IHH)})", hyp(f"UL.u32_shrn_value({VV}, 16n)", v(SH(VV)), hi)),
                 (f"Nat.add(Nat.add({lo}, {D16(hi)}), {D16(D('s', VT))})", "ring"),
                 (f"Nat.add({v(VV)}, {D16(D('s', VT))})", hyp(f"UL.low_high(16n, {v(VV)})", f"Nat.add({lo}, {D16(hi)})", v(VV))),
                 (f"Nat.add({S}, {D16(D('s', VT))})", hyp("vvv", v(VV), S)),
                 (f"Nat.add({D('s', f'Nat.add({X}, {D16(VT)})')}, {VC})", "ring"))
    nil = calc(f"Nat.add({D('s', '0n')}, {VC})", (f"Nat.add(0n, {VC})", hyp("UL.dbl_zero(s)", D("s", "0n"), "0n")), (VC, "="))
    hc16 = f"PL.bq.ltle({VC}, {D('s', '1n')}, {W16}, hc, UL.dbl_le_exp(s, 16n, 1n, hs))"
    hcty = btrue(f"Nat.is_lt({VC}, {D('s', p1)})")
    sig = f"(xs: {LIST}, +s: Nat, +c: U32, +hx: {OKT('xs')}, +hs: {btrue('Nat.is_le(s, 16n)')}, +hc: {hcty})"
    put(f"""def bd.sbv{sig} -> {{{V('N.bn.shlb(xs, s, c)')} == Nat.add({D('s', V('xs'))}, {VC}) : Nat}}:
  match xs:
    case Nil{{}}:
      Equal.trans(Nat, {V('N.bn.lone(U32.is_zero(c), c)')}, {VC}, Nat.add({D('s', '0n')}, {VC}), PL.bq.lone(c, U32.is_zero(c), {{==}}), Equal.sym(Nat, Nat.add({D('s', '0n')}, {VC}), {VC}, {nil.text}))
    case Con{{+x, +t}}:
{pre}      +ih = bd.sbv(t, s, {SH(VV)}, {hts}, hs, hcp)
      {chain.text}

def bd.sbk{sig} -> {OKT('N.bn.shlb(xs, s, c)')}:
  match xs:
    case Nil{{}}:
      PL.bq.okl(c, U32.is_zero(c), {{==}}, {hc16})
    case Con{{+x, +t}}:
{pre}      PL.bq.and3(U32.is_zero({SH(AND(VV))}), {OK(REST)}, PL.bq.mk({VV}), bd.sbk(t, s, {SH(VV)}, {hts}, hs, hcp))
""")
    # shl
    Q, M = "Nat.div(n, 16n)", "Nat.mod(n, 16n)"
    VX = V("Con{x, t}")
    SB = f"N.bn.shlb(Con{{x, t}}, {M}, 0)"
    hs = f"PL.bq.le_succ({M}, 15n, bd.m16(n))"
    MQ = f"Nat.mul({Q}, 16n)"
    APP = f"APPEND(N.bn.zeros({Q}), {SB})"
    e = calc(V(APP),
             (D(MQ, V(SB)), hyp(f"bd.za({Q}, {SB})", V(APP), D(MQ, V(SB)))),
             (D(MQ, f"Nat.add({D(M, VX)}, 0n)"), hyp(f"bd.sbv(Con{{x, t}}, {M}, 0, hx, {hs}, bd.dp({M}))", V(SB), f"Nat.add({D(M, VX)}, 0n)")),
             (D(MQ, D(M, VX)), hyp(f"UL.nat_add_zero({D(M, VX)})", f"Nat.add({D(M, VX)}, 0n)", D(M, VX))),
             (D(f"Nat.add({MQ}, {M})", VX), hyp(f"UL.dbl_dbl({MQ}, {M}, {VX})", D(MQ, D(M, VX)), D(f"Nat.add({MQ}, {M})", VX))),
             (D("n", VX), hyp("bd.d16(n)", f"Nat.add({MQ}, {M})", "n")))
    put(f"""def bd.slv(xs: {LIST}, +n: Nat, +hx: {OKT('xs')}) -> {{{V('N.bn.shl(xs, n)')} == {D('n', V('xs'))} : Nat}}:
  match xs:
    case Nil{{}}:
      Equal.sym(Nat, {D('n', '0n')}, 0n, UL.dbl_zero(n))
    case Con{{+x, +t}}:
      {e.text}

def bd.slk(xs: {LIST}, +n: Nat, +hx: {OKT('xs')}) -> {OKT('N.bn.shl(xs, n)')}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      bd.zk({Q}, {SB}, bd.sbk(Con{{x, t}}, {M}, 0, hx, {hs}, bd.dp({M})))
""")
    # shl1
    SL1 = "U32.shln(x, 1n)"
    V1 = f"U32.add({SL1}, c)"
    D2 = f"Nat.double({W16})"
    S1 = f"Nat.add(Nat.double({X}), {VC})"
    D17 = D("17n", "1n")
    lt1x = f"bd.dlt(16n, 17n, {{==}}, {X}, hx1)"
    esl1 = tr(v(SL1), f"U.U32Nat.low(32n, {D('1n', X)})", D("1n", X), "UL.u32_shln_low(x, 1n)",
              f"UL.low_small(32n, {D('1n', X)}, PL.bq.ltle({D('1n', X)}, {D17}, {W32}, {lt1x}, UL.dbl_le_exp(17n, 32n, 1n, {{==}})))")
    gx, GX = wit_lt(X, W16, "hx1")
    gc, GC = wit_le(VC, "1n", "hc")
    w = f"Nat.add(Nat.double({gx}), {gc})"
    pf = calc(f"Nat.add({w}, 1n+{S1})",
              (f"Nat.add(Nat.add(Nat.double({gx}), Nat.double({X})), Nat.add(Nat.add({gc}, {VC}), 1n))", "ring"),
              (f"Nat.add(Nat.add(Nat.double({gx}), Nat.double({X})), Nat.add(1n, 1n))", GC),
              (f"Nat.double(Nat.add({gx}, 1n+{X}))", "ring"),
              (D2, GX))
    bv1 = lt_rw(S1, D2, S1, D17, None, "bd.d17(16n, 17n, {==})", lt_from(S1, D2, w, pf))
    b2 = f"U.U32Nat.bit(U32.is_lt({V1}, {SL1}))"
    ew = calc(f"Nat.add({v(V1)}, {D('32n', b2)})",
              (f"Nat.add({v(SL1)}, {VC})", hyp(f"UL.u32_add_wrap({SL1}, c)", f"Nat.add({v(V1)}, {D('32n', b2)})", f"Nat.add({v(SL1)}, {VC})")),
              (S1, hyp("esl1", v(SL1), f"Nat.double({X})")))
    vv1 = f"UL.dbl_nowrap(32n, {b2}, {v(V1)}, {S1}, {S1}, {ew.text}, UL.nat_le_refl({S1}), PL.bq.ltle({S1}, {D17}, {W32}, bv, UL.dbl_le_exp(17n, 32n, 1n, {{==}})))"
    hi1 = f"U.U32Nat.high(16n, {v(V1)})"
    lt17 = lt_rw(S1, D17, v(V1), D17, f"Equal.sym(Nat, {v(V1)}, {S1}, vv1)", None, "bv")
    lt2 = lt_rw(hi1, "2n", v(SH(V1)), "2n", f"Equal.sym(Nat, {v(SH(V1))}, {hi1}, UL.u32_shrn_value({V1}, 16n))", None, f"UL.high_lt(16n, 1n, 17n, {v(V1)}, {{==}}, {lt17})")
    hcp1 = f"PL.bq.le1({v(SH(V1))}, {lt2})"
    pre1 = f"""      +hx1 = {hx1}
      +esl1 = {esl1}
      +bv = {bv1}
      +vv1 = {vv1}
      +hcp = {hcp1}
"""
    lo1 = f"U.U32Nat.low(16n, {v(V1)})"
    REST1 = f"N.bn.shl1(t, {SH(V1)})"
    IHR1 = f"Nat.add(Nat.double({VT}), {v(SH(V1))})"
    IHH1 = f"Nat.add(Nat.double({VT}), {hi1})"
    DVT = D16(f"Nat.double({VT})")
    chain1 = calc(f"Nat.add({v(AND(V1))}, {D16(V(REST1))})",
                  (f"Nat.add({lo1}, {D16(V(REST1))})", hyp(f"PL.bq.lo({V1})", v(AND(V1)), lo1)),
                  (f"Nat.add({lo1}, {D16(IHR1)})", hyp("ih", V(REST1), IHR1)),
                  (f"Nat.add({lo1}, {D16(IHH1)})", hyp(f"UL.u32_shrn_value({V1}, 16n)", v(SH(V1)), hi1)),
                  (f"Nat.add(Nat.add({lo1}, {D16(hi1)}), {DVT})", "ring"),
                  (f"Nat.add({v(V1)}, {DVT})", hyp(f"UL.low_high(16n, {v(V1)})", f"Nat.add({lo1}, {D16(hi1)})", v(V1))),
                  (f"Nat.add({S1}, {DVT})", hyp("vv1", v(V1), S1)),
                  (f"Nat.add(Nat.double(Nat.add({X}, {D16(VT)})), {VC})", "ring"))
    sig1 = f"(xs: {LIST}, +c: U32, +hx: {OKT('xs')}, +hc: {btrue(f'Nat.is_le({VC}, 1n)')})"
    put(f"""def bd.s1v{sig1} -> {{{V('N.bn.shl1(xs, c)')} == Nat.add(Nat.double({V('xs')}), {VC}) : Nat}}:
  match xs:
    case Nil{{}}:
      PL.bq.lone(c, U32.is_zero(c), {{==}})
    case Con{{+x, +t}}:
{pre1}      +ih = bd.s1v(t, {SH(V1)}, {hts}, hcp)
      {chain1.text}

def bd.s1k{sig1} -> {OKT('N.bn.shl1(xs, c)')}:
  match xs:
    case Nil{{}}:
      PL.bq.okl(c, U32.is_zero(c), {{==}}, PL.bq.lelt({VC}, 1n, {W16}, hc, {{==}}))
    case Con{{+x, +t}}:
{pre1}      PL.bq.and3(U32.is_zero({SH(AND(V1))}), {OK(REST1)}, PL.bq.mk({V1}), bd.s1k(t, {SH(V1)}, {hts}, hcp))
""")
    # shr1
    H = "N.bn.hd(t)"
    O = f"U.U32Nat.odd({v(H)})"
    o = f"U32.and(1, {H})"
    A = "U32.shrn(x, 1n)"
    Bw = f"U32.shln({o}, 15n)"
    L = f"U32.or({A}, {Bw})"
    H1 = f"U.U32Nat.high(1n, {X})"
    vo = tr(v(o), v(f"U32.and({H}, 1)"), O, f"Equal.cong(U32, Nat, zz => U32.to_nat(zz), {o}, U32.and({H}, 1), UL.u32_and_comm(1, {H}))",
            tr(v(f"U32.and({H}, 1)"), f"Nat.add({O}, 0n)", O, f"UL.u32_and_mask({H}, 1, 1n, {{==}})", f"UL.nat_add_zero({O})"))
    D15 = D("15n", O)
    olt = f"PL.bq.le_lt({O}, 2n, UL.nat_odd_le({v(H)}))"
    bb = lt_rw(D15, D("15n", "2n"), D15, W16, None, "bd.d2(15n, 16n, {==})",
               bt(f"Nat.is_lt({D15}, {D('15n', '2n')})", f"Nat.is_lt({O}, 2n)", f"UL.dbl_lt(15n, {O}, 2n)", olt))
    LO15 = f"U.U32Nat.low(32n, {D('15n', v(o))})"
    vbw = tr(v(Bw), LO15, D15, f"UL.u32_shln_low({o}, 15n)",
             tr(LO15, f"U.U32Nat.low(32n, {D15})", D15,
                f"Equal.cong(Nat, Nat, zz => U.U32Nat.low(32n, {D('15n', 'zz')}), {v(o)}, {O}, vo)",
                f"UL.low_small(32n, {D15}, PL.bq.ltle({D15}, {W16}, {W32}, bb, UL.dbl_le_exp(16n, 32n, 1n, {{==}})))"))
    ha = lt_rw(H1, D("15n", "1n"), v(A), D("15n", "1n"), f"Equal.sym(Nat, {v(A)}, {H1}, UL.u32_shrn_value(x, 1n))", None,
               f"UL.high_lt(1n, 15n, 16n, {X}, {{==}}, hx1)")
    SL_ = f"Nat.add({D15}, {v(A)})"
    vl = tr(v(L), v(f"U32.or({Bw}, {A})"), SL_, f"Equal.cong(U32, Nat, zz => U32.to_nat(zz), {L}, U32.or({Bw}, {A}), UL.u32_or_comm({A}, {Bw}))",
            tr(v(f"U32.or({Bw}, {A})"), f"Nat.add({v(Bw)}, {v(A)})", SL_, f"UL.u32_or_split({Bw}, {A}, 15n, {O}, vbw, ha)",
               f"Equal.cong(Nat, Nat, zz => Nat.add(zz, {v(A)}), {v(Bw)}, {D15}, vbw)"))
    gh, GH = wit_lt(v(A), D("15n", "1n"), "ha")
    go, GO = wit_le(O, "1n", f"UL.nat_odd_le({v(H)})")
    w = f"Nat.add({gh}, {D('15n', go)})"
    D151 = D("15n", "1n")
    pfl = calc(f"Nat.add({w}, 1n+{SL_})",
               (f"Nat.add({D('15n', f'Nat.add({go}, {O})')}, Nat.add({gh}, 1n+{v(A)}))", "ring"),
               (f"Nat.add({D151}, Nat.add({gh}, 1n+{v(A)}))", GO),
               (f"Nat.add({D151}, {D151})", GH),
               (f"Nat.double({D151})", "ring"))
    lb = lt_rw(SL_, f"Nat.double({D151})", v(L), W16, f"Equal.sym(Nat, {v(L)}, {SL_}, vl)", "bd.d17(15n, 16n, {==})", lt_from(SL_, f"Nat.double({D151})", w, pfl))
    RR = "N.bn.shr1(t)"
    VR = V(RR)
    OX = f"U.U32Nat.odd({X})"
    T0 = f"Nat.add(Nat.double(Nat.add({v(L)}, {D16(VR)})), {OX})"
    T1 = f"Nat.add(Nat.double(Nat.add({SL_}, {D16(VR)})), {OX})"
    T2a = f"Nat.add(Nat.add(Nat.add({OX}, Nat.double({v(A)})), Nat.double({D15})), Nat.double({D16(VR)}))"
    T2 = f"Nat.add(Nat.add(Nat.add({OX}, Nat.double({H1})), Nat.double({D15})), Nat.double({D16(VR)}))"
    T3 = f"Nat.add(Nat.add(Nat.add({OX}, Nat.double({H1})), {D16(O)}), Nat.double({D16(VR)}))"
    T4 = f"Nat.add(Nat.add({X}, {D16(O)}), Nat.double({D16(VR)}))"
    T5 = f"Nat.add({X}, {D16(f'Nat.add(Nat.double({VR}), {O})')})"
    T6 = f"Nat.add({X}, {D16(VT)})"
    ch = calc(T0,
              (T1, hyp("vl", v(L), SL_)),
              (T2a, "ring"),
              (T2, hyp("UL.u32_shrn_value(x, 1n)", v(A), H1)),
              (T3, hyp("{==}", f"Nat.double({D15})", D16(O))),
              (T4, hyp(f"UL.nat_odd_half({X})", f"Nat.add({OX}, Nat.double({H1}))", X)),
              (T5, "ring"),
              (T6, hyp("ih", f"Nat.add(Nat.double({VR}), {O})", VT)))
    pre = f"""      +hx1 = {hx1}
      +vo = {vo}
      +bb = {bb}
      +vbw = {vbw}
      +ha = {ha}
      +vl = {vl}
"""
    put(f"""def bd.srv(xs: {LIST}, +hx: {OKT('xs')}) -> {{Nat.add(Nat.double({V('N.bn.shr1(xs)')}), U.U32Nat.odd({v('N.bn.hd(xs)')})) == {V('xs')} : Nat}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
{pre}      +ih = bd.srv(t, {hts})
      {ch.text}

def bd.srk(xs: {LIST}, +hx: {OKT('xs')}) -> {OKT('N.bn.shr1(xs)')}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
{pre}      PL.bq.and3(U32.is_zero({SH(L)}), {OK(RR)}, PL.bq.vl({L}, {lb}), bd.srk(t, {hts}))
""")
    # s = B 2^(1 + p): shr1(s) = B 2^p
    Vs = V("s")
    Vp = V("N.bn.shr1(s)")
    Os = f"U.U32Nat.odd({v('N.bn.hd(s)')})"
    put(f"""def bd.hs(+s: {LIST}, +p: Nat, +B: Nat, +hs: {OKT('s')}, es: {{{Vs} == {D('1n+p', 'B')} : Nat}}) -> {{{Vp} == {D('p', 'B')} : Nat}}:
  +q1 = UL.high_unique(1n, {Vs}, {Os}, {Vp}, Equal.trans(Nat, Nat.add({Os}, Nat.double({Vp})), Nat.add(Nat.double({Vp}), {Os}), {Vs}, UL.nat_add_comm({Os}, Nat.double({Vp})), bd.srv(s, hs)), PL.bq.le_lt({Os}, 2n, UL.nat_odd_le({v('N.bn.hd(s)')})))
  +q2 = UL.high_unique(1n, {Vs}, 0n, {D('p', 'B')}, Equal.sym(Nat, {Vs}, {D('1n+p', 'B')}, es), {{==}})
  Equal.trans(Nat, {Vp}, U.U32Nat.high(1n, {Vs}), {D('p', 'B')}, q1, Equal.sym(Nat, {D('p', 'B')}, U.U32Nat.high(1n, {Vs}), q2))
""")


def G(d, A="A", B="B"):
    """the loop's result d: q B + r = A and r < B"""
    q, r = f"LL.bnlaw.value(N.BnDivMod.q({d}))", f"LL.bnlaw.value(N.BnDivMod.r({d}))"
    return f"{{Nat.add(Nat.mul({q}, {B}), {r}) == {A} : Nat}} & {btrue(f'Nat.is_lt({r}, {B})')}"


CMP = "N.bn.cmp(r, s, EQ{})"
GE = f"N.bn.ge({CMP})"


def loop():
    put("# One step of the loop, and the loop: q B 2^(i+1) + r = A, r < B 2^(i+1), s = B 2^i\n")
    Vr, Vs, Vq = V("r"), V("s"), V("q")
    LIMBS3 = f"+r: {LIST}, +s: {LIST}, +q: {LIST}"
    oks = f"+hr: {OKT('r')}, +hs: {OKT('s')}, +hq: {OKT('q')}"
    DRC = V("N.bn.div.r(N.bn.ge(c), r, s)")
    goal = (f"{{Nat.add(Nat.mul({V('N.bn.shl1(q, N.bn.div.bit(N.bn.ge(c)))')}, S), {V('N.bn.div.r(N.bn.ge(c), r, s)')}) == A : Nat}} & "
            f"{btrue(f'Nat.is_lt({DRC}, S)')}")
    Q0 = V("N.bn.shl1(q, 0)")
    Q1 = V("N.bn.shl1(q, 1)")
    e_lt = calc(f"Nat.add(Nat.mul({Q0}, S), {Vr})",
                (f"Nat.add(Nat.mul(Nat.add(Nat.double({Vq}), 0n), S), {Vr})", hyp("bd.s1v(q, 0, hq, {==})", Q0, f"Nat.add(Nat.double({Vq}), 0n)")),
                (f"Nat.add(Nat.mul({Vq}, Nat.double(S)), {Vr})", "ring"),
                ("A", hyp("inv", f"Nat.add(Nat.mul({Vq}, Nat.double(S)), {Vr})", "A")))
    l_lt = lt_rw(Vr, Vs, Vr, "S", None, "es", f"Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Nat.cmp({Vr}, {Vs}), LT{{}}, ec)")
    Dd = V("N.bn.sub(r, s, 0)")
    hle = le_rw(Vs, Vr, f"Nat.add({Vs}, U32.to_nat(0))", Vr, f"Equal.sym(Nat, Nat.add({Vs}, U32.to_nat(0)), {Vs}, UL.nat_add_zero({Vs}))", None,
                f"PL.bq.nlt_le({Vr}, {Vs}, Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Nat.cmp({Vr}, {Vs}), CC, ec))")
    e1 = calc(f"Nat.add({Dd}, S)",
              (f"Nat.add({Dd}, {Vs})", sym(hyp("es", Vs, "S"))),
              (f"Nat.add(Nat.add({Dd}, {Vs}), 0n)", sym(hyp(f"UL.nat_add_zero(Nat.add({Dd}, {Vs}))", f"Nat.add(Nat.add({Dd}, {Vs}), 0n)", f"Nat.add({Dd}, {Vs})"))),
              (Vr, hyp("sv", f"Nat.add(Nat.add({Dd}, {Vs}), 0n)", Vr)))
    e_ge = calc(f"Nat.add(Nat.mul({Q1}, S), {Dd})",
                (f"Nat.add(Nat.mul(Nat.add(Nat.double({Vq}), 1n), S), {Dd})", hyp("bd.s1v(q, 1, hq, {==})", Q1, f"Nat.add(Nat.double({Vq}), 1n)")),
                (f"Nat.add(Nat.mul({Vq}, Nat.double(S)), Nat.add({Dd}, S))", "ring"),
                (f"Nat.add(Nat.mul({Vq}, Nat.double(S)), {Vr})", hyp("e1", f"Nat.add({Dd}, S)", Vr)),
                ("A", hyp("inv", f"Nat.add(Nat.mul({Vq}, Nat.double(S)), {Vr})", "A")))
    g, Gw = wit_lt(Vr, "Nat.double(S)", "lt")
    c0 = calc(f"Nat.add(S, Nat.add({g}, 1n+{Dd}))",
              (f"Nat.add({g}, 1n+Nat.add({Dd}, S))", "ring"),
              (f"Nat.add({g}, 1n+{Vr})", hyp("e1", f"Nat.add({Dd}, S)", Vr)),
              ("Nat.double(S)", Gw),
              ("Nat.add(S, S)", "ring"))
    cpf = hyp(f"UL.nat_add_cancel(S, Nat.add({g}, 1n+{Dd}), S, {c0.text})", f"Nat.add({g}, 1n+{Dd})", "S")
    l_ge = lt_from(Dd, "S", g, cpf)
    ge_case = f"""      +hle = {hle}
      +sv = PL.bq.sv(r, s, 0, hr, hs, {{==}}, hle)
      +e1 = {e1.text}
      ({e_ge.text}, {l_ge})"""
    put(f"""def bd.drk(z: Bool, +r: {LIST}, +s: {LIST}, +hr: {OKT('r')}) -> {OKT('N.bn.div.r(z, r, s)')}:
  match z:
    case True{{}}:
      PL.bq.sk(r, s, 0)
    case False{{}}:
      hr

def bd.bk(z: Bool) -> {btrue(f"Nat.is_le({v('N.bn.div.bit(z)')}, 1n)")}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      {{==}}

def bd.st({LIMBS3}, +A: Nat, +S: Nat, {oks}, +es: {{{Vs} == S : Nat}}, +inv: {{Nat.add(Nat.mul({Vq}, Nat.double(S)), {Vr}) == A : Nat}}, +lt: {btrue(f'Nat.is_lt({Vr}, Nat.double(S))')}, c: Cmp, ec: {{Nat.cmp({Vr}, {Vs}) == c : Cmp}}) -> {goal}:
  match c:
    case LT{{}}:
      ({e_lt.text}, {l_lt})
    case EQ{{}}:
{ge_case.replace('CC', 'EQ{}')}
    case GT{{}}:
{ge_case.replace('CC', 'GT{}')}
""")
    # the loop
    cm = f"Equal.trans(Cmp, {CMP}, N.bn.step(Nat.cmp({Vr}, {Vs}), EQ{{}}), Nat.cmp({Vr}, {Vs}), PL.bq.cm(r, s, EQ{{}}, hr, hs), PL.bq.st(Nat.cmp({Vr}, {Vs})))"
    rw = f"Equal.sym(Cmp, {CMP}, Nat.cmp({Vr}, {Vs}), {cm})"
    C0 = f"Nat.cmp({Vr}, {Vs})"
    GEc = f"N.bn.ge({C0})"
    X = f"N.bn.div.r({GEc}, r, s)"
    Q2 = f"N.bn.shl1(q, N.bn.div.bit({GEc}))"
    NRU = V("N.bn.norm(N.bn.div.r(N.bn.ge(_), r, s))")
    P0 = (f"{{Nat.add(Nat.mul({V('N.bn.shl1(q, N.bn.div.bit(N.bn.ge(_)))')}, B), {V('N.bn.norm(N.bn.div.r(N.bn.ge(_), r, s))')}) == A : Nat}} & "
          f"{btrue(f'Nat.is_lt({NRU}, B)')}")
    P1 = G("N.bn.div.go(p, N.bn.div.r(N.bn.ge(_), r, s), N.bn.shr1(s), N.bn.shl1(q, N.bn.div.bit(N.bn.ge(_))))")
    VQ2 = V(Q2)
    nvx = f"PL.bq.nv({X})"
    eq0 = tr(f"Nat.add(Nat.mul({VQ2}, B), {V(f'N.bn.norm({X})')})", f"Nat.add(Nat.mul({VQ2}, B), {V(X)})", "A",
             f"Equal.cong(Nat, Nat, zz => Nat.add(Nat.mul({VQ2}, B), zz), {V(f'N.bn.norm({X})')}, {V(X)}, {nvx})", "e1")
    lt0 = tr(f"Nat.is_lt({V(f'N.bn.norm({X})')}, B)", f"Nat.is_lt({V(X)}, B)", "True{}",
             f"Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, B), {V(f'N.bn.norm({X})')}, {V(X)}, {nvx})", "l1", "Bool")
    put(f"""def bd.lp(i: Nat, {LIMBS3}, +A: Nat, +B: Nat, {oks}, +es: {{{Vs} == {D('i', 'B')} : Nat}}, +inv: {{Nat.add(Nat.mul({Vq}, {D('1n+i', 'B')}), {Vr}) == A : Nat}}, +lt: {btrue(f"Nat.is_lt({Vr}, {D('1n+i', 'B')})")}) -> {G('N.bn.div.go(i, r, s, q)')}:
  match i:
    case 0n:
      %{rw} : {P0}
      +pr = bd.st(r, s, q, A, B, hr, hs, hq, es, inv, lt, {C0}, {{==}})
      +e1 = PL.bq.c1(Nat.add(Nat.mul({VQ2}, B), {V(X)}), A, {V(X)}, B, pr)
      +l1 = PL.bq.c2(Nat.add(Nat.mul({VQ2}, B), {V(X)}), A, {V(X)}, B, pr)
      ({eq0}, {lt0})
    case 1n+p:
      %{rw} : {P1}
      +pr = bd.st(r, s, q, A, {D('1n+p', 'B')}, hr, hs, hq, es, inv, lt, {C0}, {{==}})
      +e1 = PL.bq.c1(Nat.add(Nat.mul({VQ2}, {D('1n+p', 'B')}), {V(X)}), A, {V(X)}, {D('1n+p', 'B')}, pr)
      +l1 = PL.bq.c2(Nat.add(Nat.mul({VQ2}, {D('1n+p', 'B')}), {V(X)}), A, {V(X)}, {D('1n+p', 'B')}, pr)
      bd.lp(p, {X}, N.bn.shr1(s), {Q2}, A, B, bd.drk({GEc}, r, s, hr), bd.srk(s, hs), PL.bq.s1k_(q), bd.hs(s, p, B, hs, es), e1, l1)
""".replace("PL.bq.s1k_(q)", f"bd.s1k(q, N.bn.div.bit({GEc}), hq, bd.bk({GEc}))"))
    # the start: la < lb, or d = la - lb steps
    la, lb = "N.bn.bitlen(x)", "N.bn.bitlen(y)"
    A, B = V("x"), V("y")
    fbB = bt(f"Nat.is_le({D(lb, '1n')}, Nat.double({B}))", f"Nat.is_lt(0n, {B})", "bd.fb(y, hy)", "hB")
    dA = (f"PL.bq.ltle({D('1n', A)}, {D('1n+' + la, '1n')}, {D('1n', B)}, bd.dlt({la}, 1n+{la}, {{==}}, {A}, bd.fa(x, hx)), "
            f"PL.bq.le_trans({D('1n+' + la, '1n')}, {D(lb, '1n')}, {D('1n', B)}, UL.dbl_le_exp(1n+{la}, {lb}, 1n, PL.bq.lt_sle({la}, {lb}, ez)), {fbB}))")
    small = bt(f"Nat.is_lt({A}, {B})", f"Nat.is_lt({D('1n', A)}, {D('1n', B)})", f"Equal.sym(Bool, Nat.is_lt({D('1n', A)}, {D('1n', B)}), Nat.is_lt({A}, {B}), UL.dbl_lt(1n, {A}, {B}))", dA)
    d = f"Nat.sub({la}, {lb})"
    lew = f"UL.nat_le_witness({lb}, {la}, PL.bq.nlt_le({la}, {lb}, ez))"
    # 2^la <= B 2^(1+d)
    L1 = D(la, "1n")
    L2 = D(f"Nat.add({d}, {lb})", "1n")
    L3 = D(d, D(lb, "1n"))
    L4 = D(d, f"Nat.double({B})")
    L5 = D("1n", D(d, B))
    le_a = le_rw(L3, L4, L1, L4, tr(L3, L2, L1, f"UL.dbl_dbl({d}, {lb}, 1n)", f"Equal.cong(Nat, Nat, zz => {D('zz', '1n')}, Nat.add({d}, {lb}), {la}, {lew})"), None,
                 bt(f"Nat.is_le({L3}, {L4})", f"Nat.is_le({D(lb, '1n')}, Nat.double({B}))", f"UL.dbl_le({d}, {D(lb, '1n')}, Nat.double({B}))", fbB))
    le_b = le_rw(L1, L4, L1, L5, None, f"UL.dbl_comm({d}, 1n, {B})", le_a)
    VNX = V("N.bn.norm(x)")
    ltx = lt_rw(A, L1, VNX, L1, f"Equal.sym(Nat, {VNX}, {A}, PL.bq.nv(x))", None, "bd.fa(x, hx)")
    lt_start = f"PL.bq.ltle({VNX}, {L1}, {D('1n+' + d, B)}, {ltx}, {le_b})"
    S0 = f"N.bn.shl(N.bn.norm(y), {d})"
    es0 = tr(V(S0), D(d, V("N.bn.norm(y)")), D(d, B), f"bd.slv(N.bn.norm(y), {d}, PL.bq.nk(y, hy))",
             f"Equal.cong(Nat, Nat, zz => {D(d, 'zz')}, {V('N.bn.norm(y)')}, {B}, PL.bq.nv(y))")
    put(f"""def bd.go(z: Bool, +x: {LIST}, +y: {LIST}, +hx: {OKT('x')}, +hy: {OKT('y')}, +hB: {btrue(f'Nat.is_lt(0n, {B})')}, ez: {{Nat.is_lt({la}, {lb}) == z : Bool}}) -> {G(f'N.bn.divmod.go(z, x, y, {la}, {lb})', A, B)}:
  match z:
    case True{{}}:
      ({{==}}, {small})
    case False{{}}:
      bd.lp({d}, N.bn.norm(x), {S0}, Nil{{}}, {A}, {B}, PL.bq.nk(x, hx), bd.slk(N.bn.norm(y), {d}, PL.bq.nk(y, hy)), {{==}}, {es0}, PL.bq.nv(x), {lt_start})

def bd.dm(+x: {LIST}, +y: {LIST}, +hx: {OKT('x')}, +hy: {OKT('y')}, +hB: {btrue(f'Nat.is_lt(0n, {B})')}) -> {G('N.bn.divmod(x, y)', A, B)}:
  bd.go(Nat.is_lt({la}, {lb}), x, y, hx, hy, hB, {{==}})
""")


def laws():
    put("# The results are numbers (eta), and the laws\n")
    Dg = "N.bn.div.go(i, r, s, q)"
    NXT = f"N.bn.div.go(p, N.bn.div.r({GE}, r, s), N.bn.shr1(s), N.bn.shl1(q, N.bn.div.bit({GE})))"
    put(f"""def bd.eg(i: Nat, +r: {LIST}, +s: {LIST}, +q: {LIST}) -> {{{Dg} == N.BnDivMod{{N.BnDivMod.q({Dg}), N.BnDivMod.r({Dg})}} : N.BnDivMod}}:
  match i:
    case 0n:
      {{==}}
    case 1n+p:
      bd.eg(p, N.bn.div.r({GE}, r, s), N.bn.shr1(s), N.bn.shl1(q, N.bn.div.bit({GE})))

def bd.ed(z: Bool, +a: {LIST}, +b: {LIST}, +la: Nat, +lb: Nat) -> {{N.bn.divmod.go(z, a, b, la, lb) == N.BnDivMod{{N.BnDivMod.q(N.bn.divmod.go(z, a, b, la, lb)), N.BnDivMod.r(N.bn.divmod.go(z, a, b, la, lb))}} : N.BnDivMod}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      bd.eg(Nat.sub(la, lb), N.bn.norm(a), N.bn.shl(N.bn.norm(b), Nat.sub(la, lb)), Nil{{}})

def bd.lqk(i: Nat, +r: {LIST}, +s: {LIST}, +q: {LIST}, +hq: {OKT('q')}) -> {{LL.bnlaw.valid(N.BnDivMod.q({Dg})) == True{{}} : Bool}}:
  match i:
    case 0n:
      bd.s1k(q, N.bn.div.bit({GE}), hq, bd.bk({GE}))
    case 1n+p:
      bd.lqk(p, N.bn.div.r({GE}, r, s), N.bn.shr1(s), N.bn.shl1(q, N.bn.div.bit({GE})), bd.s1k(q, N.bn.div.bit({GE}), hq, bd.bk({GE})))

def bd.lrk(i: Nat, +r: {LIST}, +s: {LIST}, +q: {LIST}, +hr: {OKT('r')}) -> {{LL.bnlaw.valid(N.BnDivMod.r({Dg})) == True{{}} : Bool}}:
  match i:
    case 0n:
      PL.bq.nk(N.bn.div.r({GE}, r, s), bd.drk({GE}, r, s, hr))
    case 1n+p:
      bd.lrk(p, N.bn.div.r({GE}, r, s), N.bn.shr1(s), N.bn.shl1(q, N.bn.div.bit({GE})), bd.drk({GE}, r, s, hr))
""")
    la, lb = "N.bn.bitlen(x)", "N.bn.bitlen(y)"
    DM = "N.bn.divmod(x, y)"
    eta = f"Equal.sym(N.BnDivMod, {DM}, N.BnDivMod{{N.BnDivMod.q({DM}), N.BnDivMod.r({DM})}}, bd.ed(Nat.is_lt({la}, {lb}), x, y, {la}, {lb}))"
    A, B = V("x"), V("y")
    MAPQ = "Maybe.map(&2, N.BnDivMod, N.BnNat, d => N.BnDivMod.q(d), "
    MAPR = "Maybe.map(&2, N.BnDivMod, N.BnNat, d => N.BnDivMod.r(d), "
    Q = f"LL.bnlaw.value(N.BnDivMod.q({DM}))"
    R = f"LL.bnlaw.value(N.BnDivMod.r({DM}))"
    zf = f"{{z == False{{}} : Bool}}"
    zt = f"{{z == True{{}} : Bool}}"
    absf = "Empty.absurd(TY, PL.bq.tf(hz))"
    abst = "Empty.absurd(TY, PL.bq.ft(hz))"
    val = f"+hx: {OKT('x')}, +hy: {OKT('y')}"
    hBt = btrue(f"Nat.is_lt(0n, {B})")
    gq = f"Nat.add(Nat.mul({Q}, {B}), {R})"
    dmc = f"bd.dm(x, y, hx, hy, hB)"
    # z = allz(y): the value of y is 0 exactly when z
    y0 = f"PL.bq.z0({B}, Equal.trans(Bool, Nat.is_eq({B}, 0n), N.bn.allz(y), True{{}}, Equal.sym(Bool, N.bn.allz(y), Nat.is_eq({B}, 0n), PL.bq.zv(y)), ez))"
    yp = f"PL.bq.nz({B}, Equal.trans(Bool, Nat.is_eq({B}, 0n), N.bn.allz(y), False{{}}, Equal.sym(Bool, N.bn.allz(y), Nat.is_eq({B}, 0n), PL.bq.zv(y)), ez))"
    ezt = f"{{N.bn.allz(y) == z : Bool}}"
    MODV = f"LL.bnlaw.value(N.bn.mod.zero(z, x, y))"
    DIVV = f"LL.bnlaw.value(N.bn.div.q(N.bn.divmod.zero(z, x, y)))"
    put(f"""def bd.dn(z: Bool, +x: {LIST}, +y: {LIST}, hz: {zt}) -> {{N.bn.divmod.zero(z, x, y) == None{{}} : Maybe<&2, N.BnDivMod>}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      {abst.replace('TY', '{N.bn.divmod.zero(False{}, x, y) == None{} : Maybe<&2, N.BnDivMod>}')}

def bd.dq(z: Bool, +x: {LIST}, +y: {LIST}, hz: {zf}) -> {{{MAPQ}N.bn.divmod.zero(z, x, y)) == Some{{N.bn.div.q(N.bn.divmod.zero(z, x, y))}} : Maybe<&2, N.BnNat>}}:
  match z:
    case True{{}}:
      {absf.replace('TY', '{' + f"{MAPQ}N.bn.divmod.zero(True{{}}, x, y)) == Some{{N.bn.div.q(N.bn.divmod.zero(True{{}}, x, y))}} : Maybe<&2, N.BnNat>" + '}')}
    case False{{}}:
      %{eta} : {{{MAPQ}Some{{_}}) == Some{{N.bn.div.q(Some{{_}})}} : Maybe<&2, N.BnNat>}}
      {{==}}

def bd.dr(z: Bool, +x: {LIST}, +y: {LIST}, hz: {zf}) -> {{{MAPR}N.bn.divmod.zero(z, x, y)) == Some{{N.bn.mod.zero(z, x, y)}} : Maybe<&2, N.BnNat>}}:
  match z:
    case True{{}}:
      {absf.replace('TY', '{' + f"{MAPR}N.bn.divmod.zero(True{{}}, x, y)) == Some{{N.bn.mod.zero(True{{}}, x, y)}} : Maybe<&2, N.BnNat>" + '}')}
    case False{{}}:
      %{eta} : {{{MAPR}Some{{_}}) == Some{{N.bn.mod.r(_)}} : Maybe<&2, N.BnNat>}}
      {{==}}

def bd.dv(z: Bool, +x: {LIST}, +y: {LIST}, {val}, ez: {ezt}, hz: {zf}) -> {{Nat.add(Nat.mul({DIVV}, {B}), {MODV}) == {A} : Nat}} & {btrue(f'Nat.is_lt({MODV}, {B})')}:
  match z:
    case True{{}}:
      {absf.replace('TY', '{Nat.add(Nat.mul(0n, ' + B + '), ' + A + ') == ' + A + ' : Nat} & ' + btrue(f'Nat.is_lt({A}, {B})'))}
    case False{{}}:
      +hB = {yp}
      %{eta} : {{Nat.add(Nat.mul(LL.bnlaw.value(N.bn.div.q(Some{{_}})), {B}), LL.bnlaw.value(N.bn.mod.r(_))) == {A} : Nat}} & {btrue(f'Nat.is_lt(LL.bnlaw.value(N.bn.mod.r(_)), {B})')}
      {dmc}

def bd.mv(z: Bool, +x: {LIST}, +y: {LIST}, {val}, ez: {ezt}) -> {{{MODV} == Nat.mod({A}, {B}) : Nat}}:
  match z:
    case True{{}}:
      %Equal.sym(Nat, {B}, 0n, {y0}) : {{{A} == Nat.mod({A}, _) : Nat}}
      {{==}}
    case False{{}}:
      +hB = {yp}
      %{eta} : {{LL.bnlaw.value(N.bn.mod.r(_)) == Nat.mod({A}, {B}) : Nat}}
      +pr = {dmc}
      +e1 = PL.bq.c1({gq}, {A}, {R}, {B}, pr)
      +l1 = PL.bq.c2({gq}, {A}, {R}, {B}, pr)
      UL.nat_mod_unique({B}, {Q}, {R}, Nat.div({A}, {B}), Nat.mod({A}, {B}), Equal.trans(Nat, {gq}, {A}, Nat.add(Nat.mul(Nat.div({A}, {B}), {B}), Nat.mod({A}, {B})), e1, Equal.sym(Nat, Nat.add(Nat.mul(Nat.div({A}, {B}), {B}), Nat.mod({A}, {B})), {A}, bd.ndm({A}, {B}, hB))), l1, bd.nml({A}, {B}, hB))

def bd.vv(z: Bool, +x: {LIST}, +y: {LIST}, {val}, ez: {ezt}) -> {{{DIVV} == Nat.div({A}, {B}) : Nat}}:
  match z:
    case True{{}}:
      %Equal.sym(Nat, {B}, 0n, {y0}) : {{0n == Nat.div({A}, _) : Nat}}
      {{==}}
    case False{{}}:
      +hB = {yp}
      %{eta} : {{LL.bnlaw.value(N.bn.div.q(Some{{_}})) == Nat.div({A}, {B}) : Nat}}
      +pr = {dmc}
      +e1 = PL.bq.c1({gq}, {A}, {R}, {B}, pr)
      +l1 = PL.bq.c2({gq}, {A}, {R}, {B}, pr)
      UL.nat_div_unique({B}, {Q}, {R}, Nat.div({A}, {B}), Nat.mod({A}, {B}), Equal.trans(Nat, {gq}, {A}, Nat.add(Nat.mul(Nat.div({A}, {B}), {B}), Nat.mod({A}, {B})), e1, Equal.sym(Nat, Nat.add(Nat.mul(Nat.div({A}, {B}), {B}), Nat.mod({A}, {B})), {A}, bd.ndm({A}, {B}, hB))), l1, bd.nml({A}, {B}, hB))

def bd.gqk(z: Bool, +x: {LIST}, +y: {LIST}, +la: Nat, +lb: Nat) -> {{LL.bnlaw.valid(N.BnDivMod.q(N.bn.divmod.go(z, x, y, la, lb))) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      bd.lqk(Nat.sub(la, lb), N.bn.norm(x), N.bn.shl(N.bn.norm(y), Nat.sub(la, lb)), Nil{{}}, {{==}})

def bd.grk(z: Bool, +x: {LIST}, +y: {LIST}, +la: Nat, +lb: Nat, +hx: {OKT('x')}) -> {{LL.bnlaw.valid(N.BnDivMod.r(N.bn.divmod.go(z, x, y, la, lb))) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      hx
    case False{{}}:
      bd.lrk(Nat.sub(la, lb), N.bn.norm(x), N.bn.shl(N.bn.norm(y), Nat.sub(la, lb)), Nil{{}}, PL.bq.nk(x, hx))

def bd.dk(z: Bool, +x: {LIST}, +y: {LIST}) -> {{LL.bnlaw.valid(N.bn.div.q(N.bn.divmod.zero(z, x, y))) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      %{eta} : {{LL.bnlaw.valid(N.bn.div.q(Some{{_}})) == True{{}} : Bool}}
      bd.gqk(Nat.is_lt({la}, {lb}), x, y, {la}, {lb})

def bd.mk(z: Bool, +x: {LIST}, +y: {LIST}, +hx: {OKT('x')}) -> {{LL.bnlaw.valid(N.bn.mod.zero(z, x, y)) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      hx
    case False{{}}:
      %{eta} : {{LL.bnlaw.valid(N.bn.mod.r(_)) == True{{}} : Bool}}
      bd.grk(Nat.is_lt({la}, {lb}), x, y, {la}, {lb}, hx)
""")
    LMR = MODV.replace("(z, ", "(N.bn.allz(y), ")
    LGQ = f"Nat.add(Nat.mul({DIVV.replace('(z, ', '(N.bn.allz(y), ')}, {B}), {LMR})"
    hz0 = f"Equal.trans(Bool, N.bn.allz(y), Nat.is_eq({B}, 0n), True{{}}, PL.bq.zv(y), Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 0n), {B}, 0n, h))"
    hzp = f"Equal.trans(Bool, N.bn.allz(y), Nat.is_eq({B}, 0n), False{{}}, PL.bq.zv(y), PL.bq.nz1({B}, h))"
    put(f"""def Laws.divmod_none(a, b, h):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.dn(N.bn.allz(y), x, y, {hz0})

def Laws.divmod_q(a, b, h):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.dq(N.bn.allz(y), x, y, {hzp})

def Laws.divmod_r(a, b, h):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.dr(N.bn.allz(y), x, y, {hzp})

def Laws.divmod_value(a, b, ha, hb, h):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      PL.bq.c1({LGQ}, {A}, {LMR}, {B}, bd.dv(N.bn.allz(y), x, y, ha, hb, {{==}}, {hzp}))

def Laws.mod_lt(a, b, ha, hb, h):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      PL.bq.c2({LGQ}, {A}, {LMR}, {B}, bd.dv(N.bn.allz(y), x, y, ha, hb, {{==}}, {hzp}))

def Laws.mod_value(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.mv(N.bn.allz(y), x, y, ha, hb, {{==}})

def Laws.div_value(a, b, ha, hb):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.vv(N.bn.allz(y), x, y, ha, hb, {{==}})

def Laws.div_valid(a, b):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.dk(N.bn.allz(y), x, y)

def Laws.mod_valid(a, b, ha):
  match a b:
    case N.BnNat{{+x}} N.BnNat{{+y}}:
      bd.mk(N.bn.allz(y), x, y, ha)
""")


SECTIONS = [natdiv, bits, tops, shifts, loop, laws]


def main():
    put("# Long division: the quotient and remainder of the values\n")
    for f in SECTIONS:
        f()
    put("")
    text = "\n".join(out).replace("LASTGO(", "List.last.go(&2, U32, ").replace("APPEND(", "List.append(&2, U32, ")
    text = re.sub(r"case 1n\+([a-z]\w*):", r"case 1n+ +\1:", text)
    # a pair of proofs is not Data: inline +pr into its two projections
    lines = text.split("\n")
    res = []
    i = 0
    while i < len(lines):
        m = re.match(r"( +)\+pr = (.*)$", lines[i])
        if m:
            e = m.group(2)
            assert lines[i + 1].endswith(", pr)") and lines[i + 2].endswith(", pr)")
            res.append(lines[i + 1][:-3] + e + ")")
            res.append(lines[i + 2][:-3] + e + ")")
            i += 3
            continue
        res.append(lines[i])
        i += 1
    text = "\n".join(res)
    hdr = ("# Generated by gen/proof_div.py; do not edit by hand. The proofs of LAWS_div.bend.\n"
           "import Base\nimport ../u32/u32.bend as U\nimport ../u32/LAWS.bend as UL\nimport ../u32/PROOF.bend as UP\n"
           "import ./bignum.bend as N\nimport ./LAWS_limbs.bend as LL\nimport ./PROOF_limbs.bend as PL\n"
           "import ./LAWS_div.bend as Laws\n\n")
    with open(PROOF, "w", newline="\n") as f:
        f.write(hdr + text)


if __name__ == "__main__":
    main()
