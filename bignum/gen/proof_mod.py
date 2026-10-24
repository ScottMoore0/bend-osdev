#!/usr/bin/env python3
"""Writes bignum/PROOF_mod.bend: the proofs of the modular laws
(LAWS_mod.bend).

  python3 gen/proof_mod.py

BnMod.add, sub and mul are BnNat.mod of add, sub and mul, so their laws
follow from LAWS_limbs, LAWS_mul and LAWS_div; the difference law
(mod_sub_add) is Nat arithmetic modulo m: with a' = a mod m and b' = b mod
m, ((a' + m - b') + b) = a' + (1 + b / m) m. The Nat lemmas on Nat.mod
(bx.mu: a quotient and remainder determine Nat.mod; bx.mam, bx.mml,
bx.mmr, bx.mal: adding multiples of m and reducing factors and summands
first change nothing) and on Nat.pow (bx.pa, bx.pm, bx.pmod) are shared
with PROOF_mont.bend.

BnMod.exp_plain is square and multiply from bit bit_len(e) - 1 down to bit
0: with E = value(e), the accumulator before bit p is X^(E >> (p + 1)) mod
m, since E >> p = 2 (E >> (p + 1)) + bit p (u32's nat_odd_half, with
bx.hh: high(1 + p, E) = half(high(p, E))); BnNat.bit(e, p) is that bit of
E (bx.bit: the limb p / 16, from bx.dv, its bit p mod 16, from bx.hl), and
E >> bit_len(e) = 0 (PROOF_div's bd.fa: E < 2^bit_len). The ring
identities come from scripts/natproof.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "scripts"))
import natproof as NP  # noqa: E402
from natproof import btrue, calc, hyp, sym, lt_rw  # noqa: E402

NP.CFG["law"] = "UL."
NP.OUT.prefix = "bx.r"
PROOF = os.path.join(HERE, "..", "PROOF_mod.bend")

out = []
_flushed = [0]


def put(s=""):
    defs = NP.OUT.defs[_flushed[0]:]
    if defs:
        out.append("\n".join(defs))
        _flushed[0] = len(NP.OUT.defs)
    out.append(s)


LIST = "List<&2, U32>"


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


def LOW(k, x):
    return f"U.U32Nat.low({k}, {x})"


def HIGH(k, x):
    return f"U.U32Nat.high({k}, {x})"


def ODD(x):
    return f"U.U32Nat.odd({x})"


def HALF(x):
    return f"U.U32Nat.half({x})"


def MOD(a, b):
    return f"Nat.mod({a}, {b})"


def ADD(a, b):
    return f"Nat.add({a}, {b})"


def MUL(a, b):
    return f"Nat.mul({a}, {b})"


def POW(a, b):
    return f"Nat.pow({a}, {b})"


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


def ndm(a, b, h="hB"):
    return hyp(f"PD.bd.ndm({a}, {b}, {h})", ADD(MUL(f"Nat.div({a}, {b})", b), MOD(a, b)), a)


def natmod():
    put("# Nat.mod: a quotient and remainder determine it; multiples of m, and\n"
        "# factors and summands reduced first, change nothing\n")
    put(f"""def bx.mu(+A: Nat, +B: Nat, +q: Nat, +r: Nat, +e: {EQ(ADD(MUL('q', 'B'), 'r'), 'A')}, +h: {LTx('r', 'B')}) -> {EQ(MOD('A', 'B'), 'r')}:
  +hB = PL.bq.lelt(0n, r, B, PL.bq.le0(r), h)
  UL.nat_mod_unique(B, Nat.div(A, B), Nat.mod(A, B), q, r, Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(A, B), B), Nat.mod(A, B)), A, Nat.add(Nat.mul(q, B), r), PD.bd.ndm(A, B, hB), Equal.sym(Nat, Nat.add(Nat.mul(q, B), r), A, e)), PD.bd.nml(A, B, hB), h)
""")
    HB = LTx("0n", "B")
    e = calc(ADD(MUL(ADD("Nat.div(A, B)", "q"), "B"), MOD("A", "B")),
             (ADD(ADD(MUL("Nat.div(A, B)", "B"), MOD("A", "B")), MUL("q", "B")), "ring"),
             (ADD("A", MUL("q", "B")), ndm("A", "B")))
    put(f"""def bx.mam(+A: Nat, +q: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(ADD('A', MUL('q', 'B')), 'B'), MOD('A', 'B'))}:
  bx.mu(Nat.add(A, Nat.mul(q, B)), B, Nat.add(Nat.div(A, B), q), Nat.mod(A, B), {e.text}, PD.bd.nml(A, B, hB))
""")

    def mam(A, q, B="B", h="hB"):
        return hyp(f"bx.mam({A}, {q}, {B}, {h})", MOD(ADD(A, MUL(q, B)), B), MOD(A, B))

    da = "Nat.div(a, B)"
    c = calc(MOD(MUL("a", "b"), "B"),
             (MOD(MUL(ADD(MUL(da, "B"), MOD("a", "B")), "b"), "B"), sym(ndm("a", "B"))),
             (MOD(ADD(MUL(MOD("a", "B"), "b"), MUL(MUL(da, "b"), "B")), "B"), "ring"),
             (MOD(MUL(MOD("a", "B"), "b"), "B"), mam(MUL(MOD("a", "B"), "b"), MUL(da, "b"))))
    put(f"""def bx.mml(+a: Nat, +b: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(MUL(MOD('a', 'B'), 'b'), 'B'), MOD(MUL('a', 'b'), 'B'))}:
  {sym(c).text}
""")
    c = calc(MOD(MUL("a", MOD("b", "B")), "B"),
             (MOD(MUL(MOD("b", "B"), "a"), "B"), "ring"),
             (MOD(MUL("b", "a"), "B"), hyp("bx.mml(b, a, B, hB)", MOD(MUL(MOD("b", "B"), "a"), "B"), MOD(MUL("b", "a"), "B"))),
             (MOD(MUL("a", "b"), "B"), "ring"))
    put(f"""def bx.mmr(+a: Nat, +b: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(MUL('a', MOD('b', 'B')), 'B'), MOD(MUL('a', 'b'), 'B'))}:
  {c.text}
""")
    c = calc(MOD(ADD("a", "b"), "B"),
             (MOD(ADD(ADD(MUL(da, "B"), MOD("a", "B")), "b"), "B"), sym(ndm("a", "B"))),
             (MOD(ADD(ADD(MOD("a", "B"), "b"), MUL(da, "B")), "B"), "ring"),
             (MOD(ADD(MOD("a", "B"), "b"), "B"), mam(ADD(MOD("a", "B"), "b"), da)))
    put(f"""def bx.mal(+a: Nat, +b: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(ADD(MOD('a', 'B'), 'b'), 'B'), MOD(ADD('a', 'b'), 'B'))}:
  {sym(c).text}

def bx.mm0(+a: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(MOD('a', 'B'), 'B'), MOD('a', 'B'))}:
  bx.mu(Nat.mod(a, B), B, 0n, Nat.mod(a, B), {{==}}, PD.bd.nml(a, B, hB))

def bx.msm(+a: Nat, +B: Nat, +h: {LTx('a', 'B')}) -> {EQ(MOD('a', 'B'), 'a')}:
  bx.mu(a, B, 0n, a, {{==}}, h)
""")
    c = calc(MOD(D("K", MOD("y", "B")), "B"),
             (MOD(MUL(MOD("y", "B"), D("K", "1n")), "B"), "ring"),
             (MOD(MUL("y", D("K", "1n")), "B"), hyp("bx.mml(y, U.U32Nat.dbl(K, 1n), B, hB)", MOD(MUL(MOD("y", "B"), D("K", "1n")), "B"), MOD(MUL("y", D("K", "1n")), "B"))),
             (MOD(D("K", "y"), "B"), "ring"))
    put(f"""def bx.mdl(+K: Nat, +y: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(D('K', MOD('y', 'B')), 'B'), MOD(D('K', 'y'), 'B'))}:
  {c.text}
""")


def pows():
    put("# Nat.pow: exponents add and multiply, and the base may be reduced first\n")
    HB = LTx("0n", "B")
    put(f"""def bx.pa(+x: Nat, a: Nat, +b: Nat) -> {EQ(POW('x', ADD('a', 'b')), MUL(POW('x', 'a'), POW('x', 'b')))}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(1n, Nat.pow(x, b)), Nat.pow(x, b), UL.nat_one_mul(Nat.pow(x, b)))
    case 1n+ +p:
      Equal.trans(Nat, Nat.mul(x, Nat.pow(x, Nat.add(p, b))), Nat.mul(x, Nat.mul(Nat.pow(x, p), Nat.pow(x, b))), Nat.mul(Nat.mul(x, Nat.pow(x, p)), Nat.pow(x, b)), Equal.cong(Nat, Nat, zz => Nat.mul(x, zz), Nat.pow(x, Nat.add(p, b)), Nat.mul(Nat.pow(x, p), Nat.pow(x, b)), bx.pa(x, p, b)), Equal.sym(Nat, Nat.mul(Nat.mul(x, Nat.pow(x, p)), Nat.pow(x, b)), Nat.mul(x, Nat.mul(Nat.pow(x, p), Nat.pow(x, b))), UL.nat_mul_assoc(x, Nat.pow(x, p), Nat.pow(x, b))))

def bx.pm(+x: Nat, +a: Nat, b: Nat) -> {EQ(POW(POW('x', 'a'), 'b'), POW('x', MUL('a', 'b')))}:
  match b:
    case 0n:
      Equal.sym(Nat, Nat.pow(x, Nat.mul(a, 0n)), 1n, Equal.cong(Nat, Nat, zz => Nat.pow(x, zz), Nat.mul(a, 0n), 0n, UL.nat_mul_zero(a)))
    case 1n+ +p:
      Equal.trans(Nat, Nat.mul(Nat.pow(x, a), Nat.pow(Nat.pow(x, a), p)), Nat.mul(Nat.pow(x, a), Nat.pow(x, Nat.mul(a, p))), Nat.pow(x, Nat.mul(a, 1n+p)), Equal.cong(Nat, Nat, zz => Nat.mul(Nat.pow(x, a), zz), Nat.pow(Nat.pow(x, a), p), Nat.pow(x, Nat.mul(a, p)), bx.pm(x, a, p)), Equal.trans(Nat, Nat.mul(Nat.pow(x, a), Nat.pow(x, Nat.mul(a, p))), Nat.pow(x, Nat.add(a, Nat.mul(a, p))), Nat.pow(x, Nat.mul(a, 1n+p)), Equal.sym(Nat, Nat.pow(x, Nat.add(a, Nat.mul(a, p))), Nat.mul(Nat.pow(x, a), Nat.pow(x, Nat.mul(a, p))), bx.pa(x, a, Nat.mul(a, p))), Equal.cong(Nat, Nat, zz => Nat.pow(x, zz), Nat.add(a, Nat.mul(a, p)), Nat.mul(a, 1n+p), Equal.sym(Nat, Nat.mul(a, 1n+p), Nat.add(a, Nat.mul(a, p)), UL.nat_mul_succ(a, p)))))
""")
    mx = MOD("x", "B")
    c = calc(MOD(MUL(mx, POW(mx, "p")), "B"),
             (MOD(MUL("x", POW(mx, "p")), "B"), hyp(f"bx.mml(x, {POW(mx, 'p')}, B, hB)", MOD(MUL(mx, POW(mx, "p")), "B"), MOD(MUL("x", POW(mx, "p")), "B"))),
             (MOD(MUL("x", MOD(POW(mx, "p"), "B")), "B"), sym(hyp(f"bx.mmr(x, {POW(mx, 'p')}, B, hB)", MOD(MUL("x", MOD(POW(mx, "p"), "B")), "B"), MOD(MUL("x", POW(mx, "p")), "B")))),
             (MOD(MUL("x", MOD(POW("x", "p"), "B")), "B"), hyp("bx.pmod(x, p, B, hB)", MOD(POW(mx, "p"), "B"), MOD(POW("x", "p"), "B"))),
             (MOD(MUL("x", POW("x", "p")), "B"), hyp(f"bx.mmr(x, {POW('x', 'p')}, B, hB)", MOD(MUL("x", MOD(POW("x", "p"), "B")), "B"), MOD(MUL("x", POW("x", "p")), "B"))))
    put(f"""def bx.pmod(+x: Nat, e: Nat, +B: Nat, +hB: {HB}) -> {EQ(MOD(POW(mx, 'e'), 'B'), MOD(POW('x', 'e'), 'B'))}:
  match e:
    case 0n:
      {{==}}
    case 1n+ +p:
      {c.text}
""")


def bits():
    put("# The low and high bits: x >> (p + 1) is half of x >> p, shifts compose,\n"
        "# and the parity of x >> s for s below 16 is that of its low 16 bits\n")
    put(f"""def bx.hh(p: Nat, +x: Nat) -> {EQ(HIGH('1n+p', 'x'), HALF(HIGH('p', 'x')))}:
  match p:
    case 0n:
      {{==}}
    case 1n+ +q:
      bx.hh(q, U.U32Nat.half(x))

def bx.hhh(a: Nat, +b: Nat, +x: Nat) -> {EQ(HIGH('b', HIGH('a', 'x')), HIGH(ADD('a', 'b'), 'x'))}:
  match a:
    case 0n:
      {{==}}
    case 1n+ +p:
      bx.hhh(p, b, U.U32Nat.half(x))

def bx.h0(k: Nat) -> {EQ(HIGH('k', '0n'), '0n')}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +p:
      bx.h0(p)

def bx.l00(+M: Nat) -> {EQ(LOW('M', '0n'), '0n')}:
  UL.low_small(M, 0n, PD.bd.dp(M))

def bx.l1o(+y: Nat) -> {EQ(LOW('1n', 'y'), ODD('y'))}:
  UL.nat_add_zero(U.U32Nat.odd(y))

def bx.od(+a: Nat, z: Nat) -> {EQ(ODD(ADD('a', 'Nat.double(z)')), ODD('a'))}:
  match z:
    case 0n:
      Equal.cong(Nat, Nat, zz => U.U32Nat.odd(zz), Nat.add(a, 0n), a, UL.nat_add_zero(a))
    case 1n+ +w:
      Equal.trans(Nat, U.U32Nat.odd(Nat.add(a, 2n+Nat.double(w))), U.U32Nat.odd(2n+Nat.add(a, Nat.double(w))), U.U32Nat.odd(a), Equal.cong(Nat, Nat, zz => U.U32Nat.odd(zz), Nat.add(a, 2n+Nat.double(w)), 2n+Nat.add(a, Nat.double(w)), Equal.trans(Nat, Nat.add(a, 2n+Nat.double(w)), 1n+Nat.add(a, 1n+Nat.double(w)), 2n+Nat.add(a, Nat.double(w)), UL.nat_add_succ(a, 1n+Nat.double(w)), Equal.cong(Nat, Nat, zz => 1n+zz, Nat.add(a, 1n+Nat.double(w)), 1n+Nat.add(a, Nat.double(w)), UL.nat_add_succ(a, Nat.double(w))))), bx.od(a, w))

def bx.hd2(+a: Nat, z: Nat) -> {EQ(HALF(ADD('a', 'Nat.double(z)')), ADD(HALF('a'), 'z'))}:
  match z:
    case 0n:
      Equal.trans(Nat, U.U32Nat.half(Nat.add(a, 0n)), U.U32Nat.half(a), Nat.add(U.U32Nat.half(a), 0n), Equal.cong(Nat, Nat, zz => U.U32Nat.half(zz), Nat.add(a, 0n), a, UL.nat_add_zero(a)), Equal.sym(Nat, Nat.add(U.U32Nat.half(a), 0n), U.U32Nat.half(a), UL.nat_add_zero(U.U32Nat.half(a))))
    case 1n+ +w:
      Equal.trans(Nat, U.U32Nat.half(Nat.add(a, 2n+Nat.double(w))), 1n+Nat.add(U.U32Nat.half(a), w), Nat.add(U.U32Nat.half(a), 1n+w), Equal.trans(Nat, U.U32Nat.half(Nat.add(a, 2n+Nat.double(w))), U.U32Nat.half(2n+Nat.add(a, Nat.double(w))), 1n+Nat.add(U.U32Nat.half(a), w), Equal.cong(Nat, Nat, zz => U.U32Nat.half(zz), Nat.add(a, 2n+Nat.double(w)), 2n+Nat.add(a, Nat.double(w)), Equal.trans(Nat, Nat.add(a, 2n+Nat.double(w)), 1n+Nat.add(a, 1n+Nat.double(w)), 2n+Nat.add(a, Nat.double(w)), UL.nat_add_succ(a, 1n+Nat.double(w)), Equal.cong(Nat, Nat, zz => 1n+zz, Nat.add(a, 1n+Nat.double(w)), 1n+Nat.add(a, Nat.double(w)), UL.nat_add_succ(a, Nat.double(w))))), Equal.cong(Nat, Nat, zz => 1n+zz, U.U32Nat.half(Nat.add(a, Nat.double(w))), Nat.add(U.U32Nat.half(a), w), bx.hd2(a, w))), Equal.sym(Nat, Nat.add(U.U32Nat.half(a), 1n+w), 1n+Nat.add(U.U32Nat.half(a), w), UL.nat_add_succ(U.U32Nat.half(a), w)))

def bx.ohi(s: Nat, +a: Nat, +k: Nat, +b: Nat) -> {EQ(ODD(HIGH('s', ADD('a', D(ADD('s', '1n+k'), 'b')))), ODD(HIGH('s', 'a')))}:
  match s:
    case 0n:
      bx.od(a, U.U32Nat.dbl(k, b))
    case 1n+ +p:
      Equal.trans(Nat, U.U32Nat.odd(U.U32Nat.high(p, U.U32Nat.half(Nat.add(a, Nat.double(U.U32Nat.dbl(Nat.add(p, 1n+k), b)))))), U.U32Nat.odd(U.U32Nat.high(p, Nat.add(U.U32Nat.half(a), U.U32Nat.dbl(Nat.add(p, 1n+k), b)))), U.U32Nat.odd(U.U32Nat.high(p, U.U32Nat.half(a))), Equal.cong(Nat, Nat, zz => U.U32Nat.odd(U.U32Nat.high(p, zz)), U.U32Nat.half(Nat.add(a, Nat.double(U.U32Nat.dbl(Nat.add(p, 1n+k), b)))), Nat.add(U.U32Nat.half(a), U.U32Nat.dbl(Nat.add(p, 1n+k), b)), bx.hd2(a, U.U32Nat.dbl(Nat.add(p, 1n+k), b))), bx.ohi(p, U.U32Nat.half(a), k, b))
""")
    K = "Nat.sub(15n, s)"
    L16, H16 = LOW("16n", "y"), HIGH("16n", "y")
    eK = TR("Nat", ADD("s", f"1n+{K}"), f"1n+{ADD('s', K)}", "16n", f"UL.nat_add_succ(s, {K})",
            TR("Nat", f"1n+{ADD('s', K)}", f"1n+{ADD(K, 's')}", "16n",
               CG("Nat", "Nat", "1n+zz", ADD("s", K), ADD(K, "s"), f"UL.nat_add_comm(s, {K})"),
               CG("Nat", "Nat", "1n+zz", ADD(K, "s"), "15n", "UL.nat_le_witness(s, 15n, hs)")))
    t0 = ODD(HIGH("s", "y"))
    t1 = ODD(HIGH("s", ADD(L16, D("16n", H16))))
    t2 = ODD(HIGH("s", ADD(L16, D(ADD("s", f"1n+{K}"), H16))))
    t3 = ODD(HIGH("s", L16))
    ch = TR("Nat", t0, t1, t3,
            CG("Nat", "Nat", ODD(HIGH("s", "zz")), "y", ADD(L16, D("16n", H16)), SY("Nat", ADD(L16, D("16n", H16)), "y", "UL.low_high(16n, y)")),
            TR("Nat", t1, t2, t3, CG("Nat", "Nat", ODD(HIGH("s", ADD(L16, D("zz", H16)))), "16n", ADD("s", f"1n+{K}"), SY("Nat", ADD("s", f"1n+{K}"), "16n", "eK")),
               f"bx.ohi(s, {L16}, {K}, {H16})"))
    put(f"""def bx.hl(+s: Nat, +y: Nat, +hs: {btrue('Nat.is_le(s, 15n)')}) -> {EQ(t3, t0)}:
  +eK = {eK}
  {SY('Nat', t0, t3, ch)}

def bx.b1(+y: U32) -> {EQ(v('U32.and(1, y)'), ODD(v('y')))}:
  Equal.trans(Nat, U32.to_nat(U32.and(1, y)), U32.to_nat(U32.and(y, 1)), U.U32Nat.odd(U32.to_nat(y)), Equal.cong(U32, Nat, zz => U32.to_nat(zz), U32.and(1, y), U32.and(y, 1), UL.u32_and_comm(1, y)), Equal.trans(Nat, U32.to_nat(U32.and(y, 1)), Nat.add(U.U32Nat.odd(U32.to_nat(y)), 0n), U.U32Nat.odd(U32.to_nat(y)), UL.u32_and_mask(y, 1, 1n, {{==}}), UL.nat_add_zero(U.U32Nat.odd(U32.to_nat(y)))))

def bx.lo1(p: Nat, +w: Nat) -> {EQ(LOW('1n+p', 'w'), ADD(LOW('p', 'w'), D('p', ODD(HIGH('p', 'w')))))}:
  match p:
    case 0n:
      UL.nat_add_zero(U.U32Nat.odd(w))
    case 1n+ +q:
      {bx_lo1_step()}

def bx.eqt(a: Nat, b: Nat, h: {btrue('Nat.is_eq(a, b)')}) -> {EQ('a', 'b')}:
  match a b:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      Empty.absurd({{0n == 1n+q : Nat}}, PL.bq.ft(h))
    case 1n+p 0n:
      Empty.absurd({{1n+p == 0n : Nat}}, PL.bq.ft(h))
    case 1n+p 1n+q:
      %bx.eqt(p, q, h) : {{1n+p == 1n+_ : Nat}}
      {{==}}

def bx.o0(O: Nat, hO: {btrue('Nat.is_le(O, 1n)')}, ez: {EQ('Nat.is_eq(O, 1n)', 'False{}', 'Bool')}) -> {EQ('O', '0n')}:
  match O:
    case 0n:
      {{==}}
    case 1n+q:
      match q:
        case 0n:
          Empty.absurd({{1n == 0n : Nat}}, PL.bq.tf(ez))
        case 1n+r:
          Empty.absurd({{2n+r == 0n : Nat}}, PL.bq.ft(hO))
""")


def bx_lo1_step():
    # low(2+q, w) = odd w + 2 low(1+q, half w), and the IH at half w
    hw = HALF("w")
    ih = hyp(f"bx.lo1(q, {hw})", LOW("1n+q", hw), ADD(LOW("q", hw), D("q", ODD(HIGH("q", hw)))))
    c = calc(ADD(ODD("w"), f"Nat.double({LOW('1n+q', hw)})"),
             (ADD(ODD("w"), f"Nat.double({ADD(LOW('q', hw), D('q', ODD(HIGH('q', hw))))})"), ih),
             (ADD(ADD(ODD("w"), f"Nat.double({LOW('q', hw)})"), f"Nat.double({D('q', ODD(HIGH('q', hw)))})"), "ring"))
    return c.text


def lists():
    put("# Limbs: the head is the low 16 bits, the tail the rest; take, drop, zeros\n")
    put(f"""def bx.hdl(xs: {LIST}, +hx: {OKT('xs')}) -> {EQ(v('N.bn.hd(xs)'), LOW('16n', V('xs')))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      UL.low_unique(16n, {V('Con{x, t}')}, U32.to_nat(x), {V('t')}, {{==}}, PL.bq.lv(x, PL.bq.and1(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx)))

def bx.tlv(xs: {LIST}) -> {EQ(ADD(v('N.bn.hd(xs)'), D('16n', V('N.bn.tl(xs)'))), V('xs'))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      {{==}}

def bx.tlk(xs: {LIST}, +hx: {OKT('xs')}) -> {OKT('N.bn.tl(xs)')}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      PL.bq.and2(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx)

def bx.hdlt(+xs: {LIST}, +hx: {OKT('xs')}) -> {LTx(v('N.bn.hd(xs)'), W16)}:
  {lt_rw(LOW('16n', V('xs')), W16, v('N.bn.hd(xs)'), W16, SY('Nat', v('N.bn.hd(xs)'), LOW('16n', V('xs')), 'bx.hdl(xs, hx)'), None, f"UL.low_lt(16n, {V('xs')})")}
""")
    wx, X = NP.wit_lt("x", W16, "hx")
    wy, Y = NP.wit_lt("y", "Dd", "hy")
    w = ADD(wx, D("16n", wy))
    S = ADD("x", D("16n", "y"))
    pf = calc(ADD(w, f"1n+{S}"),
              (ADD(ADD(wx, "1n+x"), D("16n", ADD(wy, "y"))), "ring"),
              (ADD(W16, D("16n", ADD(wy, "y"))), X),
              (D("16n", ADD(wy, "1n+y")), "ring"),
              (D("16n", "Dd"), Y))
    put(f"""def bx.st(+x: Nat, +y: Nat, +Dd: Nat, +hx: {LTx('x', W16)}, +hy: {LTx('y', 'Dd')}) -> {LTx(S, D('16n', 'Dd'))}:
  {NP.lt_from(S, D('16n', 'Dd'), w, pf)}
""")
    M = "Nat.mul(N.bn.len(t), 16n)"
    hx1 = "PL.bq.lv(x, PL.bq.and1(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx))"
    hxs = "PL.bq.and2(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx)"
    SC = ADD(v("x"), D("16n", V("t")))
    put(f"""def bx.vlt(xs: {LIST}, +hx: {OKT('xs')}) -> {LTx(V('xs'), D('Nat.mul(N.bn.len(xs), 16n)', '1n'))}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      {lt_rw(SC, D('16n', D(M, '1n')), SC, D(ADD('16n', M), '1n'), None, f'UL.dbl_dbl(16n, {M}, 1n)', f"bx.st({v('x')}, {V('t')}, {D(M, '1n')}, {hx1}, bx.vlt(t, {hxs}))")}
""")
    r = ADD("x", D("16n", LOW("M", "y")))
    q = HIGH("M", "y")
    X_ = ADD("x", D("16n", "y"))
    e = calc(ADD(r, D(ADD("16n", "M"), q)),
             (ADD(r, D("16n", D("M", q))), sym(hyp(f"UL.dbl_dbl(16n, M, {q})", D("16n", D("M", q)), D(ADD("16n", "M"), q)))),
             (ADD("x", D("16n", ADD(LOW("M", "y"), D("M", q)))), "ring"),
             (X_, hyp("UL.low_high(M, y)", ADD(LOW("M", "y"), D("M", q)), "y")))
    h = lt_rw(r, D("16n", D("M", "1n")), r, D(ADD("16n", "M"), "1n"), None, "UL.dbl_dbl(16n, M, 1n)",
              f"bx.st(x, {LOW('M', 'y')}, {D('M', '1n')}, hx, UL.low_lt(M, y))")
    put(f"""def bx.ls(+M: Nat, +x: Nat, +y: Nat, +hx: {LTx('x', W16)}) -> {EQ(LOW(ADD('16n', 'M'), X_), r)}:
  {SY('Nat', r, LOW(ADD('16n', 'M'), X_), f"UL.low_unique({ADD('16n', 'M')}, {X_}, {r}, {q}, {e.text}, {h})")}
""")
    TK = "List.take(&2, U32, t, p)"
    put(f"""def bx.tkv(xs: {LIST}, k: Nat, +hx: {OKT('xs')}) -> {EQ(V('List.take(&2, U32, xs, k)'), LOW('Nat.mul(k, 16n)', V('xs')))}:
  match xs:
    case Nil{{}}:
      match k:
        case 0n:
          {{==}}
        case 1n+ +p:
          Equal.sym(Nat, {LOW('Nat.mul(1n+p, 16n)', '0n')}, 0n, bx.l00(Nat.mul(1n+p, 16n)))
    case Con{{+x, +t}}:
      match k:
        case 0n:
          {{==}}
        case 1n+ +p:
          Equal.trans(Nat, {ADD(v('x'), D('16n', V(TK)))}, {ADD(v('x'), D('16n', LOW('Nat.mul(p, 16n)', V('t'))))}, {LOW(ADD('16n', 'Nat.mul(p, 16n)'), SC)}, Equal.cong(Nat, Nat, zz => {ADD(v('x'), D('16n', 'zz'))}, {V(TK)}, {LOW('Nat.mul(p, 16n)', V('t'))}, bx.tkv(t, p, {hxs})), Equal.sym(Nat, {LOW(ADD('16n', 'Nat.mul(p, 16n)'), SC)}, {ADD(v('x'), D('16n', LOW('Nat.mul(p, 16n)', V('t'))))}, bx.ls(Nat.mul(p, 16n), {v('x')}, {V('t')}, {hx1})))

def bx.tkk(xs: {LIST}, k: Nat, +hx: {OKT('xs')}) -> {OKT('List.take(&2, U32, xs, k)')}:
  match xs:
    case Nil{{}}:
      match k:
        case 0n:
          {{==}}
        case 1n+ +p:
          {{==}}
    case Con{{+x, +t}}:
      match k:
        case 0n:
          {{==}}
        case 1n+ +p:
          PL.bq.and3(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok({TK}), PL.bq.and1(U32.is_zero(U32.shrn(x, 16n)), LL.bnlaw.ok(t), hx), bx.tkk(t, p, {hxs}))

def bx.zv(k: Nat) -> {EQ(V('N.bn.zeros(k)'), '0n')}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +p:
      Equal.trans(Nat, {ADD(v('0'), D('16n', V('N.bn.zeros(p)')))}, {ADD(v('0'), D('16n', '0n'))}, 0n, Equal.cong(Nat, Nat, zz => {ADD(v('0'), D('16n', 'zz'))}, {V('N.bn.zeros(p)')}, 0n, bx.zv(p)), {{==}})

def bx.zk(k: Nat) -> {OKT('N.bn.zeros(k)')}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +p:
      bx.zk(p)
""")
    DR = "N.bn.drop(p, t)"
    hu = f"UL.high_unique(16n, {V('Con{x, t}')}, {v('x')}, {V('t')}, {{==}}, {hx1})"
    MP = "Nat.mul(p, 16n)"
    put(f"""def bx.dv(xs: {LIST}, q: Nat, +hx: {OKT('xs')}) -> {EQ(V('N.bn.drop(q, xs)'), HIGH('Nat.mul(q, 16n)', V('xs')))}:
  match xs:
    case Nil{{}}:
      match q:
        case 0n:
          {{==}}
        case 1n+ +p:
          Equal.sym(Nat, {HIGH('Nat.mul(1n+p, 16n)', '0n')}, 0n, bx.h0(Nat.mul(1n+p, 16n)))
    case Con{{+x, +t}}:
      match q:
        case 0n:
          {{==}}
        case 1n+ +p:
          Equal.trans(Nat, {V(DR)}, {HIGH(MP, V('t'))}, {HIGH(ADD('16n', MP), V('Con{x, t}'))}, bx.dv(t, p, {hxs}), Equal.trans(Nat, {HIGH(MP, V('t'))}, {HIGH(MP, HIGH('16n', V('Con{x, t}')))}, {HIGH(ADD('16n', MP), V('Con{x, t}'))}, Equal.cong(Nat, Nat, zz => {HIGH(MP, 'zz')}, {V('t')}, {HIGH('16n', V('Con{x, t}'))}, {hu}), bx.hhh(16n, {MP}, {V('Con{x, t}')})))

def bx.dk(xs: {LIST}, q: Nat, +hx: {OKT('xs')}) -> {OKT('N.bn.drop(q, xs)')}:
  match xs:
    case Nil{{}}:
      match q:
        case 0n:
          {{==}}
        case 1n+ +p:
          {{==}}
    case Con{{+x, +t}}:
      match q:
        case 0n:
          hx
        case 1n+ +p:
          bx.dk(t, p, {hxs})
""")
    # BnNat.bit(e, i) is bit i of value(e)
    Q, S_ = "Nat.div(i, 16n)", "Nat.mod(i, 16n)"
    DRi = f"N.bn.drop({Q}, ls)"
    W = f"N.bn.hd({DRi})"
    A = f"U32.and(1, U32.shrn({W}, {S_}))"
    MQ = MUL(Q, "16n")
    c = calc(v(A),
             (ODD(v(f"U32.shrn({W}, {S_})")), hyp(f"bx.b1(U32.shrn({W}, {S_}))", v(A), ODD(v(f"U32.shrn({W}, {S_})")))),
             (ODD(HIGH(S_, v(W))), hyp(f"UL.u32_shrn_value({W}, {S_})", v(f"U32.shrn({W}, {S_})"), HIGH(S_, v(W)))),
             (ODD(HIGH(S_, LOW("16n", V(DRi)))), hyp(f"bx.hdl({DRi}, bx.dk(ls, {Q}, he))", v(W), LOW("16n", V(DRi)))),
             (ODD(HIGH(S_, V(DRi))), hyp(f"bx.hl({S_}, {V(DRi)}, PD.bd.m16(i))", ODD(HIGH(S_, LOW("16n", V(DRi)))), ODD(HIGH(S_, V(DRi))))),
             (ODD(HIGH(S_, HIGH(MQ, V("ls")))), hyp(f"bx.dv(ls, {Q}, he)", V(DRi), HIGH(MQ, V("ls")))),
             (ODD(HIGH(ADD(MQ, S_), V("ls"))), hyp(f"bx.hhh({MQ}, {S_}, {V('ls')})", HIGH(S_, HIGH(MQ, V("ls"))), HIGH(ADD(MQ, S_), V("ls")))),
             (ODD(HIGH("i", V("ls"))), hyp("PD.bd.d16(i)", ADD(MQ, S_), "i")))
    G = f"Nat.is_eq({ODD(HIGH('i', V('ls')))}, 1n)"
    put(f"""def bx.bit(e: N.BnNat, +i: Nat, +he: {VT('e')}) -> {EQ('N.BnNat.bit(e, i)', f"Nat.is_eq({ODD(HIGH('i', VAL('e')))}, 1n)", 'Bool')}:
  match e:
    case N.BnNat{{+ls}}:
      Equal.trans(Bool, U32.is_eq({A}, 1), Nat.is_eq({v(A)}, 1n), {G}, UL.u32_eq_value({A}, 1), Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 1n), {v(A)}, {ODD(HIGH('i', V('ls')))}, {c.text}))
""")


def modlaws():
    put("# The modular operations: BnNat.mod of the sum, difference and product\n")
    a, b, m = "a", "b", "m"
    VA, VB, VM = VAL(a), VAL(b), VAL(m)
    S = "N.BnNat.add(a, b)"
    P = "N.BnNat.mul(a, b)"
    Am, Bm = "N.BnNat.mod(a, m)", "N.BnNat.mod(b, m)"
    Pp = f"N.BnNat.add({Am}, m)"
    Sb = f"N.BnNat.sub({Pp}, {Bm})"
    c = calc(VAL(f"N.BnNat.mod({Sb}, m)"),
             (MOD(VAL(Sb), VM), hyp(f"LD.mod_value({Sb}, m, LL.sub_valid({Pp}, {Bm}), hm)", VAL(f"N.BnNat.mod({Sb}, m)"), MOD(VAL(Sb), VM))),
             (MOD(f"Nat.sub({VAL(Pp)}, {VAL(Bm)})", VM), hyp(f"LL.sub_value({Pp}, {Bm}, LL.add_valid({Am}, m, LD.mod_valid(a, m, ha), hm), LD.mod_valid(b, m, hb))", VAL(Sb), f"Nat.sub({VAL(Pp)}, {VAL(Bm)})")),
             (MOD(f"Nat.sub({ADD(VAL(Am), VM)}, {VAL(Bm)})", VM), hyp(f"LL.add_value({Am}, m, LD.mod_valid(a, m, ha), hm)", VAL(Pp), ADD(VAL(Am), VM))),
             (MOD(f"Nat.sub({ADD(MOD(VA, VM), VM)}, {VAL(Bm)})", VM), hyp("LD.mod_value(a, m, ha, hm)", VAL(Am), MOD(VA, VM))),
             (MOD(f"Nat.sub({ADD(MOD(VA, VM), VM)}, {MOD(VB, VM)})", VM), hyp("LD.mod_value(b, m, hb, hm)", VAL(Bm), MOD(VB, VM))))
    # mod_sub_add, on Nat
    A_, M_ = "A", "M"
    Ap, Bp = MOD("A", "M"), MOD("Bv", "M")
    Sn = f"Nat.sub({ADD(Ap, 'M')}, {Bp})"
    dB = "Nat.div(Bv, M)"
    hle = f"PL.bq.le_trans({Bp}, M, {ADD(Ap, 'M')}, PL.bq.lt_le({Bp}, M, PD.bd.nml(Bv, M, hM)), UL.nat_le_add(M, {Ap}))"
    wit = hyp(f"UL.nat_le_witness({Bp}, {ADD(Ap, 'M')}, {hle})", ADD(Sn, Bp), ADD(Ap, "M"))
    c2 = calc(MOD(ADD(MOD(Sn, "M"), "Bv"), "M"),
              (MOD(ADD(Sn, "Bv"), "M"), hyp(f"bx.mal({Sn}, Bv, M, hM)", MOD(ADD(MOD(Sn, "M"), "Bv"), "M"), MOD(ADD(Sn, "Bv"), "M"))),
              (MOD(ADD(Sn, ADD(MUL(dB, "M"), Bp)), "M"), sym(ndm("Bv", "M", "hM"))),
              (MOD(ADD(ADD(Sn, Bp), MUL(dB, "M")), "M"), "ring"),
              (MOD(ADD(ADD(Ap, "M"), MUL(dB, "M")), "M"), wit),
              (MOD(ADD(Ap, MUL(ADD("1n", dB), "M")), "M"), "ring"),
              (MOD(Ap, "M"), hyp(f"bx.mam({Ap}, {ADD('1n', dB)}, M, hM)", MOD(ADD(Ap, MUL(ADD("1n", dB), "M")), "M"), MOD(Ap, "M"))),
              (MOD("A", "M"), hyp("bx.mm0(A, M, hM)", MOD(Ap, "M"), MOD("A", "M"))))
    SUBV = MOD(f"Nat.sub({ADD(MOD(VA, VM), VM)}, {MOD(VB, VM)})", VM)
    put(f"""def Laws.mod_add_value(a, b, m, ha, hb, hm):
  Equal.trans(Nat, {VAL(f'N.BnNat.mod({S}, m)')}, {MOD(VAL(S), VM)}, {MOD(ADD(VA, VB), VM)}, LD.mod_value({S}, m, LL.add_valid(a, b, ha, hb), hm), Equal.cong(Nat, Nat, zz => Nat.mod(zz, {VM}), {VAL(S)}, {ADD(VA, VB)}, LL.add_value(a, b, ha, hb)))

def Laws.mod_add_valid(a, b, m, ha, hb):
  LD.mod_valid({S}, m, LL.add_valid(a, b, ha, hb))

def Laws.mod_sub_value(a, b, m, ha, hb, hm):
  {c.text}

def bx.sbn(+A: Nat, +Bv: Nat, +M: Nat, +hM: {LTx('0n', 'M')}) -> {EQ(MOD(ADD(MOD(Sn, 'M'), 'Bv'), 'M'), MOD('A', 'M'))}:
  {c2.text}

def Laws.mod_sub_add(a, b, m, ha, hb, hm, hm0):
  Equal.trans(Nat, {MOD(ADD(VAL('Md.BnMod.sub(a, b, m)'), VB), VM)}, {MOD(ADD(SUBV, VB), VM)}, {MOD(VA, VM)}, Equal.cong(Nat, Nat, zz => {MOD(ADD('zz', VB), VM)}, {VAL('Md.BnMod.sub(a, b, m)')}, {SUBV}, Laws.mod_sub_value(a, b, m, ha, hb, hm)), bx.sbn({VA}, {VB}, {VM}, hm0))

def Laws.mod_sub_valid(a, b, m):
  LD.mod_valid({Sb}, m, LL.sub_valid({Pp}, {Bm}))

def Laws.mod_mul_value(a, b, m, ha, hb, hm):
  Equal.trans(Nat, {VAL(f'N.BnNat.mod({P}, m)')}, {MOD(VAL(P), VM)}, {MOD(MUL(VA, VB), VM)}, LD.mod_value({P}, m, LM.mul_valid(a, b), hm), Equal.cong(Nat, Nat, zz => Nat.mod(zz, {VM}), {VAL(P)}, {MUL(VA, VB)}, LM.mul_value(a, b, ha, hb)))

def Laws.mod_mul_valid(a, b, m):
  LD.mod_valid({P}, m, LM.mul_valid(a, b))
""")


def expplain():
    put("# The reference exponentiation: square, and multiply where the bit is set\n")
    X, VM, VE = VAL("xm"), VAL("m"), VAL("e")
    SQ = "Md.BnMod.mul(acc, acc, m)"
    PH = POW(X, "H")
    DH = "Nat.double(H)"
    esq = calc(VAL(SQ),
               (MOD(MUL(VAL("acc"), VAL("acc")), VM), hyp("Laws.mod_mul_value(acc, acc, m, ha, ha, hm)", VAL(SQ), MOD(MUL(VAL("acc"), VAL("acc")), VM))),
               (MOD(MUL(MOD(PH, VM), MOD(PH, VM)), VM), hyp("ea", VAL("acc"), MOD(PH, VM))),
               (MOD(MUL(PH, MOD(PH, VM)), VM), hyp(f"bx.mml({PH}, {MOD(PH, VM)}, {VM}, hm0)", MOD(MUL(MOD(PH, VM), MOD(PH, VM)), VM), MOD(MUL(PH, MOD(PH, VM)), VM))),
               (MOD(MUL(PH, PH), VM), hyp(f"bx.mmr({PH}, {PH}, {VM}, hm0)", MOD(MUL(PH, MOD(PH, VM)), VM), MOD(MUL(PH, PH), VM))),
               (MOD(POW(X, ADD("H", "H")), VM), sym(hyp(f"bx.pa({X}, H, H)", POW(X, ADD("H", "H")), MUL(PH, PH)))),
               (MOD(POW(X, DH), VM), sym(hyp("UL.nat_double(H)", DH, ADD("H", "H")))))
    PD_ = POW(X, DH)
    eO = hyp("eO", "O", "1n")
    ct = calc(VAL(f"Md.BnMod.mul({SQ}, xm, m)"),
              (MOD(MUL(VAL(SQ), X), VM), hyp(f"Laws.mod_mul_value({SQ}, xm, m, Laws.mod_mul_valid(acc, acc, m), hx, hm)", VAL(f"Md.BnMod.mul({SQ}, xm, m)"), MOD(MUL(VAL(SQ), X), VM))),
              (MOD(MUL(MOD(PD_, VM), X), VM), hyp("esq", VAL(SQ), MOD(PD_, VM))),
              (MOD(MUL(PD_, X), VM), hyp(f"bx.mml({PD_}, {X}, {VM}, hm0)", MOD(MUL(MOD(PD_, VM), X), VM), MOD(MUL(PD_, X), VM))),
              (MOD(MUL(X, PD_), VM), "ring"),
              (MOD(POW(X, ADD("1n", DH)), VM), "="),
              (MOD(POW(X, ADD("O", DH)), VM), sym(eO)))
    eO0 = hyp("eO", "O", "0n")
    cf = calc(VAL(SQ),
              (MOD(PD_, VM), hyp("esq", VAL(SQ), MOD(PD_, VM))),
              (MOD(POW(X, ADD("0n", DH)), VM), "="),
              (MOD(POW(X, ADD("O", DH)), VM), sym(eO0)))
    PICK = f"Md.bn.pexp.pick(z, {SQ}, xm, m)"
    put(f"""def bx.pkv(z: Bool, +acc: N.BnNat, +xm: N.BnNat, +m: N.BnNat, +H: Nat, +O: Nat, ez: {EQ('Nat.is_eq(O, 1n)', 'z', 'Bool')}, +hO: {btrue('Nat.is_le(O, 1n)')}, +hm: {VT('m')}, +hm0: {LTx('0n', VM)}, +hx: {VT('xm')}, +ha: {VT('acc')}, +ea: {EQ(VAL('acc'), MOD(PH, VM))}) -> {EQ(VAL(PICK), MOD(POW(X, ADD('O', DH)), VM))}:
  match z:
    case True{{}}:
      +esq = {esq.text}
      +eO = bx.eqt(O, 1n, ez)
      {ct.text}
    case False{{}}:
      +esq = {esq.text}
      +eO = bx.o0(O, hO, ez)
      {cf.text}

def bx.pkk(z: Bool, +acc: N.BnNat, +xm: N.BnNat, +m: N.BnNat) -> {VT(PICK)}:
  match z:
    case True{{}}:
      Laws.mod_mul_valid({SQ}, xm, m)
    case False{{}}:
      Laws.mod_mul_valid(acc, acc, m)
""")
    GO = lambda i, acc: f"Md.bn.pexp.go({i}, xm, e, m, {acc})"
    BIT = "N.BnNat.bit(e, p)"
    O = ODD(HIGH("p", VE))
    H1 = HIGH("1n+p", VE)
    ACC2 = f"Md.bn.pexp.pick({BIT}, {SQ}, xm, m)"
    e2 = calc(ADD(O, f"Nat.double({H1})"),
              (ADD(O, f"Nat.double({HALF(HIGH('p', VE))})"), hyp(f"bx.hh(p, {VE})", H1, HALF(HIGH("p", VE)))),
              (HIGH("p", VE), hyp(f"UL.nat_odd_half({HIGH('p', VE)})", ADD(O, f"Nat.double({HALF(HIGH('p', VE))})"), HIGH("p", VE))))
    e1 = f"bx.pkv({BIT}, acc, xm, m, {H1}, {O}, Equal.sym(Bool, {BIT}, Nat.is_eq({O}, 1n), bx.bit(e, p, he)), UL.nat_odd_le({HIGH('p', VE)}), hm, hm0, hx, ha, ea)"
    ea2 = TR("Nat", VAL(ACC2), MOD(POW(X, ADD(O, f"Nat.double({H1})")), VM), MOD(POW(X, HIGH("p", VE)), VM), e1,
             CG("Nat", "Nat", MOD(POW(X, "zz"), VM), ADD(O, f"Nat.double({H1})"), HIGH("p", VE), e2.text))
    put(f"""def bx.pev(i: Nat, +xm: N.BnNat, +e: N.BnNat, +m: N.BnNat, +acc: N.BnNat, +hm: {VT('m')}, +hm0: {LTx('0n', VM)}, +hx: {VT('xm')}, +he: {VT('e')}, +ha: {VT('acc')}, +ea: {EQ(VAL('acc'), MOD(POW(X, HIGH('i', VE)), VM))}) -> {EQ(VAL(GO('i', 'acc')), MOD(POW(X, VE), VM))}:
  match i:
    case 0n:
      ea
    case 1n+ +p:
      bx.pev(p, xm, e, m, {ACC2}, hm, hm0, hx, he, bx.pkk({BIT}, acc, xm, m), {ea2})

def bx.pgk(i: Nat, +xm: N.BnNat, +e: N.BnNat, +m: N.BnNat, +acc: N.BnNat, +ha: {VT('acc')}) -> {VT(GO('i', 'acc'))}:
  match i:
    case 0n:
      ha
    case 1n+ +p:
      bx.pgk(p, xm, e, m, {ACC2}, bx.pkk({BIT}, acc, xm, m))
""")
    L = "N.bn.bitlen(es)"
    VES = V("es")
    VM = VAL("m")
    XM = "N.BnNat.mod(x, m)"
    ONE = "N.BnNat.mod(N.BnNat.one(), m)"
    ehz = f"UL.high_unique({L}, {VES}, {VES}, 0n, Equal.trans(Nat, {ADD(VES, D(L, '0n'))}, {ADD(VES, '0n')}, {VES}, Equal.cong(Nat, Nat, zz => {ADD(VES, 'zz')}, {D(L, '0n')}, 0n, UL.dbl_zero({L})), UL.nat_add_zero({VES})), PD.bd.fa(es, he))"
    ea0 = TR("Nat", VAL(ONE), MOD("1n", VM), MOD(POW(VAL(XM), HIGH(L, VES)), VM), f"LD.mod_value(N.BnNat.one(), m, {{==}}, hm)",
             CG("Nat", "Nat", MOD(POW(VAL(XM), "zz"), VM), "0n", HIGH(L, VES), ehz))
    fin = calc(MOD(POW(VAL(XM), VES), VM),
               (MOD(POW(MOD(VAL("x"), VM), VES), VM), hyp("LD.mod_value(x, m, hx, hm)", VAL(XM), MOD(VAL("x"), VM))),
               (MOD(POW(VAL("x"), VES), VM), hyp(f"bx.pmod({VAL('x')}, {VES}, {VM}, hm0)", MOD(POW(MOD(VAL("x"), VM), VES), VM), MOD(POW(VAL("x"), VES), VM))))
    GOE = f"Md.bn.pexp.go({L}, {XM}, N.BnNat{{es}}, m, {ONE})"
    put(f"""def Laws.exp_plain_value(x, e, m, hx, he, hm, hm0):
  match e:
    case N.BnNat{{+es}}:
      Equal.trans(Nat, {VAL(GOE)}, {MOD(POW(VAL(XM), VES), VM)}, {MOD(POW(VAL('x'), VES), VM)}, bx.pev({L}, {XM}, N.BnNat{{es}}, m, {ONE}, hm, hm0, LD.mod_valid(x, m, hx), he, LD.mod_valid(N.BnNat.one(), m, {{==}}), {ea0}), {fin.text})

def Laws.exp_plain_valid(x, e, m):
  bx.pgk(N.BnNat.bit_len(e), {XM}, e, m, {ONE}, LD.mod_valid(N.BnNat.one(), m, {{==}}))
""")


def main():
    put("# The modular operations and the reference exponentiation\n")
    natmod()
    pows()
    bits()
    lists()
    modlaws()
    expplain()
    put("")
    text = "\n".join(out)
    hdr = ("# Generated by gen/proof_mod.py; do not edit by hand. The proofs of LAWS_mod.bend.\n"
           "import Base\nimport ../u32/u32.bend as U\nimport ../u32/LAWS.bend as UL\nimport ../u32/PROOF.bend as UP\n"
           "import ./bignum.bend as N\nimport ./modular.bend as Md\nimport ./LAWS_limbs.bend as LL\nimport ./PROOF_limbs.bend as PL\n"
           "import ./LAWS_mul.bend as LM\nimport ./PROOF_mul.bend as PM\nimport ./LAWS_div.bend as LD\nimport ./PROOF_div.bend as PD\n"
           "import ./LAWS_mod.bend as Laws\n\n")
    with open(PROOF, "w", newline="\n") as f:
        f.write(hdr + text)


if __name__ == "__main__":
    main()
