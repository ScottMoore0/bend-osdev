#!/usr/bin/env python3
"""Writes kmath/PROOF.bend: the proofs of kmath's laws.

  * Nat arithmetic: addition's identities, commutativity and associativity,
    and multiplication's distributivity and associativity, by induction;
    inequalities as witnesses (x <= y as some w with w + x = y), so that
    they compose by these equations alone;
  * Base's Nat.divmod: for b = 1 + bp, q * b + r = a and r <= bp, by
    induction on its counting loop with the invariant m + r = bp;
  * gcd: by induction on Euclid's fuel, which stays at least b; at each step
    the witnesses for (b, a mod b) give those for (a, b), since a = q b + r;
  * isqrt: by induction on the bits, with the invariant r^2 <= n <
    (r + 2^(b+1))^2 before bit b.

Run: python3 kmath/gen/proof.py
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "PROOF.bend")
out = []


def emit(s=""):
    out.append(s)


def add(a, b):
    return f"Nat.add({a}, {b})"


def mul(a, b):
    return f"Nat.mul({a}, {b})"


def S(a):
    return f"1n+{a}"


def eq(a, b, t="Nat"):
    return "{" + f"{a} == {b} : {t}" + "}"


def sym(a, b, e, t="Nat"):
    return f"Equal.sym({t}, {a}, {b}, {e})"


def trans(a, b, c, ab, bc, t="Nat"):
    return f"Equal.trans({t}, {a}, {b}, {c}, {ab}, {bc})"


def chain(terms, eqs, t="Nat"):
    if len(eqs) == 1:
        return eqs[0]
    return trans(terms[0], terms[1], terms[-1], eqs[0], chain(terms[1:], eqs[1:], t), t)


def cong(var, body, a, b, e, ta="Nat", tb="Nat"):
    return f"Equal.cong({ta}, {tb}, {var} => {body}, {a}, {b}, {e})"


def LE(x, y):
    return f"Sigma<&1, &1, Nat, w => {eq(add('w', x), y)}>"


def DV(x, g):
    return f"Sigma<&1, &1, Nat, u => {eq(mul('u', g), x)}>"


def nat_lemmas():
    emit("# Nat arithmetic")
    emit()
    emit(f"def add_zero_r(+a: Nat) -> {eq(add('a', '0n'), 'a')}:")
    emit("  match a:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit(f"      {cong('z', S('z'), add('p', '0n'), 'p', 'add_zero_r(p)')}")
    emit()
    emit(f"def add_succ_r(+a: Nat, +b: Nat) -> {eq(add('a', S('b')), S(add('a', 'b')))}:")
    emit("  match a:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit(f"      {cong('z', S('z'), add('p', S('b')), S(add('p', 'b')), 'add_succ_r(p, b)')}")
    emit()
    emit(f"def add_comm(+a: Nat, +b: Nat) -> {eq(add('a', 'b'), add('b', 'a'))}:")
    emit("  match a:")
    emit("    case 0n:")
    emit(f"      {sym(add('b', '0n'), 'b', 'add_zero_r(b)')}")
    emit("    case 1n+p:")
    t = [S(add("p", "b")), S(add("b", "p")), add("b", S("p"))]
    e = [cong("z", S("z"), add("p", "b"), add("b", "p"), "add_comm(p, b)"), sym(add("b", S("p")), S(add("b", "p")), "add_succ_r(b, p)")]
    emit(f"      {chain(t, e)}")
    emit()
    emit(f"def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {eq(add(add('a', 'b'), 'c'), add('a', add('b', 'c')))}:")
    emit("  match a:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit(f"      {cong('z', S('z'), add(add('p', 'b'), 'c'), add('p', add('b', 'c')), 'add_assoc(p, b, c)')}")
    emit()
    emit(f"def mul_add_l(+x: Nat, +y: Nat, +g: Nat) -> {eq(mul(add('x', 'y'), 'g'), add(mul('x', 'g'), mul('y', 'g')))}:")
    emit("  match x:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    t = [add("g", mul(add("p", "y"), "g")), add("g", add(mul("p", "g"), mul("y", "g"))), add(add("g", mul("p", "g")), mul("y", "g"))]
    e = [cong("z", add("g", "z"), mul(add("p", "y"), "g"), add(mul("p", "g"), mul("y", "g")), "mul_add_l(p, y, g)"),
         sym(t[2], t[1], f"add_assoc(g, {mul('p', 'g')}, {mul('y', 'g')})")]
    emit(f"      {chain(t, e)}")
    emit()
    emit(f"def mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {eq(mul(mul('a', 'b'), 'c'), mul('a', mul('b', 'c')))}:")
    emit("  match a:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    t = [mul(add("b", mul("p", "b")), "c"), add(mul("b", "c"), mul(mul("p", "b"), "c")), add(mul("b", "c"), mul("p", mul("b", "c")))]
    e = [f"mul_add_l(b, {mul('p', 'b')}, c)", cong("z", add(mul("b", "c"), "z"), mul(mul("p", "b"), "c"), mul("p", mul("b", "c")), "mul_assoc(p, b, c)")]
    emit(f"      {chain(t, e)}")
    emit()
    emit(f"def mul_one_l(+a: Nat) -> {eq(mul('1n', 'a'), 'a')}:")
    emit("  add_zero_r(a)")
    emit()
    emit("def npred(n: Nat) -> Nat:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      0n")
    emit("    case 1n+p:")
    emit("      p")
    emit()
    emit(f"def succ_inj(-x: Nat, -y: Nat, e: {eq(S('x'), S('y'))}) -> {eq('x', 'y')}:")
    emit(f"  {cong('z', 'npred(z)', S('x'), S('y'), 'e')}")
    emit()
    emit("def ndisc(n: Nat) -> Type:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      Empty")
    emit("    case 1n+p:")
    emit("      Unit")
    emit()
    emit(f"def succ_ne_zero(-x: Nat, e: {eq(S('x'), '0n')}) -> Empty:")
    emit("  %e : ndisc(_)")
    emit("  Unit{}")
    emit()
    emit(f"def add_eq_zero(+w: Nat, +b: Nat, e: {eq(add('w', 'b'), '0n')}) -> {eq('b', '0n')}:")
    emit("  match w:")
    emit("    case 0n:")
    emit("      e")
    emit("    case 1n+v:")
    emit(f"      Empty.absurd({eq('b', '0n')}, succ_ne_zero({add('v', 'b')}, e))")
    emit()


def divmod_lemmas():
    emit("# Base's Nat.divmod, for a divisor 1 + bp: q (1 + bp) + r = a and r <= bp")
    emit()
    b = S("bp")
    G = "Nat.divmod.go(n, m, d, r)"

    def spec(n, m, d, r):
        g = f"Nat.divmod.go({n}, {m}, {d}, {r})"
        q, rr = f"Pair.fst(Nat, Nat, {g})", f"Pair.snd(Nat, Nat, {g})"
        return f"{eq(add(mul(q, b), rr), add(n, add(mul(d, b), r)))} & {LE(rr, 'bp')}"

    def fix(name, n, args, ih_spec, target_n, target_r, eqn_terms, eqn_eqs):
        # from the inner spec, the outer: the same remainder bound, and the
        # sum rewritten by eqn (a chain from the inner right side to the outer)
        g = f"Nat.divmod.go({args})"
        q, rr = f"Pair.fst(Nat, Nat, {g})", f"Pair.snd(Nat, Nat, {g})"
        lhs = add(mul(q, b), rr)
        return lhs

    # m = 0: go(1+np, 0, d, r) = go(np, r, 1+d, 0), with r = bp
    gi = "Nat.divmod.go(np, r, 1n+d, 0n)"
    q, rr = f"Pair.fst(Nat, Nat, {gi})", f"Pair.snd(Nat, Nat, {gi})"
    M = mul("d", b)
    t = [add("np", add(mul(S("d"), b), "0n")), add("np", mul(S("d"), b)), S(add("np", add("bp", M))), S(add("np", add(M, "bp"))), S(add("np", add(M, "r")))]
    e = [cong("z", add("np", "z"), add(mul(S("d"), b), "0n"), mul(S("d"), b), f"add_zero_r({mul(S('d'), b)})"),
         f"add_succ_r(np, {add('bp', M)})",
         cong("z", S(add("np", "z")), add("bp", M), add(M, "bp"), f"add_comm(bp, {M})"),
         cong("z", S(add("np", add(M, "z"))), "bp", "r", sym("r", "bp", "inv"))]
    emit(f"def ds.m0(+np: Nat, +d: Nat, +r: Nat, +bp: Nat, +inv: {eq('r', 'bp')}, ih: {spec('np', 'r', S('d'), '0n')}) -> {spec(S('np'), '0n', 'd', 'r')}:")
    emit("  (e1, le) = ih")
    emit(f"  ({trans(add(mul(q, b), rr), t[0], t[-1], 'e1', chain(t, e))}, le)")
    emit()
    gi = "Nat.divmod.go(np, mp, d, 1n+r)"
    q, rr = f"Pair.fst(Nat, Nat, {gi})", f"Pair.snd(Nat, Nat, {gi})"
    t = [add("np", add(M, S("r"))), add("np", S(add(M, "r"))), S(add("np", add(M, "r")))]
    e = [cong("z", add("np", "z"), add(M, S("r")), S(add(M, "r")), f"add_succ_r({M}, r)"), f"add_succ_r(np, {add(M, 'r')})"]
    emit(f"def ds.m1(+np: Nat, +mp: Nat, +d: Nat, +r: Nat, +bp: Nat, ih: {spec('np', 'mp', 'd', S('r'))}) -> {spec(S('np'), S('mp'), 'd', 'r')}:")
    emit("  (e1, le) = ih")
    emit(f"  ({trans(add(mul(q, b), rr), t[0], t[-1], 'e1', chain(t, e))}, le)")
    emit()
    emit(f"def ds(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +inv: {eq(add('m', 'r'), 'bp')}) -> {spec('n', 'm', 'd', 'r')}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      ({==}, (m, inv))")
    emit("    case 1n+np:")
    emit("      match m:")
    emit("        case 0n:")
    emit(f"          ds.m0(np, d, r, bp, inv, ds(np, r, 1n+d, 0n, bp, {trans(add('r', '0n'), 'r', 'bp', 'add_zero_r(r)', 'inv')}))")
    emit("        case 1n+mp:")
    emit(f"          ds.m1(np, mp, d, r, bp, ds(np, mp, d, 1n+r, bp, {trans(add('mp', S('r')), S(add('mp', 'r')), 'bp', 'add_succ_r(mp, r)', 'inv')}))")
    emit()
    # divmod(a, 1 + q)
    D_, R_ = "Nat.div(a, 1n+q)", "Nat.mod(a, 1n+q)"
    emit(f"def dm.eq(+a: Nat, +q: Nat, p: {spec('a', 'q', '0n', '0n').replace('bp', 'q')}) -> {eq(add(mul(D_, S('q')), R_), 'a')}:")
    emit("  (e1, le) = p")
    emit(f"  {trans(add(mul(D_, S('q')), R_), add('a', '0n'), 'a', 'e1', 'add_zero_r(a)')}")
    emit()
    emit(f"def dm.le(+a: Nat, +q: Nat, p: {spec('a', 'q', '0n', '0n').replace('bp', 'q')}) -> {LE(R_, 'q')}:")
    emit("  (e1, le) = p")
    emit("  le")
    emit()
    emit(f"def dm_eq(+a: Nat, +q: Nat) -> {eq(add(mul(D_, S('q')), R_), 'a')}:")
    emit("  dm.eq(a, q, ds(a, q, 0n, 0n, q, add_zero_r(q)))")
    emit()
    emit(f"def dm_le(+a: Nat, +q: Nat) -> {LE(R_, 'q')}:")
    emit("  dm.le(a, q, ds(a, q, 0n, 0n, q, add_zero_r(q)))")
    emit()


def gcd_lemmas():
    emit("# gcd divides both, by induction on Euclid's fuel (kept at least b)")
    emit()
    g = lambda f, a, b: f"K.kmath.gcd.go({f}, {a}, {b})"
    R_ = "Nat.mod(a, 1n+q)"
    D_ = "Nat.div(a, 1n+q)"
    # the fuel bound for the next step
    emit(f"def gd.le(+a: Nat, +q: Nat, +k: Nat, h: {LE(S('q'), S('k'))}, m: {LE(R_, 'q')}) -> {LE(R_, 'k')}:")
    emit("  (+w, e) = h")
    emit("  (+mm, em) = m")
    ewq = f"succ_inj({add('w', 'q')}, k, {trans(S(add('w', 'q')), add('w', S('q')), S('k'), sym(add('w', S('q')), S(add('w', 'q')), 'add_succ_r(w, q)'), 'e')})"
    t = [add(add("w", "mm"), R_), add("w", add("mm", R_)), add("w", "q"), "k"]
    e = [f"add_assoc(w, mm, {R_})", cong("z", add("w", "z"), add("mm", R_), "q", "em"), ewq]
    emit(f"  ({add('w', 'mm')}, {chain(t, e)})")
    emit()
    G = g("k", "1n+q", R_)
    fin = []
    fin.append(f"def gd.fin(+a: Nat, +q: Nat, +k: Nat, l: {DV(S('q'), G)}, r: {DV(R_, G)}) -> {DV('a', G)} & {DV(S('q'), G)}:")
    fin.append("  (+k1, +e1) = l")
    fin.append("  (+k2, e2) = r")
    t = [mul(add(mul(D_, "k1"), "k2"), G), add(mul(mul(D_, "k1"), G), mul("k2", G)), add(mul(D_, mul("k1", G)), mul("k2", G)),
         add(mul(D_, S("q")), mul("k2", G)), add(mul(D_, S("q")), R_), "a"]
    e = [f"mul_add_l({mul(D_, 'k1')}, k2, {G})",
         cong("z", add("z", mul("k2", G)), mul(mul(D_, "k1"), G), mul(D_, mul("k1", G)), f"mul_assoc({D_}, k1, {G})"),
         cong("z", add(mul(D_, "z"), mul("k2", G)), mul("k1", G), S("q"), "e1"),
         cong("z", add(mul(D_, S("q")), "z"), mul("k2", G), R_, "e2"),
         "dm_eq(a, q)"]
    fin.append(f"  (({add(mul(D_, 'k1'), 'k2')}, {chain(t, e)}), (k1, e1))")
    for l in fin:
        emit(l)
    emit()
    emit(f"def gd.step(+a: Nat, +q: Nat, +k: Nat, ih: {DV(S('q'), G)} & {DV(R_, G)}) -> {DV('a', G)} & {DV(S('q'), G)}:")
    emit("  (l, r) = ih")
    emit("  gd.fin(a, q, k, l, r)")
    emit()
    Gt = g("fuel", "a", "b")
    emit(f"def gd(+fuel: Nat, +a: Nat, +b: Nat, h: {LE('b', 'fuel')}) -> {DV('a', Gt)} & {DV('b', Gt)}:")
    emit("  match fuel b:")
    emit("    case 0n _:")
    emit("      (+w, e) = h")
    emit(f"      ((1n, mul_one_l(a)), (0n, {sym('b', '0n', 'add_eq_zero(w, b, e)')}))")
    emit("    case 1n+k 0n:")
    emit("      ((1n, mul_one_l(a)), (0n, {==}))")
    emit("    case 1n+k 1n+q:")
    emit(f"      gd.step(a, q, k, gd(k, 1n+q, {R_}, gd.le(a, q, k, h, dm_le(a, q))))")
    emit()
    gab = "K.KMath.gcd(a, b)"
    emit(f"def gd.l(-x: Nat, -y: Nat, -g: Nat, p: {DV('x', 'g')} & {DV('y', 'g')}) -> {DV('x', 'g')}:")
    emit("  (l, r) = p")
    emit("  l")
    emit()
    emit(f"def gd.r(-x: Nat, -y: Nat, -g: Nat, p: {DV('x', 'g')} & {DV('y', 'g')}) -> {DV('y', 'g')}:")
    emit("  (l, r) = p")
    emit("  r")
    emit()
    emit("def Laws.gcd_divides_l(a, b):")
    emit(f"  gd.l(a, b, {gab}, gd(b, a, b, (0n, {{==}})))")
    emit()
    emit("def Laws.gcd_divides_r(a, b):")
    emit(f"  gd.r(a, b, {gab}, gd(b, a, b, (0n, {{==}})))")
    emit()


def isqrt_lemmas():
    emit("# isqrt: the invariant r^2 <= n < (r + 2^(b+1))^2 before bit b")
    emit()
    T = "True{}"
    emit("def bdisc(+b: Bool) -> Type:")
    emit("  match b:")
    emit("    case True{}:")
    emit("      Unit")
    emit("    case False{}:")
    emit("      Empty")
    emit()
    emit("def bt_absurd(+e: {True{} == False{} : Bool}) -> Empty:")
    emit("  %e : bdisc(_)")
    emit("  Unit{}")
    emit()
    emit(f"def le_zero_l(+n: Nat) -> {eq('Nat.is_le(0n, n)', T, 'Bool')}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit("      {==}")
    emit()
    goal = lambda x, y: eq(f"Nat.is_lt({y}, {x})", T, "Bool")
    emit(f"def not_le_lt(+x: Nat, +y: Nat, e: {eq('Nat.is_le(x, y)', 'False{}', 'Bool')}) -> {goal('x', 'y')}:")
    emit("  match x y:")
    emit("    case 0n 0n:")
    emit(f"      Empty.absurd({goal('0n', '0n')}, bt_absurd(e))")
    emit("    case 0n 1n+q:")
    emit(f"      Empty.absurd({goal('0n', '1n+q')}, bt_absurd(e))")
    emit("    case 1n+p 0n:")
    emit("      {==}")
    emit("    case 1n+p 1n+q:")
    emit("      not_le_lt(p, q, e)")
    emit()
    emit(f"def double_add(+p: Nat) -> {eq('Nat.double(p)', add('p', 'p'))}:")
    emit("  match p:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+q:")
    t = ["2n+Nat.double(q)", "2n+" + add("q", "q"), S(add("q", S("q")))]
    e = [cong("z", "2n+z", "Nat.double(q)", add("q", "q"), "double_add(q)"),
         cong("z", S("z"), S(add("q", "q")), add("q", S("q")), sym(add("q", S("q")), S(add("q", "q")), "add_succ_r(q, q)"))]
    emit(f"      {chain(t, e)}")
    emit()
    emit(f"def add_double(+r: Nat, +p: Nat) -> {eq(add(add('r', 'p'), 'p'), add('r', 'Nat.double(p)'))}:")
    t = [add(add("r", "p"), "p"), add("r", add("p", "p")), add("r", "Nat.double(p)")]
    e = ["add_assoc(r, p, p)", cong("z", add("r", "z"), add("p", "p"), "Nat.double(p)", sym("Nat.double(p)", add("p", "p"), "double_add(p)"))]
    emit(f"  {chain(t, e)}")
    emit()
    lt = lambda n, x: eq(f"Nat.is_lt({n}, {mul(x, x)})", T, "Bool")
    emit(f"def lt_tr(+n: Nat, -x: Nat, -y: Nat, e: {eq('x', 'y')}, h: {lt('n', 'y')}) -> {lt('n', 'x')}:")
    emit(f"  {trans(f'Nat.is_lt(n, {mul('x', 'x')})', f'Nat.is_lt(n, {mul('y', 'y')})', T, cong('+z', f'Nat.is_lt(n, {mul('z', 'z')})', 'x', 'y', 'e', 'Nat', 'Bool'), 'h', 'Bool')}")
    emit()
    p2 = lambda k: f"S.KMath.pow2({k})"

    def GOAL(R):
        return f"{eq(f'Nat.is_le({mul(R, R)}, n)', T, 'Bool')} & {eq(f'Nat.is_lt(n, {mul(add(R, chr(49) + chr(110)), add(R, chr(49) + chr(110)))})', T, 'Bool')}"

    def le(x):
        return eq(f"Nat.is_le({mul(x, x)}, n)", T, "Bool")
    c = add("r", p2("k"))
    R = f"S.isqrt.go(k, n, S.isqrt.pick(ok, r, {c}))"
    ps = (f"+k: Nat, +n: Nat, +r: Nat, +ok: Bool, e: {eq(f'Nat.is_le({mul(c, c)}, n)', 'ok', 'Bool')}, "
          f"h1: {le('r')}, h2: {lt('n', add('r', p2(S('k'))))}")
    emit(f"def isp({ps}) -> {GOAL(R)}:")
    emit("  match k:")
    emit("    case 0n:")
    emit("      match ok:")
    emit("        case True{}:")
    c0 = add("r", p2("0n"))
    emit(f"          (e, lt_tr(n, {add(c0, p2('0n'))}, {add('r', f'Nat.double({p2(chr(48) + chr(110))})')}, add_double(r, {p2('0n')}), h2))")
    emit("        case False{}:")
    emit(f"          (h1, not_le_lt({mul(c0, c0)}, n, e))")
    emit("    case 1n+j:")
    emit("      match ok:")
    emit("        case True{}:")
    c1 = add("r", p2("1n+j"))
    c2 = add(c1, p2("j"))
    h2p = f"lt_tr(n, {add(c1, p2('1n+j'))}, {add('r', f'Nat.double({p2(chr(49) + chr(110) + chr(43) + chr(106))})')}, add_double(r, {p2('1n+j')}), h2)"
    emit(f"          isp(j, n, {c1}, Nat.is_le({mul(c2, c2)}, n), {{==}}, e, {h2p})")
    emit("        case False{}:")
    c3 = add("r", p2("j"))
    emit(f"          isp(j, n, r, Nat.is_le({mul(c3, c3)}, n), {{==}}, h1, not_le_lt({mul(c1, c1)}, n, e))")
    emit()
    hb = eq(f"Nat.is_lt(n, {mul(p2('bits'), p2('bits'))})", T, "Bool")
    emit(f"def isq(+bits: Nat, +n: Nat, h: {hb}) -> {GOAL('S.KMath.isqrt_nat(bits, n)')}:")
    emit("  match bits:")
    emit("    case 0n:")
    emit("      (le_zero_l(n), h)")
    emit("    case 1n+k:")
    ck = add("0n", p2("k"))
    emit(f"      isp(k, n, 0n, Nat.is_le({mul(ck, ck)}, n), {{==}}, le_zero_l(n), h)")
    emit()
    Rr = "S.KMath.isqrt_nat(bits, n)"
    emit(f"def isq.fst(+bits: Nat, +n: Nat, p: {GOAL(Rr)}) -> {le(Rr)}:")
    emit("  (a, b) = p")
    emit("  a")
    emit()
    emit(f"def isq.snd(+bits: Nat, +n: Nat, p: {GOAL(Rr)}) -> {eq(f'Nat.is_lt(n, {mul(add(Rr, chr(49) + chr(110)), add(Rr, chr(49) + chr(110)))})', T, 'Bool')}:")
    emit("  (a, b) = p")
    emit("  b")
    emit()
    # every U32 is below 2^32 = 4^16
    emit("def bdisc2(+b: Bool) -> Type:")
    emit("  match b:")
    emit("    case True{}:")
    emit("      Empty")
    emit("    case False{}:")
    emit("      Unit")
    emit()
    emit(f"def ft_absurd(+e: {eq('False{}', T, 'Bool')}) -> Empty:")
    emit("  %e : bdisc2(_)")
    emit("  Unit{}")
    emit()
    for name, l1, l0 in (("dbl_lt1", "1n+Nat.double(x)", "1n+Nat.double(0n)"), ("dbl_lt0", "Nat.double(x)", "Nat.double(0n)")):
        g = lambda a, b, l1=l1: eq(f"Nat.is_lt({l1.replace('x', a)}, Nat.double({b}))", T, "Bool")
        emit(f"def {name}(+x: Nat, +y: Nat, h: {eq('Nat.is_lt(x, y)', T, 'Bool')}) -> {g('x', 'y')}:")
        emit("  match x y:")
        emit("    case 0n 0n:")
        emit(f"      Empty.absurd({g('0n', '0n')}, ft_absurd(h))")
        emit("    case 0n 1n+q:")
        emit("      {==}")
        emit("    case 1n+p 0n:")
        emit(f"      Empty.absurd({g('1n+p', '0n')}, ft_absurd(h))")
        emit("    case 1n+p 1n+q:")
        emit(f"      {name}(p, q, h)")
        emit()
    tl = lambda k, w: eq(f"Nat.is_lt(Word.to_nat({k}, {w}), {p2(k)})", T, "Bool")
    emit(f"def tn_lt(+k: Nat, +w: Word(k)) -> {tl('k', 'w')}:")
    emit("  match k:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit("      match w:")
    emit("        case WCon{+b, +t}:")
    emit("          match b:")
    emit("            case False{}:")
    emit(f"              dbl_lt0(Word.to_nat(p, t), {p2('p')}, tn_lt(p, t))")
    emit("            case True{}:")
    emit(f"              dbl_lt1(Word.to_nat(p, t), {p2('p')}, tn_lt(p, t))")
    emit()
    emit(f"def pow2_add(+a: Nat, +b: Nat) -> {eq(p2(add('a', 'b')), mul(p2('a'), p2('b')))}:")
    emit("  match a:")
    emit("    case 0n:")
    emit(f"      {sym(mul('1n', p2('b')), p2('b'), f'mul_one_l({p2(chr(98))})')}")
    emit("    case 1n+p:")
    P_, B_ = p2("p"), p2("b")
    t = [f"Nat.double({p2(add('p', 'b'))})", f"Nat.double({mul(P_, B_)})", add(mul(P_, B_), mul(P_, B_)), mul(add(P_, P_), B_), mul(f"Nat.double({P_})", B_)]
    e = [cong("z", "Nat.double(z)", p2(add("p", "b")), mul(P_, B_), "pow2_add(p, b)"),
         f"double_add({mul(P_, B_)})",
         sym(t[3], t[2], f"mul_add_l({P_}, {P_}, {B_})"),
         cong("z", mul("z", B_), add(P_, P_), f"Nat.double({P_})", sym(f"Nat.double({P_})", add(P_, P_), f"double_add({P_})"))]
    emit(f"      {chain(t, e)}")
    emit()
    p16 = p2("16n")
    emit(f"def u32_bound(+n: U32) -> {eq(f'Nat.is_lt(U32.to_nat(n), {mul(p16, p16)})', T, 'Bool')}:")
    emit("  match n:")
    emit("    case U32{+w}:")
    k32 = add("16n", "16n")
    N = f"Word.to_nat({k32}, w)"
    U = "U32.to_nat(U32{w})"
    M = mul(p16, p16)
    t = [f"Nat.is_lt({U}, {M})", f"Nat.is_lt({N}, {M})", f"Nat.is_lt({N}, {p2(k32)})", T]
    e = [cong("z", f"Nat.is_lt(z, {M})", U, N, "{==}", "Nat", "Bool"),
         cong("z", f"Nat.is_lt({N}, z)", M, p2(k32), sym(p2(k32), M, "pow2_add(16n, 16n)"), "Nat", "Bool"),
         f"tn_lt({k32}, w)"]
    emit(f"      {chain(t, e, 'Bool')}")
    emit()
    emit("def Laws.isqrt_u32_le(n):")
    emit("  isq.fst(16n, U32.to_nat(n), isq(16n, U32.to_nat(n), u32_bound(n)))")
    emit()
    emit("def Laws.isqrt_u32_lt(n):")
    emit("  isq.snd(16n, U32.to_nat(n), isq(16n, U32.to_nat(n), u32_bound(n)))")
    emit()
    emit("def Laws.isqrt_nat_le(bits, n, h):")
    emit("  isq.fst(bits, n, isq(bits, n, h))")
    emit()
    emit("def Laws.isqrt_nat_lt(bits, n, h):")
    emit("  isq.snd(bits, n, isq(bits, n, h))")
    emit()


VECTORS = ["v_gcd", "v_gcd_zero", "v_lcm", "v_pow", "v_pow32", "v_isqrt_nat", "v_div_u64_rem", "v_div64_u64_rem",
           "v_div_s64_rem", "v_div_round_up", "v_recip_1", "v_recip_3", "v_recip_7", "v_recip_pow2", "v_recip_max",
           "v_rational_pi", "v_rational_bound", "v_rational_exact", "v_cordic_0", "v_cordic_90", "v_is_prime", "v_next_prime"]


def main():
    emit("# Generated by gen/proof.py; do not edit by hand.")
    emit("import Base")
    emit("import ../word64/word64.bend as W")
    emit("import ./kmath.bend as K")
    emit("import ./isqrt.bend as S")
    emit("import ./div64.bend as D")
    emit("import ./reciprocal.bend as R")
    emit("import ./rational.bend as Q")
    emit("import ./cordic.bend as C")
    emit("import ./prime.bend as P")
    emit("import ./LAWS.bend as Laws")
    emit()
    nat_lemmas()
    divmod_lemmas()
    gcd_lemmas()
    isqrt_lemmas()
    emit("# vectors, by computation")
    for v in VECTORS:
        emit(f"def Laws.{v}():")
        emit("  {==}")
        emit()
    with open(OUT, "w", newline="\n") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
