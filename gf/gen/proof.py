#!/usr/bin/env python3
"""Writes gf/PROOF.bend: the proofs of gf's laws.

The GF(2^8) laws are proved for every reduction polynomial, on the bits of
the bytes (gf.bend's Gf8Bits), by these steps:

  1. Bool identities (xor commutes, associates, ...), by cases;
  2. the same for a byte's eight bits at once (rb_eq joins eight bit
     equalities into one), and multiplication by x is linear;
  3. a Horner step, and so the product, is linear in each factor;
  4. every byte is the sum of its bits times the basis 1, x, ..., x^7
     (dec, by cases on its eight bits), so a product is a sum of basis
     products, and x^i * b is b multiplied by x i times (me);
  5. commutativity on the basis is computation, and extends to every byte
     by linearity; associativity follows from (x * b) * c = x * (b * c),
     which follows from commutativity and linearity;
  6. the U32 laws follow through Gf8Bits.of (Gf8Bits.to (r)) = r.

The laws for the named fields (inverses, logarithms) and the vectors are
proved by computation, the inverses over all 255 nonzero bytes, split by
their bits into one case per byte.

Run: python3 gf/gen/proof.py   (from the repository root or anywhere)
"""
import itertools, os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "PROOF.bend")

R = "G.Gf8Bits"
Z = "G.Gf8Bits.zero()"


def rec(xs):
    return R + "{" + ", ".join(xs) + "}"


def bits(p):
    return [f"{p}{i}" for i in range(8)]


def xor(a, b):
    return f"G.Gf8Bits.xor({a}, {b})"


def sel(t, a):
    return f"G.Gf8Bits.sel({t}, {a})"


def X(a, p="p"):
    return f"G.Gf8Bits.x({a}, {p})"


def step(t, acc, b, p="p"):
    return f"G.Gf8Bits.step({t}, {acc}, {b}, {p})"


def hor(ts, acc, b, p="p"):
    return f"G.Gf8Bits.horner({ts}, {acc}, {b}, {p})"


def mul(a, b, p="p"):
    return f"G.Gf8Bits.mul({a}, {b}, {p})"


def eq(a, b, t=R):
    return "{" + f"{a} == {b} : {t}" + "}"


def bxor(a, b):
    return f"Bool.xor({a}, {b})"


def band(a, b):
    return f"Bool.and({a}, {b})"


def sym(t, a, b, e):
    """e : {a == b : t}  gives  {b == a : t}"""
    return f"Equal.sym({t}, {a}, {b}, {e})"


def trans(t, a, b, c, ab, bc):
    return f"Equal.trans({t}, {a}, {b}, {c}, {ab}, {bc})"


out = []


def emit(s=""):
    out.append(s)


def cases(vs, leaf, depth=1):
    """nested matches on the Bool variables vs, leaf(assign) at each leaf"""
    lines = []

    def go(i, env, ind):
        if i == len(vs):
            lines.append("  " * ind + leaf(env))
            return
        lines.append("  " * ind + f"match {vs[i]}:")
        for val in ("True", "False"):
            lines.append("  " * (ind + 1) + f"case {val}{{}}:")
            go(i + 1, {**env, vs[i]: val}, ind + 2)

    go(0, {}, depth)
    return "\n".join(lines)


# 1. Bool identities, by cases

BOOL = [
    ("bx_comm", ["a", "b"], bxor("a", "b"), bxor("b", "a")),
    ("bx_assoc", ["a", "b", "c"], bxor(bxor("a", "b"), "c"), bxor("a", bxor("b", "c"))),
    ("bx_zr", ["a"], bxor("a", "False{}"), "a"),
    ("bx_self", ["a"], bxor("a", "a"), "False{}"),
    ("bx_swap", ["a", "b", "c", "d"], bxor(bxor("a", "b"), bxor("c", "d")), bxor(bxor("a", "c"), bxor("b", "d"))),
    ("band_xor", ["a", "b", "q"], band(bxor("a", "b"), "q"), bxor(band("a", "q"), band("b", "q"))),
    ("blin", ["a", "b", "u", "v", "q"], bxor(bxor("a", "b"), band(bxor("u", "v"), "q")), bxor(bxor("a", band("u", "q")), bxor("b", band("v", "q")))),
]


def gen_bool():
    emit("# 1. Bool identities, by cases")
    emit()
    for name, vs, l, r in BOOL:
        ps = ", ".join(f"+{v}: Bool" for v in vs)
        emit(f"def {name}({ps}) -> {eq(l, r, 'Bool')}:")
        emit(cases(vs, lambda env: "{==}"))
        emit()


# 2. bytes as eight bits

def gen_bytes():
    emit("# 2. A byte's eight bits at once")
    emit()
    a, c = bits("a"), bits("c")
    ps = ", ".join([f"-{x}: Bool" for x in a + c] + [f"e{i}: {eq(a[i], c[i], 'Bool')}" for i in range(8)])
    emit(f"def rb_eq({ps}) -> {eq(rec(a), rec(c))}:")
    for i in range(8):
        cur = a[:i] + ["_"] + c[i + 1:]
        emit(f"  %e{i} : {eq(rec(a), rec(cur))}")
    emit("  {==}")
    emit()

    def lift(name, vs, l, r, lemma):
        """a record identity from the Bool identity `lemma`, bit by bit"""
        ps = ", ".join(f"+{v}: {R}" for v in vs)
        emit(f"def {name}({ps}) -> {eq(l, r)}:")
        emit(f"  match {' '.join(vs)}:")
        emit("    case " + " ".join(rec([f"+{v}{i}" for i in range(8)]) for v in vs) + ":")
        ls, rs, es = [], [], []
        for i in range(8):
            li, ri, ei = lemma(i)
            ls.append(li), rs.append(ri), es.append(ei)
        emit(f"      rb_eq({', '.join(ls + rs + es)})")
        emit()

    lift("rx_comm", ["a", "b"], xor("a", "b"), xor("b", "a"),
         lambda i: (bxor(f"a{i}", f"b{i}"), bxor(f"b{i}", f"a{i}"), f"bx_comm(a{i}, b{i})"))
    lift("rx_assoc", ["a", "b", "c"], xor(xor("a", "b"), "c"), xor("a", xor("b", "c")),
         lambda i: (bxor(bxor(f"a{i}", f"b{i}"), f"c{i}"), bxor(f"a{i}", bxor(f"b{i}", f"c{i}")), f"bx_assoc(a{i}, b{i}, c{i})"))
    lift("rx_zr", ["a"], xor("a", Z), "a",
         lambda i: (bxor(f"a{i}", "False{}"), f"a{i}", f"bx_zr(a{i})"))
    lift("rx_self", ["a"], xor("a", "a"), Z,
         lambda i: (bxor(f"a{i}", f"a{i}"), "False{}", f"bx_self(a{i})"))
    lift("rx_swap", ["a", "b", "c", "d"], xor(xor("a", "b"), xor("c", "d")), xor(xor("a", "c"), xor("b", "d")),
         lambda i: (bxor(bxor(f"a{i}", f"b{i}"), bxor(f"c{i}", f"d{i}")), bxor(bxor(f"a{i}", f"c{i}"), bxor(f"b{i}", f"d{i}")),
                    f"bx_swap(a{i}, b{i}, c{i}, d{i})"))

    # zero on the left computes
    emit(f"def rx_zl(+a: {R}) -> {eq(xor(Z, 'a'), 'a')}:")
    emit("  match a:")
    emit("    case " + rec(bits("a")) + ":")
    emit("      {==}")
    emit()

    # multiplication by x is linear
    def xl(i):
        if i == 0:
            return (band(bxor("u7", "v7"), "p0"), bxor(band("u7", "p0"), band("v7", "p0")), "band_xor(u7, v7, p0)")
        return (bxor(bxor(f"u{i-1}", f"v{i-1}"), band(bxor("u7", "v7"), f"p{i}")),
                bxor(bxor(f"u{i-1}", band("u7", f"p{i}")), bxor(f"v{i-1}", band("v7", f"p{i}"))),
                f"blin(u{i-1}, v{i-1}, u7, v7, p{i})")
    lift("x_lin", ["u", "v", "p"], X(xor("u", "v")), xor(X("u"), X("v")), xl)

    emit(f"def x_zero(+p: {R}) -> {eq(X(Z), Z)}:")
    emit("  match p:")
    emit("    case " + rec(bits("p")) + ":")
    emit("      {==}")
    emit()


def chain(t, terms, eqs):
    """terms[0] == terms[-1] from eqs[i] : {terms[i] == terms[i+1]}"""
    if len(eqs) == 1:
        return eqs[0]
    return trans(t, terms[0], terms[1], terms[-1], eqs[0], chain(t, terms[1:], eqs[1:]))


def cong(a_t, b_t, var, body, a, b, e):
    return f"Equal.cong({a_t}, {b_t}, {var} => {body}, {a}, {b}, {e})"


LR = "List<&2, G.Gf8Bits>"
LB = "List<&2, Bool>"


def E(k):
    return rec(["True{}" if i == k else "False{}" for i in range(8)])


def gen_lin():
    emit("# 3. Selection, and a Horner step, are linear; so the product is linear in")
    emit("# each factor")
    emit()
    emit(f"def sel_xor(+t: Bool, +u: {R}, +v: {R}) -> {eq(sel('t', xor('u', 'v')), xor(sel('t', 'u'), sel('t', 'v')))}:")
    emit(cases(["t"], lambda env: "{==}"))
    emit()
    emit(f"def sel_txor(+s: Bool, +t: Bool, +b: {R}) -> {eq(sel(bxor('s', 't'), 'b'), xor(sel('s', 'b'), sel('t', 'b')))}:")
    emit("  match s t:")
    emit("    case True{} True{}:")
    emit(f"      {sym(R, xor('b', 'b'), Z, 'rx_self(b)')}")
    emit("    case True{} False{}:")
    emit(f"      {sym(R, xor('b', Z), 'b', 'rx_zr(b)')}")
    emit("    case False{} True{}:")
    emit(f"      {sym(R, xor(Z, 'b'), 'b', 'rx_zl(b)')}")
    emit("    case False{} False{}:")
    emit("      {==}")
    emit()
    emit(f"def x_sel(+t: Bool, +u: {R}, +p: {R}) -> {eq(X(sel('t', 'u')), sel('t', X('u')))}:")
    emit("  match t:")
    emit("    case True{}:")
    emit("      {==}")
    emit("    case False{}:")
    emit("      x_zero(p)")
    emit()

    # step linear in the multiplicand (and the accumulator)
    lhs = step("t", xor("A", "C"), xor("u", "v"))
    rhs = xor(step("t", "A", "u"), step("t", "C", "v"))
    xA, xC, sA, sC = X("A"), X("C"), sel("t", "u"), sel("t", "v")
    emit(f"def step_lin_b(+t: Bool, +A: {R}, +C: {R}, +u: {R}, +v: {R}, +p: {R}) -> {eq(lhs, rhs)}:")
    emit(f"  %rx_swap({xA}, {xC}, {sA}, {sC}) : {eq(lhs, '_')}")
    emit(f"  %x_lin(A, C, p) : {eq(lhs, xor('_', xor(sA, sC)))}")
    emit(f"  %sel_xor(t, u, v) : {eq(lhs, xor(X(xor('A', 'C')), '_'))}")
    emit("  {==}")
    emit()
    lhs = hor("ts", xor("A", "C"), xor("u", "v"))
    rhs = xor(hor("ts", "A", "u"), hor("ts", "C", "v"))
    emit(f"def horner_lin_b(ts: {LB}, +A: {R}, +C: {R}, +u: {R}, +v: {R}, +p: {R}) -> {eq(lhs, rhs)}:")
    emit("  match ts:")
    emit("    case Nil{}:")
    emit("      {==}")
    emit("    case Con{+t, rest}:")
    s0 = step("t", xor("A", "C"), xor("u", "v"))
    s1 = xor(step("t", "A", "u"), step("t", "C", "v"))
    emit(f"      %{sym(R, s0, s1, 'step_lin_b(t, A, C, u, v, p)')} : {eq(hor('rest', '_', xor('u', 'v')), xor(hor('rest', step('t', 'A', 'u'), 'u'), hor('rest', step('t', 'C', 'v'), 'v')))}")
    emit(f"      horner_lin_b(rest, {step('t', 'A', 'u')}, {step('t', 'C', 'v')}, u, v, p)")
    emit()
    emit(f"def m_lin_r(+a: {R}, +u: {R}, +v: {R}, +p: {R}) -> {eq(mul('a', xor('u', 'v')), xor(mul('a', 'u'), mul('a', 'v')))}:")
    emit(f"  horner_lin_b(G.Gf8Bits.top(a), {Z}, {Z}, u, v, p)")
    emit()

    # left: the bits of s xor t, paired
    emit("# pairs of bits, for the product's linearity in its first factor")
    emit("type GfPb is Data:")
    emit("  GfPb{s: Bool, t: Bool}")
    emit()
    for name, body in (("pl.x", "Bool.xor(s, t)"), ("pl.l", "s"), ("pl.r", "t")):
        emit(f"def {name}(ps: List<&2, GfPb>) -> {LB}:")
        emit("  match ps:")
        emit("    case Nil{}:")
        emit("      Nil{}")
        emit("    case Con{h, rest}:")
        emit("      match h:")
        emit("        case GfPb{s, t}:")
        emit(f"          Con{{{body}, {name}(rest)}}")
        emit()
    lhs = step(bxor("s", "t"), xor("A", "C"), "b")
    rhs = xor(step("s", "A", "b"), step("t", "C", "b"))
    sA, sC = sel("s", "b"), sel("t", "b")
    emit(f"def step_lin_a(+s: Bool, +t: Bool, +A: {R}, +C: {R}, +b: {R}, +p: {R}) -> {eq(lhs, rhs)}:")
    emit(f"  %rx_swap({X('A')}, {X('C')}, {sA}, {sC}) : {eq(lhs, '_')}")
    emit(f"  %x_lin(A, C, p) : {eq(lhs, xor('_', xor(sA, sC)))}")
    emit(f"  %sel_txor(s, t, b) : {eq(lhs, xor(X(xor('A', 'C')), '_'))}")
    emit("  {==}")
    emit()
    lhs = hor("pl.x(ps)", xor("A", "C"), "b")
    rhs = xor(hor("pl.l(ps)", "A", "b"), hor("pl.r(ps)", "C", "b"))
    emit(f"def horner_lin_a(ps: List<&2, GfPb>, +A: {R}, +C: {R}, +b: {R}, +p: {R}) -> {eq(lhs, rhs)}:")
    emit("  match ps:")
    emit("    case Nil{}:")
    emit("      {==}")
    emit("    case Con{h, rest}:")
    emit("      match h:")
    emit("        case GfPb{+s, +t}:")
    s0 = step(bxor("s", "t"), xor("A", "C"), "b")
    s1 = xor(step("s", "A", "b"), step("t", "C", "b"))
    emit(f"          %{sym(R, s0, s1, 'step_lin_a(s, t, A, C, b, p)')} : {eq(hor('pl.x(rest)', '_', 'b'), xor(hor('pl.l(rest)', step('s', 'A', 'b'), 'b'), hor('pl.r(rest)', step('t', 'C', 'b'), 'b')))}")
    emit(f"          horner_lin_a(rest, {step('s', 'A', 'b')}, {step('t', 'C', 'b')}, b, p)")
    emit()
    pairs = "[" + ", ".join(f"GfPb{{s{i}, t{i}}}" for i in range(7, -1, -1)) + "]"
    emit(f"def m_lin_l(+s: {R}, +t: {R}, +b: {R}, +p: {R}) -> {eq(mul(xor('s', 't'), 'b'), xor(mul('s', 'b'), mul('t', 'b')))}:")
    emit("  match s t:")
    emit("    case " + rec([f"+s{i}" for i in range(8)]) + " " + rec([f"+t{i}" for i in range(8)]) + ":")
    emit(f"      horner_lin_a({pairs}, {Z}, {Z}, b, p)")
    emit()

    # zero
    emit(f"def step_zero(+t: Bool, +p: {R}) -> {eq(step('t', Z, Z), Z)}:")
    emit("  match t p:")
    for v in ("True", "False"):
        emit(f"    case {v}{{}} " + rec(bits("p")) + ":")
        emit("      {==}")
    emit()
    emit(f"def horner_zero(ts: {LB}, +p: {R}) -> {eq(hor('ts', Z, Z), Z)}:")
    emit("  match ts:")
    emit("    case Nil{}:")
    emit("      {==}")
    emit("    case Con{+t, rest}:")
    emit(f"      %{sym(R, step('t', Z, Z), Z, 'step_zero(t, p)')} : {eq(hor('rest', '_', Z), Z)}")
    emit("      horner_zero(rest, p)")
    emit()
    emit(f"def m_zero_r(+a: {R}, +p: {R}) -> {eq(mul('a', Z), Z)}:")
    emit("  horner_zero(G.Gf8Bits.top(a), p)")
    emit()
    emit(f"def m_zero_l(+b: {R}, +p: {R}) -> {eq(mul(Z, 'b'), Z)}:")
    emit("  match p:")
    emit("    case " + rec(bits("p")) + ":")
    emit("      {==}")
    emit()
    emit(f"def m_sel_l(+t: Bool, +a: {R}, +b: {R}, +p: {R}) -> {eq(mul(sel('t', 'a'), 'b'), sel('t', mul('a', 'b')))}:")
    emit("  match t:")
    emit("    case True{}:")
    emit("      {==}")
    emit("    case False{}:")
    emit("      m_zero_l(b, p)")
    emit()
    emit(f"def m_sel_r(+t: Bool, +a: {R}, +b: {R}, +p: {R}) -> {eq(mul('a', sel('t', 'b')), sel('t', mul('a', 'b')))}:")
    emit("  match t:")
    emit("    case True{}:")
    emit("      {==}")
    emit("    case False{}:")
    emit("      m_zero_r(a, p)")
    emit()


def ss(ts, vs):
    return f"ss({ts}, {vs})"


def gen_basis():
    emit("# 4. Sums over the basis 1, x, ..., x^7")
    emit()
    emit("# the sum of t_i * v_i")
    emit(f"def ss(ts: {LB}, vs: {LR}) -> {R}:")
    emit("  match ts:")
    emit("    case Nil{}:")
    emit(f"      {Z}")
    emit("    case Con{t, tr}:")
    emit("      match vs:")
    emit("        case Nil{}:")
    emit(f"          {Z}")
    emit("        case Con{v, vr}:")
    emit(f"          {xor(sel('t', 'v'), 'ss(tr, vr)')}")
    emit()
    for name, body, extra in (("ml", mul("v", "b"), "+b"), ("mr", mul("b", "v"), "+b"), ("xl", X("v"), None)):
        ps = f"vs: {LR}" + (f", {extra}: {R}" if extra else "") + f", +p: {R}"
        rec_args = "vr" + (", b" if extra else "") + ", p"
        emit(f"def {name}({ps}) -> {LR}:")
        emit("  match vs:")
        emit("    case Nil{}:")
        emit("      Nil{}")
        emit("    case Con{+v, +vr}:")
        emit(f"      Con{{{body}, {name}({rec_args})}}")
        emit()
    emit(f"def basis() -> {LR}:")
    emit("  [" + ", ".join(E(k) for k in range(8)) + "]")
    emit()
    emit(f"def bl(a: {R}) -> {LB}:")
    emit("  match a:")
    emit("    case " + rec(bits("b")) + ":")
    emit("      [" + ", ".join(bits("b")) + "]")
    emit()
    emit(f"def xk(n: Nat, b: {R}, +p: {R}) -> {R}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      b")
    emit("    case 1n+k:")
    emit(f"      xk(k, {X('b')}, p)")
    emit()
    emit(f"def xs(+b: {R}, +p: {R}) -> {LR}:")
    emit("  [" + ", ".join(f"xk({k}n, b, p)" for k in range(8)) + "]")
    emit()
    emit(f"def fs(n: Nat) -> {LB}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      Nil{}")
    emit("    case 1n+k:")
    emit("      Con{False{}, fs(k)}")
    emit()

    # linearity over sums
    for name, mk, zero_l, sel_l, lin in (
            ("lin_l", lambda s: mul(s, "b"), "m_zero_l(b, p)", "m_sel_l(t, v, b, p)", "m_lin_l"),
            ("lin_r", lambda s: mul("b", s), "m_zero_r(b, p)", "m_sel_r(t, b, v, p)", "m_lin_r")):
        lst = "ml" if name == "lin_l" else "mr"
        lhs = mk(ss("ts", "vs"))
        rhs = ss("ts", f"{lst}(vs, b, p)")
        emit(f"def {name}(ts: {LB}, vs: {LR}, +b: {R}, +p: {R}) -> {eq(lhs, rhs)}:")
        emit("  match ts:")
        emit("    case Nil{}:")
        emit(f"      {zero_l}")
        emit("    case Con{+t, +tr}:")
        emit("      match vs:")
        emit("        case Nil{}:")
        emit(f"          {zero_l}")
        emit("        case Con{+v, +vr}:")
        cur = mk(xor(sel("t", "v"), ss("tr", "vr")))
        emit(f"          %{name}(tr, vr, b, p) : {eq(cur, xor(sel('t', mk('v')), '_'))}")
        emit(f"          %{sel_l} : {eq(cur, xor('_', mk(ss('tr', 'vr'))))}")
        if name == "lin_l":
            emit(f"          m_lin_l({sel('t', 'v')}, {ss('tr', 'vr')}, b, p)")
        else:
            emit(f"          m_lin_r(b, {sel('t', 'v')}, {ss('tr', 'vr')}, p)")
        emit()
    lhs = X(ss("ts", "vs"))
    emit(f"def lin_x(ts: {LB}, vs: {LR}, +p: {R}) -> {eq(lhs, ss('ts', 'xl(vs, p)'))}:")
    emit("  match ts:")
    emit("    case Nil{}:")
    emit("      x_zero(p)")
    emit("    case Con{+t, +tr}:")
    emit("      match vs:")
    emit("        case Nil{}:")
    emit("          x_zero(p)")
    emit("        case Con{+v, +vr}:")
    cur = X(xor(sel("t", "v"), ss("tr", "vr")))
    emit(f"          %lin_x(tr, vr, p) : {eq(cur, xor(sel('t', X('v')), '_'))}")
    emit(f"          %x_sel(t, v, p) : {eq(cur, xor('_', X(ss('tr', 'vr'))))}")
    emit(f"          x_lin({sel('t', 'v')}, {ss('tr', 'vr')}, p)")
    emit()

    # every byte is its bits times the basis: by cases
    emit("# every byte is the sum of its bits times the basis (by cases)")
    emit(f"def dec(+a: {R}) -> {eq(ss('bl(a)', 'basis()'), 'a')}:")
    emit("  match a:")
    emit("    case " + rec(bits("b")) + ":")
    emit(cases(bits("b"), lambda env: "{==}", depth=3))
    emit()

    # x^k * b: Horner over k zero bits multiplies by x k times
    emit(f"def hf(n: Nat, +acc: {R}, +b: {R}, +p: {R}) -> {eq(hor('fs(n)', 'acc', 'b'), 'xk(n, acc, p)')}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+k:")
    emit(f"      %{sym(R, xor(X('acc'), Z), X('acc'), 'rx_zr(' + X('acc') + ')')} : {eq(hor('fs(k)', '_', 'b'), 'xk(k, ' + X('acc') + ', p)')}")
    emit(f"      hf(k, {X('acc')}, b, p)")
    emit()
    B_, P_ = rec(bits("b")), rec(bits("p"))
    for k in range(8):
        emit(f"def me{k}(+b: {R}, +p: {R}) -> {eq(mul(E(k), 'b'), f'xk({k}n, b, p)')}:")
        emit("  match b p:")
        emit(f"    case {B_} {P_}:")
        emit(f"      hf({k}n, {B_}, {B_}, {P_})")
        emit()


def gen_ring():
    emit("# 5. Commutativity and associativity")
    emit()
    SA = ss("bl(a)", "basis()")
    # comm on a basis element: computation once p is split
    for k in range(8):
        Sb = ss("bl(b)", "basis()")
        emit(f"def comm_e{k}(+b: {R}, +p: {R}) -> {eq(mul(E(k), 'b'), mul('b', E(k)))}:")
        emit("  match p:")
        emit(f"    case {rec([f'+p{i}' for i in range(8)])}:")
        P_ = rec(bits("p"))
        emit(f"      %dec(b) : {eq(mul(E(k), '_', P_), mul('b', E(k), P_))}")
        emit(f"      %dec(b) : {eq(mul(E(k), Sb, P_), mul('_', E(k), P_))}")
        t0, t1, t2 = mul(E(k), Sb, P_), ss("bl(b)", f"mr(basis(), {E(k)}, {P_})"), mul(Sb, E(k), P_)
        e01 = f"lin_r(bl(b), basis(), {E(k)}, {P_})"
        e12 = sym(R, t2, ss("bl(b)", f"ml(basis(), {E(k)}, {P_})"), f"lin_l(bl(b), basis(), {E(k)}, {P_})")
        emit(f"      {trans(R, t0, t1, t2, e01, e12)}")
        emit()
    # ml(basis, b) == mr(basis, b)
    emit(f"def mlr(+b: {R}, +p: {R}) -> {eq('ml(basis(), b, p)', 'mr(basis(), b, p)', LR)}:")
    for k in range(8):
        cur = "[" + ", ".join([mul(E(i), "b") for i in range(k)] + ["_"] + [mul("b", E(i)) for i in range(k + 1, 8)]) + "]"
        emit(f"  %comm_e{k}(b, p) : {eq('ml(basis(), b, p)', cur, LR)}")
    emit("  {==}")
    emit()
    emit(f"def comm(+a: {R}, +b: {R}, +p: {R}) -> {eq(mul('a', 'b'), mul('b', 'a'))}:")
    emit(f"  %dec(a) : {eq(mul('_', 'b'), mul('b', 'a'))}")
    emit(f"  %dec(a) : {eq(mul(SA, 'b'), mul('b', '_'))}")
    t = [mul(SA, "b"), ss("bl(a)", "ml(basis(), b, p)"), ss("bl(a)", "mr(basis(), b, p)"), mul("b", SA)]
    e = ["lin_l(bl(a), basis(), b, p)",
         cong(LR, R, "l", ss("bl(a)", "l"), "ml(basis(), b, p)", "mr(basis(), b, p)", "mlr(b, p)"),
         sym(R, t[3], t[2], "lin_r(bl(a), basis(), b, p)")]
    emit(f"  {chain(R, t, e)}")
    emit()
    # ml(basis, b) == xs(b)
    emit(f"def ml_x(+b: {R}, +p: {R}) -> {eq('ml(basis(), b, p)', 'xs(b, p)', LR)}:")
    for k in range(8):
        cur = "[" + ", ".join([mul(E(i), "b") for i in range(k)] + ["_"] + [f"xk({i}n, b, p)" for i in range(k + 1, 8)]) + "]"
        emit(f"  %me{k}(b, p) : {eq('ml(basis(), b, p)', cur, LR)}")
    emit("  {==}")
    emit()
    # (x b) c = x (b c)
    xb = X("b")
    Sc = ss("bl(c)", "basis()")
    emit(f"def ax(+b: {R}, +c: {R}, +p: {R}) -> {eq(mul(xb, 'c'), X(mul('b', 'c')))}:")
    tl = [mul(xb, "c"), mul("c", xb), mul(Sc, xb), ss("bl(c)", f"ml(basis(), {xb}, p)"), ss("bl(c)", f"xs({xb}, p)")]
    el = [f"comm({xb}, c, p)",
          cong(R, R, "z", mul("z", xb), "c", Sc, sym(R, Sc, "c", "dec(c)")),
          f"lin_l(bl(c), basis(), {xb}, p)",
          cong(LR, R, "l", ss("bl(c)", "l"), f"ml(basis(), {xb}, p)", f"xs({xb}, p)", f"ml_x({xb}, p)")]
    tr = [X(mul("b", "c")), X(mul("c", "b")), X(mul(Sc, "b")), X(ss("bl(c)", "ml(basis(), b, p)")), X(ss("bl(c)", "xs(b, p)")), ss("bl(c)", "xl(xs(b, p), p)")]
    er = [cong(R, R, "z", X("z"), mul("b", "c"), mul("c", "b"), "comm(b, c, p)"),
          cong(R, R, "z", X(mul("z", "b")), "c", Sc, sym(R, Sc, "c", "dec(c)")),
          cong(R, R, "z", X("z"), mul(Sc, "b"), ss("bl(c)", "ml(basis(), b, p)"), "lin_l(bl(c), basis(), b, p)"),
          cong(LR, R, "l", X(ss("bl(c)", "l")), "ml(basis(), b, p)", "xs(b, p)", "ml_x(b, p)"),
          "lin_x(bl(c), xs(b, p), p)"]
    emit(f"  {trans(R, tl[0], tl[-1], tr[0], chain(R, tl, el), sym(R, tr[0], tr[-1], chain(R, tr, er)))}")
    emit()
    # (x^n b) c = x^n (b c)
    emit(f"def ak(n: Nat, +b: {R}, +c: {R}, +p: {R}) -> {eq(mul('xk(n, b, p)', 'c'), 'xk(n, ' + mul('b', 'c') + ', p)')}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+k:")
    t = [mul(f"xk(k, {xb}, p)", "c"), f"xk(k, {mul(xb, 'c')}, p)", f"xk(k, {X(mul('b', 'c'))}, p)"]
    e = [f"ak(k, {xb}, c, p)", cong(R, R, "z", "xk(k, z, p)", mul(xb, "c"), X(mul("b", "c")), "ax(b, c, p)")]
    emit(f"      {chain(R, t, e)}")
    emit()
    emit(f"def mlx_c(+b: {R}, +c: {R}, +p: {R}) -> {eq('ml(xs(b, p), c, p)', 'xs(' + mul('b', 'c') + ', p)', LR)}:")
    bc = mul("b", "c")
    for k in range(8):
        cur = "[" + ", ".join([mul(f"xk({i}n, b, p)", "c") for i in range(k)] + ["_"] + [f"xk({i}n, {bc}, p)" for i in range(k + 1, 8)]) + "]"
        emit(f"  %ak({k}n, b, c, p) : {eq('ml(xs(b, p), c, p)', cur, LR)}")
    emit("  {==}")
    emit()
    emit(f"def assoc(+a: {R}, +b: {R}, +c: {R}, +p: {R}) -> {eq(mul(mul('a', 'b'), 'c'), mul('a', mul('b', 'c')))}:")
    emit(f"  %dec(a) : {eq(mul(mul('_', 'b'), 'c'), mul('a', bc))}")
    emit(f"  %dec(a) : {eq(mul(mul(SA, 'b'), 'c'), mul('_', bc))}")
    tl = [mul(mul(SA, "b"), "c"), mul(ss("bl(a)", "ml(basis(), b, p)"), "c"), mul(ss("bl(a)", "xs(b, p)"), "c"),
          ss("bl(a)", "ml(xs(b, p), c, p)"), ss("bl(a)", f"xs({bc}, p)")]
    el = [cong(R, R, "z", mul("z", "c"), mul(SA, "b"), ss("bl(a)", "ml(basis(), b, p)"), "lin_l(bl(a), basis(), b, p)"),
          cong(LR, R, "l", mul(ss("bl(a)", "l"), "c"), "ml(basis(), b, p)", "xs(b, p)", "ml_x(b, p)"),
          "lin_l(bl(a), xs(b, p), c, p)",
          cong(LR, R, "l", ss("bl(a)", "l"), "ml(xs(b, p), c, p)", f"xs({bc}, p)", "mlx_c(b, c, p)")]
    tr = [mul(SA, bc), ss("bl(a)", f"ml(basis(), {bc}, p)"), ss("bl(a)", f"xs({bc}, p)")]
    er = [f"lin_l(bl(a), basis(), {bc}, p)",
          cong(LR, R, "l", ss("bl(a)", "l"), f"ml(basis(), {bc}, p)", f"xs({bc}, p)", f"ml_x({bc}, p)")]
    emit(f"  {trans(R, tl[0], tl[-1], tr[0], chain(R, tl, el), sym(R, tr[0], tr[-1], chain(R, tr, er)))}")
    emit()


def of(a):
    return f"G.Gf8Bits.of({a})"


def to(r):
    return f"G.Gf8Bits.to({r})"


def u32_bits(prefix, n, rest="r"):
    """U32{WCon{b0, ... WCon{b(n-1), rest}...}}"""
    s = rest
    for i in range(n - 1, -1, -1):
        s = f"WCon{{{prefix[i]}, {s}}}"
    return "U32{" + s + "}"


VECTORS128 = ["v_gcm_x1", "v_gcm_ghash", "v_cmac_k1", "v_cmac_k2", "v_gcm_mul_x", "v_gcm_mul_x_value", "v_be_mul_x",
              "v_be_mul", "v_xts_wrap", "v_xts_double", "v_gf128_octets", "v_gf128_short"]
VECTORSM = ["v_bch13_x13", "v_bch13_order", "v_bch13_mul", "v_bch13_inv", "v_bch13_log", "v_bch14_mul"]

VECTORS = ["v_aes_mul", "v_aes_mul13", "v_aes_xtime", "v_aes_inv", "v_rs_x8", "v_rs_order", "v_div",
           "v_tab_mul_aes", "v_tab_inv_aes", "v_tab_mul_rs", "v_tab_zero"]


def gen_laws():
    emit("# 6. The laws, on U32, through Gf8Bits.of (Gf8Bits.to (r)) = r")
    emit()
    emit(f"def ot(+r: {R}) -> {eq(of(to('r')), 'r')}:")
    emit("  match r:")
    emit("    case " + rec(bits("b")) + ":")
    emit("      {==}")
    emit()
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
    A, B_, C, P = of("a"), of("b"), of("c"), of("poly")

    def otsym(r):
        return sym(R, of(to(r)), r, f"ot({r})")

    def to_cong(x, y, e):
        return cong(R, "U32", "r", to("r"), x, y, e)

    F = "G.Gf8Field{+poly, gen}"
    emit("def Laws.mul_comm(f, a, b):")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      {to_cong(mul(A, B_, P), mul(B_, A, P), f'comm({A}, {B_}, {P})')}")
    emit()
    M, N = mul(A, B_, P), mul(B_, C, P)
    emit("def Laws.mul_assoc(f, a, b, c):")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      %{otsym(M)} : {eq(to(mul('_', C, P)), to(mul(A, of(to(N)), P)), 'U32')}")
    emit(f"      %{otsym(N)} : {eq(to(mul(M, C, P)), to(mul(A, '_', P)), 'U32')}")
    emit(f"      {to_cong(mul(M, C, P), mul(A, N, P), f'assoc({A}, {B_}, {C}, {P})')}")
    emit()
    BC = xor(B_, C)
    MB, MC = mul(A, B_, P), mul(A, C, P)
    emit("def Laws.mul_distrib(f, a, b, c):")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      %{otsym(BC)} : {eq(to(mul(A, '_', P)), to(xor(of(to(MB)), of(to(MC)))), 'U32')}")
    emit(f"      %{otsym(MB)} : {eq(to(mul(A, BC, P)), to(xor('_', of(to(MC)))), 'U32')}")
    emit(f"      %{otsym(MC)} : {eq(to(mul(A, BC, P)), to(xor(MB, '_')), 'U32')}")
    emit(f"      {to_cong(mul(A, BC, P), xor(MB, MC), f'm_lin_r({A}, {B_}, {C}, {P})')}")
    emit()
    emit("def Laws.mul_one(f, a):")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      {to_cong(mul(E(0), A, P), A, f'me0({A}, {P})')}")
    emit()
    emit("def Laws.mul_zero(f, a):")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      {to_cong(mul(Z, A, P), Z, f'm_zero_l({A}, {P})')}")
    emit()
    emit("def Laws.xtime_mul_x(f, a):")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      {sym('U32', to(mul(E(1), A, P)), to(X(A, P)), to_cong(mul(E(1), A, P), X(A, P), f'me1({A}, {P})'))}")
    emit()
    emit("def Laws.add_comm(a, b):")
    emit(f"  {to_cong(xor(A, B_), xor(B_, A), f'rx_comm({A}, {B_})')}")
    emit()
    AB = xor(A, B_)
    emit("def Laws.add_assoc(a, b, c):")
    emit(f"  %{otsym(AB)} : {eq(to(xor('_', C)), to(xor(A, of(to(BC)))), 'U32')}")
    emit(f"  %{otsym(BC)} : {eq(to(xor(AB, C)), to(xor(A, '_')), 'U32')}")
    emit(f"  {to_cong(xor(AB, C), xor(A, BC), f'rx_assoc({A}, {B_}, {C})')}")
    emit()
    emit("def Laws.add_zero(a):")
    emit(f"  {to_cong(xor(A, Z), A, f'rx_zr({A})')}")
    emit()
    emit("def Laws.add_self(a):")
    emit(f"  {to_cong(xor(A, A), Z, f'rx_self({A})')}")
    emit()
    # powers
    pw = lambda n: f"G.Gf8.pow(f, a, {n})"
    gm = lambda x, y: f"G.Gf8.mul(f, {x}, {y})"
    emit("def elt_pow(n: Nat, +f: G.Gf8Field, +a: U32) -> {G.Gf8.elt(G.Gf8.pow(f, a, n)) == G.Gf8.pow(f, a, n) : U32}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+k:")
    emit("      match f:")
    emit("        case G.Gf8Field{+poly, +gen}:")
    Mx = mul(A, of("G.Gf8.pow(G.Gf8Field{poly, gen}, a, k)"), P)
    emit(f"          {to_cong(of(to(Mx)), Mx, f'ot({Mx})')}")
    emit()
    emit("def Laws.pow_add(f, a, m, n):")
    emit("  match m:")
    emit("    case 0n:")
    e = trans("U32", gm(1, pw("n")), f"G.Gf8.elt({pw('n')})", pw("n"), f"Laws.mul_one(f, {pw('n')})", "elt_pow(n, f, a)")
    emit(f"      {sym('U32', gm(1, pw('n')), pw('n'), e)}")
    emit("    case 1n+k:")
    lhs, mid, rhs = gm("a", pw("Nat.add(k, n)")), gm("a", gm(pw("k"), pw("n"))), gm(gm("a", pw("k")), pw("n"))
    e1 = cong("U32", "U32", "z", gm("a", "z"), pw("Nat.add(k, n)"), gm(pw("k"), pw("n")), "Laws.pow_add(f, a, k, n)")
    e2 = sym("U32", rhs, mid, f"Laws.mul_assoc(f, a, {pw('k')}, {pw('n')})")
    emit(f"      {trans('U32', lhs, mid, rhs, e1, e2)}")
    emit()
    emit("def Laws.inv_zero(f):")
    emit("  Laws.mul_zero(f, G.Gf8.pow(f, 0, 253n))")
    emit()

    # the named fields, by cases on the low 8 bits
    # Reading only the low byte: a function of a is the same function of
    # Gf8.elt(a); the per-byte proofs then compute on closed bytes (with
    # a's high bits left symbolic, BendTT runs out of fuel)
    emit("def mul_elt_l(+f: G.Gf8Field, +a: U32, +b: U32) -> {G.Gf8.mul(f, a, b) == G.Gf8.mul(f, G.Gf8.elt(a), b) : U32}:")
    emit("  match f:")
    emit(f"    case {F}:")
    emit(f"      {cong(R, 'U32', 'z', to(mul('z', B_, P)), A, of(to(A)), sym(R, of(to(A)), A, f'ot({A})'))}")
    emit()
    emit("def pow_elt(+n: Nat, +f: G.Gf8Field, +a: U32) -> {G.Gf8.pow(f, a, n) == G.Gf8.pow(f, G.Gf8.elt(a), n) : U32}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+k:")
    ea = "G.Gf8.elt(a)"
    t = [gm("a", pw("k")), gm(ea, pw("k")), gm(ea, f"G.Gf8.pow(f, {ea}, k)")]
    e = [f"mul_elt_l(f, a, {pw('k')})", cong("U32", "U32", "z", gm(ea, "z"), pw("k"), f"G.Gf8.pow(f, {ea}, k)", "pow_elt(k, f, a)")]
    emit(f"      {chain('U32', t, e)}")
    emit()
    emit("def log_elt(+f: G.Gf8Field, +a: U32) -> {G.Gf8.log(f, a) == G.Gf8.log(f, G.Gf8.elt(a)) : Nat}:")
    body = f"G.Gf8.log.go(254n, U32.is_eq(1, {to('z')}), f, {to('z')}, 1, 0n)"
    emit(f"  {cong(R, 'Nat', '+z', body, A, of(to(A)), sym(R, of(to(A)), A, f'ot({A})'))}")
    emit()

    ub = u32_bits(bits("b"), 8)
    emit(f"def elt_bits({', '.join('+' + b + ': Bool' for b in bits('b'))}, +r: Word(24n)) -> {eq(f'G.Gf8.elt({ub})', to(rec(bits('b'))), 'U32')}:")
    emit("  {==}")
    emit()

    emit("# a nonzero byte as itself, and 0 as 1, so that the per-byte facts hold")
    emit("# for every byte and need no hypothesis while they are split into cases")
    emit("def fixz(+x: U32) -> U32:")
    emit("  Bool.pick(U32, G.Gf8.is_zero(x), 1, x)")
    emit()
    emit("def fix_nz(+a: U32, nz: {G.Gf8.is_zero(a) == False{} : Bool}) -> {fixz(G.Gf8.elt(a)) == G.Gf8.elt(a) : U32}:")
    zt = "G.Gf8Bits.is_zero(_)"
    emit(f"  %{sym(R, of(to(A)), A, f'ot({A})')} : {{Bool.pick(U32, {zt}, 1, G.Gf8.elt(a)) == G.Gf8.elt(a) : U32}}")
    emit(f"  %{sym('Bool', 'G.Gf8.is_zero(a)', 'False{}', 'nz')} : {{Bool.pick(U32, _, 1, G.Gf8.elt(a)) == G.Gf8.elt(a) : U32}}")
    emit("  {==}")
    emit()

    def per_byte(name, fd, goal, lift, motives):
        # BendTT's fuel is per def, so the 256 cases are split into 32 defs
        # of 8 (each fixes the low five bits and splits the top three)
        bs = bits("b")
        hi = bs[5:]

        def byte(xs):
            return f"fixz({to(rec(xs))})"
        for lo in itertools.product(["True{}", "False{}"], repeat=5):
            xf = byte(list(lo) + hi)
            tag = "".join("1" if v == "True{}" else "0" for v in lo)
            ps = ", ".join(f"+{b}: Bool" for b in hi)
            emit(f"def {name}.s{tag}({ps}) -> {goal(xf)}:")
            emit(cases(hi, lambda env: "{==}", depth=1))
            emit()
        x = byte(bs)
        ps = ", ".join(f"+{b}: Bool" for b in bs)
        emit(f"def {name}.bits({ps}) -> {goal(x)}:")

        def top(env):
            tag = "".join("1" if env[b] == "True" else "0" for b in bs[:5])
            return f"{name}.s{tag}(b5, b6, b7)"
        emit(cases(bs[:5], top, depth=1))
        emit()
        emit(f"def {name}.core(+a: U32) -> {goal('fixz(G.Gf8.elt(a))')}:")
        emit("  match a:")
        emit(f"    case {u32_bits(['+' + b for b in bs], 8, '+r')}:")
        ua = u32_bits(bs, 8)
        eb = sym("U32", f"G.Gf8.elt({ua})", to(rec(bs)), f"elt_bits({', '.join(bs)}, r)")
        emit(f"      %{eb} : {goal('fixz(_)')}")
        emit(f"      {name}.bits({', '.join(bs)})")
        emit()
        ea = "G.Gf8.elt(a)"
        emit(f"def {name}.lift(+a: U32, +nz: {{G.Gf8.is_zero(a) == False{{}} : Bool}}) -> {goal(ea)}:")
        for m in motives(fd):
            emit(f"  %fix_nz(a, nz) : {m}")
        emit(f"  {name}.core(a)")
        emit()
        emit(f"def Laws.{name}(a, nz):")
        emit(f"  {lift(fd)}")
        emit()

    def lift_inv(fd):
        ea = "G.Gf8.elt(a)"
        t = [f"G.Gf8.mul({fd}, a, G.Gf8.inv({fd}, a))", f"G.Gf8.mul({fd}, {ea}, G.Gf8.inv({fd}, a))",
             f"G.Gf8.mul({fd}, {ea}, G.Gf8.inv({fd}, {ea}))", "1"]
        e = [f"mul_elt_l({fd}, a, G.Gf8.inv({fd}, a))",
             cong("U32", "U32", "z", f"G.Gf8.mul({fd}, {ea}, z)", f"G.Gf8.inv({fd}, a)", f"G.Gf8.inv({fd}, {ea})", f"pow_elt(254n, {fd}, a)"),
             f"mul_inv_{fd[6:-2]}.lift(a, nz)"]
        return chain("U32", t, e)

    def lift_log(fd):
        ea = "G.Gf8.elt(a)"
        t = [f"G.Gf8.exp({fd}, G.Gf8.log({fd}, a))", f"G.Gf8.exp({fd}, G.Gf8.log({fd}, {ea}))", ea]
        e = [cong("Nat", "U32", "z", f"G.Gf8.exp({fd}, z)", f"G.Gf8.log({fd}, a)", f"G.Gf8.log({fd}, {ea})", f"log_elt({fd}, a)"),
             f"exp_log_{fd[6:-2]}.lift(a, nz)"]
        return chain("U32", t, e)

    for fld in ("aes", "rs"):
        fd = f"G.Gf8.{fld}()"
        fe = "fixz(G.Gf8.elt(a))"
        ea = "G.Gf8.elt(a)"
        per_byte(f"mul_inv_{fld}", fd, lambda x, fd=fd: eq(f"G.Gf8.mul({fd}, {x}, G.Gf8.inv({fd}, {x}))", "1", "U32"), lift_inv,
                 lambda fd: [eq(f"G.Gf8.mul({fd}, _, G.Gf8.inv({fd}, {ea}))", "1", "U32"), eq(f"G.Gf8.mul({fd}, {fe}, G.Gf8.inv({fd}, _))", "1", "U32")])
        per_byte(f"exp_log_{fld}", fd, lambda x, fd=fd: eq(f"G.Gf8.exp({fd}, G.Gf8.log({fd}, {x}))", x, "U32"), lift_log,
                 lambda fd: [eq(f"G.Gf8.exp({fd}, G.Gf8.log({fd}, _))", ea, "U32"), eq(f"G.Gf8.exp({fd}, G.Gf8.log({fd}, {fe}))", "_", "U32")])

    emit("# vectors, by computation")
    for v in VECTORS:
        emit(f"def Laws.{v}():")
        emit("  {==}")
        emit()


def gen_gfm():
    emit("# 7. GF(2^m): addition commutes (XOR, bit by bit); for the small named")
    emit("# fields, products and inverses by cases on the element's m bits")
    emit()
    emit("def word_xor_comm(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit("      match a b:")
    emit("        case WCon{+x, +at} WCon{+y, +bt}:")
    emit("          %bx_comm(x, y) : {WCon{Bool.xor(x, y), Word.xor(p, at, bt)} == WCon{_, Word.xor(p, bt, at)} : Word(1n+p)}")
    emit("          %word_xor_comm(p, at, bt) : {WCon{Bool.xor(x, y), Word.xor(p, at, bt)} == WCon{Bool.xor(x, y), _} : Word(1n+p)}")
    emit("          {==}")
    emit()
    emit("def u32_xor_comm(+a: U32, +b: U32) -> {U32.xor(a, b) == U32.xor(b, a) : U32}:")
    emit("  match a b:")
    emit("    case U32{+x} U32{+y}:")
    emit("      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, x, y), Word.xor(32n, y, x), word_xor_comm(32n, x, y))")
    emit()
    emit("def Laws.gfm_add_comm(f, a, b):")
    emit("  Equal.cong(U32, U32, z => U32.and(M.Gfm.mask(f), z), U32.xor(a, b), U32.xor(b, a), u32_xor_comm(a, b))")
    emit()

    # Gfm.elt(f, a) masks a; with a split into its low m bits and the rest
    # r, the rest becomes zero by word_and_zero (r is symbolic, so this is
    # not computation), and the per-element facts compute on closed values
    emit("def word_and_zero(+n: Nat, +r: Word(n)) -> {Word.and(n, Word.zero(n), r) == Word.zero(n) : Word(n)}:")
    emit("  match n:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit("      match r:")
    emit("        case WCon{+x, +rt}:")
    emit("          %word_and_zero(p, rt) : {WCon{False{}, Word.and(p, Word.zero(p), rt)} == WCon{False{}, _} : Word(1n+p)}")
    emit("          {==}")
    emit()

    def cw(xs, m):
        return u32_bits(xs, m, f"Word.zero({32 - m}n)")

    for fd, m in (("M.Gfm.gf16()", 4), ("M.Gfm.gf32()", 5)):
        bs = bits("b")[:m]
        w = f"Word({32 - m}n)"
        body = "U32{" + "".join(f"WCon{{{b}, " for b in bs) + "z" + "}" * m + "}"
        emit(f"def elt_bits{m}({', '.join('+' + b + ': Bool' for b in bs)}, +r: {w}) -> {eq(f'M.Gfm.elt({fd}, {u32_bits(bs, m, chr(114))})', cw(bs, m), 'U32')}:")
        emit(f"  Equal.cong({w}, U32, z => {body}, Word.and({32 - m}n, Word.zero({32 - m}n), r), Word.zero({32 - m}n), word_and_zero({32 - m}n, r))")
        emit()

    F16 = "M.Gfm.gf16()"
    raw = lambda fd, x, y: f"M.gfm.mul.raw({fd}, {x}, {y})"
    el = lambda fd, x: f"M.Gfm.elt({fd}, {x})"
    ab, bb = bits("a")[:4], bits("b")[:4]
    for lo in itertools.product(["True{}", "False{}"], repeat=4):
        tag = "".join("1" if v == "True{}" else "0" for v in lo)
        A_, B2 = cw(list(lo), 4), cw(bb, 4)
        ps = ", ".join(f"+{b}: Bool" for b in bb)
        emit(f"def comm16.s{tag}({ps}) -> {eq(raw(F16, A_, B2), raw(F16, B2, A_), 'U32')}:")
        emit(cases(bb, lambda env: "{==}", depth=1))
        emit()
    A_, B2 = cw(ab, 4), cw(bb, 4)
    ps = ", ".join(f"+{b}: Bool" for b in ab + bb)
    emit(f"def comm16.bits({ps}) -> {eq(raw(F16, A_, B2), raw(F16, B2, A_), 'U32')}:")

    def top(env):
        tag = "".join("1" if env[b] == "True" else "0" for b in ab)
        return f"comm16.s{tag}({', '.join(bb)})"
    emit(cases(ab, top, depth=1))
    emit()
    ea, eb_ = el(F16, "a"), el(F16, "b")
    emit(f"def comm16.core(+a: U32, +b: U32) -> {eq(raw(F16, ea, eb_), raw(F16, eb_, ea), 'U32')}:")
    emit("  match a b:")
    emit(f"    case {u32_bits(['+' + x for x in ab], 4, '+ra')} {u32_bits(['+' + x for x in bb], 4, '+rb')}:")
    UA, UB = u32_bits(ab, 4, "ra"), u32_bits(bb, 4, "rb")
    sa = sym("U32", el(F16, UA), cw(ab, 4), f"elt_bits4({', '.join(ab)}, ra)")
    sb = sym("U32", el(F16, UB), cw(bb, 4), f"elt_bits4({', '.join(bb)}, rb)")
    emit(f"      %{sa} : {eq(raw(F16, '_', el(F16, UB)), raw(F16, el(F16, UB), el(F16, UA)), 'U32')}")
    emit(f"      %{sa} : {eq(raw(F16, cw(ab, 4), el(F16, UB)), raw(F16, el(F16, UB), '_'), 'U32')}")
    emit(f"      %{sb} : {eq(raw(F16, cw(ab, 4), '_'), raw(F16, el(F16, UB), cw(ab, 4)), 'U32')}")
    emit(f"      %{sb} : {eq(raw(F16, cw(ab, 4), cw(bb, 4)), raw(F16, '_', cw(ab, 4)), 'U32')}")
    emit(f"      comm16.bits({', '.join(ab + bb)})")
    emit()
    emit("def Laws.gfm_mul_comm_gf16(a, b):")
    emit("  comm16.core(a, b)")
    emit()

    emit("# a nonzero element as itself, and 0 as 1")
    emit("def fixm(+x: U32) -> U32:")
    emit("  Bool.pick(U32, U32.is_eq(x, 0), 1, x)")
    emit()
    emit("def fixm_nz(+x: U32, nz: {U32.is_eq(x, 0) == False{} : Bool}) -> {fixm(x) == x : U32}:")
    emit("  %Equal.sym(Bool, U32.is_eq(x, 0), False{}, nz) : {Bool.pick(U32, _, 1, x) == x : U32}")
    emit("  {==}")
    emit()
    for name, fd, m in (("inv16", "M.Gfm.gf16()", 4), ("inv32", "M.Gfm.gf32()", 5)):
        # x * x^(2^m - 2), for x already reduced: what mul(f, a, inv(f, a)) computes, with x = elt(a)
        Gx = lambda x, fd=fd: raw(fd, x, el(fd, f"M.gfm.pow.start({fd}, {x}, U32.sub(M.Gfm.mask({fd}), 1))"))
        goal = lambda x, Gx=Gx: eq(Gx(f"fixm({x})"), "1", "U32")
        bs = bits("b")[:m]
        split = m - 4
        for lo in itertools.product(["True{}", "False{}"], repeat=split):
            tag = "".join("1" if v == "True{}" else "0" for v in lo)
            X_ = cw(list(lo) + bs[split:], m)
            ps = ", ".join(f"+{b}: Bool" for b in bs[split:])
            emit(f"def {name}.s{tag}({ps}) -> {goal(X_)}:")
            emit(cases(bs[split:], lambda env: "{==}", depth=1))
            emit()
        X_ = cw(bs, m)
        ps = ", ".join(f"+{b}: Bool" for b in bs)
        emit(f"def {name}.bits({ps}) -> {goal(X_)}:")
        if split:
            emit(cases(bs[:split], lambda env: f"{name}.s{'1' if env['b0'] == 'True' else '0'}({', '.join(bs[split:])})", depth=1))
        else:
            emit(f"  {name}.s({', '.join(bs)})")
        emit()
        ea = el(fd, "a")
        emit(f"def {name}.core(+a: U32) -> {goal(ea)}:")
        emit("  match a:")
        emit(f"    case {u32_bits(['+' + b for b in bs], m, '+r')}:")
        UA = u32_bits(bs, m, "r")
        s = sym("U32", el(fd, UA), cw(bs, m), f"elt_bits{m}({', '.join(bs)}, r)")
        emit(f"      %{s} : {eq(Gx('fixm(_)').replace('fixm(_)', 'fixm(_)', 1), '1', 'U32').replace(Gx('fixm(_)'), raw(fd, 'fixm(_)', el(fd, f'M.gfm.pow.start({fd}, fixm({el(fd, UA)}), U32.sub(M.Gfm.mask({fd}), 1))')))}")
        emit(f"      %{s} : {eq(raw(fd, f'fixm({cw(bs, m)})', el(fd, f'M.gfm.pow.start({fd}, fixm(_), U32.sub(M.Gfm.mask({fd}), 1))')), '1', 'U32')}")
        emit(f"      {name}.bits({', '.join(bs)})")
        emit()
        nz = f"{{U32.is_eq({ea}, 0) == False{{}} : Bool}}"
        emit(f"def {name}.lift(+a: U32, +nz: {nz}) -> {eq(Gx(ea), '1', 'U32')}:")
        emit(f"  %fixm_nz({ea}, nz) : {eq(raw(fd, '_', el(fd, f'M.gfm.pow.start({fd}, {ea}, U32.sub(M.Gfm.mask({fd}), 1))')), '1', 'U32')}")
        emit(f"  %fixm_nz({ea}, nz) : {eq(raw(fd, f'fixm({ea})', el(fd, f'M.gfm.pow.start({fd}, _, U32.sub(M.Gfm.mask({fd}), 1))')), '1', 'U32')}")
        emit(f"  {name}.core(a)")
        emit()
        emit(f"def Laws.gfm_mul_inv_gf{2 ** m}(a, nz):")
        emit(f"  {name}.lift(a, nz)")
        emit()
    emit("# vectors, by computation")
    for v in VECTORS128 + VECTORSM:
        emit(f"def Laws.{v}():")
        emit("  {==}")
        emit()


TAB_FIELDS = [("aes", "G.Gf8.aes()"), ("rs", "G.Gf8.rs()")]


def gen_tabs():
    """The tables (tables.bend), for the named fields: their fills are lists
    (proof_tab.bend, through array's laws), read by array's of_list_get; a
    product is exp[log a + log b] = gen^(log b + log a) = gen^(log b) *
    gen^(log a) (pow_add) = b * a (exp_log) = a * b. The table steps are
    proved for a field f and a log list l given as variables, with the named
    fields' facts as hypotheses, so that no checker computes in a named field
    while it compares the tables."""
    emit("# 7. The tables, for the named fields (proof_tab.bend, proof_tab_cases.bend)")
    emit()
    emit("# a product with a factor whose table zero test is true is 0")
    emit("def tl.zero_l(+f: G.Gf8Field, +a: U32, +b: U32, +h: {U32.is_eq(G.Gf8.elt(a), 0) == True{} : Bool}) -> {G.Gf8.mul(f, a, b) == 0 : U32}:")
    emit("  %Equal.sym(U32, G.Gf8.mul(f, a, b), G.Gf8.mul(f, G.Gf8.elt(a), b), mul_elt_l(f, a, b)) : {_ == 0 : U32}")
    emit("  %Equal.sym(U32, G.Gf8.elt(a), 0, GC.gc.elt0(a, h)) : {G.Gf8.mul(f, _, b) == 0 : U32}")
    emit("  Laws.mul_zero(f, b)")
    emit()
    emit("def tl.mul_elt(+f: G.Gf8Field, +a: U32, +b: U32) -> {G.Gf8.mul(f, G.Gf8.elt(a), G.Gf8.elt(b)) == G.Gf8.mul(f, a, b) : U32}:")
    emit("  Equal.trans(U32, G.Gf8.mul(f, G.Gf8.elt(a), G.Gf8.elt(b)), G.Gf8.mul(f, a, G.Gf8.elt(b)), G.Gf8.mul(f, a, b), Equal.sym(U32, G.Gf8.mul(f, a, G.Gf8.elt(b)), G.Gf8.mul(f, G.Gf8.elt(a), G.Gf8.elt(b)), mul_elt_l(f, a, G.Gf8.elt(b))), Equal.trans(U32, G.Gf8.mul(f, a, G.Gf8.elt(b)), G.Gf8.mul(f, G.Gf8.elt(b), a), G.Gf8.mul(f, a, b), Laws.mul_comm(f, a, G.Gf8.elt(b)), Equal.trans(U32, G.Gf8.mul(f, G.Gf8.elt(b), a), G.Gf8.mul(f, b, a), G.Gf8.mul(f, a, b), Equal.sym(U32, G.Gf8.mul(f, b, a), G.Gf8.mul(f, G.Gf8.elt(b), a), mul_elt_l(f, b, a)), Laws.mul_comm(f, b, a))))")
    emit()
    f, l = "f", "l"
    EL = f"GT.gt.elist(510n, {f}, 0n)"
    E9 = f"A.Arrays.of_list(U32, 9n, {EL}, 0)"
    L8 = f"A.Arrays.of_list(U32, 8n, {l}, 0)"
    TAB = f"GT.gt.tab({f}, {l})"
    TT = "T.Gf8Tab{" + E9 + ", " + L8 + "}"

    def LX(x):
        return f"A.Arrays.nth(U32, {l}, A.Arrays.index(8n, G.Gf8.elt({x})), 0)"
    la, lb = f"G.Gf8.log({f}, a)", f"G.Gf8.log({f}, b)"
    FA, FB = f"U32.from_nat({la})", f"U32.from_nat({lb})"
    S = f"Nat.add({lb}, {la})"
    g = f"G.Gf8.gen({f})"
    PAIR = "T.Gf8Tab & U32"
    AP = "Array<U32> & U32"
    MUL = f"G.Gf8.mul({f}, a, b)"
    HL = f"+hl: {{List.length(&2, U32, {l}) == A.Arrays.slots(8n) : Nat}}"
    HXA = f"+hxa: {{{LX('a')} == {FA} : U32}}"
    HXB = f"+hxb: {{{LX('b')} == {FB} : U32}}"
    ELA = f"+ela: {{G.Gf8.exp({f}, {la}) == G.Gf8.elt(a) : U32}}"
    ELB = f"+elb: {{G.Gf8.exp({f}, {lb}) == G.Gf8.elt(b) : U32}}"
    FL = f"+f: G.Gf8Field, +l: List<&2, U32>"

    def get8(x):
        return f"AL.of_list_get(U32, 8n, {l}, 0, hl, GT.gt.hd8(), G.Gf8.elt({x}))"
    V = f"A.Arrays.nth(U32, {EL}, A.Arrays.index(9n, U32.add({LX('a')}, {LX('b')})), 0)"
    emit("# both factors nonzero: the exp table's entry at log a + log b is the")
    emit("# product, for a field f whose log list l gives log a and log b")
    emit(f"def tl.nz({FL}, +a: U32, +b: U32, {HXA}, {HXB}, {ELA}, {ELB}) -> {{{V} == {MUL} : U32}}:")
    emit(f"  %Equal.sym(U32, {LX('a')}, {FA}, hxa) : {{A.Arrays.nth(U32, {EL}, A.Arrays.index(9n, U32.add(_, {LX('b')})), 0) == {MUL} : U32}}")
    emit(f"  %Equal.sym(U32, {LX('b')}, {FB}, hxb) : {{A.Arrays.nth(U32, {EL}, A.Arrays.index(9n, U32.add({FA}, _)), 0) == {MUL} : U32}}")
    emit(f"  %Equal.sym(U32, U32.add({FA}, {FB}), U32.from_nat({S}), GT.gt.add_nat({la}, {lb})) : {{A.Arrays.nth(U32, {EL}, A.Arrays.index(9n, _), 0) == {MUL} : U32}}")
    emit(f"  %Equal.sym(Nat, A.Arrays.index(9n, U32.from_nat({S})), {S}, AL.index_of_nat(9n, GT.gt.hd9(), {S}, GT.gt.sum_lt({lb}, {la}, GT.gt.log_lt({f}, b), GT.gt.log_lt({f}, a)))) : {{A.Arrays.nth(U32, {EL}, _, 0) == {MUL} : U32}}")
    emit(f"  %Equal.sym(U32, A.Arrays.nth(U32, {EL}, {S}, 0), G.Gf8.exp({f}, Nat.add({S}, 0n)), GT.gt.elist_nth(510n, {f}, 0n, {S}, GT.gt.lt_sum({lb}, 255n, {la}, 255n, GT.gt.log_lt({f}, b), GT.gt.log_lt({f}, a)))) : {{_ == {MUL} : U32}}")
    emit(f"  %Equal.sym(Nat, Nat.add({S}, 0n), {S}, GT.gt.add_zero_r({S})) : {{G.Gf8.exp({f}, _) == {MUL} : U32}}")
    emit(f"  %Equal.sym(U32, G.Gf8.pow({f}, {g}, {S}), G.Gf8.mul({f}, G.Gf8.pow({f}, {g}, {lb}), G.Gf8.pow({f}, {g}, {la})), Laws.pow_add({f}, {g}, {lb}, {la})) : {{_ == {MUL} : U32}}")
    emit(f"  %Equal.sym(U32, G.Gf8.exp({f}, {lb}), G.Gf8.elt(b), elb) : {{G.Gf8.mul({f}, _, G.Gf8.pow({f}, {g}, {la})) == {MUL} : U32}}")
    emit(f"  %Equal.sym(U32, G.Gf8.exp({f}, {la}), G.Gf8.elt(a), ela) : {{G.Gf8.mul({f}, G.Gf8.elt(b), _) == {MUL} : U32}}")
    emit(f"  Equal.trans(U32, G.Gf8.mul({f}, G.Gf8.elt(b), G.Gf8.elt(a)), G.Gf8.mul({f}, b, a), {MUL}, tl.mul_elt({f}, b, a), Laws.mul_comm({f}, b, a))")
    emit()
    emit("# both factors nonzero: the table's product, through its three reads")
    emit(f"def tl.nzpick({FL}, +a: U32, +b: U32, {HL}, {HXA}, {HXB}, {ELA}, {ELB}) -> {{T.gf8tab.two.pick(Bool.or(False{{}}, False{{}}), {TAB}, G.Gf8.elt(a), G.Gf8.elt(b), False{{}}) == ({TAB}, {MUL}) : {PAIR}}}:")
    emit(f"  %Equal.sym({AP}, Array.get(U32, {L8}, G.Gf8.elt(a)), ({L8}, {LX('a')}), {get8('a')}) : {{T.gf8tab.two.mid({E9}, _, G.Gf8.elt(b), False{{}}) == ({TAB}, {MUL}) : {PAIR}}}")
    emit(f"  %Equal.sym({AP}, Array.get(U32, {L8}, G.Gf8.elt(b)), ({L8}, {LX('b')}), {get8('b')}) : {{T.gf8tab.two.fin({E9}, _, {LX('a')}, False{{}}) == ({TAB}, {MUL}) : {PAIR}}}")
    IDX = f"U32.add({LX('a')}, {LX('b')})"
    emit(f"  %Equal.sym({AP}, Array.get(U32, {E9}, {IDX}), ({E9}, {V}), AL.of_list_get(U32, 9n, {EL}, 0, GT.gt.hl_elist({f}), GT.gt.hd9(), {IDX})) : {{T.gf8tab.exp.fin(_, {L8}) == ({TAB}, {MUL}) : {PAIR}}}")
    emit(f"  %Equal.sym(U32, {V}, {MUL}, tl.nz({f}, {l}, a, b, hxa, hxb, ela, elb)) : {{({TT}, _) == ({TAB}, {MUL}) : {PAIR}}}")
    emit("  {==}")
    emit()
    LOG = f"U32.from_nat({la})"
    emit("# a logarithm through the table")
    emit(f"def tl.log({FL}, +a: U32, {HL}, {HXA}) -> {{T.Gf8Tab.log({TAB}, a) == ({TAB}, {LOG}) : {PAIR}}}:")
    emit(f"  %Equal.sym({AP}, Array.get(U32, {L8}, G.Gf8.elt(a)), ({L8}, {LX('a')}), {get8('a')}) : {{T.gf8tab.log.fin({E9}, _) == ({TAB}, {LOG}) : {PAIR}}}")
    emit(f"  %Equal.sym(U32, {LX('a')}, {LOG}, hxa) : {{({TT}, _) == ({TAB}, {LOG}) : {PAIR}}}")
    emit("  {==}")
    emit()
    EXP = f"G.Gf8.exp({f}, U32.to_nat(i))"
    NI = f"A.Arrays.nth(U32, {EL}, U32.to_nat(i), 0)"
    emit("# an exponential through the table")
    emit(f"def tl.exp({FL}, +i: U32, +hi: {{Nat.is_lt(U32.to_nat(i), 510n) == True{{}} : Bool}}) -> {{T.Gf8Tab.exp({TAB}, i) == ({TAB}, {EXP}) : {PAIR}}}:")
    emit(f"  %Equal.sym({AP}, Array.get(U32, {E9}, i), ({E9}, A.Arrays.nth(U32, {EL}, A.Arrays.index(9n, i), 0)), AL.of_list_get(U32, 9n, {EL}, 0, GT.gt.hl_elist({f}), GT.gt.hd9(), i)) : {{T.gf8tab.exp.fin(_, {L8}) == ({TAB}, {EXP}) : {PAIR}}}")
    emit(f"  %Equal.sym(Nat, A.Arrays.index(9n, i), U32.to_nat(i), AL.index_of_u32(9n, i, GT.gt.lt_add_left(2n, U32.to_nat(i), 510n, hi))) : {{({TT}, A.Arrays.nth(U32, {EL}, _, 0)) == ({TAB}, {EXP}) : {PAIR}}}")
    emit(f"  %Equal.sym(U32, {NI}, G.Gf8.exp({f}, Nat.add(U32.to_nat(i), 0n)), GT.gt.elist_nth(510n, {f}, 0n, U32.to_nat(i), hi)) : {{({TT}, _) == ({TAB}, {EXP}) : {PAIR}}}")
    emit(f"  %Equal.sym(Nat, Nat.add(U32.to_nat(i), 0n), U32.to_nat(i), GT.gt.add_zero_r(U32.to_nat(i))) : {{({TT}, G.Gf8.exp({f}, _)) == ({TAB}, {EXP}) : {PAIR}}}")
    emit("  {==}")
    emit()
    NZA = f"+ela: {{G.Gf8.is_zero(a) == False{{}} : Bool}} -> {{G.Gf8.exp({f}, {la}) == G.Gf8.elt(a) : U32}}"
    NZB = f"+elb: {{G.Gf8.is_zero(b) == False{{}} : Bool}} -> {{G.Gf8.exp({f}, {lb}) == G.Gf8.elt(b) : U32}}"
    nza = f"Equal.trans(Bool, G.Gf8.is_zero(a), U32.is_eq(G.Gf8.elt(a), 0), False{{}}, Equal.sym(Bool, U32.is_eq(G.Gf8.elt(a), 0), G.Gf8.is_zero(a), GC.gc.isz(a)), ex)"
    nzb = f"Equal.trans(Bool, G.Gf8.is_zero(b), U32.is_eq(G.Gf8.elt(b), 0), False{{}}, Equal.sym(Bool, U32.is_eq(G.Gf8.elt(b), 0), G.Gf8.is_zero(b), GC.gc.isz(b)), ey)"
    emit("# the product through the table, by whether each factor is zero")
    emit(f"def tl.pick({FL}, zx: Bool, zy: Bool, +a: U32, +b: U32, +ex: {{U32.is_eq(G.Gf8.elt(a), 0) == zx : Bool}}, +ey: {{U32.is_eq(G.Gf8.elt(b), 0) == zy : Bool}}, {HL}, {HXA}, {HXB}, ela: {{G.Gf8.is_zero(a) == False{{}} : Bool}} -> {{G.Gf8.exp({f}, {la}) == G.Gf8.elt(a) : U32}}, elb: {{G.Gf8.is_zero(b) == False{{}} : Bool}} -> {{G.Gf8.exp({f}, {lb}) == G.Gf8.elt(b) : U32}}) -> {{T.gf8tab.two.pick(Bool.or(zx, zy), {TAB}, G.Gf8.elt(a), G.Gf8.elt(b), False{{}}) == ({TAB}, {MUL}) : {PAIR}}}:")
    emit("  match zx zy:")
    emit("    case True{} _:")
    emit(f"      %Equal.sym(U32, {MUL}, 0, tl.zero_l({f}, a, b, ex)) : {{({TAB}, 0) == ({TAB}, _) : {PAIR}}}")
    emit("      {==}")
    emit("    case False{} True{}:")
    emit(f"      %Equal.sym(U32, {MUL}, 0, Equal.trans(U32, {MUL}, G.Gf8.mul({f}, b, a), 0, Laws.mul_comm({f}, a, b), tl.zero_l({f}, b, a, ey))) : {{({TAB}, 0) == ({TAB}, _) : {PAIR}}}")
    emit("      {==}")
    emit("    case False{} False{}:")
    emit(f"      tl.nzpick({f}, {l}, a, b, hl, hxa, hxb, ela({nza}), elb({nzb}))")
    emit()
    emit("# a product through the table")
    emit(f"def tl.mul({FL}, +a: U32, +b: U32, {HL}, {HXA}, {HXB}, ela: {{G.Gf8.is_zero(a) == False{{}} : Bool}} -> {{G.Gf8.exp({f}, {la}) == G.Gf8.elt(a) : U32}}, elb: {{G.Gf8.is_zero(b) == False{{}} : Bool}} -> {{G.Gf8.exp({f}, {lb}) == G.Gf8.elt(b) : U32}}) -> {{T.Gf8Tab.mul({TAB}, a, b) == ({TAB}, {MUL}) : {PAIR}}}:")
    emit(f"  tl.pick({f}, {l}, U32.is_eq(G.Gf8.elt(a), 0), U32.is_eq(G.Gf8.elt(b), 0), a, b, {{==}}, {{==}}, hl, hxa, hxb, ela, elb)")
    emit()
    for n, F in TAB_FIELDS:
        L = f"GC.gc.{n}.llist()"
        TABF = f"GT.gt.tab({F}, {L})"
        MULF = f"G.Gf8.mul({F}, a, b)"
        nza = f"Equal.trans(Bool, G.Gf8.is_zero(a), U32.is_eq(G.Gf8.elt(a), 0), False{{}}, Equal.sym(Bool, U32.is_eq(G.Gf8.elt(a), 0), G.Gf8.is_zero(a), GC.gc.isz(a)), ex)"
        nzb = f"Equal.trans(Bool, G.Gf8.is_zero(b), U32.is_eq(G.Gf8.elt(b), 0), False{{}}, Equal.sym(Bool, U32.is_eq(G.Gf8.elt(b), 0), G.Gf8.is_zero(b), GC.gc.isz(b)), ey)"
        emit(f"# The {n} field")
        emit()
        emit(f"def tl.hl8_{n}() -> {{List.length(&2, U32, {L}) == A.Arrays.slots(8n) : Nat}}:")
        emit("  {==}")
        emit()
        emit(f"def Laws.tab_mul_{n}(a, b):")
        emit(f"  %GC.gc.{n}.new() : {{T.Gf8Tab.mul(_, a, b) == (_, {MULF}) : {PAIR}}}")
        emit(f"  tl.mul({F}, {L}, a, b, tl.hl8_{n}(), GC.gc.{n}.log(a), GC.gc.{n}.log(b), nz => Laws.exp_log_{n}(a, nz), nz => Laws.exp_log_{n}(b, nz))")
        emit()
        LOGF = f"U32.from_nat(G.Gf8.log({F}, a))"
        emit(f"def Laws.tab_log_{n}(a):")
        emit(f"  %GC.gc.{n}.new() : {{T.Gf8Tab.log(_, a) == (_, {LOGF}) : {PAIR}}}")
        emit(f"  tl.log({F}, {L}, a, tl.hl8_{n}(), GC.gc.{n}.log(a))")
        emit()
        EXPF = f"G.Gf8.exp({F}, U32.to_nat(i))"
        emit(f"def Laws.tab_exp_{n}(i, hi):")
        emit(f"  %GC.gc.{n}.new() : {{T.Gf8Tab.exp(_, i) == (_, {EXPF}) : {PAIR}}}")
        emit(f"  tl.exp({F}, {L}, i, hi)")
        emit()
    emit("def Laws.witness_tab_exp():")
    emit("  {==}")
    emit()


out_text = None


def main():
    emit("# Generated by gen/proof.py; do not edit by hand.")
    emit("import Base")
    emit("import ../bytes/bytes.bend as B")
    emit("import ./gf.bend as G")
    emit("import ./tables.bend as T")
    emit("import ./gf128.bend as H")
    emit("import ./gfm.bend as M")
    emit("import ../array/array.bend as A")
    emit("import ../array/LAWS.bend as AL")
    emit("import ../array/PROOF.bend as APF")
    emit("import ./proof_tab.bend as GT")
    emit("import ./proof_tab_cases.bend as GC")
    emit("import ./LAWS.bend as Laws")
    emit()
    gen_bool()
    gen_bytes()
    gen_lin()
    gen_basis()
    gen_ring()
    gen_laws()
    gen_gfm()
    gen_tabs()
    with open(OUT, "w", newline="\n") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
