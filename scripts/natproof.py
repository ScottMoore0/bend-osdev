"""natproof: writes Bend proofs of Nat identities, for bend-osdev's gen/
scripts.

Terms are parsed from Bend text (Nat.add, Nat.mul, Nat.double, U32Nat.dbl,
numerals and `kn+x`; any other call is an opaque atom). A proof is a term
pair and the Bend text of a proof of their equality. `ring(a, b)` proves
two terms equal as commutative-semiring expressions (with x * 2^k written
U32Nat.dbl(k, x)): it normalises both sides to a sorted sum of monomials,
step by step, through bend-osdev-u32's Nat laws (nat_add_assoc,
nat_mul_add, dbl_add, ...), and writes the proof as a def of its own over
the atoms, so that a use is one call. `calc` chains steps, each a ring step
or a rewrite by a given equation (its place in the term found by comparing
the two sides).

Every step is an explicit equation between printed terms, so the checkers
compare types syntactically, and no closed power of two is ever expanded
(u32/README.md, "Stating the bounds").
"""
import re

# ---------------------------------------------------------------- terms


class T:
    __slots__ = ("op", "args")

    def __init__(self, op, *args):
        self.op = op
        self.args = args

    def key(self):
        return (self.op,) + tuple(a.key() if isinstance(a, T) else a for a in self.args)

    def __eq__(self, o):
        return isinstance(o, T) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def __repr__(self):
        return show(self)

    def __str__(self):
        return show(self)


def atom(s):
    return T("atom", s)


def num(k):
    return T("num", k)


def add(a, b):
    return T("add", a, b)


def mul(a, b):
    return T("mul", a, b)


def dbl(k, x):
    return T("dbl", k, x)


def double(x):
    return T("double", x)


def succ(x):
    return T("succ", x)


ZERO = num(0)
ONE = num(1)

CFG = {"dbl": "U.U32Nat.dbl", "law": "UL."}


def show(t):
    op = t.op
    if op == "atom":
        return t.args[0]
    if op == "num":
        return f"{t.args[0]}n"
    if op == "succ":
        k, x = 0, t
        while x.op == "succ":
            k, x = k + 1, x.args[0]
        if x.op == "num":
            return f"{k + x.args[0]}n"
        return f"{k}n+{show(x)}"
    if op == "add":
        return f"Nat.add({show(t.args[0])}, {show(t.args[1])})"
    if op == "mul":
        return f"Nat.mul({show(t.args[0])}, {show(t.args[1])})"
    if op == "dbl":
        return f"{CFG['dbl']}({show(t.args[0])}, {show(t.args[1])})"
    if op == "double":
        return f"Nat.double({show(t.args[0])})"
    if op == "call":
        return f"{t.args[0]}({', '.join(show(a) for a in t.args[1:])})"
    if op == "ctor":
        return f"{t.args[0]}{{{', '.join(show(a) for a in t.args[1:])}}}"
    if op == "tuple":
        return f"({', '.join(show(a) for a in t.args)})"
    raise ValueError(op)


# a small parser for Bend expressions
_tok = re.compile(r"\s*(?:(\d+)n\+|(\d+)n|(\d+)|([A-Za-z_][A-Za-z0-9_.]*)|(.))")


def parse(s):
    toks = []
    pos = 0
    s = s.strip()
    while pos < len(s):
        m = _tok.match(s, pos)
        if not m or m.end() == pos:
            break
        pos = m.end()
        if m.group(1):
            toks.append(("plus", int(m.group(1))))
        elif m.group(2):
            toks.append(("num", int(m.group(2))))
        elif m.group(3):
            toks.append(("id", m.group(3)))
        elif m.group(4):
            toks.append(("id", m.group(4)))
        elif m.group(5) and not m.group(5).isspace():
            toks.append(("p", m.group(5)))
    toks.append(("end", None))
    i = [0]

    def peek():
        return toks[i[0]]

    def nxt():
        t = toks[i[0]]
        i[0] += 1
        return t

    def raw(t):
        # opaque text of a parsed sub-expression
        return show(t)

    def expr():
        t = peek()
        if t[0] == "plus":
            nxt()
            x = expr()
            for _ in range(t[1]):
                x = succ(x)
            return x
        return primary()

    def args_list():
        assert nxt() == ("p", "(")
        out = []
        if peek() == ("p", ")"):
            nxt()
            return out
        while True:
            out.append(expr_any())
            t = nxt()
            if t == ("p", ")"):
                return out
            assert t == ("p", ","), t

    def expr_any():
        # an argument: a Nat expression, or anything else kept as text
        t = peek()
        if t == ("p", "{"):
            # a record or braced term: keep as text up to the matching brace
            depth = 0
            parts = []
            while True:
                t = nxt()
                parts.append(t)
                if t == ("p", "{"):
                    depth += 1
                elif t == ("p", "}"):
                    depth -= 1
                    if depth == 0:
                        break
            return atom(untok(parts))
        return expr()

    def primary():
        t = nxt()
        if t[0] == "num":
            return num(t[1])
        if t[0] == "id":
            name = t[1]
            if peek() == ("p", "("):
                a = args_list()
                if name == "Nat.add":
                    return add(*a)
                if name == "Nat.mul":
                    return mul(*a)
                if name in ("U.U32Nat.dbl", "U32Nat.dbl"):
                    return dbl(*a)
                if name == "Nat.double":
                    return double(*a)
                return T("call", name, *a)
            if peek() == ("p", "{"):
                nxt()
                a = []
                if peek() == ("p", "}"):
                    nxt()
                    return T("ctor", name)
                while True:
                    a.append(expr_any())
                    tt = nxt()
                    if tt == ("p", "}"):
                        return T("ctor", name, *a)
                    assert tt == ("p", ","), tt
            return atom(name)
        if t == ("p", "("):
            e = expr_any()
            if peek() == ("p", ","):
                items = [e]
                while nxt() == ("p", ","):
                    items.append(expr_any())
                return T("tuple", *items)
            assert nxt() == ("p", ")")
            return e
        raise ValueError(f"parse: {t} in {s}")

    def untok(parts):
        out = ""
        for k, v in parts:
            if k == "id":
                out += v
            elif k == "num":
                out += f"{v}n"
            elif k == "plus":
                out += f"{v}n+"
            elif v == ",":
                out += ", "
            else:
                out += v
        return out

    r = expr()
    assert peek()[0] == "end", (s, toks[i[0]:])
    return r


def P(x):
    return parse(x) if isinstance(x, str) else x


# ---------------------------------------------------------------- proofs


class Pf:
    """A proof of {lhs == rhs : ty}. st, when known, is the list of its
    steps (x, y, paths, local): x becomes y by the local proof at the paths
    (local None: by computation)."""

    __slots__ = ("lhs", "rhs", "text", "ty", "st")

    def __init__(self, lhs, rhs, text, ty="Nat", st=None):
        self.lhs, self.rhs, self.text, self.ty = P(lhs), P(rhs), text, ty
        self.st = st

    def __repr__(self):
        return f"<{self.lhs} == {self.rhs}>"


def steps_of(p):
    if p.st is not None:
        return p.st
    if p.lhs == p.rhs:
        return []
    if p.text == "{==}":
        return [(p.lhs, p.rhs, [()], None)]
    return [(p.lhs, p.rhs, [()], p)]


def refl(t, defn=False):
    t = P(t)
    return Pf(t, t, "{==}", st=[])


def cast(a, b):
    """a and b equal by computation."""
    return Pf(a, b, "{==}")


def is_refl(p):
    return p.text == "{==}" and p.lhs == p.rhs


def sym(p):
    if p.lhs == p.rhs:
        return p
    if p.st is None:
        if p.text == "{==}":
            return Pf(p.rhs, p.lhs, "{==}", p.ty)
        return Pf(p.rhs, p.lhs, f"Equal.sym({p.ty}, {p.lhs}, {p.rhs}, {p.text})", p.ty)
    st = [(y, x, ps, (sym(loc) if loc is not None else None)) for (x, y, ps, loc) in reversed(p.st)]
    if p.text == "{==}":
        return Pf(p.rhs, p.lhs, "{==}", p.ty, st)
    return Pf(p.rhs, p.lhs, f"Equal.sym({p.ty}, {p.lhs}, {p.rhs}, {p.text})", p.ty, st)


def trans(p, q):
    assert p.rhs == q.lhs, f"trans: {p.rhs}  /  {q.lhs}"
    if p.lhs == p.rhs and p.text == "{==}":
        return q
    if q.lhs == q.rhs and q.text == "{==}":
        return p
    st = steps_of(p) + steps_of(q)
    if p.text == "{==}" and q.text == "{==}":
        return Pf(p.lhs, q.rhs, "{==}", p.ty, st)
    return Pf(p.lhs, q.rhs, f"Equal.trans({p.ty}, {p.lhs}, {p.rhs}, {q.rhs}, {p.text}, {q.text})", p.ty, st)


def chain(ps):
    out = ps[0]
    for q in ps[1:]:
        out = trans(out, q)
    return out


def subst(t, path, v):
    if not path:
        return v
    assert isinstance(t, T)
    i = path[0]
    args = list(t.args)
    args[i] = subst(args[i], path[1:], v)
    return T(t.op, *args)


def at(t, path):
    for i in path:
        t = t.args[i]
    return t


HOLE = "zz"


def cong_at(t, path, p):
    """t with p.lhs at path: a proof of t == t[path := p.rhs]."""
    assert at(t, path) == p.lhs, (at(t, path), p.lhs)
    if not path:
        return p
    if p.lhs == p.rhs:
        return refl(t)
    st = [(subst(t, path, x), subst(t, path, y), [path + q for q in ps], loc) for (x, y, ps, loc) in steps_of(p)]
    if p.text == "{==}":
        return Pf(t, subst(t, path, p.rhs), "{==}", st=st)
    ctx = subst(t, path, atom(HOLE))
    return Pf(t, subst(t, path, p.rhs), f"Equal.cong(Nat, Nat, {HOLE} => {ctx}, {p.lhs}, {p.rhs}, {p.text})", st=st)


def diffs(a, b, path=()):
    if a == b:
        return []
    if a.op == b.op and a.op not in ("atom", "num") and len(a.args) == len(b.args) and _heads(a, b):
        out = []
        for i, (x, y) in enumerate(zip(a.args, b.args)):
            if isinstance(x, T):
                out += diffs(x, y, path + (i,))
        return out
    return [path]


def _heads(a, b):
    return all(x == y for x, y in zip(a.args, b.args) if not isinstance(x, T))


def rewrite(a, b, p):
    """a == b, where b is a with occurrences of p.lhs replaced by p.rhs (or
    p.rhs by p.lhs)."""
    a, b = P(a), P(b)
    if a == b:
        return refl(a)
    # top-level match first
    if a == p.lhs and b == p.rhs:
        return p
    if a == p.rhs and b == p.lhs:
        return sym(p)
    paths = _rw_paths(a, b, p)
    fwd = [at(a, q) == p.lhs and at(b, q) == p.rhs for q in paths]
    if all(fwd):
        q = p
    else:
        assert not any(fwd), f"rewrite: mixed directions by {p}"
        q = sym(p)
    if q.text == "{==}":
        return Pf(a, b, "{==}", st=[(a, b, [()], None)])
    ctx = a
    for path in paths:
        ctx = subst(ctx, path, atom(HOLE))
    if paths == [()]:
        return q
    return Pf(a, b, f"Equal.cong(Nat, Nat, {HOLE} => {ctx}, {q.lhs}, {q.rhs}, {q.text})", st=[(a, b, list(paths), q)])


def _rw_paths(a, b, p, path=()):
    if a == b:
        return []
    if (a == p.lhs and b == p.rhs) or (a == p.rhs and b == p.lhs):
        return [path]
    if a.op == b.op and a.op not in ("atom", "num") and len(a.args) == len(b.args) and _heads(a, b):
        out = []
        for i, (x, y) in enumerate(zip(a.args, b.args)):
            if isinstance(x, T):
                out += _rw_paths(x, y, p, path + (i,))
        return out
    raise AssertionError(f"rewrite: cannot match\n  {a}\n  {b}\n  by {p}")


# ---------------------------------------------------------------- laws

def L(name, *args):
    return f"{CFG['law']}{name}({', '.join(str(P(a)) for a in args)})"


def law_add_zero(x):
    return Pf(add(x, ZERO), x, L("nat_add_zero", x))


def law_add_comm(x, y):
    return Pf(add(x, y), add(y, x), L("nat_add_comm", x, y))


def law_add_assoc(x, y, z):
    return Pf(add(add(x, y), z), add(x, add(y, z)), L("nat_add_assoc", x, y, z))


def law_add_left_comm(x, y, z):
    return Pf(add(x, add(y, z)), add(y, add(x, z)), L("nat_add_left_comm", x, y, z))


def law_mul_zero(x):
    return Pf(mul(x, ZERO), ZERO, L("nat_mul_zero", x))


def law_mul_one(x):
    return Pf(mul(x, ONE), x, L("nat_mul_one", x))


def law_one_mul(x):
    return Pf(mul(ONE, x), x, L("nat_one_mul", x))


def law_mul_comm(x, y):
    return Pf(mul(x, y), mul(y, x), L("nat_mul_comm", x, y))


def law_mul_assoc(x, y, z):
    return Pf(mul(mul(x, y), z), mul(x, mul(y, z)), L("nat_mul_assoc", x, y, z))


def law_mul_left_comm(x, y, z):
    return Pf(mul(x, mul(y, z)), mul(y, mul(x, z)), L("nat_mul_left_comm", x, y, z))


def law_mul_add(x, y, z):
    return Pf(mul(x, add(y, z)), add(mul(x, y), mul(x, z)), L("nat_mul_add", x, y, z))


def law_add_mul(x, y, z):
    return Pf(mul(add(x, y), z), add(mul(x, z), mul(y, z)), L("nat_add_mul", x, y, z))


def law_double(x):
    return Pf(double(x), add(x, x), L("nat_double", x))


def law_dbl_zero(k):
    return Pf(dbl(k, ZERO), ZERO, L("dbl_zero", k))


def law_dbl_add(k, x, y):
    return Pf(dbl(k, add(x, y)), add(dbl(k, x), dbl(k, y)), L("dbl_add", k, x, y))


def law_dbl_comm(j, k, x):
    return Pf(dbl(j, dbl(k, x)), dbl(k, dbl(j, x)), L("dbl_comm", j, k, x))


def law_dbl_mul_l(k, x, y):
    return Pf(mul(dbl(k, x), y), dbl(k, mul(x, y)), L("dbl_mul_l", k, x, y))


def law_dbl_mul_r(k, x, y):
    return Pf(mul(x, dbl(k, y)), dbl(k, mul(x, y)), L("dbl_mul_r", k, x, y))


# ---------------------------------------------------------------- ring
#
# A normal form is a sum of monomials, sorted, with no monomial twice. A
# monomial is 2^e1 ... 2^ek 2^c (a product of atoms), written
# dbl(e1, ... dbl(ek, dbl(cn, prod))): the symbolic exponents sorted, the
# numeric one c innermost (left out when 0). Two equal monomials m + m are
# merged into 2^1 m, so a numeral coefficient is kept in binary.


def tkey(t):
    return show(t)


def law_dbl_dbl(j, k, x):
    return Pf(dbl(j, dbl(k, x)), dbl(add(j, k), x), L("dbl_dbl", j, k, x))


def prod_term(fs):
    fs = list(fs)
    if not fs:
        return ONE
    s = fs[-1]
    for t in reversed(fs[:-1]):
        s = mul(t, s)
    return s


def sum_term(ts):
    ts = list(ts)
    if not ts:
        return ZERO
    s = ts[-1]
    for t in reversed(ts[:-1]):
        s = add(t, s)
    return s


def mono_term(m):
    sexps, c, facs = m
    body = prod_term(facs)
    if c:
        body = dbl(num(c), body)
    for e in reversed(sexps):
        body = dbl(e, body)
    return body


def mkey(m):
    sexps, c, facs = m
    return (tuple(tkey(e) for e in sexps), c, tuple(tkey(f) for f in facs))


def concat_sum(l1, l2):
    """add(S(l1), S(l2)) == S(l1 ++ l2)."""
    a = add(sum_term(l1), sum_term(l2))
    if not l1:
        return cast(a, sum_term(l2))
    if not l2:
        return law_add_zero(sum_term(l1))
    if len(l1) == 1:
        return refl(a)
    x, r = l1[0], l1[1:]
    p1 = law_add_assoc(x, sum_term(r), sum_term(l2))
    inner = concat_sum(r, l2)
    p2 = cong_at(p1.rhs, (1,), inner)
    return trans(p1, p2)


def concat_prod(l1, l2):
    a = mul(prod_term(l1), prod_term(l2))
    if not l1:
        return law_one_mul(prod_term(l2))
    if not l2:
        return law_mul_one(prod_term(l1))
    if len(l1) == 1:
        return refl(a)
    x, r = l1[0], l1[1:]
    p1 = law_mul_assoc(x, prod_term(r), prod_term(l2))
    inner = concat_prod(r, l2)
    p2 = cong_at(p1.rhs, (1,), inner)
    return trans(p1, p2)


def bubble(items, keyf, swap_lc, swap_c, build):
    """Sort a right-nested list; a proof build(items) == build(sorted)."""
    items = list(items)
    steps = []
    n = len(items)
    changed = True
    while changed:
        changed = False
        for i in range(n - 1):
            if keyf(items[i]) > keyf(items[i + 1]):
                cur = build(items)
                path = (1,) * i
                if i + 1 == n - 1:
                    p = swap_c(items[i], items[i + 1])
                else:
                    p = swap_lc(items[i], items[i + 1], build(items[i + 2:]))
                steps.append(cong_at(cur, path, p))
                items[i], items[i + 1] = items[i + 1], items[i]
                changed = True
    if not steps:
        return items, refl(build(items))
    return items, chain(steps)


def sort_prod(fs):
    return bubble(fs, tkey, law_mul_left_comm, law_mul_comm, prod_term)


def chain_term(exps, body):
    t = body
    for e in reversed(exps):
        t = dbl(e, t)
    return t


def ekey(e):
    return (1, e.args[0], "") if e.op == "num" else (0, 0, tkey(e))


def norm_chain(exps, body):
    """chain_term(exps, body) == mono form: (sexps, c, proof)."""
    es = list(exps)
    steps = []
    changed = True
    while changed:
        changed = False
        for i in range(len(es) - 1):
            if ekey(es[i]) > ekey(es[i + 1]):
                cur = chain_term(es, body)
                p = law_dbl_comm(es[i], es[i + 1], chain_term(es[i + 2:], body))
                steps.append(cong_at(cur, (1,) * i, p))
                es[i], es[i + 1] = es[i + 1], es[i]
                changed = True
    # combine the numeric exponents at the end
    while len(es) >= 2 and es[-1].op == "num" and es[-2].op == "num":
        cur = chain_term(es, body)
        j, k = es[-2], es[-1]
        path = (1,) * (len(es) - 2)
        p = trans(law_dbl_dbl(j, k, body), cast(dbl(add(j, k), body), dbl(num(j.args[0] + k.args[0]), body)))
        steps.append(cong_at(cur, path, p))
        es = es[:-2] + [num(j.args[0] + k.args[0])]
    # drop a numeric 0
    if es and es[-1].op == "num" and es[-1].args[0] == 0:
        cur = chain_term(es, body)
        path = (1,) * (len(es) - 1)
        steps.append(cong_at(cur, path, cast(dbl(ZERO, body), body)))
        es = es[:-1]
    c = 0
    if es and es[-1].op == "num":
        c = es[-1].args[0]
        es = es[:-1]
    m = (tuple(es), c, None)
    pf = chain(steps) if steps else refl(chain_term(exps, body))
    return m, pf


def mono_with(m, facs):
    return (m[0], m[1], tuple(facs))


def dbl_mono(k, m):
    """dbl(k, mono_term(m)) == mono_term(m')."""
    sexps, c, facs = m
    exps = [k] + list(sexps) + ([num(c)] if c else [])
    body = prod_term(facs)
    mm, pf = norm_chain(exps, body)
    m2 = mono_with(mm, facs)
    assert pf.rhs == mono_term(m2), (pf.rhs, mono_term(m2))
    return m2, pf


def mono_exps(m):
    sexps, c, facs = m
    return list(sexps) + ([num(c)] if c else [])


def mono_mul(ma, mb):
    """mul(mono_term(ma), mono_term(mb)) == mono_term(product)."""
    ea, fa = mono_exps(ma), ma[2]
    eb, fb = mono_exps(mb), mb[2]
    cur = mul(mono_term(ma), mono_term(mb))
    start = cur
    steps = []
    prefix = []
    for e in ea:
        path = (1,) * len(prefix)
        inner = at(cur, path)
        assert inner.op == "mul" and inner.args[0].op == "dbl"
        p = law_dbl_mul_l(inner.args[0].args[0], inner.args[0].args[1], inner.args[1])
        st = cong_at(cur, path, p)
        steps.append(st)
        cur = st.rhs
        prefix.append(e)
    for e in eb:
        path = (1,) * len(prefix)
        inner = at(cur, path)
        assert inner.op == "mul" and inner.args[1].op == "dbl"
        p = law_dbl_mul_r(inner.args[1].args[0], inner.args[0], inner.args[1].args[1])
        st = cong_at(cur, path, p)
        steps.append(st)
        cur = st.rhs
        prefix.append(e)
    path = (1,) * len(prefix)
    pc = concat_prod(list(fa), list(fb))
    st = cong_at(cur, path, pc)
    steps.append(st)
    cur = st.rhs
    fs, ps = sort_prod(list(fa) + list(fb))
    st = cong_at(cur, path, ps)
    steps.append(st)
    cur = st.rhs
    if MODE[0] == "cheap":
        fs = list(fs)
        while len(fs) >= 2 and fs[0].op == "num" and fs[1].op == "num":
            k = fs[0].args[0] * fs[1].args[0]
            if len(fs) == 2:
                p = cast(mul(fs[0], fs[1]), num(k))
            else:
                rest = prod_term(fs[2:])
                p = trans(sym(law_mul_assoc(fs[0], fs[1], rest)), cong_at(mul(mul(fs[0], fs[1]), rest), (0,), cast(mul(fs[0], fs[1]), num(k))))
            st = cong_at(cur, path, p)
            steps.append(st)
            cur = st.rhs
            fs = [num(k)] + fs[2:]
        if len(fs) >= 2 and fs[0] == ONE:
            st = cong_at(cur, path, law_one_mul(prod_term(fs[1:])))
            steps.append(st)
            cur = st.rhs
            fs = fs[1:]
    mm, pd = norm_chain(prefix, prod_term(fs))
    steps.append(pd)
    res = mono_with(mm, fs)
    assert pd.rhs == mono_term(res)
    return res, chain([refl(start)] + steps)


def sort_monos(ms):
    """sum of mono_terms, sorted by mkey."""
    terms = [mono_term(m) for m in ms]
    order = list(range(len(ms)))
    keyf_map = {}
    items = list(zip([mkey(m) for m in ms], ms))
    # bubble on the terms, keyed by the monomials
    pairs = list(items)
    steps = []
    n = len(pairs)
    changed = True
    while changed:
        changed = False
        for i in range(n - 1):
            if pairs[i][0] > pairs[i + 1][0]:
                cur = sum_term([mono_term(p[1]) for p in pairs])
                path = (1,) * i
                ti, tj = mono_term(pairs[i][1]), mono_term(pairs[i + 1][1])
                if i + 1 == n - 1:
                    p = law_add_comm(ti, tj)
                else:
                    p = law_add_left_comm(ti, tj, sum_term([mono_term(q[1]) for q in pairs[i + 2:]]))
                steps.append(cong_at(cur, path, p))
                pairs[i], pairs[i + 1] = pairs[i + 1], pairs[i]
                changed = True
    out = [p[1] for p in pairs]
    pf = chain(steps) if steps else refl(sum_term(terms))
    return out, pf


def canon(ms):
    """sum_term(monos) == sum_term(canonical): sorted, equal ones merged."""
    ms = list(ms)
    ms, pf = sort_monos(ms)
    steps = [pf]
    if MODE[0] == "cheap":
        while True:
            i = next((j for j in range(len(ms) - 1) if is_const(ms[j]) and is_const(ms[j + 1])), None)
            if i is None:
                break
            cur = sum_term([mono_term(m) for m in ms])
            ta, tb = mono_term(ms[i]), mono_term(ms[i + 1])
            k = ta.args[0] + tb.args[0]
            path = (1,) * i
            if i + 1 == len(ms) - 1:
                st = cong_at(cur, path, cast(add(ta, tb), num(k)))
            else:
                rest = sum_term([mono_term(m) for m in ms[i + 2:]])
                st1 = cong_at(cur, path, sym(law_add_assoc(ta, tb, rest)))
                st = trans(st1, cong_at(st1.rhs, path + (0,), cast(add(ta, tb), num(k))))
            steps.append(st)
            ms = ms[:i] + [((), 0, (num(k),))] + ms[i + 2:]
            ms, pf2 = sort_monos(ms)
            steps.append(pf2)
        return ms, chain(steps)
    while True:
        i = next((j for j in range(len(ms) - 1) if mkey(ms[j]) == mkey(ms[j + 1])), None)
        if i is None:
            break
        cur = sum_term([mono_term(m) for m in ms])
        t = mono_term(ms[i])
        path = (1,) * i
        if i + 1 == len(ms) - 1:
            focus = path
        else:
            rest = sum_term([mono_term(m) for m in ms[i + 2:]])
            st = cong_at(cur, path, sym(law_add_assoc(t, t, rest)))
            steps.append(st)
            cur = st.rhs
            focus = path + (0,)
        m2, pd = dbl_mono(ONE, ms[i])
        pm = chain([sym(law_double(t)), cast(double(t), dbl(ONE, t)), pd])
        st = cong_at(cur, focus, pm)
        steps.append(st)
        ms = ms[:i] + [m2] + ms[i + 2:]
        ms2, pf2 = sort_monos(ms)
        steps.append(pf2)
        ms = ms2
    return ms, chain(steps)


def dist(pa, pb):
    """mul(S(pa), S(pb)) == S(products), products as terms mul(mt(a), mt(b))."""
    A = [mono_term(m) for m in pa]
    B = [mono_term(m) for m in pb]
    t = mul(sum_term(A), sum_term(B))
    if not A:
        return [], cast(t, ZERO)
    if not B:
        return [], law_mul_zero(sum_term(A))
    if len(A) == 1:
        if len(B) == 1:
            return [(pa[0], pb[0])], refl(t)
        p1 = law_mul_add(A[0], B[0], sum_term(B[1:]))
        rest, p2 = dist(pa, pb[1:])
        st = cong_at(p1.rhs, (1,), p2)
        return [(pa[0], pb[0])] + rest, trans(p1, st)
    p1 = law_add_mul(A[0], sum_term(A[1:]), sum_term(B))
    l1, q1 = dist(pa[:1], pb)
    l2, q2 = dist(pa[1:], pb)
    s1 = cong_at(p1.rhs, (0,), q1)
    s2 = cong_at(s1.rhs, (1,), q2)
    terms1 = [mul(mono_term(x), mono_term(y)) for x, y in l1]
    terms2 = [mul(mono_term(x), mono_term(y)) for x, y in l2]
    s3 = concat_sum(terms1, terms2)
    return l1 + l2, chain([p1, s1, s2, s3])


UNIT = ((), 0, ())
MODE = ["full"]


def is_const(m):
    return not m[0] and m[1] == 0 and len(m[2]) == 1 and m[2][0].op == "num"


def norm(t):
    """(poly, proof t == sum_term(mono_terms(poly)))."""
    op = t.op
    if op in ("atom", "call", "ctor"):
        return [((), 0, (t,))], refl(t)
    if op == "num":
        k = t.args[0]
        if k == 0:
            return [], refl(t)
        if MODE[0] == "cheap":
            return [((), 0, (t,))], refl(t)
        assert k <= 4096, f"ring: numeral {k} too large to expand"
        bits = [i for i in range(k.bit_length()) if (k >> i) & 1]
        poly = [((), i, ()) for i in bits]
        poly, p1 = sort_monos(poly)
        return poly, trans(cast(t, sum_term([mono_term(m) for m in [((), i, ()) for i in bits]])), p1)
    if op == "succ":
        t2 = add(ONE, t.args[0])
        poly, p = norm(t2)
        return poly, trans(cast(t, t2), p)
    if op == "double":
        p0 = law_double(t.args[0])
        poly, p = norm(p0.rhs)
        return poly, trans(p0, p)
    if op == "add":
        A, pa = norm(t.args[0])
        B, pb = norm(t.args[1])
        s1 = cong_at(t, (0,), pa)
        s2 = cong_at(s1.rhs, (1,), pb)
        s3 = concat_sum([mono_term(m) for m in A], [mono_term(m) for m in B])
        poly, s4 = canon(A + B)
        return poly, chain([s1, s2, s3, s4])
    if op == "mul":
        A, pa = norm(t.args[0])
        B, pb = norm(t.args[1])
        s1 = cong_at(t, (0,), pa)
        s2 = cong_at(s1.rhs, (1,), pb)
        pairs, s3 = dist(A, B)
        steps = [s1, s2, s3]
        cur = s3.rhs
        monos = []
        for i, (x, y) in enumerate(pairs):
            m, pm = mono_mul(x, y)
            path = (1,) * i + ((0,) if i < len(pairs) - 1 else ())
            st = cong_at(cur, path, pm)
            steps.append(st)
            cur = st.rhs
            monos.append(m)
        poly, s5 = canon(monos)
        steps.append(s5)
        return poly, chain(steps)
    if op == "dbl":
        k, x = t.args
        if k == ZERO:
            poly, p = norm(x)
            return poly, trans(cast(t, x), p)
        X, px = norm(x)
        s1 = cong_at(t, (1,), px)
        steps = [s1]
        cur = s1.rhs
        terms = [mono_term(m) for m in X]
        if not terms:
            steps.append(law_dbl_zero(k))
            return [], chain(steps)
        for i in range(len(terms) - 1):
            path = (1,) * i
            p = law_dbl_add(k, terms[i], sum_term(terms[i + 1:]))
            st = cong_at(cur, path, p)
            steps.append(st)
            cur = st.rhs
        monos = []
        for i, m in enumerate(X):
            path = (1,) * i + ((0,) if i < len(X) - 1 else ())
            m2, pm = dbl_mono(k, m)
            st = cong_at(cur, path, pm)
            steps.append(st)
            cur = st.rhs
            monos.append(m2)
        poly, s5 = canon(monos)
        steps.append(s5)
        return poly, chain(steps)
    raise ValueError(op)


# ---------------------------------------------------------------- output


class Out:
    def __init__(self, prefix="ring"):
        self.defs = []
        self.seen = {}
        self.prefix = prefix

    def emit(self, s):
        self.defs.append(s)

    def text(self):
        return "\n".join(self.defs)


OUT = Out()


def atoms_of(t, acc):
    if t.op in ("atom", "call", "ctor", "tuple"):
        if t not in acc:
            acc.append(t)
        return
    if t.op == "dbl":
        k = t.args[0]
        if k.op != "num":
            if k not in acc:
                acc.append(k)
        atoms_of(t.args[1], acc)
        return
    if t.op == "num":
        return
    for a in t.args:
        atoms_of(a, acc)


def replace(t, mp):
    if t in mp:
        return mp[t]
    if t.op in ("atom", "num"):
        return t
    return T(t.op, *[replace(a, mp) if isinstance(a, T) else a for a in t.args])


def ring(a, b, name=None):
    """A proof of a == b as semiring expressions, as a call of a def of its
    own over the atoms."""
    a, b = P(a), P(b)
    if a == b:
        return refl(a)
    ats = []
    atoms_of(a, ats)
    atoms_of(b, ats)
    names = [f"x{i}" for i in range(len(ats))]
    mp = {t: atom(n) for t, n in zip(ats, names)}
    a2, b2 = replace(a, mp), replace(b, mp)
    key = (show(a2), show(b2))
    if key not in OUT.seen:
        MODE[0] = "cheap"
        pa_poly, pa = norm(a2)
        pb_poly, pb = norm(b2)
        if [mono_term(m) for m in pa_poly] != [mono_term(m) for m in pb_poly]:
            MODE[0] = "full"
            pa_poly, pa = norm(a2)
            pb_poly, pb = norm(b2)
        MODE[0] = "full"
        if [mono_term(m) for m in pa_poly] != [mono_term(m) for m in pb_poly]:
            raise AssertionError(f"ring: not equal\n  {a}\n  {b}\n  {[str(mono_term(m)) for m in pa_poly]}\n  {[str(mono_term(m)) for m in pb_poly]}")
        pf = trans(pa, sym(pb))
        nm = name or f"{OUT.prefix}{len(OUT.seen)}"
        params = ", ".join(f"+{n}: Nat" for n in names)
        lines = []
        for (x, y, ps, loc) in steps_of(pf):
            if loc is None:
                continue
            ctx = x
            for q in ps:
                ctx = subst(ctx, q, atom("_"))
            e = sym(loc)
            lines.append(f"  %{e.text} : {{{ctx} == {b2} : Nat}}")
        body = "\n".join(lines + ["  {==}"])
        OUT.emit(f"def {nm}({params}) -> {{{a2} == {b2} : Nat}}:\n{body}\n")
        OUT.seen[key] = nm
    nm = OUT.seen[key]
    return Pf(a, b, f"{nm}({', '.join(show(t) for t in ats)})")


def ring_local(a, b):
    """ring(a, b), proved on the smallest subterms that differ, in context."""
    a, b = P(a), P(b)
    if a == b:
        return refl(a)
    paths = diffs(a, b)
    pre = list(paths[0])
    for q in paths[1:]:
        k = 0
        while k < len(pre) and k < len(q) and pre[k] == q[k]:
            k += 1
        pre = pre[:k]
    while True:
        x, y = at(a, tuple(pre)), at(b, tuple(pre))
        if x.op in ("add", "mul", "dbl", "succ", "double", "num", "atom", "call", "ctor", "tuple") or not pre:
            try:
                pf = ring(x, y)
                return cong_at(a, tuple(pre), pf)
            except AssertionError:
                if not pre:
                    raise
        pre = pre[:-1]


def calc(start, *steps):
    """start, then (term, how) steps: how is 'ring', '=' (by computation),
    or a Pf to rewrite with."""
    cur = P(start)
    ps = []
    for term, how in steps:
        term = P(term)
        if how == "ring":
            ps.append(ring_local(cur, term))
        elif how == "=":
            ps.append(cast(cur, term))
        else:
            ps.append(rewrite(cur, term, how))
        cur = term
    return chain(ps)


def hyp(name, lhs, rhs):
    """a hypothesis (or any proof text) of lhs == rhs."""
    return Pf(lhs, rhs, name)


# ---------------------------------------------------------------- order


def btrue(e):
    """the type {e == True{} : Bool}."""
    return "{" + f"{e} == True{{}} : Bool" + "}"


def bcong(var, body, a, b, e):
    """Equal.cong from Nat to Bool."""
    return f"Equal.cong(Nat, Bool, {var} => {body}, {P(a)}, {P(b)}, {e})"


def btrans(a, b, c, ab, bc):
    return f"Equal.trans(Bool, {a}, {b}, {c}, {ab}, {bc})"


def bsym(a, b, e):
    return f"Equal.sym(Bool, {a}, {b}, {e})"


def le_from(x, y, w, pf):
    """{is_le(x, y) == True} from pf : w + x == y."""
    x, y = P(x), P(y)
    s = add(P(w), x)
    assert pf.lhs == s and pf.rhs == y, (pf, s, y)
    return btrans(f"Nat.is_le({x}, {y})", f"Nat.is_le({x}, {s})", "True{}",
                  bsym(f"Nat.is_le({x}, {s})", f"Nat.is_le({x}, {y})", bcong(HOLE, f"Nat.is_le({x}, {HOLE})", s, y, pf.text)),
                  f"{CFG['law']}nat_le_add({x}, {P(w)})")


def lt_from(x, y, w, pf):
    """{is_lt(x, y) == True} from pf : w + (1 + x) == y."""
    x, y = P(x), P(y)
    s = add(P(w), succ(x))
    assert pf.lhs == s and pf.rhs == y, (pf, s, y)
    return btrans(f"Nat.is_lt({x}, {y})", f"Nat.is_lt({x}, {s})", "True{}",
                  bsym(f"Nat.is_lt({x}, {s})", f"Nat.is_lt({x}, {y})", bcong(HOLE, f"Nat.is_lt({x}, {HOLE})", s, y, pf.text)),
                  f"{CFG['law']}nat_lt_add({x}, {P(w)})")


def lt_rw(x, y, x2, y2, ex, ey, h):
    """{is_lt(x2, y2) == True} from h : {is_lt(x, y) == True}, with ex : x == x2
    and ey : y == y2 (proof texts, or None where x2 is x or y2 is y)."""
    cur = h
    a, b = x, y
    if ex is not None:
        cur = btrans(f"Nat.is_lt({x2}, {b})", f"Nat.is_lt({a}, {b})", "True{}", bcong(HOLE, f"Nat.is_lt({HOLE}, {b})", x2, a, f"Equal.sym(Nat, {a}, {x2}, {ex})"), cur)
        a = x2
    if ey is not None:
        cur = btrans(f"Nat.is_lt({a}, {y2})", f"Nat.is_lt({a}, {b})", "True{}", bcong(HOLE, f"Nat.is_lt({a}, {HOLE})", y2, b, f"Equal.sym(Nat, {b}, {y2}, {ey})"), cur)
    return cur


def wit_lt(x, y, h):
    """(w, a proof of w + (1 + x) == y) from h : {is_lt(x, y) == True}."""
    w = f"Nat.sub({y}, 1n+{x})"
    return w, hyp(f"{CFG['law']}nat_lt_witness({x}, {y}, {h})", f"Nat.add({w}, 1n+{x})", y)


def wit_le(x, y, h):
    """(w, a proof of w + x == y) from h : {is_le(x, y) == True}."""
    w = f"Nat.sub({y}, {x})"
    return w, hyp(f"{CFG['law']}nat_le_witness({x}, {y}, {h})", f"Nat.add({w}, {x})", y)


def absurd(ty, w, x, pf):
    """Empty.absurd(ty, ...) from pf : w + (1 + x) == x."""
    w, x = P(w), P(x)
    assert pf.lhs == add(w, succ(x)) and pf.rhs == x, pf
    return f"Empty.absurd({ty}, {CFG['law']}nat_succ_add_absurd({w}, {x}, {pf.text}))"



# ---------------------------------------------------------------- Bend helpers

# Lemmas on the order of Nat, written into a package's PROOF.bend under a
# prefix of its own (bend_order), and on U32 and W64 values (bend_words,
# which needs U, UL, W and WL imported): contradictions from False == True,
# x < y as x + 1 <= y, transitivity, the facts from is_lt, is_le and is_eq
# being True or False, and the bounds of a value in the exact form a law
# takes them (a U32 value below 2^32: lt32).

ORDER_TEXT = r'''def PFX.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def PFX.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : PFX.bt(_)
  Unit{}

def PFX.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : PFX.bt(_)
  Unit{}

def PFX.lt_le(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, PFX.ft(h))
    case 1n+p 1n+q:
      PFX.lt_le(p, q, h)

def PFX.nz(x: Nat, e: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PFX.tf(e))
    case 1n+ +p:
      {==}

def PFX.z0(x: Nat, e: {Nat.is_eq(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, PFX.ft(e))

def PFX.le0(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      {==}

def PFX.le_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, PFX.ft(h))
    case 1n+p 1n+q:
      PFX.le_succ(p, q, h)

def PFX.le_lt(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PFX.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, PFX.ft(h))
    case 1n+p 1n+q:
      PFX.le_lt(p, q, h)

def PFX.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      PFX.le0(c)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, PFX.ft(h1))
        case 1n+q:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, PFX.ft(h2))
            case 1n+r:
              PFX.le_trans(p, q, r, h1, h2)

def PFX.lt1(v: Nat, h: {Nat.is_lt(v, 1n) == True{} : Bool}) -> {v == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          Empty.absurd({1n == 0n : Nat}, PFX.ft(h))
        case 1n+ +q:
          Empty.absurd({2n+q == 0n : Nat}, PFX.ft(h))

def PFX.nb(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def PFX.zs(k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  %e : PFX.nb(_)
  Unit{}

def PFX.lt_sle(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(1n+x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PFX.ft(h))
    case 0n 1n+q:
      PFX.le0(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, PFX.ft(h))
    case 1n+p 1n+q:
      PFX.lt_sle(p, q, h)

def PFX.lt_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  PFX.le_lt(a, c, PFX.le_trans(1n+a, b, c, PFX.lt_sle(a, b, h1), PFX.lt_le(b, c, h2)))

def PFX.nle_lt(x: Nat, y: Nat, e: {Nat.is_le(x, y) == False{} : Bool}) -> {Nat.is_lt(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PFX.tf(e))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, PFX.tf(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      PFX.nle_lt(p, q, e)

def PFX.nlt_le(x: Nat, y: Nat, e: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, PFX.tf(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      PFX.nlt_le(p, q, e)

def PFX.one(x: Nat, h1: {Nat.is_le(x, 1n) == True{} : Bool}, h2: {Nat.is_lt(0n, x) == True{} : Bool}) -> {x == 1n : Nat}:
  match x:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, PFX.ft(h2))
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          Empty.absurd({2n+q == 1n : Nat}, PFX.ft(h1))

def PFX.old(x: Nat, h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(1n, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, PFX.ft(h))
    case 1n+ +p:
      {==}

def PFX.sub0(k: Nat) -> {Nat.sub(k, 0n) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      {==}

def PFX.mn(k: Nat) -> {Nat.min(1n+k, 1n) == 1n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      {==}

def PFX.c1(-x: Nat, -y: Nat, -c: Nat, -e: Nat, pr: {x == y : Nat} & {Nat.is_lt(c, e) == True{} : Bool}) -> {x == y : Nat}:
  (+u, +v) = pr
  u

def PFX.c2(-x: Nat, -y: Nat, -c: Nat, -e: Nat, pr: {x == y : Nat} & {Nat.is_lt(c, e) == True{} : Bool}) -> {Nat.is_lt(c, e) == True{} : Bool}:
  (+u, +v) = pr
  v
'''

WORDS_TEXT = r'''def PFX.ve(+w: Word(32n)) -> {Word.to_nat(32n, w) == U32.to_nat(U32{w}) : Nat}:
  {==}

def PFX.lt32(+x: U32) -> {Nat.is_lt(U32.to_nat(x), U.U32Nat.dbl(32n, 1n)) == True{} : Bool}:
  match x:
    case U32{+w}:
      %PFX.ve(w) : {Nat.is_lt(_, U.U32Nat.dbl(32n, 1n)) == True{} : Bool}
      UL.word_value_lt(32n, w)

def PFX.fv(+d: U32) -> {W.W64.to_nat(W.W64.from_u32(d)) == U32.to_nat(d) : Nat}:
  UL.nat_add_zero(U32.to_nat(d))

def PFX.np(+m: W.W64) -> {Nat.add(U32.to_nat(W.W64.lo(m)), U.U32Nat.dbl(32n, U32.to_nat(W.W64.hi(m)))) == W.W64.to_nat(m) : Nat}:
  %WL.parts_of(m) : {Nat.add(U32.to_nat(W.W64.lo(m)), U.U32Nat.dbl(32n, U32.to_nat(W.W64.hi(m)))) == W.W64.to_nat(_) : Nat}
  Equal.sym(Nat, W.W64.to_nat(W.W64.from_parts(W.W64.hi(m), W.W64.lo(m))), Nat.add(U32.to_nat(W.W64.lo(m)), U.U32Nat.dbl(32n, U32.to_nat(W.W64.hi(m)))), WL.to_nat_parts(W.W64.hi(m), W.W64.lo(m)))

def PFX.lo_small(+m: W.W64, +b: U32, h: {Nat.is_lt(W.W64.to_nat(m), U32.to_nat(b)) == True{} : Bool}) -> {W.W64.to_nat(m) == U32.to_nat(W.W64.lo(m)) : Nat}:
  Equal.sym(Nat, U32.to_nat(W.W64.lo(m)), W.W64.to_nat(m), UL.dbl_nowrap(32n, U32.to_nat(W.W64.hi(m)), U32.to_nat(W.W64.lo(m)), W.W64.to_nat(m), U32.to_nat(b), PFX.np(m), PFX.lt_le(W.W64.to_nat(m), U32.to_nat(b), h), PFX.lt32(b)))

def PFX.wnz(+d: W.W64, h: {W.W64.is_zero(d) == False{} : Bool}) -> {Nat.is_lt(0n, W.W64.to_nat(d)) == True{} : Bool}:
  PFX.nz(W.W64.to_nat(d), Equal.trans(Bool, Nat.is_eq(W.W64.to_nat(d), 0n), W.W64.is_zero(d), False{}, Equal.sym(Bool, W.W64.is_zero(d), Nat.is_eq(W.W64.to_nat(d), 0n), WL.eq_value(d, W.W64.zero())), h))

def PFX.wz(+d: W.W64, h: {W.W64.is_zero(d) == True{} : Bool}) -> {W.W64.to_nat(d) == 0n : Nat}:
  PFX.z0(W.W64.to_nat(d), Equal.trans(Bool, Nat.is_eq(W.W64.to_nat(d), 0n), W.W64.is_zero(d), True{}, Equal.sym(Bool, W.W64.is_zero(d), Nat.is_eq(W.W64.to_nat(d), 0n), WL.eq_value(d, W.W64.zero())), h))
'''


def bend_order(put, p):
    put("# Contradictions and the order of Nat\n")
    put(ORDER_TEXT.replace("PFX.", p + "."))
    # x + 1 < y gives x < y
    pf = calc("Nat.add(0n, 1n+x)", ("Nat.add(x, 1n)", "ring"))
    put(f"""def {p}.lt_pred(+x: Nat, +y: Nat, h: {btrue('Nat.is_lt(Nat.add(x, 1n), y)')}) -> {btrue('Nat.is_lt(x, y)')}:
  {p}.lt_trans(x, Nat.add(x, 1n), y, {lt_from("x", "Nat.add(x, 1n)", "0n", pf)}, h)
""")
    # x <= 2 (y - 1), y >= 1: x < 2 y
    w0, W0 = wit_le("x", "Nat.double(Nat.sub(y, 1n))", "h")
    Y1 = hyp(f"{CFG['law']}nat_lt_witness(0n, y, hy)", "Nat.add(Nat.sub(y, 1n), 1n)", "y")
    pf = calc(f"Nat.add(Nat.add({w0}, 1n), 1n+x)",
              (f"Nat.add(Nat.add({w0}, x), 2n)", "ring"),
              ("Nat.add(Nat.double(Nat.sub(y, 1n)), 2n)", W0),
              ("Nat.double(Nat.add(Nat.sub(y, 1n), 1n))", "ring"),
              ("Nat.double(y)", Y1))
    put(f"""def {p}.le_lt2(+x: Nat, +y: Nat, h: {btrue('Nat.is_le(x, Nat.double(Nat.sub(y, 1n)))')}, hy: {btrue('Nat.is_lt(0n, y)')}) -> {btrue('Nat.is_lt(x, Nat.double(y))')}:
  {lt_from("x", "Nat.double(y)", f"Nat.add({w0}, 1n)", pf)}
""")


def bend_u32(put, p):
    """the bound of a U32 value (lt32); needs U imported"""
    i = WORDS_TEXT.index("def PFX.fv(")
    put("# The bound of a U32 value, in the exact form a law takes it\n")
    put(WORDS_TEXT[:i].rstrip("\n").replace("PFX.", p + ".") + "\n")


def bend_words(put, p):
    """bend_u32, and W64 values: the halves, and a W64 below a U32; needs
    U, UL, W and WL (bend-osdev-word64's LAWS.bend) imported"""
    bend_u32(put, p)
    i = WORDS_TEXT.index("def PFX.fv(")
    put("# W64 values: the halves, and a W64 below a U32\n")
    put(WORDS_TEXT[i:].replace("PFX.", p + "."))


# ---------------------------------------------------------------- law files


def law_aliases(files):
    """{law name: alias} for the laws of each (path, alias) in files: a
    proof that uses another package's laws imports the law file that holds
    each of them under its own alias."""
    out = {}
    for path, alias in files:
        for line in open(path).read().split("\n"):
            if line.startswith("law ") and line.endswith(":"):
                out[line[4:-1]] = alias
    return out


def realias(text, old, aliases):
    """text with each call old.name( of a law in aliases as alias.name(."""
    for name, alias in aliases.items():
        text = text.replace(f"{old}.{name}(", f"{alias}.{name}(")
    return text
