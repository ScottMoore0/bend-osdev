#!/usr/bin/env python3
"""Writes itree/proof_heights.bend: the Nat lemmas about heights that the
balance proofs (PROOF_balance.bend) use.

  python3 gen/heights.py           rewrite proof_heights.bend
  python3 gen/heights.py --check   only check that it is up to date

Each lemma is a claim about a few Nat variables (heights), built from
Nat.is_le, Nat.is_lt, Nat.is_eq, Nat.max, successor and Bool connectives:
some hypotheses (each a Bool equal to True or False) give a conclusion.
Every such claim used here is invariant under adding one to every
variable, so it is proved by induction on all the variables at once:

  * when every variable is a successor, every comparison in the claim
    takes one step to the claim about the predecessors (Nat.cmp and
    Nat.max both peel a successor off both sides), so the claim is the
    induction hypothesis;
  * when some variable is 0, the hypotheses bound the others by small
    numbers, and the generator splits the variable that the first
    undecided hypothesis (or the conclusion) is waiting on, until every
    hypothesis is decided: a branch where one comes out wrong is absurd,
    and in every other branch the conclusion computes to True.

The splitting mirrors how the checker evaluates Base's definitions (each
matches its first argument first), so a branch is decided exactly when
the checker can decide it. A claim that is not shift-invariant (it
compares a variable with a constant) is proved by the splitting alone.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "proof_heights.bend")

# Terms. Nat: ("v", name) ("z",) ("s", t) ("max", a, b)
# Bool: ("le"|"lt"|"eq", a, b) ("and", x, y) ("or", x, y) ("not", x)
#       ("T",) ("F",) ("def", name, args)


def V(n):
    return ("v", n)


def S(t, k=1):
    for _ in range(k):
        t = ("s", t)
    return t


def mx(a, b):
    return ("max", a, b)


def le(a, b):
    return ("le", a, b)


def lt(a, b):
    return ("lt", a, b)


def eq(a, b):
    return ("eq", a, b)


def AND(x, y):
    return ("and", x, y)


def OR(x, y):
    return ("or", x, y)


def NOT(x):
    return ("not", x)


# Abbreviations, defined in the generated file, unfolded by the checker.
# name -> (parameters, body)
DEFS = {}
DEF_ORDER = []


def define(name, params, body, doc):
    DEFS[name] = (params, body, doc)
    DEF_ORDER.append(name)


def call(name, *args):
    return ("def", name, tuple(args))


a_, b_, x_ = V("a"), V("b"), V("x")
define("nr", ["a", "b"], AND(le(a_, S(b_)), le(b_, S(a_))),
       "a and b differ by at most one")
define("nr2", ["a", "b"], AND(le(a_, S(b_, 2)), le(b_, S(a_, 2))),
       "a and b differ by at most two")
define("grow", ["a", "x"], AND(le(a_, x_), le(x_, S(a_))),
       "x is a or a + 1")
define("shrink", ["a", "x"], AND(le(x_, a_), le(a_, S(x_))),
       "x is a or a - 1")
define("balh", ["a", "b", "x"],
       AND(le(mx(a_, b_), x_), AND(le(x_, S(mx(a_, b_))), OR(NOT(call("nr", a_, b_)), eq(x_, S(mx(a_, b_)))))),
       "x is the larger of a and b, or one more; one more when a and b differ by at most one\n"
       "# (the height of a node rebalanced from subtrees of heights a and b)")


def nr(a, b):
    return call("nr", a, b)


def nr2(a, b):
    return call("nr2", a, b)


def grow(a, x):
    return call("grow", a, x)


def shrink(a, x):
    return call("shrink", a, x)


def balh(a, b, x):
    return call("balh", a, b, x)


def subst_def(body, params, args):
    m = dict(zip(params, args))

    def go(t):
        if t[0] == "v":
            return m.get(t[1], t)
        if t[0] in ("z", "T", "F"):
            return t
        if t[0] == "def":
            return ("def", t[1], tuple(go(u) for u in t[2]))
        return (t[0],) + tuple(go(u) for u in t[1:])
    return go(body)


# Evaluation to head form, as the checker does. env: var -> term

class Stuck(Exception):
    def __init__(self, var):
        self.var = var
        self.bounded = False


def closed(t, env):
    t = resolve(t, env)

    def go(u):
        if u[0] == "v":
            return False
        if u[0] in ("z", "T", "F"):
            return True
        if u[0] == "def":
            return all(go(w) for w in u[2])
        return all(go(w) for w in u[1:])
    return go(t)


def whnf_nat(t, env):
    while True:
        k = t[0]
        if k == "v":
            if t[1] in env:
                t = env[t[1]]
                continue
            raise Stuck(t[1])
        if k in ("z", "s"):
            return t
        if k == "max":
            ra = whnf_nat(t[1], env)
            if ra[0] == "z":
                t = t[2]
                continue
            rb = whnf_nat(t[2], env)
            if rb[0] == "z":
                return ra
            return ("s", ("max", ra[1], rb[1]))
        raise ValueError(t)


def cmp(a, b, env):
    while True:
        try:
            ra = whnf_nat(a, env)
        except Stuck as st:
            st.bounded = closed(b, env)
            raise
        try:
            rb = whnf_nat(b, env)
        except Stuck as st:
            st.bounded = closed(ra, env)
            raise
        if ra[0] == "z":
            return "EQ" if rb[0] == "z" else "LT"
        if rb[0] == "z":
            return "GT"
        a, b = ra[1], rb[1]


def whnf_bool(t, env):
    k = t[0]
    if k == "T":
        return True
    if k == "F":
        return False
    if k in ("le", "lt", "eq"):
        c = cmp(t[1], t[2], env)
        return {"le": c != "GT", "lt": c == "LT", "eq": c == "EQ"}[k]
    if k == "and":
        return whnf_bool(t[2], env) if whnf_bool(t[1], env) else False
    if k == "or":
        return True if whnf_bool(t[1], env) else whnf_bool(t[2], env)
    if k == "not":
        return not whnf_bool(t[1], env)
    if k == "def":
        params, body, _ = DEFS[t[1]]
        return whnf_bool(subst_def(body, params, t[2]), env)
    raise ValueError(t)


def evalb(t, env):
    """True, False, or (the variable it waits on, whether the comparison
    waiting on it has a closed other side, so that splitting it ends)."""
    try:
        return whnf_bool(t, env)
    except Stuck as s:
        return (s.var, s.bounded)


# Printing

def resolve(t, env):
    """t with the variables bound in env replaced, recursively."""
    if t[0] == "v":
        return resolve(env[t[1]], env) if t[1] in env else t
    if t[0] in ("z", "T", "F"):
        return t
    if t[0] == "def":
        return ("def", t[1], tuple(resolve(u, env) for u in t[2]))
    return (t[0],) + tuple(resolve(u, env) for u in t[1:])


def pn(t):
    k = 0
    while t[0] == "s":
        k += 1
        t = t[1]
    if t[0] == "z":
        return "%dn" % k
    if t[0] == "v":
        inner = t[1]
    elif t[0] == "max":
        inner = "Nat.max(%s, %s)" % (pn(t[1]), pn(t[2]))
    else:
        raise ValueError(t)
    return inner if k == 0 else "%dn+%s" % (k, inner)


def pb(t):
    k = t[0]
    if k == "T":
        return "True{}"
    if k == "F":
        return "False{}"
    if k in ("le", "lt", "eq"):
        return "Nat.is_%s(%s, %s)" % (k, pn(t[1]), pn(t[2]))
    if k == "and":
        return "Bool.and(%s, %s)" % (pb(t[1]), pb(t[2]))
    if k == "or":
        return "Bool.or(%s, %s)" % (pb(t[1]), pb(t[2]))
    if k == "not":
        return "Bool.not(%s)" % pb(t[1])
    if k == "def":
        return "%s(%s)" % (t[1], ", ".join(pn(u) for u in t[2]))
    raise ValueError(t)


def bval(v):
    return "True{}" if v else "False{}"


# Lemma generation
#
# The checker matches binders only in order: once a later parameter has
# been matched, an earlier one (or a variable bound by its pattern) can no
# longer be. So each case where some variable is 0 goes to a helper def
# whose parameters (the remaining variables) come in an order chosen here,
# and the helper splits them in that order: each variable is split one
# successor at a time (each new pattern variable is matched next, which is
# allowed) until a hypothesis comes out wrong, the conclusion computes to
# True, or the variable is known to be 0 or at least DMAX; then the next.

DMAX = 6
NL = chr(10)


class Fail(Exception):
    pass


class Gen:
    def __init__(self):
        self.fresh = 0
        self.leaves = 0

    def name(self):
        self.fresh += 1
        return "n%d" % self.fresh

    def decided(self, hyps, concl, env, ind):
        """The leaf if hyps or concl decide the case under env, else None."""
        pad = "  " * ind
        for hname, term, want in hyps:
            r = evalb(term, env)
            if r is (not want):
                goal = "{%s == True{} : Bool}" % pb(resolve(concl, env))
                ab = "ab.ft" if want else "ab.tf"
                return [pad + "Empty.absurd(%s, %s(%s))" % (goal, ab, hname)]
        if evalb(concl, env) is True:
            return [pad + "{==}"]
        return None

    def enum(self, hyps, concl, order, idx, cur, depth, env, ind):
        """Lines deciding every case; order[idx] is being split, its current
        pattern variable is cur, split depth times so far."""
        leaf = self.decided(hyps, concl, env, ind)
        if leaf is not None:
            self.leaves += 1
            return leaf
        if idx >= len(order):
            raise Fail("undecided: %s under %s" % (pb(concl), env))
        if depth >= DMAX:
            nxt = order[idx + 1] if idx + 1 < len(order) else None
            return self.enum(hyps, concl, order, idx + 1, nxt, 0, env, ind)
        pad = "  " * ind
        p = self.name()
        e0 = dict(env)
        e0[cur] = ("z",)
        nxt = order[idx + 1] if idx + 1 < len(order) else None
        lines = [pad + "match %s:" % cur, pad + "  case 0n:"]
        lines += self.enum(hyps, concl, order, idx + 1, nxt, 0, e0, ind + 2)
        lines.append(pad + "  case 1n+%s:" % p)
        e1 = dict(env)
        e1[cur] = ("s", ("v", p))
        lines += self.enum(hyps, concl, order, idx, p, depth + 1, e1, ind + 2)
        return lines


def helper(name, doc, free, hyps, concl, env):
    """A def deciding concl under env from hyps, over the variables free, in
    the best order found. Returns (text, leaves)."""
    import itertools
    best = None
    for order in itertools.permutations(free):
        g = Gen()
        try:
            body = g.enum(hyps, concl, list(order), 0, order[0] if order else None, 0, env, 1)
        except Fail:
            continue
        if best is None or g.leaves < best[0]:
            best = (g.leaves, order, body)
    if best is None:
        raise RuntimeError("no order decides %s under %s" % (pb(concl), env))
    leaves, order, body = best
    params = ["%s: Nat" % v for v in order] + ["%s: {%s == %s : Bool}" % (h, pb(resolve(t, env)), bval(w)) for h, t, w in hyps]
    head = "def %s(%s) -> {%s == True{} : Bool}:" % (name, ", ".join(params), pb(resolve(concl, env)))
    lines = (["# " + doc] if doc else []) + [head] + body
    return NL.join(lines) + NL, leaves, order


def lemma(name, doc, vars_, hyps, concl, induct=True):
    """hyps: list of (term, value). Returns the Bend text of the lemma (its
    helpers first) and its number of leaves."""
    hs = [("e%d" % (i + 1), t, v) for i, (t, v) in enumerate(hyps)]
    hnames = [h for h, _, _ in hs]
    params = ["%s: Nat" % v for v in vars_] + ["%s: {%s == %s : Bool}" % (h, pb(t), bval(v)) for h, t, v in hs]
    head = "def %s(%s) -> {%s == True{} : Bool}:" % (name, ", ".join(params), pb(concl))
    texts = []
    total = 0
    lines = []
    if doc:
        lines += ["# " + d for d in doc.split(NL)]
    lines.append(head)
    if not induct:
        text, leaves, order = helper(name + ".go", "", vars_, hs, concl, {})
        texts.append(text)
        total += leaves
        lines.append("  %s.go(%s)" % (name, ", ".join(list(order) + hnames)))
    else:
        env = {}
        preds = []

        def top(i, ind):
            nonlocal total
            pad = "  " * ind
            v = vars_[i]
            p = v + "q"
            out = [pad + "match %s:" % v, pad + "  case 0n:"]
            e0 = dict(env)
            e0[v] = ("z",)
            free = preds + vars_[i + 1:]
            text, leaves, order = helper("%s.z%d" % (name, i + 1), "", free, hs, concl, e0)
            texts.append(text)
            total += leaves
            out.append("  " * (ind + 2) + "%s.z%d(%s)" % (name, i + 1, ", ".join(list(order) + hnames)))
            out.append(pad + "  case 1n+%s:" % p)
            env[v] = ("s", ("v", p))
            preds.append(p)
            if i + 1 < len(vars_):
                out += top(i + 1, ind + 2)
            else:
                out.append("  " * (ind + 2) + "%s(%s)" % (name, ", ".join(preds + hnames)))
            return out
        lines += top(0, 1)
    return NL.join(texts) + NL + NL.join(lines) + NL, total


def lemmas():
    a, b, c, h, x, y = V("a"), V("b"), V("c"), V("h"), V("x"), V("y")
    a1, b1, b2, h2, ap, bp = V("a1"), V("b1"), V("b2"), V("h2"), V("ap"), V("bp")
    L = []

    def add(*args, **kw):
        L.append(lemma(*args, **kw))

    # bal without a rotation: the subtrees differ by at most one, and the
    # node's height is one more than the larger
    add("mk_nr", "neither subtree is two higher: they differ by at most one",
        ["a", "b"], [(lt(S(b), a), False), (lt(S(a), b), False)], nr(a, b))
    add("mk_balh", "neither subtree is two higher: the node's height is one more than the larger",
        ["a", "b"], [(lt(S(b), a), False), (lt(S(a), b), False)], balh(a, b, S(mx(a, b))))

    # rot_r, single: l = (a, b) of height h, two higher than r (c); a >= b
    sr = [(lt(a, b), False), (eq(h, S(mx(a, b))), True), (nr(a, b), True), (lt(S(c), h), True), (nr2(h, c), True)]
    add("rr1_a", "single right rotation: the new right child is balanced",
        ["a", "b", "c", "h"], sr, nr(b, c))
    add("rr1_b", "single right rotation: the new root is balanced",
        ["a", "b", "c", "h"], sr, nr(a, S(mx(b, c))))
    add("rr1_h", "single right rotation: the height",
        ["a", "b", "c", "h"], sr, balh(h, c, S(mx(a, S(mx(b, c))))))
    # rot_r, double: l = (a, (b1, b2) of height h2) of height h
    dr = [(lt(a, h2), True), (eq(h, S(mx(a, h2))), True), (nr(a, h2), True), (lt(S(c), h), True),
          (nr2(h, c), True), (eq(h2, S(mx(b1, b2))), True), (nr(b1, b2), True)]
    dv = ["a", "b1", "b2", "c", "h", "h2"]
    add("rr2_a", "double right rotation: the new left child is balanced", dv, dr, nr(a, b1))
    add("rr2_b", "double right rotation: the new right child is balanced", dv, dr, nr(b2, c))
    add("rr2_c", "double right rotation: the new root is balanced", dv, dr, nr(S(mx(a, b1)), S(mx(b2, c))))
    add("rr2_h", "double right rotation: the height", dv, dr,
        balh(h, c, S(mx(S(mx(a, b1)), S(mx(b2, c))))))
    # rot_l, single: r = (b, a) of height h, two higher than l (c); a >= b
    # (a = height of rr, b = height of rl)
    sl = [(lt(a, b), False), (eq(h, S(mx(b, a))), True), (nr(b, a), True), (lt(S(c), h), True), (nr2(c, h), True)]
    add("rl1_a", "single left rotation: the new left child is balanced",
        ["a", "b", "c", "h"], sl, nr(c, b))
    add("rl1_b", "single left rotation: the new root is balanced",
        ["a", "b", "c", "h"], sl, nr(S(mx(c, b)), a))
    add("rl1_h", "single left rotation: the height",
        ["a", "b", "c", "h"], sl, balh(c, h, S(mx(S(mx(c, b)), a))))
    # rot_l, double: r = ((b1, b2) of height h2, a) of height h
    dl = [(lt(a, h2), True), (eq(h, S(mx(h2, a))), True), (nr(h2, a), True), (lt(S(c), h), True),
          (nr2(c, h), True), (eq(h2, S(mx(b1, b2))), True), (nr(b1, b2), True)]
    add("rl2_a", "double left rotation: the new left child is balanced", dv, dl, nr(c, b1))
    add("rl2_b", "double left rotation: the new right child is balanced", dv, dl, nr(b2, a))
    add("rl2_c", "double left rotation: the new root is balanced", dv, dl, nr(S(mx(c, b1)), S(mx(b2, a))))
    add("rl2_h", "double left rotation: the height", dv, dl,
        balh(c, h, S(mx(S(mx(c, b1)), S(mx(b2, a))))))

    # insertion: a subtree grows by at most one
    add("il_nr2", "insertion on the left: the subtrees differ by at most two",
        ["a", "ap", "b"], [(nr(a, b), True), (grow(a, ap), True)], nr2(ap, b))
    add("il_h", "insertion on the left: the node grows by at most one",
        ["a", "ap", "b", "h", "x"],
        [(eq(h, S(mx(a, b))), True), (nr(a, b), True), (grow(a, ap), True), (balh(ap, b, x), True)], grow(h, x))
    add("ir_nr2", "insertion on the right: the subtrees differ by at most two",
        ["a", "b", "bp"], [(nr(a, b), True), (grow(b, bp), True)], nr2(a, bp))
    add("ir_h", "insertion on the right: the node grows by at most one",
        ["a", "b", "bp", "h", "x"],
        [(eq(h, S(mx(a, b))), True), (nr(a, b), True), (grow(b, bp), True), (balh(a, bp, x), True)], grow(h, x))
    m = V("m")
    add("ieq_h", "replacing the root's entry keeps the height",
        ["h", "m"], [(eq(h, m), True)], grow(h, m))

    # removal: a subtree shrinks by at most one
    add("rml_nr2", "removal on the left: the subtrees differ by at most two",
        ["a", "ap", "b"], [(nr(a, b), True), (shrink(a, ap), True)], nr2(ap, b))
    add("rml_h", "removal on the left: the node shrinks by at most one",
        ["a", "ap", "b", "h", "x"],
        [(eq(h, S(mx(a, b))), True), (nr(a, b), True), (shrink(a, ap), True), (balh(ap, b, x), True)], shrink(h, x))
    add("rmr_nr2", "removal on the right: the subtrees differ by at most two",
        ["a", "b", "bp"], [(nr(a, b), True), (shrink(b, bp), True)], nr2(a, bp))
    add("rmr_h", "removal on the right: the node shrinks by at most one",
        ["a", "b", "bp", "h", "x"],
        [(eq(h, S(mx(a, b))), True), (nr(a, b), True), (shrink(b, bp), True), (balh(a, bp, x), True)], shrink(h, x))
    add("node_shrink", "a node of height h less something of the node's subtrees' height shrinks by at most one",
        ["h", "m", "x"], [(eq(h, m), True), (shrink(m, x), True)], shrink(h, x))
    # del_min: the node (t, r) loses its first entry; t has height h2 and
    # becomes x, the result has height y
    add("dm_leaf", "del_min of a node with an empty left subtree: its right subtree",
        ["b"], [(nr(("z",), b), True)], shrink(S(b), b), induct=False)
    add("dm_nr2", "del_min, the left subtree shrunk: the subtrees differ by at most two",
        ["b", "h2", "x"], [(shrink(h2, x), True), (nr(h2, b), True)], nr2(x, b))
    add("dm_h", "del_min: the node shrinks by at most one",
        ["b", "h2", "x", "y"], [(shrink(h2, x), True), (nr(h2, b), True), (balh(x, b, y), True)], shrink(S(mx(h2, b)), y))
    # merge(l, r) of the subtrees of a node of height h
    add("mg_leaf", "merge with an empty right subtree: the left one",
        ["a", "h"], [(eq(h, S(mx(a, ("z",)))), True), (nr(a, ("z",)), True)], shrink(h, a), induct=False)
    add("mg_nr2", "merge: the left subtree and the right one less its first entry differ by at most two",
        ["a", "b", "x"], [(nr(a, b), True), (shrink(b, x), True)], nr2(a, x))
    add("mg_h", "merge: the node shrinks by at most one",
        ["a", "b", "h", "x", "y"],
        [(eq(h, S(mx(a, b))), True), (nr(a, b), True), (shrink(b, x), True), (balh(a, x, y), True)], shrink(h, y))

    # the size bound: a node of height at least x + 2 has both subtrees of
    # height at least x
    add("sz_l", "a node of height at least x + 2: its left subtree has height at least x",
        ["a", "b", "h", "x"], [(le(S(x, 2), h), True), (eq(h, S(mx(a, b))), True), (nr(a, b), True)], le(x, a))
    add("sz_r", "a node of height at least x + 2: its right subtree has height at least x",
        ["a", "b", "h", "x"], [(le(S(x, 2), h), True), (eq(h, S(mx(a, b))), True), (nr(a, b), True)], le(x, b))
    return L


HEADER = """# Generated by gen/heights.py; do not edit by hand.
#
# Nat lemmas about the heights of AVL nodes, for PROOF_balance.bend. Each
# is proved by induction on all its variables at once (every comparison
# here is between two variables, so adding one to each changes nothing),
# and, where one variable is 0, by splitting the others until each
# hypothesis is decided: see gen/heights.py.
import Base

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def ab.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

"""


def render():
    out = [HEADER]
    for name in DEF_ORDER:
        params, body, doc = DEFS[name]
        out.append("# %s\ndef %s(%s) -> Bool:\n  %s\n\n" % (doc, name, ", ".join("+%s: Nat" % p for p in params), pb(body)))
    total = 0
    for text, leaves in lemmas():
        out.append(text + "\n")
        total += leaves
    return "".join(out).rstrip("\n") + "\n", total


def main():
    text, total = render()
    if "--check" in sys.argv[1:]:
        with open(OUT, encoding="utf-8", newline="") as f:
            if f.read() != text:
                print("proof_heights.bend differs from what gen/heights.py generates")
                sys.exit(1)
        print("proof_heights.bend is up to date")
        return
    with open(OUT, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print("wrote proof_heights.bend (%d leaves)" % total)


if __name__ == "__main__":
    main()
