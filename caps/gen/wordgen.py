"""Generates per-bit induction lemmas over Word(n) for Bend.

A lemma: name, word variables, hypotheses (subset pairs), and a goal
('sub', A, B) meaning {SUB(n, A, B) == True} or ('eq', A, B) meaning {A == B : Word(n)}.
Expressions: a variable name (str), ('and', x, y), ('or', x, y), ('not', x), ('zero',), ('all',).
"""
import itertools

SUB = "CapBits.subset"
ALL = "CapBits.all"
ABSURD = "bits.absurd"
ABSURD_EQ = "bits.absurd_eq"

def show(e, n, sub=None):
    if isinstance(e, str):
        return sub[e] if sub else e
    op = e[0]
    if op == 'zero':
        return "Word.zero(%s)" % n
    if op == 'all':
        return "%s(%s)" % (ALL, n)
    if op == 'not':
        return "Word.not(%s, %s)" % (n, show(e[1], n, sub))
    return "Word.%s(%s, %s, %s)" % (op, n, show(e[1], n, sub), show(e[2], n, sub))

def ev(e, env):
    if isinstance(e, str):
        return env[e]
    op = e[0]
    if op == 'zero': return False
    if op == 'all': return True
    if op == 'not': return not ev(e[1], env)
    a, b = ev(e[1], env), ev(e[2], env)
    return (a and b) if op == 'and' else (a or b)

def tail_sub(vs):
    return {v: v + "t" for v in vs}

def B(b):
    return "True{}" if b else "False{}"

def goal_type(goal, n, sub=None):
    kind, a, b = goal
    if kind == 'sub':
        return "{%s(%s, %s, %s) == True{} : Bool}" % (SUB, n, show(a, n, sub), show(b, n, sub))
    return "{%s == %s : Word(%s)}" % (show(a, n, sub), show(b, n, sub), n)

def lemma(name, vs, hyps, goal):
    params = ", ".join("%s: Word(n)" % v for v in vs)
    sig = "def %s(n: Nat%s)" % (name, (", " + params) if vs else "")
    parts = ["{%s(n, %s, %s) == True{} : Bool}" % (SUB, show(a, 'n'), show(b, 'n')) for a, b in hyps]
    out = [sig + " -> " + " -> ".join(parts + [goal_type(goal, 'n')]) + ":"]
    hl = "".join("h%d => " % i for i in range(len(hyps)))
    out.append("  match n:")
    out.append("    case 0n:")
    if goal[0] == 'eq':
        out.append("      match " + " ".join(vs) + ":")
        out.append("        case " + " ".join("WNil{}" for v in vs) + ":")
        out.append("          " + hl + "{==}")
    else:
        out.append("      " + hl + "{==}")
    out.append("    case 1n+n1:")
    out.append("      match " + " ".join(vs) + ":")
    ts = tail_sub(vs)
    for bits in itertools.product([True, False], repeat=len(vs)):
        env = dict(zip(vs, bits))
        pat = " ".join("WCon{%s, +%st}" % (B(b), v) for v, b in zip(vs, bits))
        out.append("        case %s:" % pat)
        full = {v: "WCon{%s, %st}" % (B(b), v) for v, b in zip(vs, bits)}
        bad = None
        for i, (a, b) in enumerate(hyps):
            if ev(a, env) and not ev(b, env):
                bad = i
                break
        if bad is not None:
            if goal[0] == 'sub':
                body = "%s(%s(1n+n1, %s, %s), h%d)" % (ABSURD, SUB, show(goal[1], '1n+n1', full), show(goal[2], '1n+n1', full), bad)
            else:
                body = "%s(Word(1n+n1), %s, %s, h%d)" % (ABSURD_EQ, show(goal[1], '1n+n1', full), show(goal[2], '1n+n1', full), bad)
        else:
            rec = "%s(n1%s)" % (name, "".join(", " + ts[v] for v in vs)) + "".join("(h%d)" % i for i in range(len(hyps)))
            if goal[0] == 'sub':
                assert not (ev(goal[1], env) and not ev(goal[2], env)), (name, env)
                body = rec
            else:
                ga, gb = ev(goal[1], env), ev(goal[2], env)
                assert ga == gb, (name, env)
                body = "Equal.cong(Word(n1), Word(1n+n1), w => WCon{%s, w}, %s, %s, %s)" % (B(ga), show(goal[1], 'n1', ts), show(goal[2], 'n1', ts), rec)
        out.append("          " + hl + body)
    return "\n".join(out) + "\n"

# Lemmas on capability sets. A set is a native U32 (capabilities 0 to 31) and
# a Word(9n) (32 to 40); each set lemma splits its sets into the two parts,
# with the U32 opened to its Word(32n), and applies the per-bit lemma of the
# same name at each part's width. set.sub_intro, set.sub_lo, set.sub_hi and
# set.eq_intro (hand-written, in PROOF.bend) move between a set and its parts.
SET = "C.CapSet"
SETW = "C.CapSetW"
LO, HI = "32n", "9n"

def show_set(e):
    if isinstance(e, str):
        return e
    op = e[0]
    if op == 'zero':
        return SET + ".empty()"
    if op == 'all':
        return SET + ".full()"
    if op == 'and' and not isinstance(e[2], str) and e[2][0] == 'not':
        return "%s.minus(%s, %s)" % (SET, show_set(e[1]), show_set(e[2][1]))
    if op in ('and', 'or'):
        return "%s.%s(%s, %s)" % (SET, "inter" if op == 'and' else "union", show_set(e[1]), show_set(e[2]))
    raise ValueError("no set form for %r" % (e,))

def set_goal_type(goal):
    kind, a, b = goal
    if kind == 'sub':
        return "{%s.subset(%s, %s) == True{} : Bool}" % (SET, show_set(a), show_set(b))
    return "{%s == %s : %s()}" % (show_set(a), show_set(b), SET)

def set_lemma(name, vs, hyps, goal, bits_name, set_name):
    sig = "def %s(%s)" % (set_name, ", ".join("%s: %s()" % (v, SET) for v in vs))
    parts = ["{%s.subset(%s, %s) == True{} : Bool}" % (SET, show_set(a), show_set(b)) for a, b in hyps]
    out = [sig + " -> " + " -> ".join(parts + [set_goal_type(goal)]) + ":"]
    out.append("  match " + " ".join(vs) + ":")
    out.append("    case " + " ".join("%s{U32{+%sl}, +%sh}" % (SETW, v, v) for v in vs) + ":")
    hl = "".join("+h%d => " % i for i in range(len(hyps)))
    lo = {v: v + "l" for v in vs}
    hi = {v: v + "h" for v in vs}
    # an expression's low and high parts, as the four arguments of the set.* helpers
    four = lambda a, b: "%s, %s, %s, %s" % (show(a, LO, lo), show(b, LO, lo), show(a, HI, hi), show(b, HI, hi))
    def part(n, sub, which):
        hs = "".join("(set.sub_%s(%s)(h%d))" % (which, four(a, b), i) for i, (a, b) in enumerate(hyps))
        return "%s(%s, %s)%s" % (bits_name, n, ", ".join(sub[v] for v in vs), hs)
    helper = "set.sub_intro(%s)(%s)(%s)" if goal[0] == 'sub' else "set.eq_intro(%s, %s, %s)"
    body = helper % (four(goal[1], goal[2]), part(LO, lo, "lo"), part(HI, hi, "hi"))
    out.append("      " + hl + body)
    return "\n".join(out) + "\n"
