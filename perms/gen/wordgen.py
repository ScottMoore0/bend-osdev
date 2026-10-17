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
