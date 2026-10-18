#!/usr/bin/env python3
"""Differential test cases for bend-osdev-selinux.

Writes ref/cases.bend (a Bend program that loads random small CIL policies
and asks each the security server's questions) and ref/expected.txt (the
answers of an independent model of the same semantics, below).

The model is written in Python from the same documentation the package
follows (the SELinux Notebook, the CIL reference, the libselinux man
pages), by the same author, so it is independent code but not an
independent reading of the documents: it catches implementation slips
(the CIL reader and compiler, attribute expansion, booleans, constraints,
MLS, transitions, decisions), not shared misreadings. secilc, when
installed, checks that it accepts exactly the generated policies the
package loads (see run.sh). The model refuses a policy as the package
does: a constraint operand word misused (`(eq t2 t1)`: t1 is the source
type there, not a type named t1), a name transition inside a booleanif, a
neverallow violation, and conflicting type or role transitions.

The model reads the generated CIL text with its own S-expression reader
and compiler, not the generator's data, so the package's CIL subset is
tested from text.
"""
import os, random, sys

# ---------------------------------------------------------------- reader

def read_sexps(text):
    out, stack, i, n = [], [[]], 0, len(text)
    while i < n:
        ch = text[i]
        if ch == ';':
            while i < n and text[i] != '\n':
                i += 1
        elif ch in ' \t\r\n':
            i += 1
        elif ch == '(':
            stack.append([]); i += 1
        elif ch == ')':
            top = stack.pop(); stack[-1].append(top); i += 1
        elif ch == '"':
            j = text.index('"', i + 1)
            stack[-1].append(text[i + 1:j]); i = j + 1
        else:
            j = i
            while j < n and text[j] not in ' \t\r\n();"':
                j += 1
            stack[-1].append(text[i:j]); i = j
    assert len(stack) == 1
    return stack[0]

# ---------------------------------------------------------------- model

class Policy:
    pass

OPS = ('and', 'or', 'xor', 'not', 'all', 'range')

# the operand words of a constraint expression: never a user, role or type
# of that name; a right operand that is one must be the left one's partner
WORDS = {'u1', 'u2', 'u3', 'r1', 'r2', 'r3', 't1', 't2', 't3', 'l1', 'l2', 'h1', 'h2'}
PARTNER = {'u1': 'u2', 'r1': 'r2', 't1': 't2'}

def cons_error(e):
    op = e[0]
    if op in ('and', 'or'):
        return cons_error(e[1]) or cons_error(e[2])
    if op == 'not':
        return cons_error(e[1])
    x, y = e[1], e[2]
    if x in ('l1', 'h1', 'l2', 'h2'):
        return None
    if isinstance(y, str) and y in WORDS and PARTNER.get(x) != y:
        return 'bad statement: constraint operand ' + y
    return None

def compile_error(st):
    """The compiler's first refusal, in statement order, of the rules the
    generator can get wrong: a misused constraint operand, and a name
    transition inside a booleanif."""
    for s in st:
        if s[0] in ('constrain', 'mlsconstrain'):
            err = cons_error(s[2])
            if err:
                return err
        elif s[0] == 'booleanif':
            for br in s[2:]:
                for r in br[1:]:
                    if r[0] == 'typetransition' and len(r) == 6:
                        return 'bad statement: booleanif: typetransition with an object name'
    return None

def compile_cil(stmts):
    P = Policy()
    st = [s for s in stmts if isinstance(s, list)]
    P.error = compile_error(st)
    if P.error:
        return P
    kw = lambda k: [s for s in st if s[0] == k]
    P.types, P.attr = [], []          # names in the type namespace, in order
    for s in st:
        if s[0] in ('type', 'typeattribute'):
            P.types.append(s[1]); P.attr.append(s[0] == 'typeattribute')
    P.tid = {n: i for i, n in enumerate(P.types)}
    for s in kw('typealiasactual'):
        P.tid[s[1]] = P.tid[s[2]]
    P.roles = ['object_r'] + [s[1] for s in kw('role') if s[1] != 'object_r']
    P.rid = {n: i for i, n in enumerate(P.roles)}
    P.users = [s[1] for s in kw('user')]
    P.uid = {n: i for i, n in enumerate(P.users)}
    commons = {s[1]: list(s[2]) for s in kw('common')}
    cc = {s[1]: s[2] for s in kw('classcommon')}
    P.classes = [(s[1], commons.get(cc.get(s[1]), []) + list(s[2])) for s in kw('class')]
    P.cid = {n: i for i, (n, _) in enumerate(P.classes)}
    P.bools = [s[1] for s in kw('boolean')]
    P.bid = {n: i for i, n in enumerate(P.bools)}
    P.state = [s[2] == 'true' for s in kw('boolean')]
    so = kw('sensitivityorder'); P.sens = list(so[0][1]) if so else []
    co = kw('categoryorder'); P.cats = list(co[0][1]) if co else []
    P.sid = {n: i for i, n in enumerate(P.sens)}
    P.gid = {n: i for i, n in enumerate(P.cats)}
    m = kw('mls'); P.mls = bool(m) and m[0][1] == 'true'
    real = frozenset(i for i, a in enumerate(P.attr) if not a)
    # attributes: each name stands for its members
    facts = {}
    for s in kw('typeattributeset'):
        facts.setdefault(P.tid[s[1]], []).append(s[2])
    memo = {}
    def tset(e):
        if isinstance(e, str):
            if e == 'all':
                return real
            i = P.tid[e]
            if not P.attr[i]:
                return frozenset([i])
            if i not in memo:
                memo[i] = frozenset().union(*[tset(x) for x in facts.get(i, [])])
            return memo[i]
        if e and e[0] in OPS:
            a = [tset(x) for x in e[1:]]
            return {'and': lambda: a[0] & a[1], 'or': lambda: frozenset().union(*a),
                    'xor': lambda: a[0] ^ a[1], 'not': lambda: real - a[0],
                    'all': lambda: real | frozenset().union(*a)}[e[0]]()
        return frozenset().union(*[tset(x) for x in e])
    P.tset = tset
    P.members = {i: tset(P.types[i]) for i in range(len(P.types)) if P.attr[i]}
    def pset(cls, e):
        perms = P.classes[P.cid[cls]][1]
        univ = frozenset(range(len(perms)))
        def go(e):
            if isinstance(e, str):
                return univ if e == 'all' else frozenset([perms.index(e)])
            if e and e[0] in OPS:
                a = [go(x) for x in e[1:]]
                return {'and': lambda: a[0] & a[1], 'or': lambda: frozenset().union(*a),
                        'xor': lambda: a[0] ^ a[1], 'not': lambda: univ - a[0],
                        'all': lambda: univ | frozenset().union(*a)}[e[0]]()
            return frozenset().union(*[go(x) for x in e])
        return go(e)
    def catset(e):
        univ = frozenset(range(len(P.cats)))
        if isinstance(e, str):
            return univ if e == 'all' else frozenset([P.gid[e]])
        if e and e[0] == 'range':
            return frozenset(range(P.gid[e[1]], P.gid[e[2]] + 1))
        if e and e[0] in OPS:
            a = [catset(x) for x in e[1:]]
            return {'and': lambda: a[0] & a[1], 'or': lambda: frozenset().union(*a),
                    'not': lambda: univ - a[0], 'xor': lambda: a[0] ^ a[1]}[e[0]]()
        return frozenset().union(*[catset(x) for x in e])
    def level(e):
        return (P.sid[e[0]], catset(e[1]) if len(e) > 1 else frozenset())
    def lrange(e):
        return (level(e[0]), level(e[1]))
    def avrule(s):
        src = tset(s[1])
        self_ = s[2] == 'self'
        tgt = frozenset() if self_ else tset(s[2])
        cls, pe = s[3]
        return (s[0], src, tgt, self_, P.cid[cls], pset(cls, pe))
    def tyrule(s):
        src = tset(s[1]); self_ = s[2] == 'self'
        tgt = frozenset() if self_ else tset(s[2])
        name = s[4] if len(s) == 6 else None
        return (s[0], src, tgt, self_, P.cid[s[3]], name, P.tid[s[-1]])
    AV = ('allow', 'auditallow', 'dontaudit', 'neverallow')
    TY = ('typetransition', 'typechange', 'typemember')
    P.av, P.ty, P.conds, P.roleallow, P.roletrans, P.cons, P.permissive = [], [], [], [], [], [], set()
    def bexpr(e):
        if isinstance(e, str):
            i = P.bid[e]
            return lambda bs: bs[i]
        a = [bexpr(x) for x in e[1:]]
        op = e[0]
        if op == 'not': return lambda bs: not a[0](bs)
        if op == 'and': return lambda bs: a[0](bs) and a[1](bs)
        if op == 'or': return lambda bs: a[0](bs) or a[1](bs)
        if op == 'xor': return lambda bs: a[0](bs) != a[1](bs)
        if op == 'eq': return lambda bs: a[0](bs) == a[1](bs)
        if op == 'neq': return lambda bs: a[0](bs) != a[1](bs)
        raise ValueError(op)
    SEL = {'u1': ('u', 0), 'u2': ('u', 1), 'r1': ('r', 0), 'r2': ('r', 1), 't1': ('t', 0), 't2': ('t', 1)}
    LSEL = {'l1': (0, 0), 'h1': (0, 1), 'l2': (1, 0), 'h2': (1, 1)}
    def names(kind, e):
        if kind == 't':
            return tset(e)
        ids = P.uid if kind == 'u' else P.rid
        return frozenset([ids[e]]) if isinstance(e, str) else frozenset(ids[x] for x in e)
    def cexpr(e):
        op = e[0]
        if op in ('and', 'or'):
            a, b = cexpr(e[1]), cexpr(e[2])
            return (lambda s, t: a(s, t) and b(s, t)) if op == 'and' else (lambda s, t: a(s, t) or b(s, t))
        if op == 'not':
            a = cexpr(e[1]); return lambda s, t: not a(s, t)
        x, y = e[1], e[2]
        if x in LSEL:
            lx, ly = LSEL[x], LSEL[y]
            f = {'dom': dom, 'domby': lambda a, b: dom(b, a), 'eq': lambda a, b: dom(a, b) and dom(b, a),
                 'neq': lambda a, b: not (dom(a, b) and dom(b, a)),
                 'incomp': lambda a, b: not dom(a, b) and not dom(b, a)}[op]
            return lambda s, t: f((s, t)[lx[0]][3][lx[1]], (s, t)[ly[0]][3][ly[1]])
        kind, side = SEL[x]
        k = 'urt'.index(kind)
        sense = op == 'eq'
        if isinstance(y, str) and y in SEL and SEL[y] == (kind, 1) and side == 0:
            return lambda s, t: (s[k] == t[k]) == sense
        ns = names(kind, y)
        return lambda s, t: ((s, t)[side][k] in ns) == sense
    for s in st:
        k = s[0]
        if k in AV:
            P.av.append(avrule(s))
        elif k in TY:
            P.ty.append(tyrule(s))
        elif k == 'booleanif':
            c = [bexpr(s[1]), [], [], [], [], s[1]]
            for br in s[2:]:
                off = 1 if br[0] == 'true' else 3
                for r in br[1:]:
                    if r[0] in AV: c[off].append(avrule(r))
                    else: c[off + 1].append(tyrule(r))
            P.conds.append(c)
        elif k == 'roleallow':
            P.roleallow.append((P.rid[s[1]], P.rid[s[2]]))
        elif k == 'roletransition':
            P.roletrans.append((P.rid[s[1]], tset(s[2]), P.cid[s[3]], P.rid[s[4]]))
        elif k in ('constrain', 'mlsconstrain'):
            cls, pe = s[1]
            P.cons.append((k == 'mlsconstrain', P.cid[cls], pset(cls, pe), cexpr(s[2])))
        elif k == 'typepermissive':
            P.permissive.add(P.tid[s[1]])
    P.level, P.lrange = level, lrange
    return P

def dom(a, b):
    return a[0] >= b[0] and b[1] <= a[1]

def rule_matches(r, st, tt, c):
    return st in r[1] and (tt in r[2] or (r[3] and st == tt)) and r[4] == c

def active_av(P):
    out = list(P.av)
    for c in P.conds:
        out += c[1] if c[0](P.state) else c[3]
    return out

def active_ty(P):
    out = list(P.ty)
    for c in P.conds:
        out += c[2] if c[0](P.state) else c[4]
    return out

def neverallow_ok(P):
    allows = list(P.av)
    for c in P.conds:
        allows += c[1] + c[3]
    allows = [a for a in allows if a[0] == 'allow']
    for n in P.av:
        if n[0] != 'neverallow':
            continue
        for a in allows:
            if n[4] != a[4] or not (n[5] & a[5]):
                continue
            # some (s, t) both match
            for s_ in n[1] & a[1]:
                ts = (n[2] | ({s_} if n[3] else set())) & (a[2] | ({s_} if a[3] else set()))
                if ts:
                    return False
    return True

def trans_conflict(P):
    """The load-time transition check: 'type rule conflict' when two type
    rules of the same kind match some source, target and class in common,
    name the same object (or none) and give different types, unless they
    are in the two branches of one condition ((not e) is e with its branches
    swapped); 'role transition conflict' likewise for roletransition."""
    def place(e, br):
        return (e[1], not br) if isinstance(e, list) and e[0] == 'not' else (e, br)
    placed = [(None, r) for r in P.ty]
    for c in P.conds:
        placed += [(place(c[5], True), r) for r in c[2]] + [(place(c[5], False), r) for r in c[4]]
    def meet(a, b):
        for s_ in a[1] & b[1]:
            if (a[2] | ({s_} if a[3] else set())) & (b[2] | ({s_} if b[3] else set())):
                return True
        return False
    for i, (pa, a) in enumerate(placed):
        for pb, b in placed[i + 1:]:
            excl = pa is not None and pb is not None and pa[0] == pb[0] and pa[1] != pb[1]
            if not excl and a[0] == b[0] and a[4] == b[4] and a[5] == b[5] and a[6] != b[6] and meet(a, b):
                return 'type rule conflict'
    rts = P.roletrans
    for i, a in enumerate(rts):
        for b in rts[i + 1:]:
            if a[0] == b[0] and a[1] & b[1] and a[2] == b[2] and a[3] != b[3]:
                return 'role transition conflict'
    return None

def compute_av(P, s, t, c):
    nperms = len(P.classes[c][1])
    st, tt = s[2], t[2]
    def union(kind):
        out = set()
        for r in active_av(P):
            if r[0] == kind and rule_matches(r, st, tt, c):
                out |= r[5]
        return out
    allowed = union('allow')
    for (m, cls, perms, e) in P.cons:
        if cls == c and (not m or P.mls) and not e(s, t):
            allowed -= perms
    return allowed, union('auditallow'), set(range(nperms)) - union('dontaudit')

def check(P, opts, s, t, c, req):
    allowed, aa, ad = compute_av(P, s, t, c)
    if req <= allowed:
        return (True, False, bool(req & aa))
    lenient = (not opts[0]) or (opts[1] and s[2] in P.permissive)
    return (lenient, True, bool((req - allowed) & ad))

def find_ty(P, kind, st, tt, c, name):
    rules = [r for r in active_ty(P) if r[0] == kind and rule_matches(r, st, tt, c)]
    if name is not None:
        for r in rules:
            if r[5] == name:
                return r[6]
    for r in rules:
        if r[5] is None:
            return r[6]
    return None

def role_trans(P, r, tt, c):
    for (a, ts, cls, res) in P.roletrans:
        if a == r and tt in ts and cls == c:
            return res
    return None

def compute_create(P, s, t, c, name):
    proc = P.cid.get('process') == c
    ty = find_ty(P, 'typetransition', s[2], t[2], c, name)
    ro = role_trans(P, s[1], t[2], c)
    if proc:
        return (s[0], s[1] if ro is None else ro, s[2] if ty is None else ty, s[3])
    return (s[0], 0 if ro is None else ro, t[2] if ty is None else ty, (s[3][0], s[3][0]))

def compute_relabel(P, s, t, c, kind):
    ty = find_ty(P, kind, s[2], t[2], c, None)
    return (t[0], t[1], t[2] if ty is None else ty, t[3])

# ---------------------------------------------------------------- text

def show_level(P, l):
    s = P.sens[l[0]]
    return s + (':' + ','.join(P.cats[i] for i in sorted(l[1])) if l[1] else '')

def show_ctx(P, c):
    lo, hi = c[3]
    rg = show_level(P, lo) if dom(lo, hi) and dom(hi, lo) else show_level(P, lo) + '-' + show_level(P, hi)
    return '%s:%s:%s:%s' % (P.users[c[0]], P.roles[c[1]], P.types[c[2]], rg)

def show_perms(P, c, bits):
    names = [P.classes[c][1][i] for i in sorted(bits)]
    return '{ ' + ' '.join(names) + ' }' if names else '{ }'

def show_av(P, c, av):
    a, aa, ad = av
    return 'allowed %s auditallow %s auditdeny %s' % (show_perms(P, c, a), show_perms(P, c, aa), show_perms(P, c, ad))

def show_dec(d):
    return 'granted %s denied %s audited %s' % d

# ---------------------------------------------------------------- generator

def gen_policy(rng):
    nt = rng.randint(2, 4); types = ['t%d' % i for i in range(nt)]
    na = rng.randint(0, 2); attrs = ['a%d' % i for i in range(na)]
    nr = rng.randint(1, 2); roles = ['r%d' % i for i in range(nr)]
    nu = rng.randint(1, 2); users = ['u%d' % i for i in range(nu)]
    ns = rng.randint(1, 3); sens = ['s%d' % i for i in range(ns)]
    ncat = rng.randint(1, 4); cats = ['c%d' % i for i in range(ncat)]
    nb = rng.randint(0, 2); bools = ['b%d' % i for i in range(nb)]
    mls = rng.random() < 0.7
    classes = [('process', ['fork', 'transition', 'sigchld'])]
    common = None
    if rng.random() < 0.5:
        common = ('cm', ['ioctl', 'read'])
    for i in range(rng.randint(1, 3)):
        perms = ['p%d_%d' % (i, j) for j in range(rng.randint(1, 4))]
        classes.append(('k%d' % i, perms))
    L = []
    L.append('(handleunknown allow)')
    L.append('(mls %s)' % ('true' if mls else 'false'))
    if common:
        L.append('(common %s (%s))' % (common[0], ' '.join(common[1])))
    for n, ps in classes:
        L.append('(class %s (%s))' % (n, ' '.join(ps)))
    if common:
        L.append('(classcommon k0 cm)')
    L.append('(classorder (%s))' % ' '.join(n for n, _ in classes))
    L.append('(sid kernel)')
    L.append('(sidorder (kernel))')
    for s in sens:
        L.append('(sensitivity %s)' % s)
    L.append('(sensitivityorder (%s))' % ' '.join(sens))
    for c in cats:
        L.append('(category %s)' % c)
    L.append('(categoryorder (%s))' % ' '.join(cats))
    for s in sens:
        L.append('(sensitivitycategory %s (range %s %s))' % (s, cats[0], cats[-1]))
    for t in types:
        L.append('(type %s)' % t)
    for a in attrs:
        L.append('(typeattribute %s)' % a)
    tnames = types + attrs
    def texpr(prev):
        r = rng.random()
        if r < 0.5:
            return '(%s)' % ' '.join(rng.sample(types, rng.randint(1, len(types))))
        if r < 0.65:
            return '(not %s)' % rng.choice(types)
        if r < 0.8:
            return '(and (all) (not %s))' % rng.choice(types)
        if r < 0.9 and prev:
            return '(or %s %s)' % (rng.choice(types), rng.choice(prev))
        return '(%s)' % rng.choice(types)
    for i, a in enumerate(attrs):
        if i == 1 and rng.random() < 0.5:
            L.append('(typeattributeset %s (%s %s))' % (a, attrs[0], rng.choice(types)))
        else:
            L.append('(typeattributeset %s %s)' % (a, texpr(attrs[:i])))
    if rng.random() < 0.3:
        L.append('(typealias al0)')
        L.append('(typealiasactual al0 %s)' % rng.choice(types))
        tnames = tnames + ['al0']
    for r in roles:
        L.append('(role %s)' % r)
        L.append('(roletype %s %s)' % (r, rng.choice(tnames)))
    for u in users:
        L.append('(user %s)' % u)
        L.append('(userrole %s %s)' % (u, rng.choice(roles)))
        L.append('(userlevel %s (%s))' % (u, sens[0]))
        L.append('(userrange %s ((%s) (%s (range %s %s))))' % (u, sens[0], sens[-1], cats[0], cats[-1]))
    L.append('(sidcontext kernel (%s %s %s ((%s) (%s))))' % (users[0], roles[0], types[0], sens[0], sens[0]))
    for b in bools:
        L.append('(boolean %s %s)' % (b, rng.choice(['true', 'false'])))
    def cp():
        n, ps = rng.choice(classes)
        if n == 'k0' and common:
            ps = common[1] + ps
        r = rng.random()
        if r < 0.7:
            return '(%s (%s))' % (n, ' '.join(rng.sample(ps, rng.randint(1, len(ps)))))
        if r < 0.85:
            return '(%s (all))' % n
        return '(%s (not (%s)))' % (n, rng.choice(ps))
    def avr(kind):
        tgt = 'self' if rng.random() < 0.2 else rng.choice(tnames)
        return '(%s %s %s %s)' % (kind, rng.choice(tnames), tgt, cp())
    def tyr(kind, named):
        n = rng.choice([c for c, _ in classes])
        nm = ' "obj%d"' % rng.randint(0, 1) if named else ''
        return '(%s %s %s %s%s %s)' % (kind, rng.choice(tnames), rng.choice(tnames), n, nm, rng.choice(types))
    for i in range(rng.randint(4, 12)):
        L.append(avr(rng.choice(['allow'] * 5 + ['auditallow', 'dontaudit'])))
    for b in bools:
        if rng.random() < 0.8:
            e = b if rng.random() < 0.6 else rng.choice(['(not %s)' % b, '(and %s %s)' % (b, bools[0]), '(or %s %s)' % (b, bools[-1]), '(xor %s %s)' % (b, bools[0]), '(eq %s %s)' % (b, bools[-1])])
            # a name transition here is refused (rarely, so most policies load)
            tb = ' '.join([avr('allow') for _ in range(rng.randint(1, 2))] + ([tyr('typetransition', rng.random() < 0.15)] if rng.random() < 0.4 else []))
            fb = ' '.join([avr(rng.choice(['allow', 'dontaudit'])) for _ in range(rng.randint(0, 2))])
            L.append('(booleanif %s (true %s)%s)' % (e, tb, (' (false %s)' % fb) if fb else ''))
    for i in range(rng.randint(0, 3)):
        L.append(tyr('typetransition', rng.random() < 0.3))
    if rng.random() < 0.5:
        L.append(tyr('typechange', False))
    if rng.random() < 0.5:
        L.append(tyr('typemember', False))
    if nr > 1 and rng.random() < 0.6:
        L.append('(roleallow %s %s)' % (roles[0], roles[1]))
    if rng.random() < 0.5:
        L.append('(roletransition %s %s process %s)' % (rng.choice(roles), rng.choice(tnames), rng.choice(roles)))
    plain_t = [n for n in tnames if n not in WORDS]
    plain_r = [n for n in roles if n not in WORDS]
    def cexpr(depth):
        r = rng.random()
        if depth < 2 and r < 0.25:
            return '(%s %s %s)' % (rng.choice(['and', 'or']), cexpr(depth + 1), cexpr(depth + 1))
        if depth < 2 and r < 0.3:
            return '(not %s)' % cexpr(depth + 1)
        r = rng.random()
        op = rng.choice(['eq', 'neq'])
        if r < 0.25:
            return '(%s %s)' % (op, rng.choice(['u1 u2', 'r1 r2', 't1 t2']))
        # a name that is an operand word (t1, r1, ...) reads as that operand
        # in CIL, and is mostly refused there: chosen rarely, so most
        # policies load
        if r < 0.5:
            return '(%s %s %s)' % (op, rng.choice(['t1', 't2']), rng.choice(tnames if rng.random() < 0.15 else plain_t))
        if r < 0.6:
            return '(%s %s %s)' % (op, rng.choice(['r1', 'r2']), rng.choice(roles if rng.random() < 0.15 else plain_r))
        if r < 0.7:
            return '(%s %s (%s))' % (op, rng.choice(['u1', 'u2']), ' '.join(rng.sample(users, len(users))))
        return '(%s %s %s)' % (rng.choice(['dom', 'domby', 'incomp', 'eq', 'neq']), rng.choice(['l1', 'h1']), rng.choice(['l2', 'h2']))
    for i in range(rng.randint(0, 2)):
        L.append('(constrain %s %s)' % (cp(), cexpr(0)))
    for i in range(rng.randint(0, 2)):
        L.append('(mlsconstrain %s (%s %s %s))' % (cp(), rng.choice(['dom', 'domby', 'eq', 'incomp']), rng.choice(['l1', 'h1']), rng.choice(['l2', 'h2'])))
    if rng.random() < 0.3:
        L.append('(typepermissive %s)' % rng.choice(types))
    if rng.random() < 0.35:
        L.append(avr('neverallow').replace('self', rng.choice(tnames)))
    rng.shuffle(L)  # statement order does not matter in CIL (rule order does, below)
    return '\n'.join(L) + '\n', types, roles, users, sens, cats, classes, common, bools

def rand_level(rng, sens, cats):
    s = rng.choice(sens)
    k = rng.random()
    if k < 0.4:
        return s
    if k < 0.7:
        return s + ':' + ','.join(sorted(rng.sample(cats, rng.randint(1, len(cats))), key=cats.index))
    a = rng.randrange(len(cats)); b = rng.randrange(a, len(cats))
    return s + ':' + (cats[a] if a == b else cats[a] + '.' + cats[b])

def rand_ctx(rng, users, roles, types, sens, cats, obj=False):
    lo = rand_level(rng, sens, cats)
    rg = lo if rng.random() < 0.5 else lo + '-' + rand_level(rng, sens, cats)
    role = 'object_r' if obj and rng.random() < 0.7 else rng.choice(roles)
    return '%s:%s:%s:%s' % (rng.choice(users), role, rng.choice(types), rg)

def parse_ctx(P, text):
    parts = text.split(':')
    u, r, t = parts[:3]
    def lev(x):
        q = x.split(':')
        cs = set()
        if len(q) > 1:
            for item in q[1].split(','):
                ab = item.split('.')
                if len(ab) == 1:
                    cs.add(P.gid[ab[0]])
                else:
                    cs |= set(range(P.gid[ab[0]], P.gid[ab[1]] + 1))
        return (P.sid[q[0]], frozenset(cs))
    rest = ':'.join(parts[3:])
    lr = rest.split('-')
    lo = lev(lr[0]); hi = lev(lr[1]) if len(lr) > 1 else lo
    return (P.uid[u], P.rid[r], P.tid[t], (lo, hi))

def bstr(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'

NL = chr(10)

HELPERS = '''import Base
import ../../bytes/bytes.bend as B
import ../bits.bend as Bits
import ../contexts.bend as C
import ../policy.bend as P
import ../avc.bend as A
import ../selinux.bend as S

def SeRef.show_avd(+p: P.SePolicy, +c: Nat, v: A.SeAvd) -> String:
  match v:
    case A.SeAvd{a, aa, ad}:
      "allowed " ++ S.Selinux.perms_show(p, c, a) ++ " auditallow " ++ S.Selinux.perms_show(p, c, aa) ++ " auditdeny " ++ S.Selinux.perms_show(p, c, ad)

def SeRef.av.go(+p: P.SePolicy, +cls: String, r: Result<&2, &2, P.SeError, A.SeAvd>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{v}:
      SeRef.show_avd(p, Result.default(&2, &2, P.SeError, Nat, S.Selinux.class(p, cls), 0n), v)

def SeRef.av(+p: P.SePolicy, s: String, t: String, +cls: String) -> String:
  SeRef.av.go(p, cls, S.Selinux.compute_av(p, s, t, cls))

def SeRef.dec(r: Result<&2, &2, P.SeError, A.SeDecision>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{d}:
      match d:
        case A.SeDecision{g, dn, au}:
          "granted " ++ Bool.show(g) ++ " denied " ++ Bool.show(dn) ++ " audited " ++ Bool.show(au)

def SeRef.str(r: Result<&2, &2, P.SeError, String>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{x}:
      x

def SeRef.relabel.go(+p: P.SePolicy, r: Result<&2, &2, P.SeError, C.SeContext>, q: Result<&2, &2, P.SeError, C.SeContext>, k: Result<&2, &2, P.SeError, Nat>, kind: Bool) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{+s}:
      match q:
        case Fail{e}:
          S.SeError.show(e)
        case Done{+t}:
          match k:
            case Fail{e}:
              S.SeError.show(e)
            case Done{+c}:
              match kind:
                case True{}:
                  S.Selinux.context_show(p, A.SeAvc.compute_relabel(p, s, t, c))
                case False{}:
                  S.Selinux.context_show(p, A.SeAvc.compute_member(p, s, t, c))

# typechange (True) or typemember (False)
def SeRef.relabel(+p: P.SePolicy, kind: Bool, s: String, t: String, cls: String) -> String:
  SeRef.relabel.go(p, S.Selinux.context(p, s), S.Selinux.context(p, t), S.Selinux.class(p, cls), kind)

def SeRef.setb(+p: P.SePolicy, b: String, v: Bool) -> P.SePolicy:
  Result.default(&2, &2, P.SeError, P.SePolicy, S.Selinux.set_bool(p, b, v), p)

'''

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    npol = int(os.environ.get('NPOL', '30'))
    defs, mains, expect, cils = [], [], [], []
    for k in range(npol):
        text, types, roles, users, sens, cats, classes, common, bools = gen_policy(rng)
        cils.append(text)
        P = compile_cil(read_sexps(text))
        lines = []
        refused = P.error or ('neverallow violated' if not neverallow_ok(P) else trans_conflict(P))
        if refused:
            expect.append('policy %d: %s' % (k, refused))
        else:
            expect.append('policy %d: loaded' % k)
            cnames = [n for n, _ in classes]
            def perms_of(n):
                ps = dict(classes)[n]
                return (common[1] + ps) if (n == 'k0' and common) else ps
            qs = []
            for i in range(12):
                s = rand_ctx(rng, users, roles, types, sens, cats)
                t = rand_ctx(rng, users, roles, types, sens, cats, obj=True)
                c = rng.choice(cnames)
                qs.append(('av', s, t, c))
            # aimed at the allow rules in force: a source and target they name
            rules = [r for r in active_av(P) if r[0] == 'allow' and r[1]]
            for i in range(6 if rules else 0):
                r = rng.choice(rules)
                st = P.types[rng.choice(sorted(r[1]))]
                tts = sorted(r[2] | (r[1] if r[3] else frozenset()))
                tt = P.types[rng.choice(tts)] if tts else st
                s = rand_ctx(rng, users, roles, [st], sens, cats)
                t = rand_ctx(rng, users, roles, [tt], sens, cats, obj=True)
                qs.append(('av', s, t, P.classes[r[4]][0]))
            for i in range(4):
                s = rand_ctx(rng, users, roles, types, sens, cats)
                t = rand_ctx(rng, users, roles, types, sens, cats, obj=True)
                c = rng.choice(cnames)
                ps = rng.sample(perms_of(c), rng.randint(1, len(perms_of(c))))
                o = rng.choice([(True, True), (False, True), (True, False)])
                qs.append(('check', o, s, t, c, ps))
            for i in range(4):
                s = rand_ctx(rng, users, roles, types, sens, cats)
                t = rand_ctx(rng, users, roles, types, sens, cats, obj=True)
                c = rng.choice(cnames)
                nm = rng.choice([None, None, 'obj0', 'obj1'])
                qs.append(('create', s, t, c, nm))
            for i in range(2):
                s = rand_ctx(rng, users, roles, types, sens, cats)
                t = rand_ctx(rng, users, roles, types, sens, cats, obj=True)
                qs.append(('relabel', rng.random() < 0.5, s, t, rng.choice(cnames)))
            for b in bools:
                v = rng.random() < 0.5
                s = rand_ctx(rng, users, roles, types, sens, cats)
                t = rand_ctx(rng, users, roles, types, sens, cats, obj=True)
                qs.append(('bool', b, v, s, t, rng.choice(cnames)))
            body = []
            for q in qs:
                if q[0] == 'av':
                    _, s, t, c = q
                    ci = P.cid[c]
                    expect.append(show_av(P, ci, compute_av(P, parse_ctx(P, s), parse_ctx(P, t), ci)))
                    body.append('IO.print(SeRef.av(p, %s, %s, %s))' % (bstr(s), bstr(t), bstr(c)))
                elif q[0] == 'check':
                    _, o, s, t, c, ps = q
                    ci = P.cid[c]
                    req = set(P.classes[ci][1].index(x) for x in ps)
                    expect.append(show_dec(check(P, o, parse_ctx(P, s), parse_ctx(P, t), ci, req)))
                    body.append('IO.print(SeRef.dec(S.Selinux.check(A.SeOptions{%s{}, %s{}}, p, %s, %s, %s, [%s])))' % (o[0], o[1], bstr(s), bstr(t), bstr(c), ', '.join(bstr(x) for x in ps)))
                elif q[0] == 'create':
                    _, s, t, c, nm = q
                    ci = P.cid[c]
                    expect.append(show_ctx(P, compute_create(P, parse_ctx(P, s), parse_ctx(P, t), ci, nm)))
                    body.append('IO.print(SeRef.str(S.Selinux.create(p, %s, %s, %s, %s)))' % (bstr(s), bstr(t), bstr(c), 'None{}' if nm is None else 'Some{%s}' % bstr(nm)))
                elif q[0] == 'relabel':
                    _, ch, s, t, c = q
                    ci = P.cid[c]
                    expect.append(show_ctx(P, compute_relabel(P, parse_ctx(P, s), parse_ctx(P, t), ci, 'typechange' if ch else 'typemember')))
                    body.append('IO.print(SeRef.relabel(p, %s{}, %s, %s, %s))' % (ch, bstr(s), bstr(t), bstr(c)))
                elif q[0] == 'bool':
                    _, b, v, s, t, c = q
                    old = list(P.state)
                    P.state[P.bid[b]] = v
                    ci = P.cid[c]
                    expect.append(show_av(P, ci, compute_av(P, parse_ctx(P, s), parse_ctx(P, t), ci)))
                    P.state = old
                    body.append('IO.print(SeRef.av(SeRef.setb(p, %s, %s{}), %s, %s, %s))' % (bstr(b), v, bstr(s), bstr(t), bstr(c)))
            lines = body
        defs.append('def SeRef.pol%d() -> String:\n  %s\n' % (k, bstr(text)))
        if lines:
            run = '\n'.join('      ' + l for l in ['IO.print("policy %d: loaded")' % k] + lines)
            defs.append('def SeRef.run%d(r: Result<&2, &2, P.SeError, P.SePolicy>) -> IO(Unit):\n  match r:\n    case Fail{e}:\n      IO.print("policy %d: " ++ S.SeError.show(e))\n    case Done{+p}:\n      do IO<Unit>:\n%s\n' % (k, k, run))
        else:
            defs.append('def SeRef.run%d(r: Result<&2, &2, P.SeError, P.SePolicy>) -> IO(Unit):\n  match r:\n    case Fail{e}:\n      IO.print("policy %d: " ++ S.SeError.show(e))\n    case Done{p}:\n      IO.print("policy %d: loaded")\n' % (k, k, k))
        mains.append('    SeRef.run%d(S.Selinux.load_string(SeRef.pol%d()))' % (k, k))
    with open(os.path.join(here, 'cases.bend'), 'w', newline=NL) as f:
        f.write(HELPERS + '\n'.join(defs) + '\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(mains) + '\n')
    with open(os.path.join(here, 'expected.txt'), 'w', newline=NL) as f:
        f.write('\n'.join(expect) + '\n')
    os.makedirs(os.path.join(here, 'cil'), exist_ok=True)
    for k, text in enumerate(cils):
        with open(os.path.join(here, 'cil', 'pol%02d.cil' % k), 'w', newline=NL) as f:
            f.write(text)
    print(len(expect), 'cases')

main()
