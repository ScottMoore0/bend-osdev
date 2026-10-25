"""The proofs of gcd's greatest-ness and of the lcm laws (kmath.bend), for
gen/proof.py, on top of PROOF.bend's divides lemmas (gd, gd.le) and its
specification of Base's Nat.divmod (dm_eq, dm_le):

  * Euclid's invariant: a common divisor d of a and 1 + q divides a mod
    (1 + q), since r + (a / (1 + q)) v d = u d gives r = (u - (a / (1 + q))
    v) d (gm.sub: a sum with a multiple of d that is a multiple of d is the
    difference of the multiples); so by induction on Euclid's fuel, d
    divides gcd(a, b) (gm.gg);
  * homogeneity, gcd(m a, m b) = m gcd(a, b): (m a) mod (m b) = m (a mod b)
    by the uniqueness of a remainder (gm.mh), and the two runs of Euclid's
    loop step together (gm.hom);
  * lcm(a, b) = (a / g) b with g = gcd(a, b) = k1 g' ... : for b not 0, g is
    not 0 and a / g = k1 where a = k1 g (gm.k1), so lcm = k1 b = k2 a; a
    common multiple m = u a = v b, not 0, has a b dividing m a and m b, so
    a b divides gcd(m a, m b) = m g, and a b = lcm g; cancelling g gives
    lcm dividing m.

The ring identities are written by scripts/natproof.py (u32's Nat laws).
"""
import natproof as N
from natproof import calc, hyp, lt_from


def eq(a, b, t="Nat"):
    return "{" + f"{a} == {b} : {t}" + "}"


def DV(x, g):
    return f"Sigma<&1, &1, Nat, u => {eq(f'Nat.mul(u, {g})', x)}>"


def LE(x, y):
    return f"Sigma<&1, &1, Nat, w => {eq(f'Nat.add(w, {x})', y)}>"


def GO(f, a, b):
    return f"K.kmath.gcd.go({f}, {a}, {b})"


def sym(a, b, e):
    return f"Equal.sym(Nat, {a}, {b}, {e})"


def trans(a, b, c, ab, bc):
    return f"Equal.trans(Nat, {a}, {b}, {c}, {ab}, {bc})"


def buffered(emit0):
    """an emitter that holds each def's lines until its closing blank line, so
    that the ring identities its proofs need are written before it"""
    buf = []

    def emit(s=""):
        buf.append(s)
        if s == "":
            for line in buf:
                emit0(line)
            buf.clear()
    return emit


def more(emit0):
    emit = buffered(emit0)
    emit("# gcd is the greatest common divisor: Euclid's invariant (a common divisor")
    emit("# of a and b divides a mod b), by induction on Euclid's fuel")
    emit()
    # gm.sub: r + y d = x d gives (x - y) d = r
    goal = eq("Nat.mul(Nat.sub(x, y), d)", "R")
    emit(f"def gm.sub(+y: Nat, +x: Nat, +d: Nat, +R: Nat, e: {eq('Nat.add(R, Nat.mul(y, d))', 'Nat.mul(x, d)')}) -> {goal}:")
    emit("  match y x:")
    emit("    case 0n 0n:")
    emit(f"      {sym('R', '0n', trans('R', 'Nat.add(R, 0n)', '0n', sym('Nat.add(R, 0n)', 'R', 'UL.nat_add_zero(R)'), 'e'))}")
    emit("    case 0n 1n+xp:")
    emit(f"      {sym('R', 'Nat.mul(1n+xp, d)', trans('R', 'Nat.add(R, 0n)', 'Nat.mul(1n+xp, d)', sym('Nat.add(R, 0n)', 'R', 'UL.nat_add_zero(R)'), 'e'))}")
    emit("    case 1n+yp 0n:")
    M = "Nat.mul(1n+yp, d)"
    emit(f"      {sym('R', '0n', f'add_eq_zero({M}, R, ' + trans(f'Nat.add({M}, R)', f'Nat.add(R, {M})', '0n', f'UL.nat_add_comm({M}, R)', 'e') + ')')}")
    emit("    case 1n+yp 1n+xp:")
    E = hyp("e", "Nat.add(R, Nat.mul(1n+yp, d))", "Nat.mul(1n+xp, d)")
    pf = calc("Nat.add(d, Nat.add(R, Nat.mul(yp, d)))",
              ("Nat.add(R, Nat.mul(1n+yp, d))", "ring"),
              ("Nat.mul(1n+xp, d)", E),
              ("Nat.add(d, Nat.mul(xp, d))", "="))
    emit(f"      gm.sub(yp, xp, d, R, UL.nat_add_cancel(d, Nat.add(R, Nat.mul(yp, d)), Nat.mul(xp, d), {pf.text}))")
    emit()
    # gm.mod: d | a and d | 1 + q give d | a mod (1 + q)
    R, D = "Nat.mod(a, 1n+q)", "Nat.div(a, 1n+q)"
    pf = calc(f"Nat.add({R}, Nat.mul(Nat.mul({D}, v), d))",
              (f"Nat.add(Nat.mul({D}, Nat.mul(v, d)), {R})", "ring"),
              (f"Nat.add(Nat.mul({D}, 1n+q), {R})", hyp("ev", "Nat.mul(v, d)", "1n+q")),
              ("a", hyp("UD.nat_div_mod(a, q)", f"Nat.add(Nat.mul({D}, 1n+q), {R})", "a")),
              ("Nat.mul(u, d)", N.sym(hyp("eu", "Nat.mul(u, d)", "a"))))
    emit(f"def gm.mod(+a: Nat, +q: Nat, +d: Nat, +u: Nat, +v: Nat, eu: {eq('Nat.mul(u, d)', 'a')}, ev: {eq('Nat.mul(v, d)', '1n+q')}) -> {DV(R, 'd')}:")
    emit(f"  (Nat.sub(u, Nat.mul({D}, v)), gm.sub(Nat.mul({D}, v), u, d, {R}, {pf.text}))")
    emit()
    emit(f"def gm.gg(+fuel: Nat, +a: Nat, +b: Nat, +d: Nat, h: {LE('b', 'fuel')}, pa: {DV('a', 'd')}, pb: {DV('b', 'd')}) -> {DV(GO('fuel', 'a', 'b'), 'd')}:")
    emit("  match fuel b:")
    emit("    case 0n _:")
    emit("      pa")
    emit("    case 1n+k 0n:")
    emit("      pa")
    emit("    case 1n+k 1n+q:")
    emit("      (+u, +eu) = pa")
    emit("      (+v, +ev) = pb")
    emit(f"      gm.gg(k, 1n+q, {R}, d, gd.le(a, q, k, h, dm_le(a, q)), (v, ev), gm.mod(a, q, d, u, v, eu, ev))")
    emit()
    # homogeneity
    emit("# gcd(m a, m b) = m gcd(a, b): (m a) mod (m b) = m (a mod b), and the two")
    emit("# runs of Euclid's loop step together")
    emit()
    emit(f"def gm.z(+f: Nat, +x: Nat) -> {eq(GO('f', 'x', '0n'), 'x')}:")
    emit("  match f:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+k:")
    emit("      {==}")
    emit()
    pf = calc("Nat.add(w, 1n+x)", ("1n+Nat.add(w, x)", "ring"), ("1n+y", hyp("e", "Nat.add(w, x)", "y")))
    emit(f"def gm.slt(+x: Nat, +y: Nat, h: {LE('x', 'y')}) -> {N.btrue('Nat.is_lt(x, 1n+y)')}:")
    emit("  (+w, +e) = h")
    emit(f"  {lt_from('x', '1n+y', 'w', pf)}")
    emit()
    m = "1n+p"
    W = f"Nat.add(p, Nat.mul({m}, w))"
    pf = calc(f"Nat.add({W}, 1n+Nat.mul({m}, R))", (f"Nat.mul({m}, 1n+Nat.add(w, R))", "ring"), (f"Nat.mul({m}, 1n+q)", hyp("e", "Nat.add(w, R)", "q")))
    emit(f"def gm.mlt(+p: Nat, +R: Nat, +q: Nat, h: {LE('R', 'q')}) -> {N.btrue(f'Nat.is_lt(Nat.mul({m}, R), Nat.mul({m}, 1n+q))')}:")
    emit("  (+w, +e) = h")
    emit(f"  {lt_from(f'Nat.mul({m}, R)', f'Nat.mul({m}, 1n+q)', W, pf)}")
    emit()
    # gm.mh: (m a) mod (m (1 + q)) = m (a mod (1 + q))
    ma, B = f"Nat.mul({m}, a)", f"Nat.mul({m}, 1n+q)"
    Q = f"Nat.add(q, Nat.mul(p, 1n+q))"
    D2, R2 = f"Nat.div({ma}, {B})", f"Nat.mod({ma}, {B})"
    pf = calc(f"Nat.add(Nat.mul({D2}, {B}), {R2})",
              (ma, hyp(f"UD.nat_div_mod({ma}, {Q})", f"Nat.add(Nat.mul({D2}, {B}), {R2})", ma)),
              (f"Nat.mul({m}, Nat.add(Nat.mul({D}, 1n+q), {R}))", N.sym(hyp("UD.nat_div_mod(a, q)", f"Nat.add(Nat.mul({D}, 1n+q), {R})", "a"))),
              (f"Nat.add(Nat.mul({D}, {B}), Nat.mul({m}, {R}))", "ring"))
    emit(f"def gm.mh(+a: Nat, +q: Nat, +p: Nat) -> {eq(R2, f'Nat.mul({m}, {R})')}:")
    emit(f"  UL.nat_mod_unique({B}, {D2}, {R2}, {D}, Nat.mul({m}, {R}), {pf.text}, gm.slt({R2}, {Q}, dm_le({ma}, {Q})), gm.mlt(p, {R}, q, dm_le(a, q)))")
    emit()
    # the fuel bound for the next step of the run on m a, m b
    W2 = f"Nat.add(Nat.add(w2, p), Nat.mul({m}, w1))"
    pf = calc(f"1n+Nat.add({W2}, Nat.mul({m}, {R}))",
              (f"Nat.add(w2, Nat.mul({m}, 1n+Nat.add(w1, {R})))", "ring"),
              (f"Nat.add(w2, {B})", hyp("e1", f"Nat.add(w1, {R})", "q")),
              ("1n+k2", hyp("e2", f"Nat.add(w2, {B})", "1n+k2")))
    emit(f"def gm.h2(+a: Nat, +q: Nat, +p: Nat, +k2: Nat, h2: {LE(B, '1n+k2')}, h1: {LE(R, 'q')}) -> {LE(f'Nat.mul({m}, {R})', 'k2')}:")
    emit("  (+w2, +e2) = h2")
    emit("  (+w1, +e1) = h1")
    emit(f"  ({W2}, succ_inj(Nat.add({W2}, Nat.mul({m}, {R})), k2, {pf.text}))")
    emit()
    # gm.hom
    hgoal = eq(GO("f2", f"Nat.mul({m}, a)", f"Nat.mul({m}, b)"), f"Nat.mul({m}, {GO('fuel', 'a', 'b')})")
    emit(f"def gm.hom(+fuel: Nat, +a: Nat, +b: Nat, +f2: Nat, +p: Nat, h: {LE('b', 'fuel')}, h2: {LE(f'Nat.mul({m}, b)', 'f2')}) -> {hgoal}:")

    def zero_b(ind):
        x = f"Nat.mul({m}, 0n)"
        c = f"Equal.cong(Nat, Nat, z => {GO('f2', ma, 'z')}, {x}, 0n, UL.nat_mul_zero({m}))"
        emit(f"{ind}{trans(GO('f2', ma, x), GO('f2', ma, '0n'), ma, c, f'gm.z(f2, {ma})')}")
    emit("  match fuel b:")
    emit("    case 0n 0n:")
    zero_b("      ")
    emit("    case 0n 1n+q:")
    emit("      (+w, +e) = h")
    hg = eq(GO("f2", ma, B), f"Nat.mul({m}, {GO('0n', 'a', '1n+q')})")
    emit(f"      Empty.absurd({hg}, succ_ne_zero(q, add_eq_zero(w, 1n+q, e)))")
    emit("    case 1n+k 0n:")
    zero_b("      ")
    emit("    case 1n+k 1n+q:")
    emit("      match f2:")
    emit("        case 0n:")
    emit("          (+w2, +e2) = h2")
    hg = eq(GO("0n", ma, B), f"Nat.mul({m}, {GO('1n+k', 'a', '1n+q')})")
    emit(f"          Empty.absurd({hg}, succ_ne_zero({Q}, add_eq_zero(w2, {B}, e2)))")
    emit("        case 1n+k2:")
    h2p = "gm.h2(a, q, p, k2, h2, dm_le(a, q))"
    ih = f"gm.hom(k, 1n+q, {R}, k2, p, gd.le(a, q, k, h, dm_le(a, q)), {h2p})"
    rhs = f"Nat.mul({m}, {GO('k', '1n+q', R)})"
    c = f"Equal.cong(Nat, Nat, z => {GO('k2', B, 'z')}, {R2}, Nat.mul({m}, {R}), gm.mh(a, q, p))"
    emit(f"          {trans(GO('k2', B, R2), GO('k2', B, f'Nat.mul({m}, {R})'), rhs, c, ih)}")
    emit()
    emit("def Laws.gcd_greatest(a, b, d, u, v, eu, ev):")
    emit("  gm.gg(b, a, b, d, (0n, {==}), (u, eu), (v, ev))")
    emit()
    emit(f"def gm.mul(+m: Nat, +a: Nat, +b: Nat) -> {eq('K.KMath.gcd(Nat.mul(m, a), Nat.mul(m, b))', 'Nat.mul(m, K.KMath.gcd(a, b))')}:")
    emit("  match m:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+p:")
    emit(f"      gm.hom(b, a, b, Nat.mul({m}, b), p, (0n, {{==}}), (0n, {{==}}))")
    emit()
    emit("def Laws.gcd_mul(m, a, b):")
    emit("  gm.mul(m, a, b)")
    emit()
    emit(f"def gm.zl(+b: Nat) -> {eq('K.KMath.gcd(0n, b)', 'b')}:")
    emit("  match b:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+q:")
    emit("      gm.z(q, 1n+q)")
    emit()
    emit("def Laws.gcd_zero_l(b):")
    emit("  gm.zl(b)")
    emit()
    emit("def Laws.gcd_zero_r(a):")
    emit("  {==}")
    emit()
    lcm(emit)


def lcm(emit):
    emit("# lcm(a, b) = (a / g) b: for b not 0, g is not 0 and a / g = k1 where")
    emit("# a = k1 g, so lcm = k1 b = k2 a; a common multiple m not 0 has a b")
    emit("# dividing m a and m b, so gcd(m a, m b) = m g, and a b = lcm g")
    emit()
    goal = f"{eq('Nat.div(a, g)', 'k1')} & {N.btrue('Nat.is_lt(0n, g)')}"
    emit(f"def gm.k1(+a: Nat, +bq: Nat, +g: Nat, +k1: Nat, +k2: Nat, e1: {eq('Nat.mul(k1, g)', 'a')}, e2: {eq('Nat.mul(k2, g)', '1n+bq')}) -> {goal}:")
    emit("  match g:")
    emit("    case 0n:")
    g0 = f"{eq('Nat.div(a, 0n)', 'k1')} & {N.btrue('Nat.is_lt(0n, 0n)')}"
    z = trans("1n+bq", "Nat.mul(k2, 0n)", "0n", sym("Nat.mul(k2, 0n)", "1n+bq", "e2"), "UL.nat_mul_zero(k2)")
    emit(f"      Empty.absurd({g0}, succ_ne_zero(bq, {z}))")
    emit("    case 1n+gp:")
    g = "1n+gp"
    D, R = f"Nat.div(a, {g})", f"Nat.mod(a, {g})"
    pf = calc(f"Nat.add(Nat.mul({D}, {g}), {R})",
              ("a", hyp("UD.nat_div_mod(a, gp)", f"Nat.add(Nat.mul({D}, {g}), {R})", "a")),
              (f"Nat.mul(k1, {g})", N.sym(hyp("e1", f"Nat.mul(k1, {g})", "a"))),
              (f"Nat.add(Nat.mul(k1, {g}), 0n)", "ring"))
    emit(f"      (UL.nat_div_unique({g}, {D}, {R}, k1, 0n, {pf.text}, gm.slt({R}, gp, dm_le(a, gp)), {{==}}), {{==}})")
    emit()
    B = "1n+bq"
    G = GO(B, "a", B)
    L = f"Nat.mul(Nat.div(a, {G}), {B})"
    KK = f"{eq(f'Nat.div(a, {G})', 'k1')} & {N.btrue(f'Nat.is_lt(0n, {G})')}"
    E12 = f"e1: {eq(f'Nat.mul(k1, {G})', 'a')}, e2: {eq(f'Nat.mul(k2, {G})', B)}"
    PAB = f"pa: {DV('a', G)}, pb: {DV(B, G)}"
    GDB = f"gd({B}, a, {B}, (0n, {{==}}))"
    GDL, GDR = f"gd.l(a, {B}, {G}, {GDB})", f"gd.r(a, {B}, {G}, {GDB})"
    SG = lambda x, y: f"Sigma<&1, &1, Nat, k => {eq(x, y)}>"  # noqa: E731
    pf = calc("Nat.mul(k2, a)",
              (f"Nat.mul(k2, Nat.mul(k1, {G}))", N.sym(hyp("e1", f"Nat.mul(k1, {G})", "a"))),
              (f"Nat.mul(k1, Nat.mul(k2, {G}))", "ring"),
              (f"Nat.mul(k1, {B})", hyp("e2", f"Nat.mul(k2, {G})", B)),
              (L, N.sym(hyp("dk", f"Nat.div(a, {G})", "k1"))))
    emit(f"def gm.ml3(+a: Nat, +bq: Nat, +k1: Nat, +k2: Nat, {E12}, kk: {KK}) -> {SG('Nat.mul(k, a)', f'K.KMath.lcm(a, {B})')}:")
    emit("  (+dk, +g0) = kk")
    emit(f"  (k2, {pf.text})")
    emit()
    emit(f"def gm.ml2(+a: Nat, +bq: Nat, {PAB}) -> {SG('Nat.mul(k, a)', f'K.KMath.lcm(a, {B})')}:")
    emit("  (+k1, +e1) = pa")
    emit("  (+k2, +e2) = pb")
    emit(f"  gm.ml3(a, bq, k1, k2, e1, e2, gm.k1(a, bq, {G}, k1, k2, e1, e2))")
    emit()
    emit(f"def gm.ml(+a: Nat, +b: Nat) -> {SG('Nat.mul(k, a)', 'K.KMath.lcm(a, b)')}:")
    emit("  match b:")
    emit("    case 0n:")
    X = "Nat.div(a, K.KMath.gcd(a, 0n))"
    emit(f"      (0n, {sym(f'Nat.mul({X}, 0n)', '0n', f'UL.nat_mul_zero({X})')})")
    emit(f"    case {B}:")
    emit(f"      gm.ml2(a, bq, {GDL}, {GDR})")
    emit()
    emit("def Laws.lcm_multiple_l(a, b):")
    emit("  gm.ml(a, b)")
    emit()
    emit("def Laws.lcm_multiple_r(a, b):")
    emit("  (Nat.div(a, K.KMath.gcd(a, b)), {==})")
    emit()
    emit(f"def gm.d0(+x: Nat) -> {eq('Nat.div(0n, x)', '0n')}:")
    emit("  match x:")
    emit("    case 0n:")
    emit("      {==}")
    emit("    case 1n+y:")
    emit("      {==}")
    emit()
    emit("def Laws.lcm_zero_l(b):")
    G0 = "K.KMath.gcd(0n, b)"
    emit(f"  Equal.cong(Nat, Nat, z => Nat.mul(z, b), Nat.div(0n, {G0}), 0n, gm.d0({G0}))")
    emit()
    emit("def Laws.lcm_zero_r(a):")
    emit(f"  UL.nat_mul_zero({X})")
    emit()
    # the least common multiple
    M = "1n+p"
    AB = f"Nat.mul(a, {B})"
    MA, MB = f"Nat.mul({M}, a)", f"Nat.mul({M}, {B})"
    GG = GO(MB, MA, MB)
    EUV = f"eu: {eq('Nat.mul(u, a)', M)}, ev: {eq(f'Nat.mul(v, {B})', M)}"
    q1 = f"Nat.mul(t, Nat.mul(k1, {B}))"
    pf = calc(f"Nat.add(Nat.mul({q1}, {G}), 0n)",
              (f"Nat.mul(t, Nat.mul(Nat.mul(k1, {G}), {B}))", "ring"),
              (f"Nat.mul(t, {AB})", hyp("e1", f"Nat.mul(k1, {G})", "a")),
              (GG, hyp("et", f"Nat.mul(t, {AB})", GG)),
              (f"Nat.mul({M}, {G})", hyp(f"gm.hom({B}, a, {B}, {MB}, p, (0n, {{==}}), (0n, {{==}}))", GG, f"Nat.mul({M}, {G})")),
              (f"Nat.add(Nat.mul({M}, {G}), 0n)", "ring"))
    fin = calc(f"Nat.mul(t, {L})", (q1, hyp("dk", f"Nat.div(a, {G})", "k1")), (M, hyp("q", q1, M)))
    emit(f"def gm.le4(+a: Nat, +bq: Nat, +p: Nat, +k1: Nat, e1: {eq(f'Nat.mul(k1, {G})', 'a')}, dk: {eq(f'Nat.div(a, {G})', 'k1')}, +g0: {N.btrue(f'Nat.is_lt(0n, {G})')}, tt: {DV(GG, AB)}) -> {SG(f'Nat.mul(k, K.KMath.lcm(a, {B}))', M)}:")
    emit("  (+t, +et) = tt")
    emit(f"  +q = UL.nat_div_unique({G}, {q1}, 0n, {M}, 0n, {pf.text}, g0, g0)")
    emit(f"  (t, {fin.text})")
    emit()
    pa = calc(f"Nat.mul(v, {AB})", (f"Nat.mul(Nat.mul(v, {B}), a)", "ring"), (MA, hyp("ev", f"Nat.mul(v, {B})", M)))
    pb = calc(f"Nat.mul(u, {AB})", (f"Nat.mul(Nat.mul(u, a), {B})", "ring"), (MB, hyp("eu", "Nat.mul(u, a)", M)))
    emit(f"def gm.le3(+a: Nat, +bq: Nat, +p: Nat, +u: Nat, +v: Nat, {EUV}, +k1: Nat, +k2: Nat, {E12}, kk: {KK}) -> {SG(f'Nat.mul(k, K.KMath.lcm(a, {B}))', M)}:")
    emit("  (+dk, +g0) = kk")
    emit(f"  gm.le4(a, bq, p, k1, e1, dk, g0, gm.gg({MB}, {MA}, {MB}, {AB}, (0n, {{==}}), (v, {pa.text}), (u, {pb.text})))")
    emit()
    emit(f"def gm.le2(+a: Nat, +bq: Nat, +p: Nat, +u: Nat, +v: Nat, {EUV}, {PAB}) -> {SG(f'Nat.mul(k, K.KMath.lcm(a, {B}))', M)}:")
    emit("  (+k1, +e1) = pa")
    emit("  (+k2, +e2) = pb")
    emit(f"  gm.le3(a, bq, p, u, v, eu, ev, k1, k2, e1, e2, gm.k1(a, bq, {G}, k1, k2, e1, e2))")
    emit()
    lgoal = SG("Nat.mul(k, K.KMath.lcm(a, b))", "m")
    emit(f"def gm.least(+a: Nat, +m: Nat, +b: Nat, +u: Nat, +v: Nat, eu: {eq('Nat.mul(u, a)', 'm')}, ev: {eq('Nat.mul(v, b)', 'm')}) -> {lgoal}:")
    emit("  match m:")
    emit("    case 0n:")
    emit("      (0n, {==})")
    emit(f"    case {M}:")
    emit("      match b:")
    emit("        case 0n:")
    lg0 = SG("Nat.mul(k, K.KMath.lcm(a, 0n))", M)
    z = trans("0n", "Nat.mul(v, 0n)", M, sym("Nat.mul(v, 0n)", "0n", "UL.nat_mul_zero(v)"), "ev")
    emit(f"          Empty.absurd({lg0}, succ_ne_zero(p, {sym('0n', M, z)}))")
    emit(f"        case {B}:")
    emit(f"          gm.le2(a, bq, p, u, v, eu, ev, {GDL}, {GDR})")
    emit()
    emit("def Laws.lcm_least(a, b, m, u, v, eu, ev):")
    emit("  gm.least(a, m, b, u, v, eu, ev)")
    emit()
