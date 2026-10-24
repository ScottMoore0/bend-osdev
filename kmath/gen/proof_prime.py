"""The proofs of kmath's primality laws (LAWS_prime.bend, prime.bend), for
gen/proof.py. KMath.is_prime(n) tries 2 (n even), then the odd d = 3, 5, ...
while d <= n / d. On the value N of n, with the u32 laws for U32.div,
U32.mod, U32.is_gt (through U32.cmp) and U32.and:

  * the loop runs on d = 3 + 2 i with 2 f + d = c for its fuel f, where
    c = 2 * 32768 + 3 = 65539 (kept as that expression, a parameter of the
    loop lemmas: an equation between closed Nat values of that size
    overflows the checkers' stack, an order test does not), so d + 2 never
    wraps (d + 2 <= c < 2^17 <= 2^32), and the fuel runs out only at d = c
    > 2^16;
  * "past" (d > n / d) means N < d^2 (N = q d + r with q < d and r < d);
    not past means d^2 <= N;
  * a composite N (prime_no_divisor, by contradiction): N = k e with
    2 <= e < N gives k >= 2, so N >= 4; N is odd (n is not even), so
    m = min(e, k) is odd, at least 3, divides N and has m^2 <= N. The loop,
    with d <= m odd, stops at d = m (m divides N) or passes it by 2 (both
    odd); it never stops past (d^2 <= m^2 <= N) nor runs out of fuel
    (65539^2 > 2^32 > N); so it answers False;
  * the loop answers False only when d divides N with d^2 <= N, and then
    3 <= d < N (composite_divisor); an even n of at least 4 has 2.

Ring identities and order facts are written by scripts/natproof.py.
"""
import natproof as N
from natproof import btrue, calc, hyp, le_from, lt_from, lt_rw, wit_le, wit_lt
from proof_gcd import buffered

NN = "U32.to_nat(n)"
D = "U32.to_nat(d)"
Q = "U32.to_nat(U32.div(n, d))"
R = "U32.to_nat(U32.mod(n, d))"
D2 = "U32.add(d, 2)"
T2 = f"U32.to_nat({D2})"
ODD = "P.kprime.odd(n)"


def PAST(d):
    return f"U32.is_gt({d}, U32.div(n, {d}))"


def HIT(d):
    return f"U32.is_eq(U32.mod(n, {d}), 0)"


def GO(f, p, h, d):
    return f"P.kprime.go({f}, {p}, {h}, n, {d})"


def eq(a, b, t="Nat"):
    return "{" + f"{a} == {b} : {t}" + "}"


def bt(x):
    return btrue(x)


def tB(a, b, c, ab, bc):
    return f"Equal.trans(Bool, {a}, {b}, {c}, {ab}, {bc})"


def sB(a, b, e):
    return f"Equal.sym(Bool, {a}, {b}, {e})"


def cB(body, a, b, e):
    return f"Equal.cong(Nat, Bool, z => {body}, {a}, {b}, {e})"


def tN(a, b, c, ab, bc):
    return f"Equal.trans(Nat, {a}, {b}, {c}, {ab}, {bc})"


def sN(a, b, e):
    return f"Equal.sym(Nat, {a}, {b}, {e})"


RES = (f"Sigma<&1, &1, Nat, e => {bt('Nat.is_le(2n, e)')} & {bt(f'Nat.is_lt(e, {NN})')} & "
       f"Sigma<&1, &1, Nat, k => {eq('Nat.mul(k, e)', NN)}>>")
OD = eq(D, "3n+Nat.double(i)")
LTN4 = tB(f"Nat.is_lt({NN}, 4n)", "U32.is_lt(n, 4)", "{V}", sB("U32.is_lt(n, 4)", f"Nat.is_lt({NN}, 4n)", "UL.u32_lt_value(n, 4)"), sB("{V}", "U32.is_lt(n, 4)", "es"))
ORU = "Bool.or(U32.is_eq(n, 2), U32.is_eq(n, 3))"
ORN = f"Bool.or(Nat.is_eq({NN}, 2n), Nat.is_eq({NN}, 3n))"
B16, B17, B32 = "U.U32Nat.dbl(16n, 1n)", "U.U32Nat.dbl(17n, 1n)", "U.U32Nat.dbl(32n, 1n)"
# the loop's invariant 2 f + d, at the start (2 * 32768 + 3), and its bounds
C0 = "Nat.add(Nat.double(32768n), U32.to_nat(3))"
HC = btrue(f"Nat.is_lt(c, {B17})")
HC16 = btrue(f"Nat.is_lt({B16}, c)")


def prime(put0):
    emit = buffered(put0)
    N.bend_order(put0, "kp")
    N.bend_u32(put0, "kp")
    emit("# Primality: the facts the loop's tests give, on the values")
    emit()
    emit(f"def kp.gt(+x: Nat, +y: Nat) -> {eq('Cmp.is_gt(Nat.cmp(x, y))', 'Nat.is_lt(y, x)', 'Bool')}:")
    emit("  match x y:")
    for c in ("0n 0n", "0n 1n+q", "1n+p 0n"):
        emit(f"    case {c}:")
        emit("      {==}")
    emit("    case 1n+p 1n+q:")
    emit("      kp.gt(p, q)")
    emit()
    cm = f"Equal.cong(Cmp, Bool, c => Cmp.is_gt(c), U32.cmp(d, U32.div(n, d)), Nat.cmp({D}, {Q}), UL.u32_cmp_value(d, U32.div(n, d)))"
    emit(f"def kp.past(+n: U32, +d: U32) -> {eq(PAST('d'), f'Nat.is_lt({Q}, {D})', 'Bool')}:")
    emit(f"  {tB(PAST('d'), f'Cmp.is_gt(Nat.cmp({D}, {Q}))', f'Nat.is_lt({Q}, {D})', cm, f'kp.gt({D}, {Q})')}")
    emit()
    emit(f"def kp.irr(+x: Nat, h: {bt('Nat.is_lt(x, x)')}) -> Empty:")
    emit("  match x:")
    emit("    case 0n:")
    emit("      kp.ft(h)")
    emit("    case 1n+p:")
    emit("      kp.irr(p, h)")
    emit()
    emit(f"def kp.lt0(+x: Nat, h: {bt('Nat.is_lt(x, 0n)')}) -> Empty:")
    emit("  match x:")
    emit("    case 0n:")
    emit("      kp.ft(h)")
    emit("    case 1n+p:")
    emit("      kp.ft(h)")
    emit()
    emit("# an even number is not odd")
    emit(f"def kp.par(+i: Nat, +j: Nat, e: {eq('Nat.double(j)', '1n+Nat.double(i)')}) -> Empty:")
    emit("  match i:")
    emit("    case 0n:")
    emit("      match j:")
    emit("        case 0n:")
    emit("          kp.zs(0n, e)")
    emit("        case 1n+jp:")
    emit(f"          kp.zs(Nat.double(jp), {sN('1n+Nat.double(jp)', '0n', 'UL.nat_add_cancel(1n, 1n+Nat.double(jp), 0n, e)')})")
    emit("    case 1n+ip:")
    emit("      match j:")
    emit("        case 0n:")
    emit("          kp.zs(Nat.double(1n+ip), e)")
    emit("        case 1n+jp:")
    emit("          kp.par(ip, jp, UL.nat_add_cancel(2n, Nat.double(jp), 1n+Nat.double(ip), e))")
    emit()
    emit(f"def kp.dnz(+d: U32, +i: Nat, od: {OD}) -> {eq('U32.is_zero(d)', 'False{}', 'Bool')}:")
    emit(f"  {tB('U32.is_eq(d, 0)', f'Nat.is_eq({D}, 0n)', 'Nat.is_eq(3n+Nat.double(i), 0n)', 'UL.u32_eq_value(d, 0)', cB('Nat.is_eq(z, 0n)', D, '3n+Nat.double(i)', 'od'))}")
    emit()
    emit(f"def kp.ge2(+d: U32, +i: Nat, od: {OD}) -> {bt(f'Nat.is_le(2n, {D})')}:")
    emit(f"  {tB(f'Nat.is_le(2n, {D})', 'Nat.is_le(2n, 3n+Nat.double(i))', 'True{}', cB('Nat.is_le(2n, z)', D, '3n+Nat.double(i)', 'od'), '{==}')}")
    emit()
    # d + 2 does not wrap
    X = f"Nat.add({D}, 2n)"
    h1 = le_from(X, "c", "Nat.double(k)", hyp("ef", f"Nat.add(Nat.double(k), {X})", "c"))
    emit("# d + 2 does not wrap: d + 2 <= c < 2^17 <= 2^32")
    emit(f"def kp.d2(+d: U32, +k: Nat, +c: Nat, ef: {eq(f'Nat.add(Nat.double(k), {X})', 'c')}, +hc: {bt(f'Nat.is_lt(c, {B17})')}) -> {eq(T2, X)}:")
    emit(f"  +h1 = {h1}")
    emit(f"  +hb = kp.le_lt({X}, {B17}, kp.le_trans(1n+{X}, 1n+c, {B17}, h1, kp.lt_sle(c, {B17}, hc)))")
    emit(f"  +hz = kp.le_lt({X}, {B32}, kp.le_trans(1n+{X}, {B17}, {B32}, kp.lt_sle({X}, {B17}, hb), UL.dbl_le_exp(17n, 32n, 1n, {{==}})))")
    emit(f"  UL.dbl_nowrap(32n, U.U32Nat.bit(U32.is_lt({D2}, d)), {T2}, {X}, {X}, UL.u32_add_wrap(d, 2), UL.nat_le_refl({X}), hz)")
    emit()
    composite(emit)
    no_divisor(emit)


def step_terms(emit_lets):
    """the lets and the facts for the loop's next step: od2, ef2 (and de)"""
    efp = calc(f"Nat.add(Nat.double(k), Nat.add({D}, 2n))", (f"2n+Nat.add(Nat.double(k), {D})", "ring"),
               ("c", hyp("ef", f"2n+Nat.add(Nat.double(k), {D})", "c")))
    ef2 = calc(f"Nat.add(Nat.double(k), {T2})", (f"Nat.add(Nat.double(k), Nat.add({D}, 2n))", hyp("de", T2, f"Nat.add({D}, 2n)")),
               ("c", hyp("ef1", f"Nat.add(Nat.double(k), Nat.add({D}, 2n))", "c")))
    od2 = calc(T2, (f"Nat.add({D}, 2n)", hyp("de", T2, f"Nat.add({D}, 2n)")), ("Nat.add(3n+Nat.double(i), 2n)", hyp("od", D, "3n+Nat.double(i)")),
               ("3n+Nat.double(1n+i)", "ring"))
    return efp, ef2, od2


def composite(emit):
    emit("# composite_divisor: the loop answers False only at a d that divides n")
    emit("# with d^2 <= n")
    emit()
    # the hit case
    w, W = wit_le(D, Q, "le")
    pf = calc(f"Nat.add(Nat.add(Nat.mul({w}, {D}), {R}), Nat.mul({D}, {D}))", (f"Nat.add(Nat.mul(Nat.add({w}, {D}), {D}), {R})", "ring"),
              (f"Nat.add(Nat.mul({Q}, {D}), {R})", W), (NN, hyp("dv", f"Nat.add(Nat.mul({Q}, {D}), {R})", NN)))
    hdd = le_from(f"Nat.mul({D}, {D})", NN, f"Nat.add(Nat.mul({w}, {D}), {R})", pf)
    t = "Nat.double(i)"
    w2 = f"Nat.add(5n, Nat.add(Nat.mul(5n, {t}), Nat.mul({t}, {t})))"
    ODH = hyp("od", D, f"3n+{t}")
    pf2 = calc(f"Nat.add({w2}, 1n+{D})", (f"Nat.add({w2}, 4n+{t})", ODH), (f"Nat.mul(3n+{t}, 3n+{t})", "ring"), (f"Nat.mul({D}, {D})", ODH))
    hlt = lt_from(D, f"Nat.mul({D}, {D})", w2, pf2)
    eqk = calc(f"Nat.mul({Q}, {D})", (f"Nat.add(Nat.mul({Q}, {D}), 0n)", "ring"), (f"Nat.add(Nat.mul({Q}, {D}), {R})", N.sym(hyp("r0", R, "0n"))),
               (NN, hyp("dv", f"Nat.add(Nat.mul({Q}, {D}), {R})", NN)))
    emit(f"def kp.cd.hit(+n: U32, +d: U32, +i: Nat, ep: {eq('False{}', PAST('d'), 'Bool')}, eh: {eq('True{}', HIT('d'), 'Bool')}, +od: {OD}) -> {RES}:")
    emit("  +dz = kp.dnz(d, i, od)")
    emit("  +dv = UL.u32_divmod(n, d, dz)")
    emit(f"  +le = kp.nlt_le({Q}, {D}, {tB(f'Nat.is_lt({Q}, {D})', PAST('d'), 'False{}', sB(PAST('d'), f'Nat.is_lt({Q}, {D})', 'kp.past(n, d)'), sB('False{}', PAST('d'), 'ep'))})")
    emit(f"  +r0 = kp.z0({R}, {tB(f'Nat.is_eq({R}, 0n)', HIT('d'), 'True{}', sB(HIT('d'), f'Nat.is_eq({R}, 0n)', 'UL.u32_eq_value(U32.mod(n, d), 0)'), sB('True{}', HIT('d'), 'eh'))})")
    emit(f"  +hdd = {hdd}")
    emit(f"  +hlt = {hlt}")
    emit(f"  ({D}, (kp.ge2(d, i, od), (kp.le_lt({D}, {NN}, kp.le_trans(1n+{D}, Nat.mul({D}, {D}), {NN}, kp.lt_sle({D}, Nat.mul({D}, {D}), hlt), hdd)), ({Q}, {eqk.text}))))")
    emit()
    efp, ef2, od2 = step_terms(None)
    params = (f"+f: Nat, +past: Bool, +hit: Bool, +n: U32, +d: U32, +i: Nat, +c: Nat, ep: {eq('past', PAST('d'), 'Bool')}, eh: {eq('hit', HIT('d'), 'Bool')}, "
              f"+od: {OD}, ef: {eq(f'Nat.add(Nat.double(f), {D})', 'c')}, +hc: {HC}, r: {eq(GO('f', 'past', 'hit', 'd'), 'False{}', 'Bool')}")
    emit(f"def kp.cd({params}) -> {RES}:")
    emit("  match f past hit:")
    emit("    case _ True{} _:")
    emit(f"      Empty.absurd({RES}, kp.tf(r))")
    emit("    case _ False{} True{}:")
    emit("      kp.cd.hit(n, d, i, ep, eh, od)")
    emit("    case 0n False{} False{}:")
    emit(f"      Empty.absurd({RES}, kp.tf(r))")
    emit("    case 1n+k False{} False{}:")
    emit(f"      +ef1 = {efp.text}")
    emit("      +de = kp.d2(d, k, c, ef1, hc)")
    emit(f"      kp.cd(k, {PAST(D2)}, {HIT(D2)}, n, {D2}, 1n+i, c, {{==}}, {{==}}, {od2.text}, {ef2.text}, hc, r)")
    emit()
    # the small and even cases
    emit(f"def kp.or23(+n: U32) -> {eq(ORU, ORN, 'Bool')}:")
    a = f"Equal.cong(Bool, Bool, z => Bool.or(z, U32.is_eq(n, 3)), U32.is_eq(n, 2), Nat.is_eq({NN}, 2n), UL.u32_eq_value(n, 2))"
    b = f"Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq({NN}, 2n), z), U32.is_eq(n, 3), Nat.is_eq({NN}, 3n), UL.u32_eq_value(n, 3))"
    emit(f"  {tB(ORU, f'Bool.or(Nat.is_eq({NN}, 2n), U32.is_eq(n, 3))', ORN, a, b)}")
    emit()
    o = lambda x: bt(f"Bool.or(Nat.is_eq({x}, 2n), Nat.is_eq({x}, 3n))")  # noqa: E731
    emit(f"def kp.s23x(+x: Nat, hl: {bt('Nat.is_lt(x, 4n)')}, hg: {bt('Nat.is_le(2n, x)')}) -> {o('x')}:")
    emit("  match x:")
    emit("    case 0n:")
    emit(f"      Empty.absurd({o('0n')}, kp.ft(hg))")
    emit("    case 1n+y:")
    emit("      match y:")
    emit("        case 0n:")
    emit(f"          Empty.absurd({o('1n')}, kp.ft(hg))")
    emit("        case 1n+z:")
    emit("          match z:")
    emit("            case 0n:")
    emit("              {==}")
    emit("            case 1n+u:")
    emit("              match u:")
    emit("                case 0n:")
    emit("                  {==}")
    emit("                case 1n+v:")
    emit(f"                  Empty.absurd({o('4n+v')}, kp.lt0(v, hl))")
    emit()
    emit(f"def kp.s2x(+x: Nat, ho: {o('x')}) -> {bt('Nat.is_le(2n, x)')}:")
    emit("  match x:")
    emit("    case 0n:")
    emit(f"      Empty.absurd({bt('Nat.is_le(2n, 0n)')}, kp.ft(ho))")
    emit("    case 1n+y:")
    emit("      match y:")
    emit("        case 0n:")
    emit(f"          Empty.absurd({bt('Nat.is_le(2n, 1n)')}, kp.ft(ho))")
    emit("        case 1n+z:")
    emit("          kp.le0(z)")
    emit()
    A, AN = "U32.and(n, 1)", "U32.to_nat(U32.and(n, 1))"
    LOW, H = f"U.U32Nat.low(1n, {NN})", f"U.U32Nat.high(1n, {NN})"
    pf = calc(f"Nat.mul({H}, 2n)", (f"Nat.double({H})", "ring"), (f"Nat.add(0n, U.U32Nat.dbl(1n, {H}))", "="),
              (f"Nat.add({LOW}, U.U32Nat.dbl(1n, {H}))", N.sym(hyp("l0", LOW, "0n"))), (NN, hyp(f"UL.low_high(1n, {NN})", f"Nat.add({LOW}, U.U32Nat.dbl(1n, {H}))", NN)))
    es = lambda s: eq("small" if s is None else s, "U32.is_lt(n, 4)", "Bool")  # noqa: E731
    ee = lambda s: eq("even" if s is None else s, f"U32.is_eq({A}, 0)", "Bool")  # noqa: E731
    emit(f"def kp.cp.even(+n: U32, es: {es('False{}')}, ee: {ee('True{}')}) -> {RES}:")
    emit(f"  +lz = kp.z0({AN}, {tB(f'Nat.is_eq({AN}, 0n)', f'U32.is_eq({A}, 0)', 'True{}', sB(f'U32.is_eq({A}, 0)', f'Nat.is_eq({AN}, 0n)', f'UL.u32_eq_value({A}, 0)'), sB('True{}', f'U32.is_eq({A}, 0)', 'ee'))})")
    emit(f"  +l0 = {tN(LOW, AN, '0n', sN(AN, LOW, 'UL.u32_and_mask(n, 1, 1n, {==})'), 'lz')}")
    emit(f"  +ge4 = kp.nlt_le({NN}, 4n, {LTN4.replace('{V}', 'False{}')})")
    emit(f"  (2n, ({{==}}, (kp.le_lt(2n, {NN}, kp.le_trans(3n, 4n, {NN}, {{==}}, ge4)), ({H}, {pf.text}))))")
    emit()
    pk = eq("P.kprime.pick(small, even, n)", "{V}", "Bool")
    emit(f"def kp.cp(+small: Bool, +even: Bool, +n: U32, es: {es(None)}, ee: {ee(None)}, h: {pk.replace('{V}', 'False{}')}, +h2: {bt(f'Nat.is_le(2n, {NN})')}) -> {RES}:")
    emit("  match small even:")
    emit("    case True{} _:")
    emit(f"      +o = kp.s23x({NN}, {LTN4.replace('{V}', 'True{}')}, h2)")
    emit(f"      Empty.absurd({RES}, kp.tf({tB('True{}', ORN, 'False{}', sB(ORN, 'True{}', 'o'), tB(ORN, ORU, 'False{}', sB(ORU, ORN, 'kp.or23(n)'), 'h'))}))")
    emit("    case False{} True{}:")
    emit("      kp.cp.even(n, es, ee)")
    emit("    case False{} False{}:")
    emit(f"      kp.cd(32768n, {PAST('3')}, {HIT('3')}, n, 3, 0n, {C0}, {{==}}, {{==}}, {{==}}, {{==}}, {{==}}, h)")
    emit()
    emit("def Laws.composite_divisor(n, h, h2):")
    emit(f"  kp.cp(U32.is_lt(n, 4), U32.is_eq({A}, 0), n, {{==}}, {{==}}, h, h2)")
    emit()
    emit(f"def kp.ge(+small: Bool, +even: Bool, +n: U32, es: {es(None)}, ee: {ee(None)}, h: {pk.replace('{V}', 'True{}')}) -> {bt(f'Nat.is_le(2n, {NN})')}:")
    emit("  match small even:")
    emit("    case True{} _:")
    emit(f"      kp.s2x({NN}, {tB(ORN, ORU, 'True{}', sB(ORU, ORN, 'kp.or23(n)'), 'h')})")
    emit("    case False{} True{}:")
    emit(f"      Empty.absurd({bt(f'Nat.is_le(2n, {NN})')}, kp.ft(h))")
    emit("    case False{} False{}:")
    emit(f"      kp.le_trans(2n, 4n, {NN}, {{==}}, kp.nlt_le({NN}, 4n, {LTN4.replace('{V}', 'False{}')}))")
    emit()
    emit("def Laws.prime_ge2(n, h):")
    emit(f"  kp.ge(U32.is_lt(n, 4), U32.is_eq({A}, 0), n, {{==}}, {{==}}, h)")
    emit()


def no_divisor(emit):
    emit("# prime_no_divisor: a divisor m of n, odd, with 3 <= m and m^2 <= n, makes")
    emit("# the loop answer False")
    emit()
    # the loop stops past: N < d^2 <= m^2 <= N
    w1, W1 = wit_lt(Q, D, "hq")
    w2, W2 = wit_lt(R, D, "ml")
    dv = hyp("dv", f"Nat.add(Nat.mul({Q}, {D}), {R})", NN)
    pf = calc(f"Nat.add(Nat.add(Nat.mul({w1}, {D}), {w2}), 1n+{NN})",
              (f"Nat.add(Nat.add(Nat.mul({w1}, {D}), {w2}), 1n+Nat.add(Nat.mul({Q}, {D}), {R}))", N.sym(dv)),
              (f"Nat.add(Nat.add(Nat.mul({w1}, {D}), Nat.mul({Q}, {D})), Nat.add({w2}, 1n+{R}))", "ring"),
              (f"Nat.add(Nat.add(Nat.mul({w1}, {D}), Nat.mul({Q}, {D})), {D})", W2),
              (f"Nat.mul(Nat.add({w1}, 1n+{Q}), {D})", "ring"),
              (f"Nat.mul({D}, {D})", W1))
    lt = lt_from(NN, f"Nat.mul({D}, {D})", f"Nat.add(Nat.mul({w1}, {D}), {w2})", pf)
    EW = hyp("ew", f"Nat.add(w, {D})", "m")
    pf2 = calc(f"Nat.add(Nat.add(Nat.mul(w, m), Nat.mul({D}, w)), Nat.mul({D}, {D}))",
               (f"Nat.add(Nat.mul(w, m), Nat.mul({D}, Nat.add(w, {D})))", "ring"),
               (f"Nat.add(Nat.mul(w, m), Nat.mul({D}, m))", EW),
               (f"Nat.mul(Nat.add(w, {D}), m)", "ring"),
               ("Nat.mul(m, m)", EW))
    le2 = le_from(f"Nat.mul({D}, {D})", "Nat.mul(m, m)", f"Nat.add(Nat.mul(w, m), Nat.mul({D}, w))", pf2)
    MM = "Nat.mul(m, m)"
    HMM = f"+hmm: {bt(f'Nat.is_le({MM}, {NN})')}"
    emit(f"def kp.ln.past(+n: U32, +d: U32, +i: Nat, +m: Nat, +w: Nat, ep: {eq('True{}', PAST('d'), 'Bool')}, +od: {OD}, +ew: {eq(f'Nat.add(w, {D})', 'm')}, {HMM}) -> Empty:")
    emit("  +dz = kp.dnz(d, i, od)")
    emit("  +dv = UL.u32_divmod(n, d, dz)")
    emit("  +ml = UL.u32_mod_lt(n, d, dz)")
    emit(f"  +hq = {tB(f'Nat.is_lt({Q}, {D})', PAST('d'), 'True{}', sB(PAST('d'), f'Nat.is_lt({Q}, {D})', 'kp.past(n, d)'), sB('True{}', PAST('d'), 'ep'))}")
    emit(f"  +lt = {lt}")
    emit(f"  +le2 = {le2}")
    DD = f"Nat.mul({D}, {D})"
    emit(f"  kp.irr({NN}, kp.le_lt({NN}, {NN}, kp.le_trans(1n+{NN}, {DD}, {NN}, kp.lt_sle({NN}, {DD}, lt), kp.le_trans({DD}, {MM}, {NN}, le2, hmm))))")
    emit()
    # the fuel runs out: d = c > 2^16, so m^2 > 2^32 > N
    M16 = f"Nat.mul({B16}, {B16})"
    sq = tN(M16, f"U.U32Nat.dbl(16n, Nat.mul(1n, {B16}))", B32, f"UL.dbl_mul_l(16n, 1n, {B16})",
            tN(f"U.U32Nat.dbl(16n, Nat.mul(1n, {B16}))", f"U.U32Nat.dbl(16n, {B16})", B32,
               f"Equal.cong(Nat, Nat, z => U.U32Nat.dbl(16n, z), Nat.mul(1n, {B16}), {B16}, UL.nat_one_mul({B16}))",
               tN(f"U.U32Nat.dbl(16n, {B16})", "U.U32Nat.dbl(Nat.add(16n, 16n), 1n)", B32, "UL.dbl_dbl(16n, 16n, 1n)",
                  "Equal.cong(Nat, Nat, z => U.U32Nat.dbl(z, 1n), Nat.add(16n, 16n), 32n, {==})")))
    emit(f"def kp.ln.fuel(+n: U32, +d: U32, +m: Nat, +w: Nat, +c: Nat, ef: {eq(f'Nat.add(Nat.double(0n), {D})', 'c')}, +hc16: {HC16}, +ew: {eq(f'Nat.add(w, {D})', 'm')}, {HMM}) -> Empty:")
    emit(f"  +h16 = {tB(f'Nat.is_lt({B16}, {D})', f'Nat.is_lt({B16}, c)', 'True{}', cB(f'Nat.is_lt({B16}, z)', D, 'c', 'ef'), 'hc16')}")
    emit(f"  +dm = {le_from(D, 'm', 'w', EW)}")
    emit(f"  +h16m = kp.le_lt({B16}, m, kp.le_trans(1n+{B16}, {D}, m, kp.lt_sle({B16}, {D}, h16), dm))")
    emit(f"  +mlt = UL.nat_mul_lt({B16}, {B16}, m, m, h16m, h16m)")
    emit(f"  +l32 = {lt_rw(NN, B32, NN, M16, None, sN(M16, B32, sq), f'kp.lt32(n)')}")
    emit(f"  kp.irr({NN}, kp.le_lt({NN}, {NN}, kp.le_trans(1n+{NN}, {MM}, {NN}, kp.lt_sle({NN}, {MM}, kp.lt_trans({NN}, {M16}, {MM}, l32, mlt)), hmm)))")
    emit()
    # d = m: m divides n, so the test hits
    e = calc(f"Nat.add(Nat.mul({Q}, {D}), {R})", (NN, dv), ("Nat.mul(cm, m)", N.sym(hyp("ecm", "Nat.mul(cm, m)", NN))),
             (f"Nat.mul(cm, {D})", N.sym(hyp("ew", D, "m"))), (f"Nat.add(Nat.mul(cm, {D}), 0n)", "ring"))
    ECM = f"+ecm: {eq('Nat.mul(cm, m)', NN)}"
    emit(f"def kp.ln.eq(+n: U32, +d: U32, +i: Nat, +m: Nat, +cm: Nat, eh: {eq('False{}', HIT('d'), 'Bool')}, +od: {OD}, ew: {eq(f'Nat.add(0n, {D})', 'm')}, {ECM}) -> Empty:")
    emit("  +dz = kp.dnz(d, i, od)")
    emit("  +dv = UL.u32_divmod(n, d, dz)")
    emit("  +ml = UL.u32_mod_lt(n, d, dz)")
    emit(f"  +hz = {tB(f'Nat.is_lt(0n, {D})', 'Nat.is_lt(0n, 3n+Nat.double(i))', 'True{}', cB('Nat.is_lt(0n, z)', D, '3n+Nat.double(i)', 'od'), '{==}')}")
    emit(f"  +r0 = UL.nat_mod_unique({D}, {Q}, {R}, cm, 0n, {e.text}, ml, hz)")
    emit(f"  +hf = {tB(f'Nat.is_eq({R}, 0n)', HIT('d'), 'False{}', sB(HIT('d'), f'Nat.is_eq({R}, 0n)', 'UL.u32_eq_value(U32.mod(n, d), 0)'), sB('False{}', HIT('d'), 'eh'))}")
    emit(f"  kp.tf({tB('True{}', f'Nat.is_eq({R}, 0n)', 'False{}', cB('Nat.is_eq(z, 0n)', '0n', R, sN(R, '0n', 'r0')), 'hf')})")
    emit()
    # d + 1 = m: both odd, impossible
    pe = calc("1n+Nat.double(j)", ("m", N.sym(hyp("om", "m", "1n+Nat.double(j)"))), (f"1n+{D}", N.sym(hyp("ew", f"1n+{D}", "m"))),
              ("4n+Nat.double(i)", hyp("od", D, "3n+Nat.double(i)")))
    OM = eq("m", "1n+Nat.double(j)")
    emit(f"def kp.ln.par(+d: U32, +i: Nat, +m: Nat, +j: Nat, +od: {OD}, +om: {OM}, ew: {eq(f'Nat.add(1n, {D})', 'm')}) -> Empty:")
    emit(f"  kp.par(1n+i, j, UL.nat_add_cancel(1n, Nat.double(j), 1n+Nat.double(1n+i), {pe.text}))")
    emit()
    efp, ef2, od2 = step_terms(None)
    ew2 = calc(f"Nat.add(w2, {T2})", (f"Nat.add(w2, Nat.add({D}, 2n))", hyp("de", T2, f"Nat.add({D}, 2n)")), (f"2n+Nat.add(w2, {D})", "ring"),
               ("m", hyp("ew", f"2n+Nat.add(w2, {D})", "m")))
    params = (f"+f: Nat, +past: Bool, +hit: Bool, +w: Nat, +n: U32, +d: U32, +i: Nat, +m: Nat, +j: Nat, +cm: Nat, +c: Nat, "
              f"ep: {eq('past', PAST('d'), 'Bool')}, eh: {eq('hit', HIT('d'), 'Bool')}, +od: {OD}, ef: {eq(f'Nat.add(Nat.double(f), {D})', 'c')}, +hc: {HC}, +hc16: {HC16}, "
              f"+om: {OM}, ew: {eq(f'Nat.add(w, {D})', 'm')}, {HMM}, {ECM}")
    emit(f"def kp.ln({params}) -> {eq(GO('f', 'past', 'hit', 'd'), 'False{}', 'Bool')}:")
    emit("  match f past hit:")
    emit("    case _ True{} _:")
    emit(f"      Empty.absurd({eq(GO('f', 'True{}', 'hit', 'd'), 'False{}', 'Bool')}, kp.ln.past(n, d, i, m, w, ep, od, ew, hmm))")
    emit("    case _ False{} True{}:")
    emit("      {==}")
    emit("    case 0n False{} False{}:")
    emit(f"      Empty.absurd({eq(GO('0n', 'False{}', 'False{}', 'd'), 'False{}', 'Bool')}, kp.ln.fuel(n, d, m, w, c, ef, hc16, ew, hmm))")
    emit("    case 1n+k False{} False{}:")
    G1 = eq(GO("1n+k", "False{}", "False{}", "d"), "False{}", "Bool")
    emit("      match w:")
    emit("        case 0n:")
    emit(f"          Empty.absurd({G1}, kp.ln.eq(n, d, i, m, cm, eh, od, ew, ecm))")
    emit("        case 1n+w1:")
    emit("          match w1:")
    emit("            case 0n:")
    emit(f"              Empty.absurd({G1}, kp.ln.par(d, i, m, j, od, om, ew))")
    emit("            case 1n+w2:")
    emit(f"              +ef1 = {efp.text}")
    emit("              +de = kp.d2(d, k, c, ef1, hc)")
    emit(f"              kp.ln(k, {PAST(D2)}, {HIT(D2)}, w2, n, {D2}, 1n+i, m, j, cm, c, {{==}}, {{==}}, {od2.text}, {ef2.text}, hc, hc16, om, {ew2.text}, hmm, ecm)")
    emit()
    # m is odd, so at least 3; the loop then answers False
    ew = calc("Nat.add(Nat.double(jp), U32.to_nat(3))", ("Nat.add(Nat.double(jp), 3n)", "="), ("3n+Nat.double(jp)", "ring"),
              ("m", N.sym(hyp("om", "m", "3n+Nat.double(jp)"))))
    emit(f"def kp.fin2(+n: U32, +m: Nat, +cm: Nat, +j: Nat, {ECM}, {HMM}, +hm2: {bt('Nat.is_le(2n, m)')}, h: {bt(ODD)}, +om: {OM}) -> Empty:")
    emit("  match j:")
    emit("    case 0n:")
    emit(f"      kp.ft({tB('Nat.is_le(2n, 1n)', 'Nat.is_le(2n, m)', 'True{}', cB('Nat.is_le(2n, z)', '1n', 'm', sN('m', '1n', 'om')), 'hm2')})")
    emit("    case 1n+jp:")
    ln = f"kp.ln(32768n, {PAST('3')}, {HIT('3')}, Nat.double(jp), n, 3, 0n, m, 1n+jp, cm, {C0}, {{==}}, {{==}}, {{==}}, {{==}}, {{==}}, {{==}}, om, {ew.text}, hmm, ecm)"
    emit(f"      kp.ft({tB('False{}', ODD, 'True{}', sB(ODD, 'False{}', ln), 'h')})")
    emit()
    LOWm, J = "U.U32Nat.low(1n, m)", "U.U32Nat.high(1n, m)"
    H = f"U.U32Nat.high(1n, {NN})"
    LH = hyp("UL.low_high(1n, m)", f"Nat.add({LOWm}, U.U32Nat.dbl(1n, {J}))", "m")
    me = calc("m", (f"Nat.add({LOWm}, U.U32Nat.dbl(1n, {J}))", N.sym(LH)), (f"Nat.add(0n, U.U32Nat.dbl(1n, {J}))", hyp("ex", LOWm, "0n")), (f"Nat.double({J})", "="))
    pe = calc(f"Nat.double(Nat.mul(cm, {J}))", (f"Nat.mul(cm, Nat.double({J}))", "ring"), ("Nat.mul(cm, m)", N.sym(hyp("me", "m", f"Nat.double({J})"))),
              (NN, hyp("ecm", "Nat.mul(cm, m)", NN)), (f"1n+Nat.double({H})", hyp("on", NN, f"1n+Nat.double({H})")))
    m1 = calc("m", (f"Nat.add({LOWm}, U.U32Nat.dbl(1n, {J}))", N.sym(LH)), (f"Nat.add(1n, U.U32Nat.dbl(1n, {J}))", hyp("ex", LOWm, "1n")), (f"1n+Nat.double({J})", "="))
    GJ = eq("m", f"1n+Nat.double({J})")
    ON = f"+on: {eq(NN, f'1n+Nat.double({H})')}"
    emit(f"def kp.mj(+x: Nat, +m: Nat, +cm: Nat, +n: U32, +ex: {eq(LOWm, 'x')}, {ECM}, {ON}) -> {GJ}:")
    emit("  match x:")
    emit("    case 0n:")
    emit(f"      +me = {me.text}")
    emit(f"      Empty.absurd({GJ}, kp.par({H}, Nat.mul(cm, {J}), {pe.text}))")
    emit("    case 1n+y:")
    emit("      match y:")
    emit("        case 0n:")
    emit(f"          {m1.text}")
    emit("        case 1n+z:")
    l2 = tB("Nat.is_lt(2n+z, 2n)", f"Nat.is_lt({LOWm}, 2n)", "True{}", sB(f"Nat.is_lt({LOWm}, 2n)", "Nat.is_lt(2n+z, 2n)", cB("Nat.is_lt(z, 2n)", LOWm, "2n+z", "ex")), "UL.low_lt(1n, m)")
    emit(f"          Empty.absurd({GJ}, kp.lt0(z, {l2}))")
    emit()
    emit(f"def kp.fin(+n: U32, +m: Nat, +cm: Nat, {ECM}, {HMM}, +hm2: {bt('Nat.is_le(2n, m)')}, {ON}, h: {bt(ODD)}) -> Empty:")
    emit(f"  kp.fin2(n, m, cm, {J}, ecm, hmm, hm2, h, kp.mj({LOWm}, m, cm, n, {{==}}, ecm, on))")
    emit()
    # n odd
    A, AN = "U32.and(n, 1)", "U32.to_nat(U32.and(n, 1))"
    LOW = f"U.U32Nat.low(1n, {NN})"
    onp = calc(NN, (f"Nat.add({LOW}, U.U32Nat.dbl(1n, {H}))", N.sym(hyp(f"UL.low_high(1n, {NN})", f"Nat.add({LOW}, U.U32Nat.dbl(1n, {H}))", NN))),
               (f"Nat.add(1n, U.U32Nat.dbl(1n, {H}))", hyp("one", LOW, "1n")), (f"1n+Nat.double({H})", "="))
    emit(f"def kp.oddN(+n: U32, ee: {eq('False{}', f'U32.is_eq({A}, 0)', 'Bool')}) -> {eq(NN, f'1n+Nat.double({H})')}:")
    emit(f"  +e1 = {tB(f'Nat.is_eq({AN}, 0n)', f'U32.is_eq({A}, 0)', 'False{}', sB(f'U32.is_eq({A}, 0)', f'Nat.is_eq({AN}, 0n)', f'UL.u32_eq_value({A}, 0)'), sB('False{}', f'U32.is_eq({A}, 0)', 'ee'))}")
    emit("  +am = UL.u32_and_mask(n, 1, 1n, {==})")
    emit(f"  +pos = {tB(f'Nat.is_lt(0n, {LOW})', f'Nat.is_lt(0n, {AN})', 'True{}', cB('Nat.is_lt(0n, z)', LOW, AN, sN(AN, LOW, 'am')), f'kp.nz({AN}, e1)')}")
    emit(f"  +one = kp.one({LOW}, kp.lt_sle({LOW}, 2n, UL.low_lt(1n, {NN})), pos)")
    emit(f"  {onp.text}")
    emit()
    # m = min(e, c)
    wt, Wt = wit_le("e", "c", "et")
    pft = calc("Nat.add(Nat.mul(" + wt + ", e), Nat.mul(e, e))", (f"Nat.mul(Nat.add({wt}, e), e)", "ring"), ("Nat.mul(c, e)", Wt), (NN, hyp("hm", "Nat.mul(c, e)", NN)))
    wf, Wf = wit_le("c", "e", "lc")
    ecm = calc("Nat.mul(e, c)", ("Nat.mul(c, e)", "ring"), (NN, hyp("hm", "Nat.mul(c, e)", NN)))
    pff = calc("Nat.add(Nat.mul(" + wf + ", c), Nat.mul(c, c))", (f"Nat.mul(Nat.add({wf}, c), c)", "ring"), ("Nat.mul(e, c)", Wf), ("Nat.mul(c, e)", "ring"),
               (NN, hyp("hm", "Nat.mul(c, e)", NN)))
    HM = f"+hm: {eq('Nat.mul(c, e)', NN)}"
    emit(f"def kp.split(+t: Bool, +n: U32, +e: Nat, +c: Nat, et: {eq('Nat.is_le(e, c)', 't', 'Bool')}, +h1: {bt('Nat.is_le(2n, e)')}, +hc: {bt('Nat.is_le(2n, c)')}, {HM}, {ON}, h: {bt(ODD)}) -> Empty:")
    emit("  match t:")
    emit("    case True{}:")
    emit(f"      kp.fin(n, e, c, hm, {le_from('Nat.mul(e, e)', NN, f'Nat.mul({wt}, e)', pft)}, h1, on, h)")
    emit("    case False{}:")
    emit("      +lc = kp.lt_le(c, e, kp.nle_lt(e, c, et))")
    emit(f"      kp.fin(n, c, e, {ecm.text}, {le_from('Nat.mul(c, c)', NN, f'Nat.mul({wf}, c)', pff)}, hc, on, h)")
    emit()
    emit(f"def kp.nd(+small: Bool, +even: Bool, +n: U32, +e: Nat, +c: Nat, es: {eq('small', 'U32.is_lt(n, 4)', 'Bool')}, ee: {eq('even', f'U32.is_eq({A}, 0)', 'Bool')}, "
         f"h: {eq('P.kprime.pick(small, even, n)', 'True{}', 'Bool')}, +h1: {bt('Nat.is_le(2n, e)')}, +hc: {bt('Nat.is_le(2n, c)')}, {HM}, +h4: {bt(f'Nat.is_le(4n, {NN})')}) -> Empty:")
    emit("  match small even:")
    emit("    case True{} _:")
    emit(f"      kp.irr({NN}, kp.le_lt({NN}, {NN}, kp.le_trans(1n+{NN}, 4n, {NN}, kp.lt_sle({NN}, 4n, {LTN4.replace('{V}', 'True{}')}), h4)))")
    emit("    case False{} True{}:")
    emit("      kp.ft(h)")
    emit("    case False{} False{}:")
    emit("      kp.split(Nat.is_le(e, c), n, e, c, {==}, h1, hc, hm, kp.oddN(n, ee), h)")
    emit()
    # k >= 2, and so n >= 4
    emit(f"def kp.cf2(+c: Nat, +e: Nat, +x: Nat, hm: {eq('Nat.mul(c, e)', 'x')}, h2: {bt('Nat.is_lt(e, x)')}) -> {bt('Nat.is_le(2n, c)')}:")
    emit("  match c:")
    emit("    case 0n:")
    emit(f"      Empty.absurd({bt('Nat.is_le(2n, 0n)')}, kp.lt0(e, {tB('Nat.is_lt(e, 0n)', 'Nat.is_lt(e, x)', 'True{}', cB('Nat.is_lt(e, z)', '0n', 'x', 'hm'), 'h2')}))")
    emit("    case 1n+cp:")
    emit("      match cp:")
    emit("        case 0n:")
    E = tN("e", "Nat.mul(1n, e)", "x", sN("Nat.mul(1n, e)", "e", "UL.nat_one_mul(e)"), "hm")
    emit(f"          Empty.absurd({bt('Nat.is_le(2n, 1n)')}, kp.irr(e, {tB('Nat.is_lt(e, e)', 'Nat.is_lt(e, x)', 'True{}', cB('Nat.is_lt(e, z)', 'e', 'x', E), 'h2')}))")
    emit("        case 1n+cq:")
    emit("          kp.le0(cq)")
    emit()
    s1, W1 = wit_le("2n", "k", "hc")
    s2, W2 = wit_le("2n", "d", "h1b")
    w4 = f"Nat.add(Nat.add(Nat.mul(2n, {s1}), Nat.mul(2n, {s2})), Nat.mul({s1}, {s2}))"
    pf4 = calc(f"Nat.add({w4}, 4n)", (f"Nat.mul(Nat.add({s1}, 2n), Nat.add({s2}, 2n))", "ring"), (f"Nat.mul(k, Nat.add({s2}, 2n))", W1),
               ("Nat.mul(k, d)", W2), (NN, hyp("eb", "Nat.mul(k, d)", NN)))
    emit("def Laws.prime_no_divisor(n, d, k, h, h1, h2, e):")
    emit("  +h1b = h1")
    emit("  +eb = e")
    emit(f"  +hc = kp.cf2(k, d, {NN}, eb, h2)")
    emit(f"  +h4 = {le_from('4n', NN, w4, pf4)}")
    emit(f"  kp.nd(U32.is_lt(n, 4), U32.is_eq({A}, 0), n, d, k, {{==}}, {{==}}, h, h1b, hc, eb, h4)")
    emit()
