"""The proofs of kstr's decimal round trips, for gen/proof.py: parsing in
base 10 after formatting with %u gives the value back, for every W64
(KStr.to_u64 after KStr.format) and every U32 (KStr.to_u32 after
KStr.format32).

kfmt.digits(n, stop, v, 10, ...) puts down the digits of v least
significant first, each one in front of the ones already down, as the
remainder r of v / 10 (kfmt.divmod: q 10 + r = v, r < 10, from the U32 or
the W64 division laws), and goes on with the quotient q until it is 0. So:

  * ks.dt(n, stop, v, tl) is the list of tokens the digits read as: each
    digit byte, masked by Octets, is the token KTDigit{r} (ks.td, by the ten
    cases of r); strip_nl leaves such a list alone, and front sees a digit
    first (ks.ta, ks.tb, ks.fr, by induction on n with the same steps);
  * parsing ks.dt(n, stop, v, tl) from 0 leaves v in the accumulator
    (ks.tp, ks.tq): by induction, the digits of q leave q, and one more
    step, acc 10 + r, gives v. In 64 bits (kstr.mul64) that step does not
    overflow since v < 2^64 (ks.ml); in 32 bits (kstr.mul.fin) since v <
    2^32 (ks.ml32). The fuel n is enough: v < 2^n and q < 2^(n - 1).

Every lemma that holds 2^32 or 2^64 states it in the exact form a law
takes it (u32/README.md, "Stating the bounds"), and no fact whose type
holds one is ever bound to a name (a binding's type is normalized).
"""
import natproof as N
from natproof import btrue, calc, hyp, le_from, lt_rw, sym

R64 = "Result<&2, &2, K.KStrError, W.W64>"
R32 = "Result<&2, &2, K.KStrError, U32>"
TL = "List<&2, K.KStrTok>"
W32 = "U.U32Nat.dbl(32n, 1n)"
W64 = "U.U32Nat.dbl(64n, 1n)"


def v32(x):
    return f"U32.to_nat({x})"


def v64(x):
    return f"W.W64.to_nat({x})"


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


def DQR(v):
    return f"F.kfmt.divmod(U32.is_eq(W.W64.hi({v}), 0), {v}, 10)"


def Q(v):
    return f"F.kfmt.q({DQR(v)})"


def R(v):
    return f"F.kfmt.r({DQR(v)})"


def DIG(r):
    return f"F.kfmt.digit.pick(U32.is_lt({r}, 10), False{{}}, {r})"


def DS(n, z, v, acc):
    return f"F.kfmt.digits({n}, {z}, {v}, 10, False{{}}, {acc})"


def DT(n, z, v, tl):
    return f"ks.dt({n}, {z}, {v}, {tl})"


def ZQ(v):
    return f"W.W64.is_zero({Q(v)})"


def lemmas(put):
    N.bend_order(put, "ks")
    N.bend_words(put, "ks")
    put(f"""# More bounds: a W64 value below 2^64, x <= 0, and a W64 below 2^32 has a
# zero high half

def ks.le00(x: Nat, h: {btrue('Nat.is_le(x, 0n)')}) -> {{x == 0n : Nat}}:
  match x:
    case 0n:
      {{==}}
    case 1n+ +p:
      Empty.absurd({{1n+p == 0n : Nat}}, ks.ft(h))

def ks.d64(+n: Nat, +m: Nat, +y: Nat, e: {{Nat.add(n, n) == m : Nat}}, h: {btrue(f'Nat.is_lt(y, {D("m", "1n")})')}) -> {btrue(f'Nat.is_lt(y, {D("n", D("n", "1n"))})')}:
  %Equal.sym(Nat, {D("n", D("n", "1n"))}, {D("Nat.add(n, n)", "1n")}, UL.dbl_dbl(n, n, 1n)) : {btrue('Nat.is_lt(y, _)')}
  %Equal.sym(Nat, Nat.add(n, n), m, e) : {btrue(f'Nat.is_lt(y, {D("_", "1n")})')}
  h

def ks.lelt(+a: Nat, +b: Nat, +c: Nat, h1: {btrue('Nat.is_le(a, b)')}, h2: {btrue('Nat.is_lt(b, c)')}) -> {btrue('Nat.is_lt(a, c)')}:
  ks.le_lt(a, c, ks.le_trans(1n+a, 1n+b, c, h1, ks.lt_sle(b, c, h2)))
""")
    # x + 2^n y < 2^(2n), for x, y < 2^n
    WL_ = hyp("wl", "Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+l), 1n+l)", D("n", "1n"))
    WH = hyp("wh", "Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+h), 1n+h)", D("n", "1n"))
    a = "Nat.sub(U.U32Nat.dbl(n, 1n), 1n+l)"
    b = "Nat.sub(U.U32Nat.dbl(n, 1n), 1n+h)"
    w = f"Nat.add({D('n', b)}, {a})"
    pf = calc(f"Nat.add({w}, 1n+Nat.add(l, {D('n', 'h')}))",
              (f"Nat.add({D('n', b)}, Nat.add(Nat.add({a}, 1n+l), {D('n', 'h')}))", "ring"),
              (f"Nat.add({D('n', b)}, Nat.add({D('n', '1n')}, {D('n', 'h')}))", WL_),
              (D("n", f"Nat.add({b}, 1n+h)"), "ring"),
              (D("n", D("n", "1n")), WH))
    lt = N.lt_from(f"Nat.add(l, {D('n', 'h')})", D("n", D("n", "1n")), w, pf)
    put(f"""def ks.g(+n: Nat, +m: Nat, +l: Nat, +h: Nat, e: {{Nat.add(n, n) == m : Nat}}, hl: {btrue(f'Nat.is_lt(l, {D("n", "1n")})')}, hh: {btrue(f'Nat.is_lt(h, {D("n", "1n")})')}) -> {btrue(f'Nat.is_lt(Nat.add(l, {D("n", "h")}), {D("m", "1n")})')}:
  %e : {btrue(f'Nat.is_lt(Nat.add(l, {D("n", "h")}), {D("_", "1n")})')}
  %UL.dbl_dbl(n, n, 1n) : {btrue(f'Nat.is_lt(Nat.add(l, {D("n", "h")}), _)')}
  +wl = UL.nat_lt_witness(l, {D("n", "1n")}, hl)
  +wh = UL.nat_lt_witness(h, {D("n", "1n")}, hh)
  {lt}

def ks.lt64(+v: W.W64) -> {btrue(f'Nat.is_lt({v64("v")}, {W64})')}:
  %ks.np(v) : {btrue(f'Nat.is_lt(_, {W64})')}
  ks.g(32n, 64n, {v32('W.W64.lo(v)')}, {v32('W.W64.hi(v)')}, {{==}}, ks.lt32(W.W64.lo(v)), ks.lt32(W.W64.hi(v)))
""")
    # a W64 below 2^32: its low half is its value, its high half is 0
    m = "m"
    NP = hyp("ks.np(m)", f"Nat.add({v32('W.W64.lo(m)')}, {D('32n', v32('W.W64.hi(m)'))})", v64(m))
    put(f"""def ks.lo32(+m: W.W64, h: {btrue(f'Nat.is_lt({v64("m")}, {W32})')}) -> {{{v32('W.W64.lo(m)')} == {v64('m')} : Nat}}:
  UL.dbl_nowrap(32n, {v32('W.W64.hi(m)')}, {v32('W.W64.lo(m)')}, {v64('m')}, {v64('m')}, ks.np(m), UL.nat_le_refl({v64('m')}), h)
""")
    lo, hi = v32("W.W64.lo(m)"), v32("W.W64.hi(m)")
    e = calc(f"Nat.add({lo}, {D('32n', hi)})",
             (v64(m), NP),
             (lo, sym(hyp("lq", lo, v64(m)))),
             (f"Nat.add({lo}, 0n)", sym(hyp(f"UL.nat_add_zero({lo})", f"Nat.add({lo}, 0n)", lo))))
    z = hyp(f"UL.nat_add_cancel({lo}, {D('32n', hi)}, 0n, {e.text})", D("32n", hi), "0n")
    le0 = N.btrans(f"Nat.is_le({hi}, 0n)", f"Nat.is_le({hi}, {D('32n', hi)})", "True{}",
                   N.bcong("zz", f"Nat.is_le({hi}, zz)", "0n", D("32n", hi), f"Equal.sym(Nat, {D('32n', hi)}, 0n, {z.text})"),
                   f"UL.nat_le_dbl(32n, {hi})")
    put(f"""def ks.hi0(+m: W.W64, +lq: {{{lo} == {v64('m')} : Nat}}) -> {{{hi} == 0n : Nat}}:
  ks.le00({hi}, {le0})

def ks.hz(+m: W.W64, +h0: {{{hi} == 0n : Nat}}) -> {{U32.is_eq(W.W64.hi(m), 0) == True{{}} : Bool}}:
  Equal.trans(Bool, U32.is_eq(W.W64.hi(m), 0), Nat.is_eq({hi}, 0n), True{{}}, UL.u32_eq_value(W.W64.hi(m), 0), Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 0n), {hi}, 0n, h0))
""")


def divmod_facts(put):
    put("# kfmt.divmod(..., v, 10): q 10 + r = v and r < 10, by U32 or by W64 division\n")
    v = "v"
    DM = "W.W64.divmod(v, W.W64.from_u32(10))"
    QR = f"F.kfmt.qr64({DM})"
    put(f"""def ks.oq(p: W.W64 & W.W64) -> {{W.W64.fst(p) == F.kfmt.q(F.kfmt.qr64(p)) : W.W64}}:
  (q, r) = p
  {{==}}

def ks.or(p: W.W64 & W.W64) -> {{W.W64.lo(W.W64.snd(p)) == F.kfmt.r(F.kfmt.qr64(p)) : U32}}:
  (q, r) = p
  {{==}}

def ks.dmv(+v: W.W64) -> {{Nat.add(Nat.mul({v64(f'F.kfmt.q({QR})')}, 10n), {v32(f'F.kfmt.r({QR})')}) == {v64('v')} : Nat}}:
  %ks.oq({DM}) : {{Nat.add(Nat.mul({v64('_')}, 10n), {v32(f'F.kfmt.r({QR})')}) == {v64('v')} : Nat}}
  %ks.or({DM}) : {{Nat.add(Nat.mul({v64(f'W.W64.fst({DM})')}, 10n), {v32('_')}) == {v64('v')} : Nat}}
  %ks.lo_small(W.W64.snd({DM}), 10, WL.mod_lt(v, W.W64.from_u32(10), {{==}})) : {{Nat.add(Nat.mul({v64(f'W.W64.fst({DM})')}, 10n), _) == {v64('v')} : Nat}}
  WL.divmod_value(v, W.W64.from_u32(10), {{==}})

def ks.dml(+v: W.W64) -> {btrue(f'Nat.is_lt({v32(f"F.kfmt.r({QR})")}, 10n)')}:
  +lt = WL.mod_lt(v, W.W64.from_u32(10), {{==}})
  %ks.or({DM}) : {btrue(f'Nat.is_lt({v32("_")}, 10n)')}
  %ks.lo_small(W.W64.snd({DM}), 10, lt) : {btrue('Nat.is_lt(_, 10n)')}
  lt
""")
    # the 32-bit case: hi v = 0
    L = "W.W64.lo(v)"
    QS = f"W.W64.from_u32(U32.div({L}, 10))"
    RS = f"U32.mod({L}, 10)"
    hv = v32("W.W64.hi(v)")
    H0 = hyp("h0", hv, "0n")
    e = calc(f"Nat.add(Nat.mul({v64(QS)}, 10n), {v32(RS)})",
             (f"Nat.add(Nat.mul({v32(f'U32.div({L}, 10)')}, 10n), {v32(RS)})", hyp(f"ks.fv(U32.div({L}, 10))", v64(QS), v32(f"U32.div({L}, 10)"))),
             (v32(L), hyp(f"UL.u32_divmod({L}, 10, {{==}})", f"Nat.add(Nat.mul({v32(f'U32.div({L}, 10)')}, 10n), {v32(RS)})", v32(L))),
             (f"Nat.add({v32(L)}, 0n)", sym(hyp(f"UL.nat_add_zero({v32(L)})", f"Nat.add({v32(L)}, 0n)", v32(L)))),
             (f"Nat.add({v32(L)}, {D('32n', '0n')})", "="),
             (f"Nat.add({v32(L)}, {D('32n', hv)})", sym(H0)),
             (v64("v"), hyp("ks.np(v)", f"Nat.add({v32(L)}, {D('32n', hv)})", v64("v"))))
    h0 = (f"ks.z0({hv}, Equal.trans(Bool, Nat.is_eq({hv}, 0n), U32.is_eq(W.W64.hi(v), 0), True{{}}, "
          f"Equal.sym(Bool, U32.is_eq(W.W64.hi(v), 0), Nat.is_eq({hv}, 0n), UL.u32_eq_value(W.W64.hi(v), 0)), es))")
    pair = (f"{{Nat.add(Nat.mul({v64('F.kfmt.q(F.kfmt.divmod(s, v, 10))')}, 10n), {v32('F.kfmt.r(F.kfmt.divmod(s, v, 10))')}) == {v64('v')} : Nat}} & "
            + btrue(f"Nat.is_lt({v32('F.kfmt.r(F.kfmt.divmod(s, v, 10))')}, 10n)"))
    put(f"""def ks.dm1(+v: W.W64, s: Bool, es: {{U32.is_eq(W.W64.hi(v), 0) == s : Bool}}) -> {pair}:
  match s:
    case True{{}}:
      +h0 = {h0}
      ({e.text}, UL.u32_mod_lt({L}, 10, {{==}}))
    case False{{}}:
      (ks.dmv(v), ks.dml(v))
""")
    args = f"Nat.add(Nat.mul({v64(Q('v'))}, 10n), {v32(R('v'))}), {v64('v')}, {v32(R('v'))}, 10n"
    put(f"""def ks.dmq(+v: W.W64) -> {{Nat.add(Nat.mul({v64(Q('v'))}, 10n), {v32(R('v'))}) == {v64('v')} : Nat}}:
  ks.c1({args}, ks.dm1(v, U32.is_eq(W.W64.hi(v), 0), {{==}}))

def ks.dmr(+v: W.W64) -> {btrue(f'Nat.is_lt({v32(R("v"))}, 10n)')}:
  ks.c2({args}, ks.dm1(v, U32.is_eq(W.W64.hi(v), 0), {{==}}))

# q < 2^k when q 10 + r = v < 2^m, m = 1 + k
def ks.hq(+k: Nat, +m: Nat, +q: Nat, +r: Nat, +v: Nat, em: {{1n+k == m : Nat}}, e: {{Nat.add(Nat.mul(q, 10n), r) == v : Nat}}, h: {btrue(f'Nat.is_lt(v, {D("m", "1n")})')}) -> {btrue(f'Nat.is_lt(q, {D("k", "1n")})')}:
  {hq_body()}
""")


def hq_body():
    E = hyp("e", "Nat.add(Nat.mul(q, 10n), r)", "v")
    w = "Nat.add(Nat.mul(q, 8n), r)"
    pf = calc(f"Nat.add({w}, Nat.double(q))", ("Nat.add(Nat.mul(q, 10n), r)", "ring"), ("v", E))
    le = le_from("Nat.double(q)", "v", w, pf)
    hm = (f"Equal.trans(Bool, Nat.is_lt(v, {D('1n+k', '1n')}), Nat.is_lt(v, {D('m', '1n')}), True{{}}, "
          f"Equal.cong(Nat, Bool, zz => Nat.is_lt(v, {D('zz', '1n')}), 1n+k, m, em), h)")
    lt = f"ks.lelt(Nat.double(q), v, {D('1n+k', '1n')}, {le}, {hm})"
    return (f"Equal.trans(Bool, Nat.is_lt(q, {D('k', '1n')}), Nat.is_lt({D('1n', 'q')}, {D('1n', D('k', '1n'))}), True{{}}, "
            f"Equal.sym(Bool, Nat.is_lt({D('1n', 'q')}, {D('1n', D('k', '1n'))}), Nat.is_lt(q, {D('k', '1n')}), UL.dbl_lt(1n, q, {D('k', '1n')})), {lt})")


def tokens(put):
    put("# The digit bytes as tokens\n")
    # r < 10: tok(byte(digit r)) = KTDigit{r}, by the ten cases of r's value
    goal = "{K.KStr.tok(B.byte(" + DIG("r") + ")) == K.KTDigit{r} : K.KStrTok}"
    gl = "{K.KStr.tok(B.byte(" + DIG("_") + ")) == K.KTDigit{_} : K.KStrTok}"
    out = []

    def go(depth, ind, k):
        pad = "  " * ind
        if k == 10:
            out.append(pad + f"match n{depth}:")
            out.append(pad + "  case 0n:")
            out.append(pad + f"    Empty.absurd({goal}, ks.ft(h))")
            out.append(pad + "  case 1n+ +x:")
            out.append(pad + f"    Empty.absurd({goal}, ks.ft(h))")
            return
        out.append(pad + f"match n{depth}:")
        out.append(pad + "  case 0n:")
        out.append(pad + f"    %Equal.sym(U32, r, {k}, UL.u32_value_eq(r, {k}, e)) : {gl}")
        out.append(pad + "    {==}")
        out.append(pad + f"  case 1n+n{depth + 1}:")
        go(depth + 1, ind + 2, k + 1)
    go(0, 1, 0)
    put(f"""def ks.tdn(n0: Nat, +r: U32, e: {{{v32('r')} == n0 : Nat}}, h: {btrue('Nat.is_lt(n0, 10n)')}) -> {goal}:
""" + "\n".join(out) + f"""

def ks.td(+r: U32, h: {btrue(f'Nat.is_lt({v32("r")}, 10n)')}) -> {goal}:
  ks.tdn({v32('r')}, r, {{==}}, h)

# the tokens of the digits of v (least significant last), onto tl
def ks.dt(n: Nat, z: Bool, +v: W.W64, tl: {TL}) -> {TL}:
  match n z:
    case 0n True{{}}:
      tl
    case 1n+k True{{}}:
      tl
    case 0n False{{}}:
      tl
    case 1n+k False{{}}:
      ks.dt(k, {ZQ('v')}, {Q('v')}, Con{{K.KTDigit{{{R('v')}}}, tl}})

# the position after them
def ks.pos(n: Nat, z: Bool, +v: W.W64, pos: Nat) -> Nat:
  match n z:
    case 0n True{{}}:
      pos
    case 1n+k True{{}}:
      pos
    case 0n False{{}}:
      pos
    case 1n+k False{{}}:
      1n+ks.pos(k, {ZQ('v')}, {Q('v')}, pos)

def ks.ta(n: Nat, z: Bool, +v: W.W64, +acc: List<&2, U32>) -> {{K.kstr.toks(B.mask({DS('n', 'z', 'v', 'acc')})) == {DT('n', 'z', 'v', 'K.kstr.toks(B.mask(acc))')} : {TL}}}:
  match n z:
    case 0n True{{}}:
      {{==}}
    case 1n+ +k True{{}}:
      {{==}}
    case 0n False{{}}:
      {{==}}
    case 1n+ +k False{{}}:
      Equal.trans({TL}, K.kstr.toks(B.mask({DS('k', ZQ('v'), Q('v'), f'Con{{{DIG(R("v"))}, acc}}')})), {DT('k', ZQ('v'), Q('v'), f'K.kstr.toks(B.mask(Con{{{DIG(R("v"))}, acc}}))')}, {DT('k', ZQ('v'), Q('v'), f'Con{{K.KTDigit{{{R("v")}}}, K.kstr.toks(B.mask(acc))}}')}, ks.ta(k, {ZQ('v')}, {Q('v')}, Con{{{DIG(R('v'))}, acc}}), Equal.cong(K.KStrTok, {TL}, zz => {DT('k', ZQ('v'), Q('v'), 'Con{zz, K.kstr.toks(B.mask(acc))}')}, K.KStr.tok(B.byte({DIG(R('v'))})), K.KTDigit{{{R('v')}}}, ks.td({R('v')}, ks.dmr(v))))

def ks.tb(n: Nat, z: Bool, +v: W.W64, +tl: {TL}) -> {{K.kstr.strip_nl({DT('n', 'z', 'v', 'tl')}) == {DT('n', 'z', 'v', 'K.kstr.strip_nl(tl)')} : {TL}}}:
  match n z:
    case 0n True{{}}:
      {{==}}
    case 1n+ +k True{{}}:
      {{==}}
    case 0n False{{}}:
      {{==}}
    case 1n+ +k False{{}}:
      ks.tb(k, {ZQ('v')}, {Q('v')}, Con{{K.KTDigit{{{R('v')}}}, tl}})

def ks.fr(n: Nat, z: Bool, +v: W.W64, +d: U32, +tl: {TL}) -> {{K.kstr.front(10, {DT('n', 'z', 'v', 'Con{K.KTDigit{d}, tl}')}, False{{}}) == Done{{K.KStrDigits{{False{{}}, 10, {DT('n', 'z', 'v', 'Con{K.KTDigit{d}, tl}')}, 0n}}}} : Result<&2, &2, K.KStrError, K.KStrDigits>}}:
  match n z:
    case 0n True{{}}:
      {{==}}
    case 1n+ +k True{{}}:
      {{==}}
    case 0n False{{}}:
      {{==}}
    case 1n+ +k False{{}}:
      ks.fr(k, {ZQ('v')}, {Q('v')}, {R('v')}, Con{{K.KTDigit{{d}}, tl}})
""")


def mul64(put):
    """kstr.mul64(q, 10, r) = Done{v} when q 10 + r = v (< 2^64)."""
    put("# One step of the 64-bit parse: acc 10 + d, which does not overflow\n")
    q, r, v = "q", "r", "v"
    F10 = "W.W64.from_u32(10)"
    ql, qh = "W.W64.lo(q)", "W.W64.hi(q)"
    PLO = f"W.W64.mul(W.W64.from_u32({ql}), {F10})"
    MH = f"W.W64.mul(W.W64.from_u32({qh}), {F10})"
    HPw = f"W.W64.hi({PLO})"
    MID = f"W.W64.add({MH}, W.W64.from_u32({HPw}))"
    PROD = f"W.W64.from_parts(W.W64.lo({MID}), W.W64.lo({PLO}))"
    SUM = f"W.W64.add({PROD}, W.W64.from_u32(r))"
    OK = f"K.kstr.ok64(Bool.and(U32.is_eq(W.W64.hi({MID}), 0), W.W64.is_le({PROD}, {SUM})), {SUM})"
    put(f"""def ks.mu(+q: W.W64, +r: U32) -> {{K.kstr.mul64(q, 10, r) == {OK} : {R64}}}:
  {{==}}
""")
    Qv, VL, VH, V, Rv = v64(q), v32(ql), v32(qh), v64(v), v32(r)
    LP, HP = v32(f"W.W64.lo({PLO})"), v32(HPw)
    Mv = f"Nat.add(Nat.mul({VH}, 10n), {HP})"
    NPq = hyp("ks.np(q)", f"Nat.add({VL}, {D('32n', VH)})", Qv)
    E = hyp("e", f"Nat.add(Nat.mul({Qv}, 10n), {Rv})", V)
    FVL = hyp(f"ks.fv({ql})", v64(f"W.W64.from_u32({ql})"), VL)
    FVH = hyp(f"ks.fv({qh})", v64(f"W.W64.from_u32({qh})"), VH)
    FVR = hyp("ks.fv(r)", v64("W.W64.from_u32(r)"), Rv)
    FHP = hyp(f"ks.fv({HPw})", v64(f"W.W64.from_u32({HPw})"), HP)
    # V = (VL 10 + R) + 2^32 (VH 10)
    keyv = calc(f"Nat.add(Nat.add(Nat.mul({VL}, 10n), {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})",
                (f"Nat.add(Nat.mul(Nat.add({VL}, {D('32n', VH)}), 10n), {Rv})", "ring"),
                (f"Nat.add(Nat.mul({Qv}, 10n), {Rv})", NPq),
                (V, E))
    KEYV = hyp("keyv", f"Nat.add(Nat.add(Nat.mul({VL}, 10n), {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})", V)
    # (1) the low product
    w1 = f"Nat.add({D('32n', f'Nat.mul({VH}, 10n)')}, {Rv})"
    p1 = calc(f"Nat.add({w1}, Nat.mul({v64(f'W.W64.from_u32({ql})')}, {v64(F10)}))",
              (f"Nat.add({w1}, Nat.mul({v64(f'W.W64.from_u32({ql})')}, 10n))", "="),
              (f"Nat.add({w1}, Nat.mul({VL}, 10n))", FVL),
              (f"Nat.add(Nat.add(Nat.mul({VL}, 10n), {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})", "ring"),
              (V, KEYV))
    h1 = le_from(f"Nat.mul({v64(f'W.W64.from_u32({ql})')}, {v64(F10)})", V, w1, p1)
    vplo = calc(v64(PLO), (f"Nat.mul({v64(f'W.W64.from_u32({ql})')}, {v64(F10)})", hyp(f"WL.mul_value(W.W64.from_u32({ql}), {F10}, v, {h1})", v64(PLO), f"Nat.mul({v64(f'W.W64.from_u32({ql})')}, {v64(F10)})")),
                (f"Nat.mul({v64(f'W.W64.from_u32({ql})')}, 10n)", "="),
                (f"Nat.mul({VL}, 10n)", FVL))
    VPLO = hyp("vplo", v64(PLO), f"Nat.mul({VL}, 10n)")
    NPP = hyp(f"ks.np({PLO})", f"Nat.add({LP}, {D('32n', HP)})", v64(PLO))
    # V = (LP + R) + 2^32 M
    key2 = calc(f"Nat.add(Nat.add({LP}, {Rv}), {D('32n', Mv)})",
                (f"Nat.add(Nat.add(Nat.add({LP}, {D('32n', HP)}), {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})", "ring"),
                (f"Nat.add(Nat.add({v64(PLO)}, {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})", NPP),
                (f"Nat.add(Nat.add(Nat.mul({VL}, 10n), {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})", VPLO),
                (V, KEYV))
    KEY2 = hyp("key2", f"Nat.add(Nat.add({LP}, {Rv}), {D('32n', Mv)})", V)
    # (3) the high product: VH 10 <= 2^32 (VH 10) <= V
    dle = le_from(D("32n", f"Nat.mul({VH}, 10n)"), V, f"Nat.add(Nat.mul({VL}, 10n), {Rv})",
                  calc(f"Nat.add(Nat.add(Nat.mul({VL}, 10n), {Rv}), {D('32n', f'Nat.mul({VH}, 10n)')})", (V, KEYV)))
    h3x = f"ks.le_trans(Nat.mul({VH}, 10n), {D('32n', f'Nat.mul({VH}, 10n)')}, {V}, UL.nat_le_dbl(32n, Nat.mul({VH}, 10n)), {dle})"
    h3 = N.btrans(f"Nat.is_le(Nat.mul({v64(f'W.W64.from_u32({qh})')}, {v64(F10)}), {V})", f"Nat.is_le(Nat.mul({VH}, 10n), {V})", "True{}",
                  N.bcong("zz", f"Nat.is_le(Nat.mul(zz, 10n), {V})", v64(f"W.W64.from_u32({qh})"), VH, "ks.fv(" + qh + ")"), h3x)
    vmh = calc(v64(MH), (f"Nat.mul({v64(f'W.W64.from_u32({qh})')}, {v64(F10)})", hyp(f"WL.mul_value(W.W64.from_u32({qh}), {F10}, v, {h3})", v64(MH), f"Nat.mul({v64(f'W.W64.from_u32({qh})')}, {v64(F10)})")),
               (f"Nat.mul({v64(f'W.W64.from_u32({qh})')}, 10n)", "="),
               (f"Nat.mul({VH}, 10n)", FVH))
    VMH = hyp("vmh", v64(MH), f"Nat.mul({VH}, 10n)")
    # (4) the middle: M <= 2^32 M <= V
    dle2 = le_from(D("32n", Mv), V, f"Nat.add({LP}, {Rv})", calc(f"Nat.add(Nat.add({LP}, {Rv}), {D('32n', Mv)})", (V, KEY2)))
    h4x = f"ks.le_trans({Mv}, {D('32n', Mv)}, {V}, UL.nat_le_dbl(32n, {Mv}), {dle2})"
    X4 = f"Nat.add({v64(MH)}, {v64(f'W.W64.from_u32({HPw})')})"
    e4 = calc(X4, (f"Nat.add(Nat.mul({VH}, 10n), {v64(f'W.W64.from_u32({HPw})')})", VMH), (Mv, FHP))
    h4 = N.btrans(f"Nat.is_le({X4}, {V})", f"Nat.is_le({Mv}, {V})", "True{}", N.bcong("zz", f"Nat.is_le(zz, {V})", X4, Mv, e4.text), h4x)
    vmid = calc(v64(MID), (X4, hyp(f"WL.add_value({MH}, W.W64.from_u32({HPw}), v, {h4})", v64(MID), X4)), (Mv, e4))
    VMID = hyp("vmid", v64(MID), Mv)
    # (5) M < 2^32
    mlt = (f"Equal.trans(Bool, Nat.is_lt({Mv}, {W32}), Nat.is_lt({D('32n', Mv)}, {D('32n', W32)}), True{{}}, "
           f"Equal.sym(Bool, Nat.is_lt({D('32n', Mv)}, {D('32n', W32)}), Nat.is_lt({Mv}, {W32}), UL.dbl_lt(32n, {Mv}, {W32})), "
           f"ks.lelt({D('32n', Mv)}, {V}, {D('32n', W32)}, {dle2}, ks.d64(32n, 64n, {V}, {{==}}, ks.lt64(v))))")
    midlt = lt_rw(Mv, W32, v64(MID), W32, f"Equal.sym(Nat, {v64(MID)}, {Mv}, vmid)", None, mlt)
    # (6) the halves of the middle
    LOM = v32(f"W.W64.lo({MID})")
    # (7) the product, (8) the sum
    vprod = calc(v64(PROD), (f"Nat.add({LP}, {D('32n', LOM)})", hyp(f"WL.to_nat_parts(W.W64.lo({MID}), W.W64.lo({PLO}))", v64(PROD), f"Nat.add({LP}, {D('32n', LOM)})")),
                 (f"Nat.add({LP}, {D('32n', v64(MID))})", hyp("lom", LOM, v64(MID))),
                 (f"Nat.add({LP}, {D('32n', Mv)})", VMID))
    VPROD = hyp("vprod", v64(PROD), f"Nat.add({LP}, {D('32n', Mv)})")
    X8 = f"Nat.add({v64(PROD)}, {v64('W.W64.from_u32(r)')})"
    e8 = calc(X8, (f"Nat.add(Nat.add({LP}, {D('32n', Mv)}), {v64('W.W64.from_u32(r)')})", VPROD),
              (f"Nat.add(Nat.add({LP}, {D('32n', Mv)}), {Rv})", FVR),
              (f"Nat.add(Nat.add({LP}, {Rv}), {D('32n', Mv)})", "ring"),
              (V, KEY2))
    h8 = le_from(X8, V, "0n", calc(f"Nat.add(0n, {X8})", (X8, "="), (V, hyp("e8", X8, V))))
    vsum = calc(v64(SUM), (X8, hyp(f"WL.add_value({PROD}, W.W64.from_u32(r), v, {h8})", v64(SUM), X8)), (V, hyp("e8", X8, V)))
    # (9) prod <= sum
    lex = N.btrans(f"Nat.is_le({v64(PROD)}, {v64(SUM)})", f"Nat.is_le({v64(PROD)}, Nat.add({v64('W.W64.from_u32(r)')}, {v64(PROD)}))", "True{}",
                   N.bcong("zz", f"Nat.is_le({v64(PROD)}, zz)", v64(SUM), f"Nat.add({v64('W.W64.from_u32(r)')}, {v64(PROD)})",
                           f"Equal.trans(Nat, {v64(SUM)}, {X8}, Nat.add({v64('W.W64.from_u32(r)')}, {v64(PROD)}), {hyp(f'WL.add_value({PROD}, W.W64.from_u32(r), v, {h8})', v64(SUM), X8).text}, UL.nat_add_comm({v64(PROD)}, {v64('W.W64.from_u32(r)')}))"),
                   f"UL.nat_le_add({v64(PROD)}, {v64('W.W64.from_u32(r)')})")
    LE = f"Equal.trans(Bool, W.W64.is_le({PROD}, {SUM}), Nat.is_le({v64(PROD)}, {v64(SUM)}), True{{}}, WL.le_value({PROD}, {SUM}), {lex})"
    okt = lambda a, b, c: f"K.kstr.ok64(Bool.and({a}, {b}), {c})"  # noqa: E731
    put(f"""def ks.ml(+q: W.W64, +r: U32, +v: W.W64, +e: {{Nat.add(Nat.mul({Qv}, 10n), {Rv}) == {V} : Nat}}) -> {{K.kstr.mul64(q, 10, r) == Done{{v}} : {R64}}}:
  +keyv = {keyv.text}
  +vplo = {vplo.text}
  +key2 = {key2.text}
  +vmh = {vmh.text}
  +vmid = {vmid.text}
  +lom = ks.lo32({MID}, {midlt})
  +vprod = {vprod.text}
  +e8 = {e8.text}
  %Equal.sym({R64}, K.kstr.mul64(q, 10, r), {OK}, ks.mu(q, r)) : {{_ == Done{{v}} : {R64}}}
  %Equal.sym(Bool, U32.is_eq(W.W64.hi({MID}), 0), True{{}}, ks.hz({MID}, ks.hi0({MID}, lom))) : {{{okt('_', f'W.W64.is_le({PROD}, {SUM})', SUM)} == Done{{v}} : {R64}}}
  %Equal.sym(Bool, W.W64.is_le({PROD}, {SUM}), True{{}}, {LE}) : {{{okt('True{}', '_', SUM)} == Done{{v}} : {R64}}}
  Equal.cong(W.W64, {R64}, zz => Done{{zz}}, {SUM}, v, WL.value_eq({SUM}, v, {vsum.text}))
""")


def mul32(put):
    """kstr.mul.fin(lo q 10 + r) = Done{lo v} when q 10 + r = v < 2^32."""
    put("# One step of the 32-bit parse\n")
    q, r, v = "q", "r", "v"
    F10 = "W.W64.from_u32(10)"
    LQ = "W.W64.lo(q)"
    MU = f"W.W64.mul(W.W64.from_u32({LQ}), {F10})"
    PP = f"W.W64.add({MU}, W.W64.from_u32(r))"
    Qv, V, Rv = v64(q), v64(v), v32(r)
    E = hyp("e", f"Nat.add(Nat.mul({Qv}, 10n), {Rv})", V)
    qle = le_from(Qv, V, f"Nat.add(Nat.mul({Qv}, 9n), {Rv})",
                  calc(f"Nat.add(Nat.add(Nat.mul({Qv}, 9n), {Rv}), {Qv})", (f"Nat.add(Nat.mul({Qv}, 10n), {Rv})", "ring"), (V, E)))
    qlt = f"ks.lelt({Qv}, {V}, {W32}, {qle}, hv)"
    LQV = hyp("lqv", v32(LQ), Qv)
    FLQ = hyp(f"ks.fv({LQ})", v64(f"W.W64.from_u32({LQ})"), v32(LQ))
    FR = hyp("ks.fv(r)", v64("W.W64.from_u32(r)"), Rv)
    X1 = f"Nat.mul({v64(f'W.W64.from_u32({LQ})')}, {v64(F10)})"
    e1 = calc(X1, (f"Nat.mul({v64(f'W.W64.from_u32({LQ})')}, 10n)", "="), (f"Nat.mul({v32(LQ)}, 10n)", FLQ), (f"Nat.mul({Qv}, 10n)", LQV))
    h1 = le_from(X1, V, Rv, calc(f"Nat.add({Rv}, {X1})", (f"Nat.add({Rv}, Nat.mul({Qv}, 10n))", e1), (f"Nat.add(Nat.mul({Qv}, 10n), {Rv})", "ring"), (V, E)))
    X2 = f"Nat.add({v64(MU)}, {v64('W.W64.from_u32(r)')})"
    VMU = hyp(f"WL.mul_value(W.W64.from_u32({LQ}), {F10}, v, {h1})", v64(MU), X1)
    e2 = calc(X2, (f"Nat.add({X1}, {v64('W.W64.from_u32(r)')})", VMU), (f"Nat.add(Nat.mul({Qv}, 10n), {v64('W.W64.from_u32(r)')})", e1),
              (f"Nat.add(Nat.mul({Qv}, 10n), {Rv})", FR), (V, E))
    h2 = le_from(X2, V, "0n", calc(f"Nat.add(0n, {X2})", (X2, "="), (V, hyp("e2", X2, V))))
    vp = calc(v64(PP), (X2, hyp(f"WL.add_value({MU}, W.W64.from_u32(r), v, {h2})", v64(PP), X2)), (V, hyp("e2", X2, V)))
    put(f"""def ks.ml32(+q: W.W64, +r: U32, +v: W.W64, +e: {{Nat.add(Nat.mul({Qv}, 10n), {Rv}) == {V} : Nat}}, +hv: {btrue(f'Nat.is_lt({V}, {W32})')}) -> {{K.kstr.mul.fin({PP}) == Done{{W.W64.lo(v)}} : {R32}}}:
  +lqv = ks.lo32(q, {qlt})
  +e2 = {e2.text}
  %Equal.sym(W.W64, {PP}, v, WL.value_eq({PP}, v, {vp.text})) : {{K.kstr.mul.fin(_) == Done{{W.W64.lo(v)}} : {R32}}}
  %Equal.sym(Bool, U32.is_eq(W.W64.hi(v), 0), True{{}}, ks.hz(v, ks.hi0(v, ks.lo32(v, hv)))) : {{K.kstr.ok(_, W.W64.lo(v)) == Done{{W.W64.lo(v)}} : {R32}}}
  {{==}}
""")


def parse(put):
    put("# The parse of the digit tokens\n")
    v = "v"
    Qv, Rv = Q(v), R(v)
    ltu = (f"Equal.trans(Bool, U32.is_lt({Rv}, 10), Nat.is_lt({v32(Rv)}, 10n), True{{}}, UL.u32_lt_value({Rv}, 10), ks.dmr(v))")
    # one digit step, 64 and 32 bits
    put(f"""def ks.sp(+v: W.W64, +tl: {TL}, +p: Nat) -> {{K.kstr.digits64(Con{{K.KTDigit{{{Rv}}}, tl}}, 10, Done{{{Qv}}}, p) == K.kstr.digits64(tl, 10, Done{{v}}, 1n+p) : {R64}}}:
  Equal.cong({R64}, {R64}, zz => K.kstr.digits64(tl, 10, zz, 1n+p), K.kstr.step64.digit(U32.is_lt({Rv}, 10), 10, {Qv}, {Rv}, p), Done{{v}}, Equal.trans({R64}, K.kstr.step64.digit(U32.is_lt({Rv}, 10), 10, {Qv}, {Rv}, p), K.kstr.step64.digit(True{{}}, 10, {Qv}, {Rv}, p), Done{{v}}, Equal.cong(Bool, {R64}, zz => K.kstr.step64.digit(zz, 10, {Qv}, {Rv}, p), U32.is_lt({Rv}, 10), True{{}}, {ltu}), ks.ml({Qv}, {Rv}, v, ks.dmq(v))))

def ks.sq(+v: W.W64, +tl: {TL}, +p: Nat, +hv: {btrue(f'Nat.is_lt({v64("v")}, {W32})')}) -> {{K.kstr.digits(Con{{K.KTDigit{{{Rv}}}, tl}}, 10, Done{{W.W64.lo({Qv})}}, p) == K.kstr.digits(tl, 10, Done{{W.W64.lo(v)}}, 1n+p) : {R32}}}:
  Equal.cong({R32}, {R32}, zz => K.kstr.digits(tl, 10, zz, 1n+p), K.kstr.step.digit(U32.is_lt({Rv}, 10), 10, W.W64.lo({Qv}), {Rv}, p), Done{{W.W64.lo(v)}}, Equal.trans({R32}, K.kstr.step.digit(U32.is_lt({Rv}, 10), 10, W.W64.lo({Qv}), {Rv}, p), K.kstr.step.digit(True{{}}, 10, W.W64.lo({Qv}), {Rv}, p), Done{{W.W64.lo(v)}}, Equal.cong(Bool, {R32}, zz => K.kstr.step.digit(zz, 10, W.W64.lo({Qv}), {Rv}, p), U32.is_lt({Rv}, 10), True{{}}, {ltu}), ks.ml32({Qv}, {Rv}, v, ks.dmq(v), hv)))
""")
    # v = 0 when is_zero(v); and not when fuel is 0 and v < 1
    vz = f"WL.value_eq(v, W.W64.zero(), ks.wz(v, ez))"
    nz = (f"Equal.trans(Bool, Nat.is_eq({v64('v')}, 0n), W.W64.is_zero(v), False{{}}, "
          f"Equal.sym(Bool, W.W64.is_zero(v), Nat.is_eq({v64('v')}, 0n), WL.eq_value(v, W.W64.zero())), ez)")
    absurd0 = (f"ks.tf(Equal.trans(Bool, True{{}}, Nat.is_eq({v64('v')}, 0n), False{{}}, "
               f"Equal.sym(Bool, Nat.is_eq({v64('v')}, 0n), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 0n), {v64('v')}, 0n, ks.lt1({v64('v')}, hf))), {nz}))")
    hfq = f"ks.hq(k, 1n+k, {v64(Qv)}, {v32(Rv)}, {v64('v')}, {{==}}, ks.dmq(v), hf)"
    # the quotient is below 2^32 too: q <= v
    E = hyp("ks.dmq(v)", f"Nat.add(Nat.mul({v64(Qv)}, 10n), {v32(Rv)})", v64("v"))
    qle = le_from(v64(Qv), v64("v"), f"Nat.add(Nat.mul({v64(Qv)}, 9n), {v32(Rv)})",
                  calc(f"Nat.add(Nat.add(Nat.mul({v64(Qv)}, 9n), {v32(Rv)}), {v64(Qv)})", (f"Nat.add(Nat.mul({v64(Qv)}, 10n), {v32(Rv)})", "ring"), (v64("v"), E)))
    hvq = f"ks.lelt({v64(Qv)}, {v64('v')}, {W32}, {qle}, hv)"
    put(f"""def ks.tp(n: Nat, z: Bool, +v: W.W64, ez: {{W.W64.is_zero(v) == z : Bool}}, +tl: {TL}, +pos: Nat, hf: {btrue(f'Nat.is_lt({v64("v")}, {D("n", "1n")})')}) -> {{K.kstr.digits64({DT('n', 'z', 'v', 'tl')}, 10, Done{{W.W64.zero()}}, pos) == K.kstr.digits64(tl, 10, Done{{v}}, ks.pos(n, z, v, pos)) : {R64}}}:
  match n z:
    case 0n True{{}}:
      %Equal.sym(W.W64, v, W.W64.zero(), {vz}) : {{K.kstr.digits64(tl, 10, Done{{W.W64.zero()}}, pos) == K.kstr.digits64(tl, 10, Done{{_}}, pos) : {R64}}}
      {{==}}
    case 1n+ +k True{{}}:
      %Equal.sym(W.W64, v, W.W64.zero(), {vz}) : {{K.kstr.digits64(tl, 10, Done{{W.W64.zero()}}, pos) == K.kstr.digits64(tl, 10, Done{{_}}, pos) : {R64}}}
      {{==}}
    case 0n False{{}}:
      Empty.absurd({{K.kstr.digits64(tl, 10, Done{{W.W64.zero()}}, pos) == K.kstr.digits64(tl, 10, Done{{v}}, pos) : {R64}}}, {absurd0})
    case 1n+ +k False{{}}:
      Equal.trans({R64}, K.kstr.digits64({DT('k', ZQ('v'), Qv, f'Con{{K.KTDigit{{{Rv}}}, tl}}')}, 10, Done{{W.W64.zero()}}, pos), K.kstr.digits64(Con{{K.KTDigit{{{Rv}}}, tl}}, 10, Done{{{Qv}}}, ks.pos(k, {ZQ('v')}, {Qv}, pos)), K.kstr.digits64(tl, 10, Done{{v}}, 1n+ks.pos(k, {ZQ('v')}, {Qv}, pos)), ks.tp(k, {ZQ('v')}, {Qv}, {{==}}, Con{{K.KTDigit{{{Rv}}}, tl}}, pos, {hfq}), ks.sp(v, tl, ks.pos(k, {ZQ('v')}, {Qv}, pos)))

def ks.tq(n: Nat, z: Bool, +v: W.W64, ez: {{W.W64.is_zero(v) == z : Bool}}, +tl: {TL}, +pos: Nat, hf: {btrue(f'Nat.is_lt({v64("v")}, {D("n", "1n")})')}, +hv: {btrue(f'Nat.is_lt({v64("v")}, {W32})')}) -> {{K.kstr.digits({DT('n', 'z', 'v', 'tl')}, 10, Done{{0}}, pos) == K.kstr.digits(tl, 10, Done{{W.W64.lo(v)}}, ks.pos(n, z, v, pos)) : {R32}}}:
  match n z:
    case 0n True{{}}:
      %Equal.sym(W.W64, v, W.W64.zero(), {vz}) : {{K.kstr.digits(tl, 10, Done{{0}}, pos) == K.kstr.digits(tl, 10, Done{{W.W64.lo(_)}}, pos) : {R32}}}
      {{==}}
    case 1n+ +k True{{}}:
      %Equal.sym(W.W64, v, W.W64.zero(), {vz}) : {{K.kstr.digits(tl, 10, Done{{0}}, pos) == K.kstr.digits(tl, 10, Done{{W.W64.lo(_)}}, pos) : {R32}}}
      {{==}}
    case 0n False{{}}:
      Empty.absurd({{K.kstr.digits(tl, 10, Done{{0}}, pos) == K.kstr.digits(tl, 10, Done{{W.W64.lo(v)}}, pos) : {R32}}}, {absurd0})
    case 1n+ +k False{{}}:
      Equal.trans({R32}, K.kstr.digits({DT('k', ZQ('v'), Qv, f'Con{{K.KTDigit{{{Rv}}}, tl}}')}, 10, Done{{0}}, pos), K.kstr.digits(Con{{K.KTDigit{{{Rv}}}, tl}}, 10, Done{{W.W64.lo({Qv})}}, ks.pos(k, {ZQ('v')}, {Qv}, pos)), K.kstr.digits(tl, 10, Done{{W.W64.lo(v)}}, 1n+ks.pos(k, {ZQ('v')}, {Qv}, pos)), ks.tq(k, {ZQ('v')}, {Qv}, {{==}}, Con{{K.KTDigit{{{Rv}}}, tl}}, pos, {hfq}, {hvq}), ks.sq(v, tl, ks.pos(k, {ZQ('v')}, {Qv}, pos), hv))
""")


def laws(put):
    put("# The round trips\n")
    v = "v"
    Qv, Rv = Q(v), R(v)
    D64 = DS("64n", "False{}", "v", "Nil{}")
    DT63 = DT("63n", ZQ(v), Qv, f"Con{{K.KTDigit{{{Rv}}}, Nil{{}}}}")
    hf63 = f"ks.hq(63n, 64n, {v64(Qv)}, {v32(Rv)}, {v64('v')}, {{==}}, ks.dmq(v), ks.lt64(v))"
    FR = "Result<&2, &2, K.KStrError, K.KStrDigits>"
    put(f"""def ks.r64(+v: W.W64) -> {{K.kstr.u64.fin(K.kstr.front(10, K.kstr.strip_nl(K.kstr.toks(B.Octets.to_list(B.Octets.of_list({D64})))), False{{}})) == Done{{v}} : {R64}}}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list({D64})), B.mask({D64}), BL.octets_to_of({D64})) : {{K.kstr.u64.fin(K.kstr.front(10, K.kstr.strip_nl(K.kstr.toks(_)), False{{}})) == Done{{v}} : {R64}}}
  %Equal.sym({TL}, K.kstr.toks(B.mask({D64})), {DT('64n', 'False{}', 'v', 'Nil{}')}, ks.ta(64n, False{{}}, v, Nil{{}})) : {{K.kstr.u64.fin(K.kstr.front(10, K.kstr.strip_nl(_), False{{}})) == Done{{v}} : {R64}}}
  %Equal.sym({TL}, K.kstr.strip_nl({DT('64n', 'False{}', 'v', 'Nil{}')}), {DT('64n', 'False{}', 'v', 'Nil{}')}, ks.tb(64n, False{{}}, v, Nil{{}})) : {{K.kstr.u64.fin(K.kstr.front(10, _, False{{}})) == Done{{v}} : {R64}}}
  %Equal.sym({FR}, K.kstr.front(10, {DT63}, False{{}}), Done{{K.KStrDigits{{False{{}}, 10, {DT63}, 0n}}}}, ks.fr(63n, {ZQ('v')}, {Qv}, {Rv}, Nil{{}})) : {{K.kstr.u64.fin(_) == Done{{v}} : {R64}}}
  Equal.trans({R64}, K.kstr.digits64({DT63}, 10, Done{{W.W64.zero()}}, 0n), K.kstr.digits64(Con{{K.KTDigit{{{Rv}}}, Nil{{}}}}, 10, Done{{{Qv}}}, ks.pos(63n, {ZQ('v')}, {Qv}, 0n)), Done{{v}}, ks.tp(63n, {ZQ('v')}, {Qv}, {{==}}, Con{{K.KTDigit{{{Rv}}}, Nil{{}}}}, 0n, {hf63}), ks.sp(v, Nil{{}}, ks.pos(63n, {ZQ('v')}, {Qv}, 0n)))

def Laws.dec64_round_trip(v):
  ks.r64(v)
""")
    # 32 bits: v as the W64 W64{0, v}
    w = "W.W64.from_u32(v)"
    Qw, Rw = Q(w), R(w)
    D32 = DS("64n", "False{}", w, "Nil{}")
    DTw = DT("63n", ZQ(w), Qw, f"Con{{K.KTDigit{{{Rw}}}, Nil{{}}}}")
    hvw = lt_rw(v32("v"), W32, v64(w), W32, f"Equal.sym(Nat, {v64(w)}, {v32('v')}, ks.fv(v))", None, "ks.lt32(v)")
    hf63w = f"ks.hq(63n, 64n, {v64(Qw)}, {v32(Rw)}, {v64(w)}, {{==}}, ks.dmq({w}), ks.lt64({w}))"
    E = hyp(f"ks.dmq({w})", f"Nat.add(Nat.mul({v64(Qw)}, 10n), {v32(Rw)})", v64(w))
    qle = le_from(v64(Qw), v64(w), f"Nat.add(Nat.mul({v64(Qw)}, 9n), {v32(Rw)})",
                  calc(f"Nat.add(Nat.add(Nat.mul({v64(Qw)}, 9n), {v32(Rw)}), {v64(Qw)})", (f"Nat.add(Nat.mul({v64(Qw)}, 10n), {v32(Rw)})", "ring"), (v64(w), E)))
    hvq = f"ks.lelt({v64(Qw)}, {v64(w)}, {W32}, {qle}, {hvw})"
    put(f"""def ks.r32(+v: U32) -> {{K.kstr.u32.fin(K.kstr.front(10, K.kstr.strip_nl(K.kstr.toks(B.Octets.to_list(B.Octets.of_list({D32})))), False{{}})) == Done{{v}} : {R32}}}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list({D32})), B.mask({D32}), BL.octets_to_of({D32})) : {{K.kstr.u32.fin(K.kstr.front(10, K.kstr.strip_nl(K.kstr.toks(_)), False{{}})) == Done{{v}} : {R32}}}
  %Equal.sym({TL}, K.kstr.toks(B.mask({D32})), {DT('64n', 'False{}', w, 'Nil{}')}, ks.ta(64n, False{{}}, {w}, Nil{{}})) : {{K.kstr.u32.fin(K.kstr.front(10, K.kstr.strip_nl(_), False{{}})) == Done{{v}} : {R32}}}
  %Equal.sym({TL}, K.kstr.strip_nl({DT('64n', 'False{}', w, 'Nil{}')}), {DT('64n', 'False{}', w, 'Nil{}')}, ks.tb(64n, False{{}}, {w}, Nil{{}})) : {{K.kstr.u32.fin(K.kstr.front(10, _, False{{}})) == Done{{v}} : {R32}}}
  %Equal.sym({FR}, K.kstr.front(10, {DTw}, False{{}}), Done{{K.KStrDigits{{False{{}}, 10, {DTw}, 0n}}}}, ks.fr(63n, {ZQ(w)}, {Qw}, {Rw}, Nil{{}})) : {{K.kstr.u32.fin(_) == Done{{v}} : {R32}}}
  Equal.trans({R32}, K.kstr.digits({DTw}, 10, Done{{0}}, 0n), K.kstr.digits(Con{{K.KTDigit{{{Rw}}}, Nil{{}}}}, 10, Done{{W.W64.lo({Qw})}}, ks.pos(63n, {ZQ(w)}, {Qw}, 0n)), Done{{v}}, ks.tq(63n, {ZQ(w)}, {Qw}, {{==}}, Con{{K.KTDigit{{{Rw}}}, Nil{{}}}}, 0n, {hf63w}, {hvq}), ks.sq({w}, Nil{{}}, ks.pos(63n, {ZQ(w)}, {Qw}, 0n), {hvw}))

def Laws.dec32_round_trip(v):
  ks.r32(v)
""")


def dec(put):
    lemmas(put)
    divmod_facts(put)
    tokens(put)
    mul64(put)
    mul32(put)
    parse(put)
    laws(put)
