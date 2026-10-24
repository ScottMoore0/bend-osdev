"""The proofs of kstr's octal and hexadecimal round trips (LAWS_oct.bend,
LAWS_hex.bend), for gen/proof.py: the decimal method (gen/proof_dec.py,
run with its base set to 8 or 16 and its letters' case), with what differs:

  * hex digits: a remainder r from 10 to 15 is a letter, 87 + r (%x) or 55
    + r (%X), and reads back as KTDigit{r} (the 16 cases of r);
  * base 16's front end looks for a "0x" at the second token: the digits'
    second token is a digit or there is none (ks.fra, ks.frb);
  * the 32-bit accumulator: base 8 and base 16 shift the digit in instead
    of multiplying, refusing an accumulator with its top three or four bits
    set. With q B + r = v < 2^32: q < 2^29 (2^28), so the test passes, and
    the shifted value is q 2^3 + r (u32's shln, or and the low bits laws) or,
    for base 16's kstr.ins4 (the bits of r below those of q), q 2^4 + r: a
    word's value splits as that of its low m bits plus 2^m that of the rest
    (ks.cv, on a copy of word64's bit concatenation), so ins4's value is
    r + 2^4 q (ks.i4).
"""
import re

import natproof as N
from natproof import btrue, calc, hyp, le_from, lt_rw
import proof_dec as P
from proof_dec import D, DT, Q, R, R32, TL, W32, ZQ, v32, v64

FRR = "Result<&2, &2, K.KStrError, K.KStrDigits>"


def capture(fn, *args):
    buf = []
    fn(buf.append, *args)
    return "\n".join(buf)


def hexfront(put):
    put("# base 16: the second token is never an x\n")
    dtb = DT("n", "z", "v", "Con{K.KTDigit{d}, Con{K.KTDigit{e}, tl}}")
    dta = DT("n", "z", "v", "Con{K.KTDigit{d}, Nil{}}")
    cases = lambda step: f"""  match n z:
    case 0n True{{}}:
      {{==}}
    case 1n+ +k True{{}}:
      {{==}}
    case 0n False{{}}:
      {{==}}
    case 1n+ +k False{{}}:
      {step}
"""  # noqa: E731
    put(f"""def ks.frb(n: Nat, z: Bool, +v: W.W64, +d: U32, +e: U32, +tl: {TL}) -> {{K.kstr.front(16, {dtb}, False{{}}) == Done{{K.KStrDigits{{False{{}}, 16, {dtb}, 0n}}}} : {FRR}}}:
""" + cases(f"ks.frb(k, {ZQ('v')}, {Q('v')}, {R('v')}, d, Con{{K.KTDigit{{e}}, tl}})") + f"""
def ks.fra(n: Nat, z: Bool, +v: W.W64, +d: U32) -> {{K.kstr.front(16, {dta}, False{{}}) == Done{{K.KStrDigits{{False{{}}, 16, {dta}, 0n}}}} : {FRR}}}:
""" + cases(f"ks.frb(k, {ZQ('v')}, {Q('v')}, {R('v')}, d, Nil{{}})"))


def words(put):
    """a word's value as its low m bits' and the rest's, and kstr.ins4's"""
    put("# A word's value: its low m bits, plus 2^m the rest (on a copy of word64's\n# bit concatenation); and so kstr.ins4's value\n")
    X, T, Bv = "Word.to_nat(Nat.add(p, n), ks.cat(p, n, t, b))", "Word.to_nat(p, t)", "Word.to_nat(n, b)"
    DB = D("p", Bv)
    rg = N.ring(f"Nat.double(Nat.add({T}, {DB}))", f"Nat.add(Nat.double({T}), Nat.double({DB}))")
    A1, A2 = f"Nat.add({T}, {DB})", f"Nat.add(Nat.double({T}), Nat.double({DB}))"
    ih = "ks.cv(p, n, t, b)"
    f0 = f"Equal.trans(Nat, Nat.double({X}), Nat.double({A1}), {A2}, Equal.cong(Nat, Nat, zz => Nat.double(zz), {X}, {A1}, {ih}), {rg.text})"
    f1 = (f"Equal.trans(Nat, 1n+Nat.double({X}), 1n+Nat.double({A1}), 1n+{A2}, Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), {X}, {A1}, {ih}), "
          f"Equal.cong(Nat, Nat, zz => 1n+zz, Nat.double({A1}), {A2}, {rg.text}))")
    AN = "Word.to_nat(Nat.add(28n, 4n), ks.cat(28n, 4n, x, r))"
    DN = "Word.to_nat(Nat.add(4n, 28n), ks.cat(4n, 28n, y, s))"
    CI = "Word.to_nat(Nat.add(4n, 28n), ks.cat(4n, 28n, y, x))"
    Wx, Wr, Wy = "Word.to_nat(28n, x)", "Word.to_nat(4n, r)", "Word.to_nat(4n, y)"
    ax = calc(AN, (f"Nat.add({Wx}, {D('28n', Wr)})", hyp("ca", AN, f"Nat.add({Wx}, {D('28n', Wr)})")),
              (f"Nat.add({Wx}, {D('28n', '0n')})", hyp("r0", Wr, "0n")),
              (f"Nat.add({Wx}, 0n)", hyp("UL.dbl_zero(28n)", D("28n", "0n"), "0n")), (Wx, "ring"))
    res = calc(CI, (f"Nat.add({Wy}, {D('4n', Wx)})", hyp("ks.cv(4n, 28n, y, x)", CI, f"Nat.add({Wy}, {D('4n', Wx)})")),
               (f"Nat.add({DN}, {D('4n', Wx)})", hyp("dy", Wy, DN)), (f"Nat.add({DN}, {D('4n', AN)})", N.sym(ax)))
    bits = [f"a{i}" for i in range(28)]
    xa = "WNil{}"
    for b in reversed(bits):
        xa = f"WCon{{{b}, {xa}}}"
    pa = "r"
    for b in reversed(bits):
        pa = f"WCon{{{b}, {pa}}}"
    ys = "WNil{}"
    pd = "s"
    for b in reversed([f"d{i}" for i in range(4)]):
        ys = f"WCon{{{b}, {ys}}}"
        pd = f"WCon{{{b}, {pd}}}"
    put(f"""def ks.cat(m: Nat, n: Nat, a: Word(m), b: Word(n)) -> Word(Nat.add(m, n)):
  match m:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{{h, t}}:
          WCon{{h, ks.cat(p, n, t, b)}}

def ks.cv(+m: Nat, +n: Nat, +a: Word(m), +b: Word(n)) -> {{Word.to_nat(Nat.add(m, n), ks.cat(m, n, a, b)) == Nat.add(Word.to_nat(m, a), {D('m', 'Word.to_nat(n, b)')}) : Nat}}:
  match m:
    case 0n:
      {{==}}
    case 1n+p:
      match a:
        case WCon{{+h, +t}}:
          match h:
            case False{{}}:
              {f0}
            case True{{}}:
              {f1}

def ks.i4g(+x: Word(28n), +r: Word(4n), +y: Word(4n), +s: Word(28n), +ha: {{U.U32Nat.high(28n, {AN}) == 0n : Nat}}, +hd: {btrue(f'Nat.is_lt({DN}, {D("4n", "1n")})')}) -> {{{CI} == Nat.add({DN}, {D('4n', AN)}) : Nat}}:
  +ca = ks.cv(28n, 4n, x, r)
  +cd = ks.cv(4n, 28n, y, s)
  +r0 = Equal.trans(Nat, {Wr}, U.U32Nat.high(28n, {AN}), 0n, UL.high_unique(28n, {AN}, {Wx}, {Wr}, Equal.sym(Nat, {AN}, Nat.add({Wx}, {D('28n', Wr)}), ca), UL.word_value_lt(28n, x)), ha)
  +dy = UL.dbl_nowrap(4n, Word.to_nat(28n, s), {Wy}, {DN}, {DN}, Equal.sym(Nat, {DN}, Nat.add({Wy}, {D('4n', 'Word.to_nat(28n, s)')}), cd), UL.nat_le_refl({DN}), hd)
  {res.text}

def ks.i4(+a: U32, +d: U32, +ha: {{U.U32Nat.high(28n, U32.to_nat(a)) == 0n : Nat}}, +hd: {btrue(f'Nat.is_lt(U32.to_nat(d), {D("4n", "1n")})')}) -> {{U32.to_nat(K.kstr.ins4(a, d)) == Nat.add(U32.to_nat(d), {D('4n', 'U32.to_nat(a)')}) : Nat}}:
  match a d:
    case U32{{{pa}}} U32{{{pd}}}:
      ks.i4g({xa}, r, {ys}, s, ha, hd)
""")


def mul32_shift(put):
    """one step of the 32-bit parse in base 8 or 16: the shift"""
    B = P.CFG["base"]
    k = 3 if B == 8 else 4
    j = 32 - k
    kn, jn = f"{k}n", f"{j}n"
    put(f"# One step of the 32-bit parse: the digit shifted in, {k} bits\n")
    q, r, v = "q", "r", "v"
    LQ = "W.W64.lo(q)"
    QL, Qv, V, Rv = v32(LQ), v64(q), v64(v), v32(r)
    BN, B1N = P.BN(), P.B1N()
    E = hyp("e", f"Nat.add(Nat.mul({Qv}, {BN}), {Rv})", V)
    qle = le_from(Qv, V, f"Nat.add(Nat.mul({Qv}, {B1N}), {Rv})",
                  calc(f"Nat.add(Nat.add(Nat.mul({Qv}, {B1N}), {Rv}), {Qv})", (f"Nat.add(Nat.mul({Qv}, {BN}), {Rv})", "ring"), (V, E)))
    qlt = f"ks.lelt({Qv}, {V}, {W32}, {qle}, hv)"
    DK = D(kn, QL)
    dk = "Nat.double(" * k + Qv + ")" * k
    ek = calc(f"Nat.add({DK}, {Rv})", (f"Nat.add({D(kn, Qv)}, {Rv})", hyp("lqv", QL, Qv)), (f"Nat.add({dk}, {Rv})", "="),
              (f"Nat.add(Nat.mul({Qv}, {BN}), {Rv})", "ring"), (V, E))
    EK = hyp("ek", f"Nat.add({DK}, {Rv})", V)
    hk = f"ks.lelt({DK}, {V}, {W32}, {le_from(DK, V, Rv, calc(f'Nat.add({Rv}, {DK})', (f'Nat.add({DK}, {Rv})', 'ring'), (V, EK)))}, hv)"
    DJ = D(jn, "1n")
    DKJ = D(kn, DJ)
    kj = (f"Equal.trans(Nat, {DKJ}, {D(f'Nat.add({kn}, {jn})', '1n')}, {W32}, UL.dbl_dbl({kn}, {jn}, 1n), "
          f"Equal.cong(Nat, Nat, zz => U.U32Nat.dbl(zz, 1n), Nat.add({kn}, {jn}), 32n, {{==}}))")
    # (a fact whose type holds 2^32 is never bound to a name: a binding's
    # type is normalized)
    hk2 = lt_rw(DK, W32, DK, DKJ, None, f"Equal.sym(Nat, {DKJ}, {W32}, {kj})", hk)
    hj = (f"Equal.trans(Bool, Nat.is_lt({QL}, {DJ}), Nat.is_lt({DK}, {DKJ}), True{{}}, "
          f"Equal.sym(Bool, Nat.is_lt({DK}, {DKJ}), Nat.is_lt({QL}, {DJ}), UL.dbl_lt({kn}, {QL}, {DJ})), {hk2})")
    HJ = f"U.U32Nat.high({jn}, {QL})"
    S = f"U32.shrn({LQ}, {jn})"
    shz = (f"Equal.trans(Bool, U32.is_eq({S}, 0), Nat.is_eq(U32.to_nat({S}), 0n), True{{}}, UL.u32_eq_value({S}, 0), "
           f"Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, 0n), U32.to_nat({S}), 0n, sh))")
    if B == 8:
        SL = f"U32.shln({LQ}, 3n)"
        X = f"U32.or({SL}, r)"
        pre = f"  +sl = Equal.trans(Nat, U32.to_nat({SL}), U.U32Nat.low(32n, {DK}), {DK}, UL.u32_shln_low({LQ}, 3n), UL.low_small(32n, {DK}, {hk}))\n"
        xv = calc(f"U32.to_nat({X})", (f"Nat.add(U32.to_nat({SL}), {Rv})", hyp(f"UL.u32_or_split({SL}, r, 3n, {QL}, sl, hr)", f"U32.to_nat({X})", f"Nat.add(U32.to_nat({SL}), {Rv})")),
                  (f"Nat.add({DK}, {Rv})", hyp("sl", f"U32.to_nat({SL})", DK)), (V, EK))
    else:
        X = f"K.kstr.ins4({LQ}, r)"
        pre = ""
        xv = calc(f"U32.to_nat({X})", (f"Nat.add({Rv}, {D('4n', QL)})", hyp(f"ks.i4({LQ}, r, h0, hr)", f"U32.to_nat({X})", f"Nat.add({Rv}, {D('4n', QL)})")),
                  (f"Nat.add({D('4n', QL)}, {Rv})", "ring"), (V, EK))
    xe = f"UL.u32_value_eq({X}, W.W64.lo(v), Equal.trans(Nat, U32.to_nat({X}), {V}, U32.to_nat(W.W64.lo(v)), {xv.text}, Equal.sym(Nat, U32.to_nat(W.W64.lo(v)), {V}, ks.lo32(v, hv))))"
    put(f"""def ks.ml32(+q: W.W64, +r: U32, +v: W.W64, +e: {{Nat.add(Nat.mul({Qv}, {BN}), {Rv}) == {V} : Nat}}, +hv: {btrue(f'Nat.is_lt({V}, {W32})')}, +hr: {btrue(f'Nat.is_lt({Rv}, {BN})')}) -> {{K.kstr.ok(U32.is_eq({S}, 0), {X}) == Done{{W.W64.lo(v)}} : {R32}}}:
  +lqv = ks.lo32(q, {qlt})
  +ek = {ek.text}
  +h0 = ks.lt1({HJ}, UL.high_lt({jn}, 0n, {jn}, {QL}, {{==}}, {hj}))
  +sh = Equal.trans(Nat, U32.to_nat({S}), {HJ}, 0n, UL.u32_shrn_value({LQ}, {jn}), h0)
{pre}  %Equal.sym(Bool, U32.is_eq({S}, 0), True{{}}, {shz}) : {{K.kstr.ok(_, {X}) == Done{{W.W64.lo(v)}} : {R32}}}
  Equal.cong(U32, {R32}, zz => Done{{zz}}, {X}, W.W64.lo(v), {xe})
""")


def close_paren(s, i):
    """the index of the parenthesis closing the one at s[i]"""
    d = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            d += 1
        elif s[j] == ")":
            d -= 1
            if d == 0:
                return j
    raise ValueError


def variant_laws(put, n64, n32, sfx):
    t = capture(P.laws)
    t = t.replace("Laws.dec64_round_trip", f"Laws.{n64}").replace("Laws.dec32_round_trip", f"Laws.{n32}")
    t = t.replace("ks.r64(", f"ks.r64{sfx}(").replace("ks.r32(", f"ks.r32{sfx}(").replace("ks.ta(", f"ks.ta{sfx}(")
    if P.CFG["base"] == 16:
        while "ks.fr(" in t:
            i = t.index("ks.fr(")
            j = close_paren(t, i + 5)
            inner = t[i + 6:j]
            assert inner.endswith(", Nil{}"), inner[-20:]
            t = t[:i] + "ks.fra(" + inner[:-len(", Nil{}")] + ")" + t[j + 1:]
    put(t)


def tokens(put, variants):
    """the token lemmas, once for each (up, sfx) case of the letters: the
    digit lemmas (ks.tdn, ks.td, ks.ta) for each, the rest once"""
    first = True
    for up, sfx in variants:
        P.CFG["up"] = up
        blocks = re.split(r"\n\n(?=def |# )", capture(P.tokens))
        keep = []
        for blk in blocks:
            m = re.search(r"^def (\S+?)\(", blk, re.M)
            name = m.group(1) if m else None
            if first:
                if not (name == "ks.fr" and P.CFG["base"] == 16):
                    keep.append(blk)
            elif name in ("ks.tdn", "ks.td", "ks.ta"):
                keep.append(blk)
        t = "\n\n".join(keep)
        if not first:
            t = t.replace("ks.tdn(", f"ks.tdn{sfx}(").replace("ks.td(", f"ks.td{sfx}(").replace("ks.ta(", f"ks.ta{sfx}(")
        put(t)
        first = False


def fmt(put, base, variants, laws):
    """the round trips in base 8 or 16: variants are (up, suffix) for the
    letters' case, laws (up, suffix, 64-bit law, 32-bit law)"""
    P.CFG["base"] = base
    P.CFG["up"] = "False{}"
    P.lemmas(put)
    P.divmod_facts(put)
    tokens(put, variants)
    if base == 16:
        hexfront(put)
        words(put)
    P.mul64(put)
    mul32_shift(put)
    t = capture(P.parse)
    t = t.replace("ks.dmq(v), hv)))", "ks.dmq(v), hv, ks.dmr(v))))")
    put(t)
    for up, sfx, n64, n32 in laws:
        P.CFG["up"] = up
        variant_laws(put, n64, n32, sfx)
    P.CFG["base"] = 10
    P.CFG["up"] = "False{}"
