"""The proofs of kstr's padding laws (LAWS_pad.bend), for gen/proof.py.
KStr.format(f, v) is the bytes of kfmt.pad(w, zero, left, sign, digits),
with fill = w - len(sign ++ digits): sign ++ digits ++ fill spaces (left),
sign ++ fill zeros ++ digits (zero), or fill spaces ++ sign ++ digits; with
no width it is sign ++ digits itself, the unpadded form u. So, for any
lists sign and digits:

  * the length is len(u) + fill = max(w, len(u)) (kp.pl, kp.mx), through
    the lengths of an append and of kfmt.repeat (kp.la, kp.rl) and bytes'
    octets_len_of_list;
  * the bytes of a list append are the append of the bytes (kp.oa, from
    bytes' octets_to_of, octets_append_list and octets_of_to, and the mask
    of an append, kp.ma); kfmt.repeat(n, c, acc) is n c's before acc
    (kp.rc, kp.rs); so left-justified, the first len(u) bytes are u
    (octets_take_append_le, octets_take_len), and right-justified, dropping
    fill bytes leaves u (octets_drop_append_add, octets_drop_zero).
"""
import natproof as N
from natproof import calc, hyp

TL = "List<&2, U32>"
OC = "B.Octets"


def eq(a, b, t="Nat"):
    return "{" + f"{a} == {b} : {t}" + "}"


def tr(t, a, b, c, ab, bc):
    return f"Equal.trans({t}, {a}, {b}, {c}, {ab}, {bc})"


def sy(t, a, b, e):
    return f"Equal.sym({t}, {a}, {b}, {e})"


def cg(ta, tb, body, a, b, e):
    return f"Equal.cong({ta}, {tb}, z => {body}, {a}, {b}, {e})"


def SG():
    return "F.kfmt.sign.pick(Bool.and(F.kfmt.signed(c), F.kfmt.neg(v)), Bool.and(F.kfmt.signed(c), p), Bool.and(F.kfmt.signed(c), s))"


def DS():
    return "F.kfmt.digits(64n, False{}, F.kfmt.mag.pick(Bool.and(F.kfmt.signed(c), F.kfmt.neg(v)), v), F.kfmt.base(c), F.kfmt.upper(c), Nil{})"


def pad(put0):
    lines = []

    def put(s=""):
        lines.append(s)
        if s == "":
            for x in lines:
                put0(x)
            lines.clear()
    put("# Lists: the length of an append and of kfmt.repeat; kfmt.repeat as an")
    put("# append; the mask of an append")
    put()
    put(f"def kp.la(+a: {TL}, +b: {TL}) -> {eq('B.len(B.append(a, b))', 'Nat.add(B.len(a), B.len(b))')}:")
    put("  match a:")
    put("    case Nil{}:")
    put("      {==}")
    put("    case Con{+h, +t}:")
    put(f"      {cg('Nat', 'Nat', '1n+z', 'B.len(B.append(t, b))', 'Nat.add(B.len(t), B.len(b))', 'kp.la(t, b)')}")
    put()
    R = lambda n, acc: f"F.kfmt.repeat({n}, c, {acc})"  # noqa: E731
    put(f"def kp.rl(+n: Nat, +c: U32, +acc: {TL}) -> {eq(f'B.len({R(chr(110), chr(97) + chr(99) + chr(99))})', 'Nat.add(n, B.len(acc))')}:")
    put("  match n:")
    put("    case 0n:")
    put("      {==}")
    put("    case 1n+k:")
    put(f"      {tr('Nat', f'B.len({R(chr(107), chr(67) + chr(111) + chr(110) + chr(123) + chr(99) + chr(44) + chr(32) + chr(97) + chr(99) + chr(99) + chr(125))})', 'Nat.add(k, 1n+B.len(acc))', '1n+Nat.add(k, B.len(acc))', 'kp.rl(k, c, Con{c, acc})', 'UL.nat_add_succ(k, B.len(acc))')}")
    put()
    put(f"def kp.rc(+n: Nat, +c: U32, +acc: {TL}) -> {eq(R('n', 'Con{c, acc}'), 'Con{c, ' + R('n', 'acc') + '}', TL)}:")
    put("  match n:")
    put("    case 0n:")
    put("      {==}")
    put("    case 1n+k:")
    put("      kp.rc(k, c, Con{c, acc})")
    put()
    A = R("k", "Con{c, acc}")
    Bm = "Con{c, " + R("k", "acc") + "}"
    Cm = "Con{c, B.append(" + R("k", "Nil{}") + ", acc)}"
    Dm = "B.append(" + R("k", "Con{c, Nil{}}") + ", acc)"
    step = tr(TL, A, Bm, Dm, "kp.rc(k, c, acc)",
              tr(TL, Bm, Cm, Dm, cg(TL, TL, "Con{c, z}", R("k", "acc"), "B.append(" + R("k", "Nil{}") + ", acc)", "kp.rs(k, c, acc)"),
                 cg(TL, TL, "B.append(z, acc)", "Con{c, " + R("k", "Nil{}") + "}", R("k", "Con{c, Nil{}}"),
                    sy(TL, R("k", "Con{c, Nil{}}"), "Con{c, " + R("k", "Nil{}") + "}", "kp.rc(k, c, Nil{})"))))
    put(f"def kp.rs(+n: Nat, +c: U32, +acc: {TL}) -> {eq(R('n', 'acc'), 'B.append(' + R('n', 'Nil{}') + ', acc)', TL)}:")
    put("  match n:")
    put("    case 0n:")
    put("      {==}")
    put("    case 1n+k:")
    put(f"      {step}")
    put()
    put(f"def kp.ma(+xs: {TL}, +ys: {TL}) -> {eq('B.mask(B.append(xs, ys))', 'B.append(B.mask(xs), B.mask(ys))', TL)}:")
    put("  match xs:")
    put("    case Nil{}:")
    put("      {==}")
    put("    case Con{+h, +t}:")
    put(f"      {cg(TL, TL, 'Con{B.byte(h), z}', 'B.mask(B.append(t, ys))', 'B.append(B.mask(t), B.mask(ys))', 'kp.ma(t, ys)')}")
    put()
    # the bytes of an append
    L, Ao, Bo = "B.Octets.of_list(B.append(xs, ys))", "B.Octets.of_list(xs)", "B.Octets.of_list(ys)"
    Ro = f"B.Octets.append({Ao}, {Bo})"
    tlR = tr(TL, f"B.Octets.to_list({Ro})", f"B.append(B.Octets.to_list({Ao}), B.Octets.to_list({Bo}))", "B.append(B.mask(xs), B.mask(ys))",
             f"BL.octets_append_list({Ao}, {Bo})",
             tr(TL, f"B.append(B.Octets.to_list({Ao}), B.Octets.to_list({Bo}))", f"B.append(B.mask(xs), B.Octets.to_list({Bo}))", "B.append(B.mask(xs), B.mask(ys))",
                cg(TL, TL, f"B.append(z, B.Octets.to_list({Bo}))", f"B.Octets.to_list({Ao})", "B.mask(xs)", "BL.octets_to_of(xs)"),
                cg(TL, TL, "B.append(B.mask(xs), z)", f"B.Octets.to_list({Bo})", "B.mask(ys)", "BL.octets_to_of(ys)")))
    tl = tr(TL, f"B.Octets.to_list({L})", "B.mask(B.append(xs, ys))", f"B.Octets.to_list({Ro})", "BL.octets_to_of(B.append(xs, ys))",
            tr(TL, "B.mask(B.append(xs, ys))", "B.append(B.mask(xs), B.mask(ys))", f"B.Octets.to_list({Ro})", "kp.ma(xs, ys)",
               sy(TL, f"B.Octets.to_list({Ro})", "B.append(B.mask(xs), B.mask(ys))", tlR)))
    oa = tr(OC, L, f"B.Octets.of_list(B.Octets.to_list({L}))", Ro, sy(OC, f"B.Octets.of_list(B.Octets.to_list({L}))", L, f"BL.octets_of_to({L})"),
            tr(OC, f"B.Octets.of_list(B.Octets.to_list({L}))", f"B.Octets.of_list(B.Octets.to_list({Ro}))", Ro,
               cg(TL, OC, "B.Octets.of_list(z)", f"B.Octets.to_list({L})", f"B.Octets.to_list({Ro})", tl), f"BL.octets_of_to({Ro})"))
    put("# the bytes of a list append are the append of the bytes")
    put(f"def kp.oa(+xs: {TL}, +ys: {TL}) -> {eq(L, Ro, OC)}:")
    put(f"  {oa}")
    put()
    # n + (w - n) = max(w, n)
    put(f"def kp.mx(+w: Nat, +n: Nat) -> {eq('Nat.add(n, Nat.sub(w, n))', 'Nat.max(w, n)')}:")
    put("  match w n:")
    put("    case 0n 0n:")
    put("      {==}")
    put("    case 0n 1n+q:")
    put(f"      {cg('Nat', 'Nat', '1n+z', 'Nat.add(q, 0n)', 'q', 'UL.nat_add_zero(q)')}")
    put("    case 1n+p 0n:")
    put("      {==}")
    put("    case 1n+p 1n+q:")
    put(f"      {cg('Nat', 'Nat', '1n+z', 'Nat.add(q, Nat.sub(p, q))', 'Nat.max(p, q)', 'kp.mx(p, q)')}")
    put()
    # the length of the padded list, case by case
    LS, LD = "B.len(sg)", "B.len(ds)"
    LN = f"Nat.add({LS}, {LD})"
    X = "B.append(sg, ds)"
    goal = f"Nat.add({LN}, f)"
    la = hyp("kp.la(sg, ds)", f"B.len({X})", LN)
    p1 = calc(f"B.len(B.append({X}, F.kfmt.repeat(f, 32, Nil{{}})))",
              (f"Nat.add(B.len({X}), B.len(F.kfmt.repeat(f, 32, Nil{{}})))", hyp(f"kp.la({X}, F.kfmt.repeat(f, 32, Nil{{}}))", f"B.len(B.append({X}, F.kfmt.repeat(f, 32, Nil{{}})))", f"Nat.add(B.len({X}), B.len(F.kfmt.repeat(f, 32, Nil{{}})))")),
              (f"Nat.add({LN}, B.len(F.kfmt.repeat(f, 32, Nil{{}})))", la),
              (f"Nat.add({LN}, Nat.add(f, 0n))", hyp("kp.rl(f, 32, Nil{})", "B.len(F.kfmt.repeat(f, 32, Nil{}))", "Nat.add(f, 0n)")),
              (goal, "ring"))
    p2 = calc("B.len(B.append(sg, F.kfmt.repeat(f, 48, ds)))",
              (f"Nat.add({LS}, B.len(F.kfmt.repeat(f, 48, ds)))", hyp("kp.la(sg, F.kfmt.repeat(f, 48, ds))", "B.len(B.append(sg, F.kfmt.repeat(f, 48, ds)))", f"Nat.add({LS}, B.len(F.kfmt.repeat(f, 48, ds)))")),
              (f"Nat.add({LS}, Nat.add(f, {LD}))", hyp("kp.rl(f, 48, ds)", "B.len(F.kfmt.repeat(f, 48, ds))", f"Nat.add(f, {LD})")),
              (goal, "ring"))
    p3 = calc(f"B.len(F.kfmt.repeat(f, 32, {X}))",
              (f"Nat.add(f, B.len({X}))", hyp(f"kp.rl(f, 32, {X})", f"B.len(F.kfmt.repeat(f, 32, {X}))", f"Nat.add(f, B.len({X}))")),
              (f"Nat.add(f, {LN})", la), (goal, "ring"))
    put(f"def kp.pl(+l: Bool, +z: Bool, +f: Nat, +sg: {TL}, +ds: {TL}) -> {eq('B.len(F.kfmt.pad.pick(l, z, f, sg, ds))', goal)}:")
    put("  match l z:")
    put("    case True{} _:")
    put(f"      {p1.text}")
    put("    case False{} True{}:")
    put(f"      {p2.text}")
    put("    case False{} False{}:")
    put(f"      {p3.text}")
    put()
    U = f"B.Octets.of_list({X})"
    LU = f"B.Octets.len({U})"
    FILL = f"Nat.sub(w, {LN})"
    PAD = lambda z, l: f"F.kfmt.pad(w, {z}, {l}, sg, ds)"  # noqa: E731
    lenu = calc(LU, (f"B.len({X})", hyp(f"BL.octets_len_of_list({X})", LU, f"B.len({X})")), (LN, la))
    put(f"def kp.lu(+sg: {TL}, +ds: {TL}) -> {eq(LU, LN)}:")
    put(f"  {lenu.text}")
    put()
    LUH = hyp("kp.lu(sg, ds)", LU, LN)
    plen = calc(f"B.Octets.len(B.Octets.of_list({PAD('z', 'l')}))",
                (f"B.len({PAD('z', 'l')})", hyp(f"BL.octets_len_of_list({PAD('z', 'l')})", f"B.Octets.len(B.Octets.of_list({PAD('z', 'l')}))", f"B.len({PAD('z', 'l')})")),
                (f"B.len(F.kfmt.pad.pick(l, z, {FILL}, sg, ds))", "="),
                (f"Nat.add({LN}, {FILL})", hyp(f"kp.pl(l, z, {FILL}, sg, ds)", f"B.len(F.kfmt.pad.pick(l, z, {FILL}, sg, ds))", f"Nat.add({LN}, {FILL})")),
                (f"Nat.max(w, {LN})", hyp(f"kp.mx(w, {LN})", f"Nat.add({LN}, {FILL})", f"Nat.max(w, {LN})")),
                (f"Nat.max(w, {LU})", N.sym(LUH)))
    put(f"def kp.plen(+w: Nat, +z: Bool, +l: Bool, +sg: {TL}, +ds: {TL}) -> {eq(f'B.Octets.len(B.Octets.of_list({PAD(chr(122), chr(108))}))', f'Nat.max(w, {LU})')}:")
    put(f"  {plen.text}")
    put()
    put("def Laws.pad_len(c, w, z, l, p, s, v):")
    put(f"  kp.plen(w, z, l, {SG()}, {DS()})")
    put()
    # left-justified
    REP = f"F.kfmt.repeat({FILL}, 32, Nil{{}})"
    AP = f"B.Octets.append({U}, B.Octets.of_list({REP}))"
    left = tr(OC, f"B.Octets.take({LU}, B.Octets.of_list(B.append({X}, {REP})))", f"B.Octets.take({LU}, {AP})", U,
              cg(OC, OC, f"B.Octets.take({LU}, z)", f"B.Octets.of_list(B.append({X}, {REP}))", AP, f"kp.oa({X}, {REP})"),
              tr(OC, f"B.Octets.take({LU}, {AP})", f"B.Octets.take({LU}, {U})", U,
                 f"BL.octets_take_append_le({LU}, {U}, B.Octets.of_list({REP}), UL.nat_le_refl({LU}))", f"BL.octets_take_len({U})"))
    put(f"def kp.pleft(+w: Nat, +z: Bool, +sg: {TL}, +ds: {TL}) -> {eq(f'B.Octets.take({LU}, B.Octets.of_list({PAD(chr(122), chr(84) + chr(114) + chr(117) + chr(101) + chr(123) + chr(125))}))', U, OC)}:")
    put(f"  {left}")
    put()
    put("def Laws.pad_left(c, w, z, p, s, v):")
    put(f"  kp.pleft(w, z, {SG()}, {DS()})")
    put()
    # right-justified with spaces
    RA = f"B.Octets.of_list({REP})"
    LA = f"B.Octets.len({RA})"
    e2 = calc(f"Nat.sub(w, {LU})", (FILL, LUH), (f"Nat.add({FILL}, 0n)", "ring"),
              (f"B.len({REP})", N.sym(hyp(f"kp.rl({FILL}, 32, Nil{{}})", f"B.len({REP})", f"Nat.add({FILL}, 0n)"))),
              (f"Nat.add(B.len({REP}), 0n)", "ring"),
              (f"Nat.add({LA}, 0n)", N.sym(hyp(f"BL.octets_len_of_list({REP})", LA, f"B.len({REP})"))))
    RX = f"F.kfmt.repeat({FILL}, 32, {X})"
    OL = f"B.Octets.of_list({RX})"
    AU = f"B.Octets.append({RA}, {U})"
    e1 = tr(OC, OL, f"B.Octets.of_list(B.append({REP}, {X}))", AU,
            cg(TL, OC, "B.Octets.of_list(z)", RX, f"B.append({REP}, {X})", f"kp.rs({FILL}, 32, {X})"), f"kp.oa({REP}, {X})")
    right = tr(OC, f"B.Octets.drop(Nat.sub(w, {LU}), {OL})", f"B.Octets.drop(Nat.add({LA}, 0n), {OL})", U,
               cg("Nat", OC, f"B.Octets.drop(z, {OL})", f"Nat.sub(w, {LU})", f"Nat.add({LA}, 0n)", e2.text),
               tr(OC, f"B.Octets.drop(Nat.add({LA}, 0n), {OL})", f"B.Octets.drop(Nat.add({LA}, 0n), {AU})", U,
                  cg(OC, OC, f"B.Octets.drop(Nat.add({LA}, 0n), z)", OL, AU, e1),
                  tr(OC, f"B.Octets.drop(Nat.add({LA}, 0n), {AU})", f"B.Octets.drop(0n, {U})", U,
                     f"BL.octets_drop_append_add({RA}, 0n, {U})", f"BL.octets_drop_zero({U})")))
    put(f"def kp.pright(+w: Nat, +sg: {TL}, +ds: {TL}) -> {eq(f'B.Octets.drop(Nat.sub(w, {LU}), B.Octets.of_list({PAD(chr(70) + chr(97) + chr(108) + chr(115) + chr(101) + chr(123) + chr(125), chr(70) + chr(97) + chr(108) + chr(115) + chr(101) + chr(123) + chr(125))}))', U, OC)}:")
    put(f"  {right}")
    put()
    put("def Laws.pad_right(c, w, p, s, v):")
    put(f"  kp.pright(w, {SG()}, {DS()})")
    put()
