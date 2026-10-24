"""The proof of kmath's recip_exact (reciprocal.bend), for gen/proof.py:
Granlund and Montgomery's Theorem 4.2 for 32-bit words, every a and every
d >= 1.

With l = fls(d - 1), so that d <= 2^l < 2d, and c = 2^l - d (the wrapping
U32.sub(U32.shln(1, l), d)), the precomputation is Q = floor(c 2^32 / d)
(word64's division: Q d + r0 = c 2^32, r0 < d), m = Q + 1 (no wrap: Q + 1 <
2^32 since c < d), and the divide step takes t = floor(a m / 2^32) (a m = t
2^32 + s, s < 2^32), with t <= a. The core (km.k_core) is the theorem: with
a = q d + r, r < d, the quotient of a + t by 2^l is q. The shifts compute
that quotient: t + ((a - t) >> 1) >> (l - 1) is (a + t) >> l for l >= 1
(km.shk), and a itself for l = 0 (d = 1).

Every lemma that reasons with 2^32 takes it as a variable w (the K-lemmas
km.k_*), and is used at w = U32Nat.dbl(32n, 1n) only with hypotheses whose
types are exactly that instance, so no closed power of two is ever
compared by computation (u32/README.md, "Stating the bounds").
"""
from natproof import absurd, bcong, btrue, calc, hyp, le_from, lt_from, lt_rw, sym, wit_le, wit_lt


def v32(x):
    return f"U32.to_nat({x})"


def v64(x):
    return f"W.W64.to_nat({x})"


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


def A(x, y):
    return f"Nat.add({x}, {y})"


def M(x, y):
    return f"Nat.mul({x}, {y})"


def klemmas(put):
    put("# The theorem, with 2^32 as a variable w and 2^l as Dl\n")
    # c + d = 2^l < 2 d: c < d
    g, G = wit_lt("Dl", "Nat.double(dv)", "p2")
    pf = calc(f"Nat.add(dv, Nat.add({g}, 1n+cv))",
              (f"Nat.add({g}, 1n+Nat.add(cv, dv))", "ring"),
              (f"Nat.add({g}, 1n+Dl)", hyp("e5", "Nat.add(cv, dv)", "Dl")),
              ("Nat.double(dv)", G),
              ("Nat.add(dv, dv)", "ring"))
    c = hyp(f"UL.nat_add_cancel(dv, Nat.add({g}, 1n+cv), dv, {pf.text})", f"Nat.add({g}, 1n+cv)", "dv")
    put(f"""def km.k_cd(+dv: Nat, +cv: Nat, +Dl: Nat, e5: {{Nat.add(cv, dv) == Dl : Nat}}, p2: {btrue('Nat.is_lt(Dl, Nat.double(dv))')}) -> {btrue('Nat.is_lt(cv, dv)')}:
  {lt_from("cv", "dv", g, c)}
""")

    # Q d + r0 = c w, c < d < w: Q + 1 < w
    U = hyp("uu", "Nat.add(u, w)", "Nat.add(qv, 1n)")
    C1 = hyp("c1", "Nat.add(c, 1n+cv)", "dv")
    D1 = hyp("d1", "Nat.add(dd, 1n+dv)", "w")
    H1 = hyp("h1", "Nat.add(Nat.mul(qv, dv), r0)", "Nat.mul(cv, w)")
    S = "Nat.add(r0, Nat.add(Nat.mul(u, dv), Nat.add(Nat.mul(w, c), w)))"
    pf = calc(f"Nat.add(Nat.mul(cv, w), {S})",
              ("Nat.add(r0, Nat.add(Nat.mul(u, dv), Nat.mul(w, Nat.add(c, 1n+cv))))", "ring"),
              ("Nat.add(r0, Nat.add(Nat.mul(u, dv), Nat.mul(w, dv)))", C1),
              ("Nat.add(r0, Nat.mul(Nat.add(u, w), dv))", "ring"),
              ("Nat.add(r0, Nat.mul(Nat.add(qv, 1n), dv))", U),
              ("Nat.add(dv, Nat.add(Nat.mul(qv, dv), r0))", "ring"),
              ("Nat.add(dv, Nat.mul(cv, w))", H1),
              ("Nat.add(Nat.mul(cv, w), dv)", "ring"))
    X0 = hyp(f"UL.nat_add_cancel(Nat.mul(cv, w), {S}, dv, {pf.text})", S, "dv")
    K = "Nat.add(r0, Nat.add(Nat.mul(u, dv), Nat.add(Nat.mul(w, c), dd)))"
    pf2 = calc(f"Nat.add({K}, 1n+dv)",
               ("Nat.add(r0, Nat.add(Nat.mul(u, dv), Nat.add(Nat.mul(w, c), Nat.add(dd, 1n+dv))))", "ring"),
               (S, D1),
               ("dv", X0))
    ty = btrue("Nat.is_lt(Nat.add(qv, 1n), w)")
    put(f"""def km.k_q1(+w: Nat, +dv: Nat, +cv: Nat, +qv: Nat, +r0: Nat, +h1: {{Nat.add(Nat.mul(qv, dv), r0) == Nat.mul(cv, w) : Nat}}, +hc: {btrue('Nat.is_lt(cv, dv)')}, +hd: {btrue('Nat.is_lt(dv, w)')}, z: Bool, ez: {{Nat.is_lt(Nat.add(qv, 1n), w) == z : Bool}}) -> {ty}:
  match z:
    case True{{}}:
      ez
    case False{{}}:
      +u = Nat.sub(Nat.add(qv, 1n), w)
      +uu = UL.nat_le_witness(w, Nat.add(qv, 1n), km.nlt_le(Nat.add(qv, 1n), w, ez))
      +c = Nat.sub(dv, 1n+cv)
      +c1 = UL.nat_lt_witness(cv, dv, hc)
      +dd = Nat.sub(w, 1n+dv)
      +d1 = UL.nat_lt_witness(dv, w, hd)
      {absurd(ty, K, "dv", pf2)}

def km.k_q(+w: Nat, +dv: Nat, +cv: Nat, +qv: Nat, +r0: Nat, +h1: {{Nat.add(Nat.mul(qv, dv), r0) == Nat.mul(cv, w) : Nat}}, +hc: {btrue('Nat.is_lt(cv, dv)')}, +hd: {btrue('Nat.is_lt(dv, w)')}) -> {ty}:
  km.k_q1(w, dv, cv, qv, r0, h1, hc, hd, Nat.is_lt(Nat.add(qv, 1n), w), {{==}})
""")

    # s + t w = a (Q + 1), Q + 1 < w: t <= a
    U = hyp("uu", "Nat.add(u, 1n+av)", "t")
    G = hyp("gg", "Nat.add(g, 1n+Nat.add(qv, 1n))", "w")
    H2 = hyp("h2", "Nat.add(s, Nat.mul(t, w))", "Nat.mul(av, Nat.add(qv, 1n))")
    X = "Nat.mul(av, Nat.add(qv, 1n))"
    K = "Nat.add(s, Nat.add(Nat.mul(u, w), Nat.add(g, Nat.add(Nat.add(qv, 1n), Nat.add(Nat.mul(av, g), av)))))"
    WW = "Nat.add(g, 1n+Nat.add(qv, 1n))"
    pf = calc(f"Nat.add({K}, 1n+{X})",
              (f"Nat.add(s, Nat.add(Nat.mul(u, w), Nat.add({WW}, Nat.mul(av, {WW}))))", "ring"),
              ("Nat.add(s, Nat.add(Nat.mul(u, w), Nat.add(w, Nat.mul(av, w))))", G),
              ("Nat.add(s, Nat.mul(Nat.add(u, 1n+av), w))", "ring"),
              ("Nat.add(s, Nat.mul(t, w))", U),
              (X, H2))
    put(f"""def km.k_ta1(+w: Nat, +av: Nat, +qv: Nat, +s: Nat, +t: Nat, +h2: {{Nat.add(s, Nat.mul(t, w)) == {X} : Nat}}, +hq: {btrue('Nat.is_lt(Nat.add(qv, 1n), w)')}, z: Bool, ez: {{Nat.is_le(t, av) == z : Bool}}) -> {btrue('Nat.is_le(t, av)')}:
  match z:
    case True{{}}:
      ez
    case False{{}}:
      +u = Nat.sub(t, 1n+av)
      +uu = UL.nat_lt_witness(av, t, km.nle_lt(t, av, ez))
      +g = Nat.sub(w, 1n+Nat.add(qv, 1n))
      +gg = UL.nat_lt_witness(Nat.add(qv, 1n), w, hq)
      {absurd(btrue("Nat.is_le(t, av)"), K, X, pf)}

def km.k_ta(+w: Nat, +av: Nat, +qv: Nat, +s: Nat, +t: Nat, +h2: {{Nat.add(s, Nat.mul(t, w)) == {X} : Nat}}, +hq: {btrue('Nat.is_lt(Nat.add(qv, 1n), w)')}) -> {btrue('Nat.is_le(t, av)')}:
  km.k_ta1(w, av, qv, s, t, h2, hq, Nat.is_le(t, av), {{==}})
""")

    # the core
    Xt = "Nat.add(av, t)"
    qD = "Nat.mul(q, Dl)"
    LHS = f"Nat.add(Nat.mul(dv, Nat.mul({Xt}, w)), Nat.add(Nat.mul(dv, s), Nat.mul(av, r0)))"
    RS = "Nat.add(Nat.mul(q, Nat.mul(dv, Nat.mul(w, Dl))), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, dv)))"
    H1 = hyp("h1", "Nat.add(Nat.mul(qv, dv), r0)", "Nat.mul(cv, w)")
    H2 = hyp("h2", "Nat.add(s, Nat.mul(t, w))", "Nat.mul(av, Nat.add(qv, 1n))")
    H3 = hyp("h3", "Nat.add(Nat.mul(q, dv), r)", "av")
    H5 = hyp("h5", "Nat.add(cv, dv)", "Dl")
    EQS = calc(LHS,
               ("Nat.add(Nat.mul(av, Nat.mul(dv, w)), Nat.add(Nat.mul(dv, Nat.add(s, Nat.mul(t, w))), Nat.mul(av, r0)))", "ring"),
               ("Nat.add(Nat.mul(av, Nat.mul(dv, w)), Nat.add(Nat.mul(dv, Nat.mul(av, Nat.add(qv, 1n))), Nat.mul(av, r0)))", H2),
               ("Nat.add(Nat.mul(av, Nat.mul(dv, w)), Nat.add(Nat.mul(av, dv), Nat.mul(av, Nat.add(Nat.mul(qv, dv), r0))))", "ring"),
               ("Nat.add(Nat.mul(av, Nat.mul(dv, w)), Nat.add(Nat.mul(av, dv), Nat.mul(av, Nat.mul(cv, w))))", H1),
               ("Nat.add(Nat.mul(av, Nat.mul(w, Nat.add(cv, dv))), Nat.mul(av, dv))", "ring"),
               ("Nat.add(Nat.mul(av, Nat.mul(w, Dl)), Nat.mul(av, dv))", H5),
               ("Nat.add(Nat.mul(Nat.add(Nat.mul(q, dv), r), Nat.mul(w, Dl)), Nat.mul(av, dv))", H3),
               (RS, "ring"))
    eqs = hyp("eqs", LHS, RS)
    # below: X + 1 + u = q Dl
    U = hyp("uu", f"Nat.add(u, 1n+{Xt})", qD)
    S1 = hyp("s1", "Nat.add(s1v, 1n+s)", "w")
    E1 = hyp("e1", "Nat.add(e1v, 1n+r0)", "dv")
    R2 = f"Nat.add(Nat.mul(Nat.add(u, 1n+{Xt}), Nat.mul(dv, w)), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, dv)))"
    LR2 = calc(LHS, (RS, eqs),
               (f"Nat.add(Nat.mul({qD}, Nat.mul(dv, w)), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, dv)))", "ring"),
               (R2, U))
    K1 = "Nat.add(Nat.mul(u, Nat.mul(dv, w)), Nat.add(Nat.mul(dv, s1v), Nat.add(e1v, Nat.add(r0, Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.add(Nat.mul(av, e1v), av))))))"
    T = (f"Nat.add(Nat.mul(u, Nat.mul(dv, w)), Nat.add(Nat.add(Nat.mul(dv, s1v), Nat.add(Nat.add(e1v, 1n+r0), Nat.mul(dv, s))), "
         f"Nat.add(Nat.mul({Xt}, Nat.mul(dv, w)), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, Nat.add(e1v, 1n+r0))))))")
    T1 = (f"Nat.add(Nat.mul(u, Nat.mul(dv, w)), Nat.add(Nat.add(Nat.mul(dv, s1v), Nat.add(dv, Nat.mul(dv, s))), "
          f"Nat.add(Nat.mul({Xt}, Nat.mul(dv, w)), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, dv)))))")
    T2 = (f"Nat.add(Nat.mul(u, Nat.mul(dv, w)), Nat.add(Nat.mul(dv, Nat.add(s1v, 1n+s)), "
          f"Nat.add(Nat.mul({Xt}, Nat.mul(dv, w)), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, dv)))))")
    T3 = (f"Nat.add(Nat.mul(u, Nat.mul(dv, w)), Nat.add(Nat.mul(dv, w), "
          f"Nat.add(Nat.mul({Xt}, Nat.mul(dv, w)), Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.mul(av, dv)))))")
    pf_lo = calc(f"Nat.add({K1}, 1n+{LHS})",
                 (T, "ring"), (T1, E1), (T2, "ring"), (T3, S1), (R2, "ring"), (LHS, sym(LR2)))
    # above: rem = Dl + u
    rem = f"Nat.sub({Xt}, {qD})"
    RW = hyp("rw", f"Nat.add({rem}, {qD})", Xt)
    UU = hyp("uu", "Nat.add(u, Dl)", rem)
    R1 = hyp("r1", "Nat.add(r1v, 1n+r)", "dv")
    A1 = hyp("a1", "Nat.add(a1v, 1n+av)", "w")
    L2 = f"Nat.add(Nat.mul(dv, Nat.mul(Nat.add(Nat.add(u, Dl), {qD}), w)), Nat.add(Nat.mul(dv, s), Nat.mul(av, r0)))"
    L2RS = calc(L2,
                (f"Nat.add(Nat.mul(dv, Nat.mul(Nat.add({rem}, {qD}), w)), Nat.add(Nat.mul(dv, s), Nat.mul(av, r0)))", UU),
                (LHS, RW), (RS, eqs))
    K2 = "Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, cv), Nat.add(Nat.mul(a1v, dv), Nat.add(r1v, Nat.add(r, Nat.add(Nat.mul(dv, s), Nat.mul(av, r0))))))))"
    tail = "Nat.add(Nat.mul(r, Nat.mul(w, Dl)), Nat.add(Nat.mul(q, Nat.mul(dv, Nat.mul(w, Dl))), Nat.add(Nat.mul(dv, s), Nat.mul(av, r0))))"
    U1 = (f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, cv), Nat.add(Nat.mul(a1v, dv), "
          f"Nat.add(Nat.add(r1v, 1n+r), Nat.add(Nat.mul(av, dv), {tail}))))))")
    U2 = (f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, cv), Nat.add(Nat.mul(a1v, dv), "
          f"Nat.add(dv, Nat.add(Nat.mul(av, dv), {tail}))))))")
    U3 = f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, cv), Nat.add(Nat.mul(Nat.add(a1v, 1n+av), dv), {tail}))))"
    U4 = f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, cv), Nat.add(Nat.mul(w, dv), {tail}))))"
    U5 = f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, Nat.add(cv, dv)), {tail})))"
    U6 = f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(r1v, Nat.mul(w, Dl)), Nat.add(Nat.mul(w, Dl), {tail})))"
    tail2 = "Nat.add(Nat.mul(q, Nat.mul(dv, Nat.mul(w, Dl))), Nat.add(Nat.mul(dv, s), Nat.mul(av, r0)))"
    U7 = f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(Nat.add(r1v, 1n+r), Nat.mul(w, Dl)), {tail2}))"
    U8 = f"Nat.add(Nat.mul(dv, Nat.mul(w, u)), Nat.add(Nat.mul(dv, Nat.mul(w, Dl)), {tail2}))"
    pf_hi = calc(f"Nat.add({K2}, 1n+{RS})",
                 (U1, "ring"), (U2, R1), (U3, "ring"), (U4, A1), (U5, "ring"), (U6, H5), (U7, "ring"), (U8, R1), (L2, "ring"), (RS, L2RS))
    pair = "{" + f"Nat.add({rem}, {qD}) == {Xt} : Nat" + "} & " + btrue(f"Nat.is_lt({rem}, Dl)")
    hyps = ("+w: Nat, +Dl: Nat, +av: Nat, +dv: Nat, +cv: Nat, +qv: Nat, +r0: Nat, +s: Nat, +t: Nat, +q: Nat, +r: Nat, "
            "+h1: {Nat.add(Nat.mul(qv, dv), r0) == Nat.mul(cv, w) : Nat}, +h1b: " + btrue("Nat.is_lt(r0, dv)") + ", "
            "+h2: {Nat.add(s, Nat.mul(t, w)) == Nat.mul(av, Nat.add(qv, 1n)) : Nat}, +h2b: " + btrue("Nat.is_lt(s, w)") + ", "
            "+h3: {Nat.add(Nat.mul(q, dv), r) == av : Nat}, +h3b: " + btrue("Nat.is_lt(r, dv)") + ", "
            "+h4: " + btrue("Nat.is_lt(av, w)") + ", +h5: {Nat.add(cv, dv) == Dl : Nat}")
    args = "w, Dl, av, dv, cv, qv, r0, s, t, q, r, h1, h1b, h2, h2b, h3, h3b, h4, h5"
    put(f"""def km.k_core1(+w: Nat, +Dl: Nat, +av: Nat, +dv: Nat, +cv: Nat, +qv: Nat, +r0: Nat, +s: Nat, +t: Nat, +q: Nat, +r: Nat, +h1: {{Nat.add(Nat.mul(qv, dv), r0) == Nat.mul(cv, w) : Nat}}, +h2: {{Nat.add(s, Nat.mul(t, w)) == Nat.mul(av, Nat.add(qv, 1n)) : Nat}}, +h3: {{Nat.add(Nat.mul(q, dv), r) == av : Nat}}, +h5: {{Nat.add(cv, dv) == Dl : Nat}}) -> {{{LHS} == {RS} : Nat}}:
  {EQS.text}

def km.k_core(+w: Nat, +Dl: Nat, +av: Nat, +dv: Nat, +cv: Nat, +qv: Nat, +r0: Nat, +s: Nat, +t: Nat, +q: Nat, +r: Nat, +h1: {{Nat.add(Nat.mul(qv, dv), r0) == Nat.mul(cv, w) : Nat}}, +h1b: {btrue('Nat.is_lt(r0, dv)')}, +h2: {{Nat.add(s, Nat.mul(t, w)) == Nat.mul(av, Nat.add(qv, 1n)) : Nat}}, +h2b: {btrue('Nat.is_lt(s, w)')}, +h3: {{Nat.add(Nat.mul(q, dv), r) == av : Nat}}, +h3b: {btrue('Nat.is_lt(r, dv)')}, +h4: {btrue('Nat.is_lt(av, w)')}, +h5: {{Nat.add(cv, dv) == Dl : Nat}}, z1: Bool, ez1: {{Nat.is_le({qD}, {Xt}) == z1 : Bool}}, z2: Bool, ez2: {{Nat.is_lt({rem}, Dl) == z2 : Bool}}) -> {pair}:
  match z1:
    case True{{}}:
      match z2:
        case True{{}}:
          (UL.nat_le_witness({qD}, {Xt}, ez1), ez2)
        case False{{}}:
          +eqs = km.k_core1(w, Dl, av, dv, cv, qv, r0, s, t, q, r, h1, h2, h3, h5)
          +rw = UL.nat_le_witness({qD}, {Xt}, ez1)
          +u = Nat.sub({rem}, Dl)
          +uu = UL.nat_le_witness(Dl, {rem}, km.nlt_le({rem}, Dl, ez2))
          +r1v = Nat.sub(dv, 1n+r)
          +r1 = UL.nat_lt_witness(r, dv, h3b)
          +a1v = Nat.sub(w, 1n+av)
          +a1 = UL.nat_lt_witness(av, w, h4)
          {absurd(pair, K2, RS, pf_hi)}
    case False{{}}:
      +eqs = km.k_core1(w, Dl, av, dv, cv, qv, r0, s, t, q, r, h1, h2, h3, h5)
      +u = Nat.sub({qD}, 1n+{Xt})
      +uu = UL.nat_lt_witness({Xt}, {qD}, km.nle_lt({qD}, {Xt}, ez1))
      +s1v = Nat.sub(w, 1n+s)
      +s1 = UL.nat_lt_witness(s, w, h2b)
      +e1v = Nat.sub(dv, 1n+r0)
      +e1 = UL.nat_lt_witness(r0, dv, h1b)
      {absurd(pair, K1, LHS, pf_lo)}
""")
    _ = (hyps, args)

    # the shifts: (t + ((a - t) >> 1)) >> k = (a + t) >> (1 + k)
    y = "Nat.sub(a, t)"
    z = f"Nat.add(t, U.U32Nat.half({y}))"
    lo, hi = f"U.U32Nat.low(k, {z})", f"U.U32Nat.high(k, {z})"
    Y = hyp(f"UL.nat_le_witness(t, a, ht)", f"Nat.add({y}, t)", "a")
    LHZ = hyp(f"UL.low_high(k, {z})", f"Nat.add({lo}, {D('k', hi)})", z)
    OH = hyp(f"UL.nat_odd_half({y})", f"Nat.add(U.U32Nat.odd({y}), Nat.double(U.U32Nat.half({y})))", y)
    e = calc(f"Nat.add(Nat.add(U.U32Nat.odd({y}), Nat.double({lo})), {D('1n+k', hi)})",
             (f"Nat.add(Nat.add(U.U32Nat.odd({y}), Nat.double({lo})), Nat.double({D('k', hi)}))", "="),
             (f"Nat.add(U.U32Nat.odd({y}), Nat.double(Nat.add({lo}, {D('k', hi)})))", "ring"),
             (f"Nat.add(U.U32Nat.odd({y}), Nat.double({z}))", LHZ),
             (f"Nat.add(Nat.add(U.U32Nat.odd({y}), Nat.double(U.U32Nat.half({y}))), Nat.double(t))", "ring"),
             (f"Nat.add({y}, Nat.double(t))", OH),
             (f"Nat.add(Nat.add({y}, t), t)", "ring"),
             ("Nat.add(a, t)", Y))
    so = f"Nat.sub(1n, U.U32Nat.odd({y}))"
    OW = hyp(f"UL.nat_le_witness(U.U32Nat.odd({y}), 1n, UL.nat_odd_le({y}))", f"Nat.add({so}, U.U32Nat.odd({y}))", "1n")
    gl, LW = wit_lt(lo, D("k", "1n"), f"UL.low_lt(k, {z})")
    pf = calc(f"Nat.add(Nat.add(Nat.double({gl}), {so}), 1n+Nat.add(U.U32Nat.odd({y}), Nat.double({lo})))",
              (f"Nat.add(Nat.add(Nat.double({gl}), Nat.double({lo})), 1n+Nat.add({so}, U.U32Nat.odd({y})))", "ring"),
              (f"Nat.add(Nat.add(Nat.double({gl}), Nat.double({lo})), 1n+1n)", OW),
              (f"Nat.double(Nat.add({gl}, 1n+{lo}))", "ring"),
              (f"Nat.double({D('k', '1n')})", LW),
              (D("1n+k", "1n"), "="))
    hlt = lt_from(f"Nat.add(U.U32Nat.odd({y}), Nat.double({lo}))", D("1n+k", "1n"), f"Nat.add(Nat.double({gl}), {so})", pf)
    put(f"""def km.shk(+k: Nat, +a: Nat, +t: Nat, +ht: {btrue('Nat.is_le(t, a)')}) -> {{U.U32Nat.high(k, {z}) == U.U32Nat.high(1n+k, Nat.add(a, t)) : Nat}}:
  UL.high_unique(1n+k, Nat.add(a, t), Nat.add(U.U32Nat.odd({y}), Nat.double({lo})), {hi}, {e.text}, {hlt})

def km.mlt64(+n: Nat, +m: Nat, +x: Nat, +y: Nat, e: {{Nat.add(n, n) == m : Nat}}, hx: {btrue(f'Nat.is_lt(x, {D("n", "1n")})')}, hy: {btrue(f'Nat.is_lt(y, {D("n", "1n")})')}) -> {btrue(f'Nat.is_lt(Nat.mul(x, y), {D("m", "1n")})')}:
  %e : {btrue(f'Nat.is_lt(Nat.mul(x, y), {D("_", "1n")})')}
  %UL.dbl_dbl(n, n, 1n) : {btrue('Nat.is_lt(Nat.mul(x, y), _)')}
  %Equal.trans(Nat, Nat.mul({D('n', '1n')}, {D('n', '1n')}), {D('n', f"Nat.mul(1n, {D('n', '1n')})")}, {D('n', D('n', '1n'))}, UL.dbl_mul_l(n, 1n, {D('n', '1n')}), Equal.cong(Nat, Nat, zz => {D('n', 'zz')}, Nat.mul(1n, {D('n', '1n')}), {D('n', '1n')}, UL.nat_one_mul({D('n', '1n')}))) : {btrue('Nat.is_lt(Nat.mul(x, y), _)')}
  UL.nat_mul_lt(x, y, {D('n', '1n')}, {D('n', '1n')}, hx, hy)
""")


def glue(put):
    put("# The words: the precomputation's values, and the divide step\n")
    av, dv = v32("a"), v32("d")
    Dl = D("l", "1n")
    W = D("32n", "1n")
    SH = "U32.shln(1, l)"
    SUBW = f"U32.sub({SH}, d)"
    cv = v32(SUBW)
    NUM = f"W.W64.from_parts({SUBW}, 0)"
    FD = "W.W64.from_u32(d)"
    Q = f"W.W64.div({NUM}, {FD})"
    R0 = f"W.W64.mod({NUM}, {FD})"
    qv, r0 = v64(Q), v64(R0)
    LQ = f"W.W64.lo({Q})"
    MM = f"U32.add({LQ}, 1)"
    sub1 = "U32.sub(d, 1)"
    fls1 = f"R.KMath.fls({sub1})"
    lt_sle = f"km.lt_sle(0n, {dv}, dv1)"
    # d <= 2^l < 2 d
    E1 = calc(f"1n+Nat.sub({dv}, 1n)", (f"Nat.add(Nat.sub({dv}, 1n), 1n)", "ring"),
              (dv, hyp(f"UL.nat_lt_witness(0n, {dv}, dv1)", f"Nat.add(Nat.sub({dv}, 1n), 1n)", dv)))
    s0 = (f"UL.u32_value_eq({sub1}, 0, km.z0({v32(sub1)}, Equal.trans(Bool, Nat.is_eq({v32(sub1)}, 0n), U32.is_eq({sub1}, 0), True{{}}, "
          f"Equal.sym(Bool, U32.is_eq({sub1}, 0), Nat.is_eq({v32(sub1)}, 0n), UL.u32_eq_value({sub1}, 0)), ez)))")
    put(f"""def km.rd0(+d: U32, +l: Nat, +el: {{{fls1} == l : Nat}}, +dv1: {btrue(f'Nat.is_lt(0n, {dv})')}) -> {btrue(f'Nat.is_lt(Nat.sub({dv}, 1n), {Dl})')}:
  %el : {btrue(f'Nat.is_lt(Nat.sub({dv}, 1n), {D("_", "1n")})')}
  %UL.u32_sub_value(d, 1, {lt_sle}) : {btrue(f'Nat.is_lt(_, {D(fls1, "1n")})')}
  Laws.fls_lt({sub1})

def km.rd1(+d: U32, +l: Nat, +el: {{{fls1} == l : Nat}}, +dv1: {btrue(f'Nat.is_lt(0n, {dv})')}) -> {btrue(f'Nat.is_le({dv}, {Dl})')}:
  %{E1.text} : {btrue(f'Nat.is_le(_, {Dl})')}
  km.lt_sle(Nat.sub({dv}, 1n), {Dl}, km.rd0(d, l, el, dv1))

def km.rd4(+d: U32, +k: Nat, +el: {{{fls1} == 1n+k : Nat}}, +dv1: {btrue(f'Nat.is_lt(0n, {dv})')}, ez: {{U32.is_zero({sub1}) == False{{}} : Bool}}) -> {btrue(f'Nat.is_le({D("1n+k", "1n")}, Nat.double(Nat.sub({dv}, 1n)))')}:
  %el : {btrue(f'Nat.is_le({D("_", "1n")}, Nat.double(Nat.sub({dv}, 1n)))')}
  %UL.u32_sub_value(d, 1, {lt_sle}) : {btrue(f'Nat.is_le({D(fls1, "1n")}, Nat.double(_))')}
  Laws.fls_le({sub1}, ez)

def km.rd3(+d: U32, +k: Nat, +el: {{{fls1} == 1n+k : Nat}}, +dv1: {btrue(f'Nat.is_lt(0n, {dv})')}, z: Bool, ez: {{U32.is_zero({sub1}) == z : Bool}}) -> {btrue(f'Nat.is_lt({D("1n+k", "1n")}, Nat.double({dv}))')}:
  match z:
    case True{{}}:
      +s0 = {s0}
      Empty.absurd({btrue(f'Nat.is_lt({D("1n+k", "1n")}, Nat.double({dv}))')}, km.zs(k, Equal.trans(Nat, 0n, {fls1}, 1n+k, Equal.sym(Nat, {fls1}, 0n, Equal.trans(Nat, {fls1}, R.KMath.fls(0), 0n, Equal.cong(U32, Nat, zz => R.KMath.fls(zz), {sub1}, 0, s0), {{==}})), el)))
    case False{{}}:
      km.le_lt2({D("1n+k", "1n")}, {dv}, km.rd4(d, k, el, dv1, ez), dv1)

def km.rd2(+d: U32, +l: Nat, +el: {{{fls1} == l : Nat}}, +dv1: {btrue(f'Nat.is_lt(0n, {dv})')}) -> {btrue(f'Nat.is_lt({Dl}, Nat.double({dv}))')}:
  match l:
    case 0n:
      km.old({dv}, dv1)
    case 1n+ +k:
      km.rd3(d, k, el, dv1, U32.is_zero({sub1}), {{==}})
""")
    # c + d = 2^l
    b = f"U.U32Nat.bit(U32.is_lt({SH}, d))"
    hh = f"U.U32Nat.high(32n, {Dl})"
    x1 = f"Nat.sub({Dl}, {dv})"
    Yv = f"Nat.add({x1}, {D('32n', b)})"
    SW = hyp(f"UL.u32_sub_wrap({SH}, d)", f"Nat.add({cv}, {dv})", f"Nat.add({v32(SH)}, {D('32n', b)})")
    SL = hyp(f"UL.u32_shln_low(1, l)", v32(SH), f"U.U32Nat.low(32n, {D('l', '1n')})")
    LH = hyp(f"UL.low_high(32n, {Dl})", f"Nat.add(U.U32Nat.low(32n, {Dl}), {D('32n', hh)})", Dl)
    X1 = hyp("x1e", f"Nat.add({x1}, {dv})", Dl)
    pf = calc(f"Nat.add({dv}, Nat.add({cv}, {D('32n', hh)}))",
              (f"Nat.add(Nat.add({cv}, {dv}), {D('32n', hh)})", "ring"),
              (f"Nat.add(Nat.add({v32(SH)}, {D('32n', b)}), {D('32n', hh)})", SW),
              (f"Nat.add(Nat.add(U.U32Nat.low(32n, {Dl}), {D('32n', b)}), {D('32n', hh)})", SL),
              (f"Nat.add(Nat.add(U.U32Nat.low(32n, {Dl}), {D('32n', hh)}), {D('32n', b)})", "ring"),
              (f"Nat.add({Dl}, {D('32n', b)})", LH),
              (f"Nat.add(Nat.add({x1}, {dv}), {D('32n', b)})", X1),
              (f"Nat.add({dv}, {Yv})", "ring"))
    yy = f"UL.nat_add_cancel({dv}, Nat.add({cv}, {D('32n', hh)}), {Yv}, {pf.text})"
    u1 = hyp(f"UL.low_unique(32n, {Yv}, {cv}, {hh}, {yy}, km.lt32({SUBW}))", cv, f"U.U32Nat.low(32n, {Yv})")
    x1lt = f"km.lt_trans({x1}, {dv}, {W}, km.k_cd({dv}, {x1}, {Dl}, x1e, p2), km.lt32(d))"
    u2 = hyp(f"UL.low_unique(32n, {Yv}, {x1}, {b}, {{==}}, {x1lt})", x1, f"U.U32Nat.low(32n, {Yv})")
    cd = calc(f"Nat.add({cv}, {dv})", (f"Nat.add(U.U32Nat.low(32n, {Yv}), {dv})", u1), (f"Nat.add({x1}, {dv})", sym(u2)), (Dl, X1))
    put(f"""def km.rcd(+d: U32, +l: Nat, +p1: {btrue(f'Nat.is_le({dv}, {Dl})')}, +p2: {btrue(f'Nat.is_lt({Dl}, Nat.double({dv}))')}) -> {{Nat.add({cv}, {dv}) == {Dl} : Nat}}:
  +x1e = UL.nat_le_witness({dv}, {Dl}, p1)
  {cd.text}
""")
    # Q d + r0 = c w and r0 < d
    FV = hyp("km.fv(d)", v64(FD), dv)
    DMV = hyp(f"WL.divmod_value({NUM}, {FD}, h)", f"Nat.add(Nat.mul({qv}, {v64(FD)}), {r0})", v64(NUM))
    TN = hyp(f"WL.to_nat_parts({SUBW}, 0)", v64(NUM), f"Nat.add(U32.to_nat(0), {D('32n', cv)})")
    DM = hyp(f"UL.dbl_mul_r(32n, {cv}, 1n)", f"Nat.mul({cv}, {W})", D("32n", f"Nat.mul({cv}, 1n)"))
    MO = hyp(f"UL.nat_mul_one({cv})", f"Nat.mul({cv}, 1n)", cv)
    h1 = calc(f"Nat.add(Nat.mul({qv}, {dv}), {r0})",
              (f"Nat.add(Nat.mul({qv}, {v64(FD)}), {r0})", FV),
              (v64(NUM), DMV),
              (f"Nat.add(U32.to_nat(0), {D('32n', cv)})", TN),
              (D("32n", cv), "="),
              (D("32n", f"Nat.mul({cv}, 1n)"), MO),
              (f"Nat.mul({cv}, {W})", DM))
    # m = Q + 1
    qlt = f"km.lt_pred({qv}, {W}, q1)"
    AW = hyp(f"UL.u32_add_wrap({LQ}, 1)", f"Nat.add({v32(MM)}, {D('32n', f'U.U32Nat.bit(U32.is_lt({MM}, {LQ}))')})", f"Nat.add({v32(LQ)}, U32.to_nat(1))")
    LQV = hyp("lq", v32(LQ), qv)
    em = calc(f"Nat.add({v32(MM)}, {D('32n', f'U.U32Nat.bit(U32.is_lt({MM}, {LQ}))')})",
              (f"Nat.add({v32(LQ)}, U32.to_nat(1))", AW),
              (f"Nat.add({qv}, U32.to_nat(1))", LQV),
              (f"Nat.add({qv}, 1n)", "="))
    put(f"""def km.rh1(+d: U32, +l: Nat, +h: {{U32.is_zero(d) == False{{}} : Bool}}) -> {{Nat.add(Nat.mul({qv}, {dv}), {r0}) == Nat.mul({cv}, {W}) : Nat}}:
  {h1.text}

def km.rh1b(+d: U32, +l: Nat, +h: {{U32.is_zero(d) == False{{}} : Bool}}) -> {btrue(f'Nat.is_lt({r0}, {dv})')}:
  %km.fv(d) : {btrue(f'Nat.is_lt({r0}, _)')}
  WL.mod_lt({NUM}, {FD}, h)

def km.rvm(+d: U32, +l: Nat, +q1: {btrue(f'Nat.is_lt(Nat.add({qv}, 1n), {W})')}) -> {{{v32(MM)} == Nat.add({qv}, 1n) : Nat}}:
  +lq = UL.dbl_nowrap(32n, {v32(f'W.W64.hi({Q})')}, {v32(LQ)}, {qv}, {qv}, km.np({Q}), UL.nat_le_refl({qv}), {qlt})
  UL.dbl_nowrap(32n, U.U32Nat.bit(U32.is_lt({MM}, {LQ})), {v32(MM)}, Nat.add({qv}, 1n), Nat.add({qv}, 1n), {em.text}, UL.nat_le_refl(Nat.add({qv}, 1n)), q1)
""")
    # a m = t w + s
    Aw, Bw = "W.W64.from_u32(a)", f"W.W64.from_u32({MM})"
    XM = f"W.W64.mul({Aw}, {Bw})"
    P0 = f"Nat.mul({v64(Aw)}, {v64(Bw)})"
    tv, sv = v32(f"W.W64.hi({XM})"), v32(f"W.W64.lo({XM})")
    hA = lt_rw(av, W, v64(Aw), W, f"Equal.sym(Nat, {v64(Aw)}, {av}, km.fv(a))", None, "km.lt32(a)")
    hB = lt_rw(v32(MM), W, v64(Bw), W, f"Equal.sym(Nat, {v64(Bw)}, {v32(MM)}, km.fv({MM}))", None, f"km.lt32({MM})")
    plt = f"km.mlt64(32n, 64n, {v64(Aw)}, {v64(Bw)}, {{==}}, {hA}, {hB})"
    xv = f"UL.dbl_nowrap(64n, U.U32Nat.high(64n, {P0}), {v64(XM)}, {P0}, {P0}, WL.mul_wrap({Aw}, {Bw}), UL.nat_le_refl({P0}), {plt})"
    h2 = calc(f"Nat.add({sv}, Nat.mul({tv}, {W}))",
              (f"Nat.add({sv}, {D('32n', f'Nat.mul({tv}, 1n)')})", hyp(f"UL.dbl_mul_r(32n, {tv}, 1n)", f"Nat.mul({tv}, {W})", D("32n", f"Nat.mul({tv}, 1n)"))),
              (f"Nat.add({sv}, {D('32n', tv)})", hyp(f"UL.nat_mul_one({tv})", f"Nat.mul({tv}, 1n)", tv)),
              (v64(XM), hyp(f"km.np({XM})", f"Nat.add({sv}, {D('32n', tv)})", v64(XM))),
              (P0, hyp(xv, v64(XM), P0)),
              (f"Nat.mul({av}, {v64(Bw)})", hyp("km.fv(a)", v64(Aw), av)),
              (f"Nat.mul({av}, {v32(MM)})", hyp(f"km.fv({MM})", v64(Bw), v32(MM))),
              (f"Nat.mul({av}, Nat.add({qv}, 1n))", hyp("vm", v32(MM), f"Nat.add({qv}, 1n)")))
    put(f"""def km.rh2(+a: U32, +d: U32, +l: Nat, +vm: {{{v32(MM)} == Nat.add({qv}, 1n) : Nat}}) -> {{Nat.add({sv}, Nat.mul({tv}, {W})) == Nat.mul({av}, Nat.add({qv}, 1n)) : Nat}}:
  {h2.text}
""")
    fin(put)
    # all together
    q, r = v32("U32.div(a, d)"), v32("U32.mod(a, d)")
    Xt = f"Nat.add({av}, {tv})"
    qD = f"Nat.mul({q}, {Dl})"
    rem = f"Nat.sub({Xt}, {qD})"
    # facts whose types hold 2^32 are passed on whole, never bound: a
    # binding's type is normalized, and 2^32 would be computed
    H1E = "km.rh1(d, l, h)"
    Q1E = f"km.k_q({W}, {dv}, {cv}, {qv}, {r0}, {H1E}, km.k_cd({dv}, {cv}, {Dl}, cd, p2), km.lt32(d))"
    H2E = "km.rh2(a, d, l, vm)"
    core = (f"km.k_core({W}, {Dl}, {av}, {dv}, {cv}, {qv}, {r0}, {sv}, {tv}, {q}, {r}, {H1E}, h1b, {H2E}, km.lt32(W.W64.lo({XM})), h3, h3b, km.lt32(a), cd, "
            f"Nat.is_le({qD}, {Xt}), {{==}}, Nat.is_lt({rem}, {Dl}), {{==}})")
    nzd = (f"Equal.trans(Bool, Nat.is_eq({dv}, 0n), U32.is_eq(d, 0), False{{}}, "
           f"Equal.sym(Bool, U32.is_eq(d, 0), Nat.is_eq({dv}, 0n), UL.u32_eq_value(d, 0)), h)")
    cargs = f"Nat.add({rem}, {qD}), {Xt}, {rem}, {Dl}"
    T = f"W.W64.hi({XM})"
    SHF = f"U32.shrn(U32.add({T}, U32.shrn(U32.sub(a, {T}), Nat.min(l, 1n))), Nat.sub(l, 1n))"
    put(f"""# the divide step, unfolded
def km.kd(+a: U32, +m: U32, +s1: Nat, +s2: Nat) -> {{R.krecip.divide(a, m, s1, s2) == U32.shrn(U32.add(W.W64.hi(W.W64.mul(W.W64.from_u32(a), W.W64.from_u32(m))), U32.shrn(U32.sub(a, W.W64.hi(W.W64.mul(W.W64.from_u32(a), W.W64.from_u32(m)))), s1)), s2) : U32}}:
  {{==}}
""")
    put(f"""def km.ry(+a: U32, +d: U32, +l: Nat, +el: {{{fls1} == l : Nat}}, +h: {{U32.is_zero(d) == False{{}} : Bool}}) -> {{R.krecip.divide(a, {MM}, Nat.min(l, 1n), Nat.sub(l, 1n)) == U32.div(a, d) : U32}}:
  +dv1 = km.nz({dv}, {nzd})
  +p1 = km.rd1(d, l, el, dv1)
  +p2 = km.rd2(d, l, el, dv1)
  +cd = km.rcd(d, l, p1, p2)
  +h1b = km.rh1b(d, l, h)
  +vm = km.rvm(d, l, {Q1E})
  +ta = km.k_ta({W}, {av}, {qv}, {sv}, {tv}, {H2E}, {Q1E})
  +h3 = UL.u32_divmod(a, d, h)
  +h3b = UL.u32_mod_lt(a, d, h)
  Equal.trans(U32, R.krecip.divide(a, {MM}, Nat.min(l, 1n), Nat.sub(l, 1n)), {SHF}, U32.div(a, d), km.kd(a, {MM}, Nat.min(l, 1n), Nat.sub(l, 1n)), km.fin(a, d, l, W.W64.hi({XM}), ta, h3, h3b, p1, dv1, km.c1({cargs}, {core}), km.c2({cargs}, {core})))

def Laws.recip_exact(a, d, h):
  km.ry(a, d, {fls1}, {{==}}, h)
""")


def fin(put):
    """the shifts, for any t <= a: l = 0 (d = 1) gives a; l = 1 + k gives
    (a + t) >> l, which is q by the core."""
    av, dv, tv = v32("a"), v32("d"), v32("t")
    q, r = v32("U32.div(a, d)"), v32("U32.mod(a, d)")
    Dl = D("l", "1n")
    Xt = f"Nat.add({av}, {tv})"
    qD = f"Nat.mul({q}, {Dl})"
    rem = f"Nat.sub({Xt}, {qD})"
    SUB = "U32.sub(a, t)"
    y = f"Nat.sub({av}, {tv})"
    SV = hyp("sv", v32(SUB), y)
    AT = hyp(f"UL.nat_le_witness({tv}, {av}, ta)", f"Nat.add({y}, {tv})", av)
    # l = 0
    b0 = calc(f"Nat.add(0n, Nat.add({tv}, {v32(SUB)}))",
              (f"Nat.add({tv}, {v32(SUB)})", "="),
              (f"Nat.add({tv}, {y})", SV),
              (f"Nat.add({y}, {tv})", "ring"),
              (av, AT))
    bound0 = le_from(f"Nat.add({tv}, {v32(SUB)})", av, "0n", b0)
    Z0 = f"U32.add(t, {SUB})"
    ONE = hyp("one", dv, "1n")
    e0 = calc(f"Nat.add(Nat.mul({q}, 1n), {r})", (f"Nat.add(Nat.mul({q}, {dv}), {r})", ONE), (av, hyp("h3", f"Nat.add(Nat.mul({q}, {dv}), {r})", av)),
              (f"Nat.add(Nat.mul({av}, 1n), 0n)", "ring"))
    rlt = lt_rw(r, dv, r, "1n", None, "one", "h3b")
    qa = hyp(f"UL.nat_div_unique(1n, {q}, {r}, {av}, 0n, {e0.text}, r1, {{==}})", q, av)
    v0 = calc(v32(Z0), (f"Nat.add({tv}, {v32(SUB)})", hyp(f"UL.u32_add_value(t, {SUB}, a, {bound0})", v32(Z0), f"Nat.add({tv}, {v32(SUB)})")),
              (f"Nat.add({tv}, {y})", SV), (f"Nat.add({y}, {tv})", "ring"), (av, AT), (q, sym(qa)))
    # l = 1 + k
    S1v = f"U32.shrn({SUB}, 1n)"
    Zs = f"U32.add(t, {S1v})"
    S1 = hyp(f"UL.u32_shrn_value({SUB}, 1n)", v32(S1v), f"U.U32Nat.high(1n, {v32(SUB)})")
    OH = hyp(f"UL.nat_odd_half({y})", f"Nat.add(U.U32Nat.odd({y}), Nat.double(U.U32Nat.half({y})))", y)
    w1 = f"Nat.add(U.U32Nat.odd({y}), U.U32Nat.half({y}))"
    b1 = calc(f"Nat.add({w1}, Nat.add({tv}, {v32(S1v)}))",
              (f"Nat.add({w1}, Nat.add({tv}, U.U32Nat.high(1n, {v32(SUB)})))", S1),
              (f"Nat.add({w1}, Nat.add({tv}, U.U32Nat.high(1n, {y})))", SV),
              (f"Nat.add({w1}, Nat.add({tv}, U.U32Nat.half({y})))", "="),
              (f"Nat.add(Nat.add(U.U32Nat.odd({y}), Nat.double(U.U32Nat.half({y}))), {tv})", "ring"),
              (f"Nat.add({y}, {tv})", OH),
              (av, AT))
    bound1 = le_from(f"Nat.add({tv}, {v32(S1v)})", av, w1, b1)
    D1k = D("1n+k", "1n")
    qD1 = f"Nat.mul({q}, {D1k})"
    rem1 = f"Nat.sub({Xt}, {qD1})"
    erq = calc(f"Nat.add({rem1}, {D('1n+k', q)})",
               (f"Nat.add({rem1}, {D('1n+k', f'Nat.mul({q}, 1n)')})", sym(hyp(f"UL.nat_mul_one({q})", f"Nat.mul({q}, 1n)", q))),
               (f"Nat.add({rem1}, {qD1})", sym(hyp(f"UL.dbl_mul_r(1n+k, {q}, 1n)", qD1, D("1n+k", f"Nat.mul({q}, 1n)")))),
               (Xt, hyp("rw", f"Nat.add({rem1}, {qD1})", Xt)))
    HU = hyp(f"UL.high_unique(1n+k, {Xt}, {rem1}, {q}, {erq.text}, ltq)", q, f"U.U32Nat.high(1n+k, {Xt})")
    v1 = calc(v32(f"U32.shrn({Zs}, k)"),
              (f"U.U32Nat.high(k, {v32(Zs)})", hyp(f"UL.u32_shrn_value({Zs}, k)", v32(f"U32.shrn({Zs}, k)"), f"U.U32Nat.high(k, {v32(Zs)})")),
              (f"U.U32Nat.high(k, Nat.add({tv}, {v32(S1v)}))", hyp(f"UL.u32_add_value(t, {S1v}, a, {bound1})", v32(Zs), f"Nat.add({tv}, {v32(S1v)})")),
              (f"U.U32Nat.high(k, Nat.add({tv}, U.U32Nat.high(1n, {v32(SUB)})))", S1),
              (f"U.U32Nat.high(k, Nat.add({tv}, U.U32Nat.high(1n, {y})))", SV),
              (f"U.U32Nat.high(k, Nat.add({tv}, U.U32Nat.half({y})))", "="),
              (f"U.U32Nat.high(1n+k, {Xt})", hyp(f"km.shk(k, {av}, {tv}, ta)", f"U.U32Nat.high(k, Nat.add({tv}, U.U32Nat.half({y})))", f"U.U32Nat.high(1n+k, {Xt})")),
              (q, sym(HU)))
    goal1 = f"{{U32.shrn(U32.add(t, U32.shrn({SUB}, _)), Nat.sub(1n+k, 1n)) == U32.div(a, d) : U32}}"
    put(f"""def km.fin(+a: U32, +d: U32, +l: Nat, +t: U32, +ta: {btrue(f'Nat.is_le({tv}, {av})')}, h3: {{Nat.add(Nat.mul({q}, {dv}), {r}) == {av} : Nat}}, h3b: {btrue(f'Nat.is_lt({r}, {dv})')}, p1: {btrue(f'Nat.is_le({dv}, {Dl})')}, dv1: {btrue(f'Nat.is_lt(0n, {dv})')}, rw: {{Nat.add({rem}, {qD}) == {Xt} : Nat}}, ltq: {btrue(f'Nat.is_lt({rem}, {Dl})')}) -> {{U32.shrn(U32.add(t, U32.shrn({SUB}, Nat.min(l, 1n))), Nat.sub(l, 1n)) == U32.div(a, d) : U32}}:
  match l:
    case 0n:
      +sv = UL.u32_sub_value(a, t, ta)
      +one = km.one({dv}, p1, dv1)
      +r1 = {rlt}
      UL.u32_value_eq({Z0}, U32.div(a, d), {v0.text})
    case 1n+ +k:
      %Equal.sym(Nat, Nat.min(1n+k, 1n), 1n, km.mn(k)) : {goal1}
      %Equal.sym(Nat, Nat.sub(k, 0n), k, km.sub0(k)) : {{U32.shrn({Zs}, _) == U32.div(a, d) : U32}}
      +sv = UL.u32_sub_value(a, t, ta)
      UL.u32_value_eq(U32.shrn({Zs}, k), U32.div(a, d), {v1.text})
""")


def recip(put):
    klemmas(put)
    glue(put)
