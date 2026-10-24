"""The proofs of kmath's laws on the number of bits (KMath.fls) and on
reciprocal division (KRecip, Granlund and Montgomery's Theorem 4.2), for
gen/proof.py. Ring identities are written by scripts/natproof.py.
"""
from natproof import absurd, bcong, btrans, btrue, calc, hyp, le_from, lt_from, lt_rw, sym, wit_le, wit_lt

GO = "R.krecip.bits.go"
STEP = "R.krecip.bits.step"


def v32(x):
    return f"U32.to_nat({x})"


def D(k, x):
    return f"U.U32Nat.dbl({k}, {x})"


def fls(put):
    put("# The number of bits: KMath.fls(x) is krecip.bits.go(32n, x, 0n), which adds 1\n"
        "# to acc and halves x while x is not 0\n")
    x, sx = v32("x"), v32("U32.shr(x)")
    # x is 0 (U32.is_eq(x, 0) == True): its value is 0, and so is its half's
    x0 = (f"km.z0({x}, Equal.trans(Bool, Nat.is_eq({x}, 0n), U32.is_eq(x, 0), True{{}}, "
          f"Equal.sym(Bool, U32.is_eq(x, 0), Nat.is_eq({x}, 0n), UL.u32_eq_value(x, 0)), ez))")
    E = (f"Equal.trans(Nat, {sx}, U.U32Nat.half({x}), {x}, UL.u32_shr_value(x), "
         f"Equal.trans(Nat, U.U32Nat.half({x}), U.U32Nat.half(0n), {x}, Equal.cong(Nat, Nat, zz => U.U32Nat.half(zz), {x}, 0n, x0), Equal.sym(Nat, {x}, 0n, x0)))")
    nzx = (f"Equal.trans(Bool, Nat.is_eq({x}, 0n), U32.is_eq(x, 0), False{{}}, "
           f"Equal.sym(Bool, U32.is_eq(x, 0), Nat.is_eq({x}, 0n), UL.u32_eq_value(x, 0)), ez)")
    # the bound on the half: x < 2^(1+k) gives x / 2 < 2^k
    hx1 = lt_rw(f"U.U32Nat.high(1n, {x})", D("k", "1n"), sx, D("k", "1n"),
                f"Equal.sym(Nat, {sx}, U.U32Nat.half({x}), UL.u32_shr_value(x))", None,
                f"UL.high_lt(1n, k, 1n+k, {x}, {{==}}, hx)")

    # fls(x) <= 32
    put(f"""def km.fbt(+k: Nat, +acc: Nat, z: Bool, +g: Nat, ih: {btrue(f'Nat.is_le(g, Nat.add(k, {STEP}(z, acc)))')}) -> {btrue('Nat.is_le(g, 1n+Nat.add(k, acc))')}:
  match z:
    case True{{}}:
      km.le_succ(g, Nat.add(k, acc), ih)
    case False{{}}:
      %UL.nat_add_succ(k, acc) : {btrue('Nat.is_le(g, _)')}
      ih

def km.fb(n: Nat, +x: U32, +acc: Nat) -> {btrue(f'Nat.is_le({GO}(n, x, acc), Nat.add(n, acc))')}:
  match n:
    case 0n:
      UL.nat_le_refl(acc)
    case 1n+ +k:
      km.fbt(k, acc, U32.is_eq(x, 0), {GO}(k, U32.shr(x), {STEP}(U32.is_eq(x, 0), acc)), km.fb(k, U32.shr(x), {STEP}(U32.is_eq(x, 0), acc)))

def Laws.fls_bound(x):
  km.fb(32n, x, 0n)
""")

    # x < 2^fls(x): 2^acc (1 + x) <= 2^go(n, x, acc)
    hv = sx
    w = f"Nat.sub(1n, U.U32Nat.odd({x}))"
    OH = hyp(f"UL.nat_odd_half({x})", f"Nat.add(U.U32Nat.odd({x}), Nat.double(U.U32Nat.half({x})))", x)
    OW = hyp(f"UL.nat_le_witness(U.U32Nat.odd({x}), 1n, UL.nat_odd_le({x}))", f"Nat.add({w}, U.U32Nat.odd({x}))", "1n")
    HV = hyp(f"UL.u32_shr_value(x)", hv, f"U.U32Nat.half({x})")
    pf = calc(f"Nat.add({w}, 1n+{x})",
              (f"Nat.add({w}, 1n+Nat.add(U.U32Nat.odd({x}), Nat.double(U.U32Nat.half({x}))))", OH),
              (f"Nat.add(Nat.add({w}, U.U32Nat.odd({x})), 1n+Nat.double(U.U32Nat.half({x})))", "ring"),
              (f"Nat.add(1n, 1n+Nat.double(U.U32Nat.half({x})))", OW),
              (f"Nat.add(1n, 1n+Nat.double({hv}))", HV),
              (f"Nat.double(1n+{hv})", "ring"))
    le1 = le_from(f"1n+{x}", f"Nat.double(1n+{hv})", w, pf)
    A, B, C = D("acc", f"1n+{x}"), D("1n+acc", f"1n+{hv}"), D("acc", f"Nat.double(1n+{hv})")
    X = (f"Equal.trans(Bool, Nat.is_le({A}, {B}), Nat.is_le({A}, {C}), Nat.is_le(1n+{x}, Nat.double(1n+{hv})), "
         f"{bcong('zz', f'Nat.is_le({A}, zz)', B, C, f'UL.dbl_comm(1n, acc, 1n+{hv})')}, UL.dbl_le(acc, 1n+{x}, Nat.double(1n+{hv})))")
    M = btrans(f"Nat.is_le({A}, {B})", f"Nat.is_le(1n+{x}, Nat.double(1n+{hv}))", "True{}", X, le1)
    put(f"""def km.flt(+acc: Nat, +x: U32, z: Bool, ez: {{U32.is_eq(x, 0) == z : Bool}}, +g: Nat, ih: {btrue(f'Nat.is_le({D(f"{STEP}(z, acc)", f"1n+{sx}")}, g)')}) -> {btrue(f'Nat.is_le({D("acc", f"1n+{x}")}, g)')}:
  match z:
    case True{{}}:
      +x0 = {x0}
      %{E} : {btrue(f'Nat.is_le({D("acc", "1n+_")}, g)')}
      ih
    case False{{}}:
      km.le_trans({A}, {B}, g, {M}, ih)

def km.fl(n: Nat, +x: U32, +acc: Nat, hx: {btrue(f'Nat.is_lt({x}, {D("n", "1n")})')}) -> {btrue(f'Nat.is_le({D("acc", f"1n+{x}")}, {D(f"{GO}(n, x, acc)", "1n")})')}:
  match n:
    case 0n:
      %Equal.sym(Nat, {x}, 0n, km.lt1({x}, hx)) : {btrue(f'Nat.is_le({D("acc", "1n+_")}, {D("acc", "1n")})')}
      UL.nat_le_refl({D("acc", "1n")})
    case 1n+ +k:
      km.flt(acc, x, U32.is_eq(x, 0), {{==}}, {D(f"{GO}(k, U32.shr(x), {STEP}(U32.is_eq(x, 0), acc))", "1n")}, km.fl(k, U32.shr(x), {STEP}(U32.is_eq(x, 0), acc), {hx1}))

def Laws.fls_lt(x):
  km.le_lt({x}, {D("R.KMath.fls(x)", "1n")}, km.fl(32n, x, 0n, km.lt32(x)))
""")

    # 2^fls(x) <= 2 x for x not 0: 2^go(n, x, acc) <= 2^acc F(x), F(y) = 2 y + [y = 0]
    def F(y):
        return f"Nat.add(Nat.double({y}), U.U32Nat.bit(Nat.is_eq({y}, 0n)))"
    v, h = "v", "hv"
    vw = f"Nat.sub({v}, 1n)"
    VW = hyp("vw", f"Nat.add({vw}, 1n)", v)
    H0 = hyp("h0", h, "0n")
    p_t = calc(f"Nat.add(Nat.double({vw}), Nat.double(Nat.add(Nat.double({h}), 1n)))",
               (f"Nat.add(Nat.double({vw}), Nat.double(Nat.add(Nat.double(0n), 1n)))", H0),
               (f"Nat.add(Nat.double(Nat.add({vw}, 1n)), 0n)", "ring"),
               (f"Nat.add(Nat.double({v}), 0n)", VW))
    le_t = le_from(f"Nat.double(Nat.add(Nat.double({h}), 1n))", f"Nat.add(Nat.double({v}), 0n)", f"Nat.double({vw})", p_t)
    OH2 = hyp(f"UL.nat_odd_half({v})", f"Nat.add(U.U32Nat.odd({v}), Nat.double(U.U32Nat.half({v})))", v)
    HX = hyp("hvx", h, f"U.U32Nat.half({v})")
    p_f = calc(f"Nat.add(Nat.double(U.U32Nat.odd({v})), Nat.double(Nat.add(Nat.double({h}), 0n)))",
               (f"Nat.add(Nat.double(Nat.add(U.U32Nat.odd({v}), Nat.double({h}))), 0n)", "ring"),
               (f"Nat.add(Nat.double(Nat.add(U.U32Nat.odd({v}), Nat.double(U.U32Nat.half({v})))), 0n)", HX),
               (f"Nat.add(Nat.double({v}), 0n)", OH2))
    le_f = le_from(f"Nat.double(Nat.add(Nat.double({h}), 0n))", f"Nat.add(Nat.double({v}), 0n)", f"Nat.double(U.U32Nat.odd({v}))", p_f)
    put(f"""def km.fe2(+v: Nat, +hv: Nat, z: Bool, ez: {{Nat.is_eq(hv, 0n) == z : Bool}}, +hvx: {{hv == U.U32Nat.half(v) : Nat}}, nz: {{Nat.is_eq(v, 0n) == False{{}} : Bool}}) -> {btrue(f'Nat.is_le(Nat.double(Nat.add(Nat.double(hv), U.U32Nat.bit(z))), Nat.add(Nat.double(v), 0n))')}:
  match z:
    case True{{}}:
      +h0 = km.z0(hv, ez)
      +vw = UL.nat_lt_witness(0n, v, km.nz(v, nz))
      {le_t}
    case False{{}}:
      {le_f}
""")
    Fh, Fx = F(sx), F(x)
    A2 = D("1n+acc", Fh)
    C2 = D("acc", f"Nat.add(Nat.double({x}), 0n)")
    X2 = (f"Equal.trans(Bool, Nat.is_le({A2}, {C2}), Nat.is_le({D('acc', f'Nat.double({Fh})')}, {C2}), Nat.is_le(Nat.double({Fh}), Nat.add(Nat.double({x}), 0n)), "
          f"{bcong('zz', f'Nat.is_le(zz, {C2})', A2, D('acc', f'Nat.double({Fh})'), f'UL.dbl_comm(1n, acc, {Fh})')}, UL.dbl_le(acc, Nat.double({Fh}), Nat.add(Nat.double({x}), 0n)))")
    A3 = f"km.fe2({x}, {sx}, Nat.is_eq({sx}, 0n), {{==}}, UL.u32_shr_value(x), nz)"
    M2 = btrans(f"Nat.is_le({A2}, {C2})", f"Nat.is_le(Nat.double({Fh}), Nat.add(Nat.double({x}), 0n))", "True{}", X2, A3)
    put(f"""def km.fet(+acc: Nat, +x: U32, z: Bool, ez: {{U32.is_eq(x, 0) == z : Bool}}, +g: Nat, ih: {btrue(f'Nat.is_le(g, {D(f"{STEP}(z, acc)", Fh)})')}) -> {btrue(f'Nat.is_le(g, {D("acc", Fx)})')}:
  match z:
    case True{{}}:
      +x0 = {x0}
      %{E} : {btrue(f'Nat.is_le(g, {D("acc", F("_"))})')}
      ih
    case False{{}}:
      +nz = {nzx}
      %Equal.sym(Bool, Nat.is_eq({x}, 0n), False{{}}, nz) : {btrue(f'Nat.is_le(g, {D("acc", f"Nat.add(Nat.double({x}), U.U32Nat.bit(_))")})')}
      km.le_trans(g, {A2}, {C2}, ih, {M2})

def km.fe(n: Nat, +x: U32, +acc: Nat, hx: {btrue(f'Nat.is_lt({x}, {D("n", "1n")})')}) -> {btrue(f'Nat.is_le({D(f"{GO}(n, x, acc)", "1n")}, {D("acc", Fx)})')}:
  match n:
    case 0n:
      %Equal.sym(Nat, {x}, 0n, km.lt1({x}, hx)) : {btrue(f'Nat.is_le({D("acc", "1n")}, {D("acc", F("_"))})')}
      UL.nat_le_refl({D("acc", "1n")})
    case 1n+ +k:
      km.fet(acc, x, U32.is_eq(x, 0), {{==}}, {D(f"{GO}(k, U32.shr(x), {STEP}(U32.is_eq(x, 0), acc))", "1n")}, km.fe(k, U32.shr(x), {STEP}(U32.is_eq(x, 0), acc), {hx1}))

def Laws.fls_le(x, h):
  %UL.nat_add_zero(Nat.double({x})) : {btrue(f'Nat.is_le({D("R.KMath.fls(x)", "1n")}, _)')}
  %Equal.trans(Bool, Nat.is_eq({x}, 0n), U32.is_eq(x, 0), False{{}}, Equal.sym(Bool, U32.is_eq(x, 0), Nat.is_eq({x}, 0n), UL.u32_eq_value(x, 0)), h) : {btrue(f'Nat.is_le({D("R.KMath.fls(x)", "1n")}, Nat.add(Nat.double({x}), U.U32Nat.bit(_)))')}
  km.fe(32n, x, 0n, km.lt32(x))
""")
