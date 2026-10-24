"""The proofs of kmath's 64-bit division laws (div64.bend), for
gen/proof.py: KMath.div_u64_rem and the rest are word64's W64.divmod with
the parts taken apart, so word64's laws (divmod_value, mod_lt, add_value)
give the Nat facts, and the ring identities between them are written by
scripts/natproof.py.
"""
import natproof as N
from natproof import btrue, calc, hyp, le_from, lt_from


def v32(x):
    return f"U32.to_nat({x})"


def v64(x):
    return f"W.W64.to_nat({x})"


def helpers(put):
    N.bend_order(put, "km")
    N.bend_words(put, "km")
    put("""# The parts of a quotient pair and of a KDiv64

def km.fst(p: W.W64 & W.W64) -> {W.W64.fst(p) == Laws.kmlaw.fst(p) : W.W64}:
  (q, r) = p
  {==}

def km.snd(p: W.W64 & W.W64) -> {W.W64.snd(p) == Laws.kmlaw.snd(p) : W.W64}:
  (q, r) = p
  {==}

def km.oq(p: W.W64 & W.W64) -> {W.W64.fst(p) == Laws.kmlaw.q(D.kdiv64.of(p)) : W.W64}:
  (q, r) = p
  {==}

def km.or(p: W.W64 & W.W64) -> {W.W64.lo(W.W64.snd(p)) == Laws.kmlaw.r(D.kdiv64.of(p)) : U32}:
  (q, r) = p
  {==}

def km.up(p: W.W64 & W.W64) -> {W.W64.add(W.W64.fst(p), W.W64.from_u32(D.kdiv64.bit(W.W64.is_zero(W.W64.snd(p))))) == D.kdiv64.up(p) : W.W64}:
  (q, r) = p
  {==}

def km.mlt(+n: W.W64, +d: U32, h: {U32.is_zero(d) == False{} : Bool}) -> {Nat.is_lt(W.W64.to_nat(W.W64.mod(n, W.W64.from_u32(d))), U32.to_nat(d)) == True{} : Bool}:
  %km.fv(d) : {Nat.is_lt(W.W64.to_nat(W.W64.mod(n, W.W64.from_u32(d))), _) == True{} : Bool}
  WL.mod_lt(n, W.W64.from_u32(d), h)
""")


def division(put):
    put("# 64-bit division: the parts of word64's W64.divmod\n")
    DMd = "W.W64.divmod(n, W.W64.from_u32(d))"
    Rq = "Laws.kmlaw.r(D.KMath.div_u64_rem(n, d))"
    put(f"""def Laws.div_u64_rem_value(n, d, h):
  +hh = h
  %km.oq({DMd}) : {{Nat.add(Nat.mul(W.W64.to_nat(_), U32.to_nat(d)), U32.to_nat({Rq})) == W.W64.to_nat(n) : Nat}}
  %km.or({DMd}) : {{Nat.add(Nat.mul(W.W64.to_nat(W.W64.fst({DMd})), U32.to_nat(d)), U32.to_nat(_)) == W.W64.to_nat(n) : Nat}}
  %km.lo_small(W.W64.snd({DMd}), d, km.mlt(n, d, hh)) : {{Nat.add(Nat.mul(W.W64.to_nat(W.W64.fst({DMd})), U32.to_nat(d)), _) == W.W64.to_nat(n) : Nat}}
  %km.fv(d) : {{Nat.add(Nat.mul(W.W64.to_nat(W.W64.fst({DMd})), _), W.W64.to_nat(W.W64.snd({DMd}))) == W.W64.to_nat(n) : Nat}}
  WL.divmod_value(n, W.W64.from_u32(d), hh)

def Laws.div_u64_rem_lt(n, d, h):
  +lt = km.mlt(n, d, h)
  %km.or({DMd}) : {{Nat.is_lt(U32.to_nat(_), U32.to_nat(d)) == True{{}} : Bool}}
  %km.lo_small(W.W64.snd({DMd}), d, lt) : {{Nat.is_lt(_, U32.to_nat(d)) == True{{}} : Bool}}
  lt

def Laws.div_u64_q(n, d):
  km.oq({DMd})

def Laws.div_u64_rem_zero(n):
  {{==}}
""")
    DM = "W.W64.divmod(n, d)"
    put(f"""def Laws.div64_u64_rem_value(n, d, h):
  %km.fst({DM}) : {{Nat.add(Nat.mul(W.W64.to_nat(_), W.W64.to_nat(d)), W.W64.to_nat(Laws.kmlaw.snd({DM}))) == W.W64.to_nat(n) : Nat}}
  %km.snd({DM}) : {{Nat.add(Nat.mul(W.W64.to_nat(W.W64.fst({DM})), W.W64.to_nat(d)), W.W64.to_nat(_)) == W.W64.to_nat(n) : Nat}}
  WL.divmod_value(n, d, h)

def Laws.div64_u64_rem_lt(n, d, h):
  %km.snd({DM}) : {{Nat.is_lt(W.W64.to_nat(_), W.W64.to_nat(d)) == True{{}} : Bool}}
  WL.mod_lt(n, d, h)

def Laws.div64_u64_q(n, d):
  km.fst({DM})

def Laws.div64_u64_rem_zero(n):
  {{==}}
""")
    round_up(put)


def round_up(put):
    """n / d rounded up: q + [r != 0], with q d + r = n and r < d."""
    q, r, dd, nn = v64("W.W64.div(n, d)"), v64("W.W64.mod(n, d)"), v64("d"), v64("n")
    UP = {b: f"W.W64.add(W.W64.div(n, d), W.W64.from_u32(D.kdiv64.bit({b})))" for b in ("True{}", "False{}", "z")}
    one = {"True{}": "0n", "False{}": "1n"}
    E = hyp("e", f"Nat.add(Nat.mul({q}, {dd}), {r})", nn)
    dw = f"Nat.sub({dd}, 1n)"
    DW = hyp("dw", f"Nat.add({dw}, 1n)", dd)
    LW = hyp("lw", f"Nat.add(Nat.sub({dd}, 1n+{r}), 1n+{r})", dd)
    rl = f"Nat.sub({dd}, 1n+{r})"
    goal = (btrue(f"Nat.is_le({nn}, Nat.mul({v64(UP['z'])}, {dd}))") + " & " +
            btrue(f"Nat.is_lt(Nat.mul({v64(UP['z'])}, {dd}), Nat.add({nn}, {dd}))"))
    bodies = {}
    for b in ("True{}", "False{}"):
        o = one[b]
        V = v64(UP[b])
        ob = v64(f"W.W64.from_u32(D.kdiv64.bit({b}))")
        if b == "True{}":
            R = hyp("r0", r, "0n")
            # q + 0 <= n: (q dw) + (q + 0) = q d = q d + 0 = n
            bound = calc(f"Nat.add(Nat.mul({q}, {dw}), Nat.add({q}, {ob}))",
                         (f"Nat.add(Nat.mul({q}, {dw}), Nat.add({q}, 0n))", "="),
                         (f"Nat.mul({q}, Nat.add({dw}, 1n))", "ring"),
                         (f"Nat.mul({q}, {dd})", DW),
                         (f"Nat.add(Nat.mul({q}, {dd}), 0n)", "ring"),
                         (f"Nat.add(Nat.mul({q}, {dd}), {r})", R),
                         (nn, E))
            hb = le_from(f"Nat.add({q}, {ob})", nn, f"Nat.mul({q}, {dw})", bound)
            VAL = hyp(f"WL.add_value(W.W64.div(n, d), W.W64.from_u32(D.kdiv64.bit({b})), n, {hb})", V, f"Nat.add({q}, {ob})")
            le = calc(f"Nat.add(0n, {nn})",
                      (nn, "="),
                      (f"Nat.add(Nat.mul({q}, {dd}), {r})", E),
                      (f"Nat.add(Nat.mul({q}, {dd}), 0n)", R),
                      (f"Nat.mul(Nat.add({q}, 0n), {dd})", "ring"),
                      (f"Nat.mul(Nat.add({q}, {ob}), {dd})", "="),
                      (f"Nat.mul({V}, {dd})", VAL))
            lt = calc(f"Nat.add({dw}, 1n+Nat.mul({V}, {dd}))",
                      (f"Nat.add({dw}, 1n+Nat.mul(Nat.add({q}, {ob}), {dd}))", VAL),
                      (f"Nat.add({dw}, 1n+Nat.mul(Nat.add({q}, 0n), {dd}))", "="),
                      (f"Nat.add(Nat.add(Nat.mul({q}, {dd}), 0n), Nat.add({dw}, 1n))", "ring"),
                      (f"Nat.add(Nat.add(Nat.mul({q}, {dd}), {r}), Nat.add({dw}, 1n))", R),
                      (f"Nat.add({nn}, Nat.add({dw}, 1n))", E),
                      (f"Nat.add({nn}, {dd})", DW))
            pre = (f"  +r0 = km.wz(W.W64.mod(n, d), ez)\n")
            wle, wlt = "0n", dw
        else:
            rw = f"Nat.sub({r}, 1n)"
            RW = hyp("rw", f"Nat.add({rw}, 1n)", r)
            # q + 1 <= n: (q dw + rw) + (q + 1) = q (dw + 1) + (rw + 1) = q d + r = n
            bound = calc(f"Nat.add(Nat.add(Nat.mul({q}, {dw}), {rw}), Nat.add({q}, {ob}))",
                         (f"Nat.add(Nat.add(Nat.mul({q}, {dw}), {rw}), Nat.add({q}, 1n))", "="),
                         (f"Nat.add(Nat.mul({q}, Nat.add({dw}, 1n)), Nat.add({rw}, 1n))", "ring"),
                         (f"Nat.add(Nat.mul({q}, {dd}), Nat.add({rw}, 1n))", DW),
                         (f"Nat.add(Nat.mul({q}, {dd}), {r})", RW),
                         (nn, E))
            hb = le_from(f"Nat.add({q}, {ob})", nn, f"Nat.add(Nat.mul({q}, {dw}), {rw})", bound)
            VAL = hyp(f"WL.add_value(W.W64.div(n, d), W.W64.from_u32(D.kdiv64.bit({b})), n, {hb})", V, f"Nat.add({q}, {ob})")
            # n <= (q + 1) d: (1 + rl) + n = q d + (rl + 1 + r) = q d + d
            le = calc(f"Nat.add(1n+{rl}, {nn})",
                      (f"Nat.add(1n+{rl}, Nat.add(Nat.mul({q}, {dd}), {r}))", E),
                      (f"Nat.add(Nat.mul({q}, {dd}), Nat.add({rl}, 1n+{r}))", "ring"),
                      (f"Nat.add(Nat.mul({q}, {dd}), {dd})", LW),
                      (f"Nat.mul(Nat.add({q}, 1n), {dd})", "ring"),
                      (f"Nat.mul(Nat.add({q}, {ob}), {dd})", "="),
                      (f"Nat.mul({V}, {dd})", VAL))
            # (q + 1) d < n + d: rw + 1 + (q + 1) d = q d + (rw + 1) + d = n + d
            lt = calc(f"Nat.add({rw}, 1n+Nat.mul({V}, {dd}))",
                      (f"Nat.add({rw}, 1n+Nat.mul(Nat.add({q}, {ob}), {dd}))", VAL),
                      (f"Nat.add({rw}, 1n+Nat.mul(Nat.add({q}, 1n), {dd}))", "="),
                      (f"Nat.add(Nat.add(Nat.mul({q}, {dd}), Nat.add({rw}, 1n)), {dd})", "ring"),
                      (f"Nat.add(Nat.add(Nat.mul({q}, {dd}), {r}), {dd})", RW),
                      (f"Nat.add({nn}, {dd})", E))
            pre = (f"  +rw = UL.nat_lt_witness(0n, {r}, km.wnz(W.W64.mod(n, d), ez))\n"
                   f"  +lw = UL.nat_lt_witness({r}, {dd}, WL.mod_lt(n, d, h))\n")
            wle, wlt = f"1n+{rl}", rw
        ple = le_from(nn, f"Nat.mul({V}, {dd})", wle, le)
        plt = lt_from(f"Nat.mul({V}, {dd})", f"Nat.add({nn}, {dd})", wlt, lt)
        common = (f"  +e = WL.divmod_value(n, d, h)\n"
                  f"  +dw = UL.nat_lt_witness(0n, {dd}, km.wnz(d, h))\n")
        bodies[b] = common + pre + f"  ({ple}, {plt})"
    put(f"""# n / d rounded up: q + 1 when the remainder is not 0, and then q + 1 <= n
def km.ru(+n: W.W64, +d: W.W64, +h: {{W.W64.is_zero(d) == False{{}} : Bool}}, z: Bool, ez: {{W.W64.is_zero(W.W64.mod(n, d)) == z : Bool}}) -> {goal}:
  match z:
    case True{{}}:
{_indent(bodies['True{}'])}
    case False{{}}:
{_indent(bodies['False{}'])}

def km.ru1(-a: Nat, -b: Nat, -c: Nat, -x: Nat, pr: {btrue('Nat.is_le(a, b)')} & {btrue('Nat.is_lt(c, x)')}) -> {btrue('Nat.is_le(a, b)')}:
  (+u, +v) = pr
  u

def km.ru2(-a: Nat, -b: Nat, -c: Nat, -x: Nat, pr: {btrue('Nat.is_le(a, b)')} & {btrue('Nat.is_lt(c, x)')}) -> {btrue('Nat.is_lt(c, x)')}:
  (+u, +v) = pr
  v
""")
    DM = "W.W64.divmod(n, d)"
    V = v64(UP["z"].replace("D.kdiv64.bit(z)", f"D.kdiv64.bit(W.W64.is_zero(W.W64.mod(n, d)))"))
    args = f"{nn}, Nat.mul({V}, {dd}), Nat.mul({V}, {dd}), Nat.add({nn}, {dd})"
    put(f"""def Laws.div64_round_up_le(n, d, h):
  %km.up({DM}) : {btrue(f'Nat.is_le({nn}, Nat.mul(W.W64.to_nat(_), {dd}))')}
  km.ru1({args}, km.ru(n, d, h, W.W64.is_zero(W.W64.mod(n, d)), {{==}}))

def Laws.div64_round_up_lt(n, d, h):
  %km.up({DM}) : {btrue(f'Nat.is_lt(Nat.mul(W.W64.to_nat(_), {dd}), Nat.add({nn}, {dd}))')}
  km.ru2({args}, km.ru(n, d, h, W.W64.is_zero(W.W64.mod(n, d)), {{==}}))
""")


def _indent(s):
    return "\n".join("    " + ln for ln in s.split("\n"))
