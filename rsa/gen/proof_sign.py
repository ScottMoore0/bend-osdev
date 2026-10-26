#!/usr/bin/env python3
"""Writes rsa/PROOF_sign.bend and rsa/PROOF_pss.bend: the proofs of the
octet-string primitives' laws and of the signature schemes' sign-then-verify
laws (LAWS_sign.bend, LAWS_pss.bend).

  python3 gen/proof_sign.py

An accepted key is the RsaPrivate of its integers (PROOF_prim.bend's kp.ksk),
so each law is proved on that RsaPrivate, with qInv t. Where
Rsa.dp_octets(sk, o) gives s, its checks passed (kq.i0, kq.i1: o has k bytes,
OS2IP(o) < n) and s is I2OSP of the CRT result x to k bytes (kq.i2); then s
has k bytes and OS2IP(s) has x's value (bignum's to_octets_len,
to_octets_value), which is c^d mod n (PROOF_prim.bend's kp.crtv with bignum's
crt_exp_nat), below n; RSAEP of it has the value c (rsa_nat_rev), and I2OSP
of it to k bytes is o (bignum's to_octets_of_value). The other direction is
the same with rsa_nat. RSASSA-PKCS1-v1_5 verification re-encodes and
compares (kq.pk2); RSASSA-PSS's verification takes I2OSP of RSAVP1's value
to emLen bytes, which is EM again (EM has emLen bytes, kz.len), and checks
it (LAWS.bend's pss_round_trip). The Nat chains come from
scripts/natproof.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "scripts"))
sys.path.insert(0, HERE)
import natproof as NP  # noqa: E402
from natproof import btrue, calc, hyp, sym  # noqa: E402
import proof_prim as PP  # noqa: E402

NP.CFG["law"] = "UL."
NP.OUT.prefix = "kq.r"

EQ, V, VT, MOD, POW, MUL, ADD = PP.EQ, PP.V, PP.VT, PP.MOD, PP.POW, PP.MUL, PP.ADD
H = hyp
RO = "Result<&2, &2, R.RsaError, B.Octets>"
RB = "Result<&2, &2, R.RsaError, Bool>"
MO = "Maybe<&2, B.Octets>"
DP, DQ, QI, OKP, OK, A1, A23, A4, A5 = PP.DP, PP.DQ, PP.QI, PP.OKP, PP.OK, PP.A1, PP.A23, PP.A4, PP.A5
XK = PP.XK
X = XK("t")
P_, Q_, Nn, E_, D_, T_ = V("p"), V("q"), V("n"), V("e"), V("d"), V("t")
PQ = MUL(P_, Q_)
BL_ = "N.BnNat.byte_len(n)"


def OF(o):
    return f"N.BnNat.of_octets({o})"


def CRT(c):
    return f"R.rsa.crt_exp({c}, p, q, {DP}, {DQ}, t)"


PRE = (f"+n: N.BnNat, +e: N.BnNat, +d: N.BnNat, +p: N.BnNat, +q: N.BnNat, +t: N.BnNat, "
       f"+hb1: {btrue(OKP)}, +hb2: {btrue(OK)}, +hmi: {EQ('Md.BnMod.inv(q, p)', 'Some{t}', 'Maybe<&2, N.BnNat>')}, "
       f"+hn: {VT('n')}, +he: {VT('e')}, +hd: {VT('d')}, +hp: {VT('p')}, +hq: {VT('q')}, "
       f"+pp: {btrue(f'LF.bnlaw.prime({P_})')}, +pq: {btrue(f'LF.bnlaw.prime({Q_})')}")
PREA = "n, e, d, p, q, t, hb1, hb2, hmi, hn, he, hd, hp, hq, pp, pq"

FACTS0 = f"""  +vn = KP.kp.fn(n, e, d, p, q, hn, hp, hq, hb2)
  +hodd = KP.kp.fodd(n, e, p, q, hn, vn, hb1)
  +hdp = KP.kp.fdp(e, d, p, he, hd, hp, KP.kp.and1({A4}, {A5}, KP.kp.and2(Bool.and({A1}, {A23}), Bool.and({A4}, {A5}), hb2)))
  +hdq = KP.kp.fdq(e, d, q, he, hd, hq, KP.kp.and2({A4}, {A5}, KP.kp.and2(Bool.and({A1}, {A23}), Bool.and({A4}, {A5}), hb2)))
  +ht = LI.inv_value(q, p, t, hq, hp, hmi)
  +vt = LI.inv_valid(q, p, t, hq, hp, hmi)
  +hpq = LR.mod_inv_ne({P_}, {Q_}, {T_}, ht)
  +hp0 = KP.kp.p0({P_}, pp)
  +hq0 = KP.kp.p0({Q_}, pq)"""


def facts_c(c, hc, hlt):
    """the facts on a representative c below n (valid by hc, below n by hlt)"""
    C = V(c)
    return f"""  +cl = KP.kp.blt({c}, n, {hc}, hn, {hlt})
  +n0 = KP.kp.ltpos({C}, {Nn}, cl)
  +pq0 = Equal.trans(Bool, Nat.is_lt(0n, {PQ}), Nat.is_lt(0n, {Nn}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt(0n, zz), {PQ}, {Nn}, Equal.sym(Nat, {Nn}, {PQ}, vn)), n0)
  +clq = Equal.trans(Bool, Nat.is_lt({C}, {PQ}), Nat.is_lt({C}, {Nn}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_lt({C}, zz), {PQ}, {Nn}, Equal.sym(Nat, {Nn}, {PQ}, vn)), cl)"""


def crtval(c, hc):
    """VAL(crt_exp(c)) == mod(pow(VAL c, D), PQ)"""
    tgt = PP_TARGET.replace(V("c"), V(c))
    return (f"Equal.trans(Nat, {V(CRT(c))}, {tgt}, {MOD(POW(V(c), D_), PQ)}, KP.kp.crtv({c}, p, q, d, t, {hc}, hp, hq, hd, vt, hp0, hq0), "
            f"LR.crt_exp_nat({P_}, {Q_}, {E_}, {D_}, {T_}, {V(c)}, pp, pq, hpq, hodd, hdp, hdq, ht))")


def below(x, hx, vx_text, vx_val, mod_of):
    """{N.BnNat.is_lt(x, n) == True} from vx_text : VAL(x) == vx_val, vx_val = mod(A, M) with M = PQ or N"""
    A, M = mod_of
    if M == PQ:
        lt = (f"Equal.trans(Bool, Nat.is_lt({V(x)}, {Nn}), Nat.is_lt({vx_val}, {PQ}), True{{}}, "
              f"Equal.trans(Bool, Nat.is_lt({V(x)}, {Nn}), Nat.is_lt({vx_val}, {Nn}), Nat.is_lt({vx_val}, {PQ}), Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, {Nn}), {V(x)}, {vx_val}, {vx_text}), Equal.cong(Nat, Bool, zz => Nat.is_lt({vx_val}, zz), {Nn}, {PQ}, vn)), "
              f"LR.nat_mod_lt({A}, {PQ}, pq0))")
    else:
        lt = (f"Equal.trans(Bool, Nat.is_lt({V(x)}, {Nn}), Nat.is_lt({vx_val}, {Nn}), True{{}}, "
              f"Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, {Nn}), {V(x)}, {vx_val}, {vx_text}), LR.nat_mod_lt({A}, {Nn}, n0))")
    return f"KP.kp.ltb({x}, n, {hx}, hn, {lt})"


def ind(text, k):
    return chr(10).join(" " * k + ln for ln in text.split(chr(10)))


def leneq(o, k, el):
    """{Nat.is_eq(B.Octets.len(o), k) == True} from el : len(o) == k"""
    return (f"Equal.trans(Bool, Nat.is_eq(B.Octets.len({o}), {k}), Nat.is_eq({k}, {k}), True{{}}, "
            f"Equal.cong(Nat, Bool, zz => Nat.is_eq(zz, {k}), B.Octets.len({o}), {k}, {el}), kq.eqr({k}))")


HEAD_SIGN = """# Generated by gen/proof_sign.py; do not edit by hand. The proofs of LAWS_sign.bend.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/PROOF_limbs.bend as PL
import ../bignum/LAWS_mont.bend as LT
import ../bignum/PROOF_mont.bend as PT
import ../bignum/LAWS_inv.bend as LI
import ../bignum/PROOF_inv.bend as PI
import ../bignum/LAWS_fermat.bend as LF
import ../bignum/PROOF_fermat.bend as PF
import ../bignum/LAWS_rsa.bend as LR
import ../bignum/PROOF_rsa.bend as PR
import ../bignum/LAWS_octets.bend as LO
import ../bignum/PROOF_octets.bend as PO
import ./rsa.bend as R
import ./pkcs1.bend as P
import ./LAWS_prim.bend as LP
import ./PROOF_prim.bend as KP
import ./LAWS_sign.bend as Laws
"""

HEAD_PSS = """# Generated by gen/proof_sign.py; do not edit by hand. The proofs of LAWS_pss.bend.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/PROOF_limbs.bend as PL
import ../bignum/LAWS_mont.bend as LT
import ../bignum/PROOF_mont.bend as PT
import ../bignum/LAWS_inv.bend as LI
import ../bignum/PROOF_inv.bend as PI
import ../bignum/LAWS_fermat.bend as LF
import ../bignum/PROOF_fermat.bend as PF
import ../bignum/LAWS_rsa.bend as LR
import ../bignum/PROOF_rsa.bend as PR
import ../bignum/LAWS_octets.bend as LO
import ../bignum/PROOF_octets.bend as PO
import ./rsa.bend as R
import ./octets.bend as O
import ./pss.bend as PS
import ./LAWS.bend as L0
import ./PROOF.bend as P0
import ./LAWS_prim.bend as LP
import ./PROOF_prim.bend as KP
import ./LAWS_sign.bend as LS
import ./PROOF_sign.bend as KS
import ./LAWS_pss.bend as Laws
"""

PP_TARGET = None


class Out:
    def __init__(self):
        self.out = []
        self.flushed = 0

    def put(self, s=""):
        defs = NP.OUT.defs[self.flushed:]
        if defs:
            self.out.append("\n".join(defs))
            self.flushed = len(NP.OUT.defs)
        self.out.append(s)

    def text(self):
        return "\n".join(s for s in self.out if s is not None).rstrip() + "\n"


def DOB(b0, b1, w):
    return (f"Result.bind(&2, &2, R.RsaError, Unit, B.Octets, R.RsaError.check({b0}, R.RsaOutOfRange{{}}), u => Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, "
            f"Result.map(&2, &2, R.RsaError, Unit, N.BnNat, u => {w}, R.RsaError.check({b1}, R.RsaOutOfRange{{}})), x => R.Rsa.i2osp(x, {BL_})))")


def sign_file():
    W = Out()
    put = W.put
    W.out.append(HEAD_SIGN)
    put("# Results, and the checks of a primitive on octet strings that succeeded\n")
    put(f"""def kq.rdisc(r: {RO}) -> Type:
  match r:
    case Fail{{x}}:
      Unit
    case Done{{y}}:
      Empty

def kq.fd(x: R.RsaError, y: B.Octets, e: {EQ('Fail{x}', 'Done{y}', RO)}) -> Empty:
  %e : kq.rdisc(_)
  Unit{{}}

def kq.tom(r: {RO}) -> {MO}:
  match r:
    case Fail{{x}}:
      None{{}}
    case Done{{y}}:
      Some{{y}}

def kq.go(mr: {MO}, +s: B.Octets, h: {EQ('R.rsa.i2osp.go(mr)', 'Done{s}', RO)}) -> {EQ('mr', 'Some{s}', MO)}:
  match mr:
    case None{{}}:
      Empty.absurd({EQ('None{}', 'Some{s}', MO)}, kq.fd(R.RsaIntegerTooLarge{{}}, s, h))
    case Some{{+y}}:
      Equal.cong({RO}, {MO}, zz => kq.tom(zz), Done{{y}}, Done{{s}}, h)

def kq.eqr(k: Nat) -> {btrue('Nat.is_eq(k, k)')}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +j:
      kq.eqr(j)

def kq.i0(b0: Bool, b1: Bool, +w: N.BnNat, +n: N.BnNat, +s: B.Octets, h: {EQ(DOB('b0', 'b1', 'w'), 'Done{s}', RO)}) -> {btrue('b0')}:
  match b0:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({btrue('False{}')}, kq.fd(R.RsaOutOfRange{{}}, s, h))

def kq.i1(b0: Bool, b1: Bool, +w: N.BnNat, +n: N.BnNat, +s: B.Octets, h: {EQ(DOB('b0', 'b1', 'w'), 'Done{s}', RO)}) -> {btrue('b1')}:
  match b0:
    case True{{}}:
      match b1:
        case True{{}}:
          {{==}}
        case False{{}}:
          Empty.absurd({btrue('False{}')}, kq.fd(R.RsaOutOfRange{{}}, s, h))
    case False{{}}:
      Empty.absurd({btrue('b1')}, kq.fd(R.RsaOutOfRange{{}}, s, h))

def kq.i2(b0: Bool, b1: Bool, +w: N.BnNat, +n: N.BnNat, +s: B.Octets, h: {EQ(DOB('b0', 'b1', 'w'), 'Done{s}', RO)}) -> {EQ(f'N.BnNat.to_octets(w, {BL_})', 'Some{s}', MO)}:
  match b0:
    case True{{}}:
      match b1:
        case True{{}}:
          kq.go(N.BnNat.to_octets(w, {BL_}), s, h)
        case False{{}}:
          Empty.absurd({EQ(f'N.BnNat.to_octets(w, {BL_})', 'Some{s}', MO)}, kq.fd(R.RsaOutOfRange{{}}, s, h))
    case False{{}}:
      Empty.absurd({EQ(f'N.BnNat.to_octets(w, {BL_})', 'Some{s}', MO)}, kq.fd(R.RsaOutOfRange{{}}, s, h))
""")
    # RSAEP after RSADP on octet strings
    Co = OF("o")
    Cm = V(Co)
    CR = CRT(Co)
    Y = f"Md.BnMod.exp({OF('s')}, e, n)"
    B0 = f"Nat.is_eq(B.Octets.len(o), {BL_})"
    B1 = f"N.BnNat.is_lt({Co}, n)"
    vy = calc(V(Y),
              (MOD(POW(V(OF("s")), E_), Nn), H(f"LT.exp_value({OF('s')}, e, n, LO.of_octets_valid(s), he, hn, n0)", V(Y), MOD(POW(V(OF("s")), E_), Nn))),
              (MOD(POW(V(OF("s")), E_), PQ), H("vn", Nn, PQ)),
              (MOD(POW(MOD(POW(Cm, D_), PQ), E_), PQ), H("vsc", V(OF("s")), MOD(POW(Cm, D_), PQ))),
              (MOD(POW(POW(Cm, D_), E_), PQ), H(f"LR.nat_pow_mod({POW(Cm, D_)}, {E_}, {PQ}, pq0)", MOD(POW(MOD(POW(Cm, D_), PQ), E_), PQ), MOD(POW(POW(Cm, D_), E_), PQ))),
              (MOD(Cm, PQ), H(f"LR.rsa_nat_rev({P_}, {Q_}, {E_}, {D_}, {Cm}, pp, pq, hpq, hdp, hdq)", MOD(POW(POW(Cm, D_), E_), PQ), MOD(Cm, PQ))),
              (Cm, H(f"LR.nat_mod_small({Cm}, {PQ}, clq)", MOD(Cm, PQ), Cm)))
    put("# RSAEP after RSADP, and RSADP after RSAEP, on octet strings\n")
    put(f"""def kq.eo3({PRE}, +o: B.Octets, +s: B.Octets, +h: {EQ(f'R.Rsa.dp_octets({X}, o)', 'Done{s}', RO)}) -> {EQ(f'R.Rsa.ep_octets(R.Rsa.public({X}), s)', 'Done{o}', RO)}:
{FACTS0}
  +i0 = kq.i0({B0}, {B1}, {CR}, n, s, h)
  +i1 = kq.i1({B0}, {B1}, {CR}, n, s, h)
  +i2 = kq.i2({B0}, {B1}, {CR}, n, s, h)
{facts_c(Co, 'LO.of_octets_valid(o)', 'i1')}
  +vc = {crtval(Co, 'LO.of_octets_valid(o)')}
  +vsc = Equal.trans(Nat, {V(OF('s'))}, {V(CR)}, {MOD(POW(Cm, D_), PQ)}, LO.to_octets_value({CR}, {BL_}, s, KP.kp.crtk({Co}, p, q, d, t), i2), vc)
  +lts = {below(OF('s'), 'LO.of_octets_valid(s)', 'vsc', MOD(POW(Cm, D_), PQ), (POW(Cm, D_), PQ))}
  +ls = {leneq('s', BL_, f'LO.to_octets_len({CR}, {BL_}, s, i2)')}
  +vy = {vy.text}
  +lo = KP.kp.eqt(B.Octets.len(o), {BL_}, i0)
  +ty = Equal.trans({MO}, N.BnNat.to_octets({Y}, {BL_}), N.BnNat.to_octets({Y}, B.Octets.len(o)), Some{{o}}, Equal.cong(Nat, {MO}, zz => N.BnNat.to_octets({Y}, zz), {BL_}, B.Octets.len(o), Equal.sym(Nat, B.Octets.len(o), {BL_}, lo)), LO.to_octets_of_value({Y}, o, LT.exp_valid({OF('s')}, e, n), Equal.sym(Nat, {V(Y)}, {Cm}, vy)))
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(s), {BL_}), True{{}}, ls) : {EQ(f"Result.bind(&2, &2, R.RsaError, Unit, B.Octets, R.RsaError.check(_, R.RsaOutOfRange{{}}), u => Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, R.Rsa.ep(R.RsaPublic{{n, e}}, {OF('s')}), x => R.Rsa.i2osp(x, {BL_})))", 'Done{o}', RO)}
  %Equal.sym(Bool, N.BnNat.is_lt({OF('s')}, n), True{{}}, lts) : {EQ(f"Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, Result.map(&2, &2, R.RsaError, Unit, N.BnNat, u => {Y}, R.RsaError.check(_, R.RsaOutOfRange{{}})), x => R.Rsa.i2osp(x, {BL_}))", 'Done{o}', RO)}
  %Equal.sym({MO}, N.BnNat.to_octets({Y}, {BL_}), Some{{o}}, ty) : {EQ('R.rsa.i2osp.go(_)', 'Done{o}', RO)}
  {{==}}

def kq.eo2({PRE}, +o: B.Octets, r: {RO}, +er: {EQ(f'R.Rsa.dp_octets({X}, o)', 'r', RO)}) -> {EQ(f'Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, r, s => R.Rsa.ep_octets(R.Rsa.public({X}), s))', 'Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, s => o, r)', RO)}:
  match r:
    case Fail{{x}}:
      {{==}}
    case Done{{+s}}:
      kq.eo3({PREA}, o, s, er)
""")
    # RSADP after RSAEP
    Ye = f"Md.BnMod.exp({Co}, e, n)"
    C2 = OF("c")
    CR2 = CRT(C2)
    vcc = calc(V(CR2),
               (MOD(POW(V(C2), D_), PQ), H("vc2", V(CR2), MOD(POW(V(C2), D_), PQ))),
               (MOD(POW(V(Ye), D_), PQ), H("vce", V(C2), V(Ye))),
               (MOD(POW(MOD(POW(Cm, E_), Nn), D_), PQ), H(f"LT.exp_value({Co}, e, n, LO.of_octets_valid(o), he, hn, n0)", V(Ye), MOD(POW(Cm, E_), Nn))),
               (MOD(POW(MOD(POW(Cm, E_), PQ), D_), PQ), H("vn", Nn, PQ)),
               (MOD(POW(POW(Cm, E_), D_), PQ), H(f"LR.nat_pow_mod({POW(Cm, E_)}, {D_}, {PQ}, pq0)", MOD(POW(MOD(POW(Cm, E_), PQ), D_), PQ), MOD(POW(POW(Cm, E_), D_), PQ))),
               (MOD(Cm, PQ), H(f"LR.rsa_nat({P_}, {Q_}, {E_}, {D_}, {Cm}, pp, pq, hpq, hdp, hdq)", MOD(POW(POW(Cm, E_), D_), PQ), MOD(Cm, PQ))),
               (Cm, H(f"LR.nat_mod_small({Cm}, {PQ}, clq)", MOD(Cm, PQ), Cm)))
    vce_val = MOD(POW(Cm, E_), Nn)
    put(f"""def kq.de3({PRE}, +o: B.Octets, +c: B.Octets, +h: {EQ(f'R.Rsa.ep_octets(R.Rsa.public({X}), o)', 'Done{c}', RO)}) -> {EQ(f'R.Rsa.dp_octets({X}, c)', 'Done{o}', RO)}:
{FACTS0}
  +i0 = kq.i0({B0}, {B1}, {Ye}, n, c, h)
  +i1 = kq.i1({B0}, {B1}, {Ye}, n, c, h)
  +i2 = kq.i2({B0}, {B1}, {Ye}, n, c, h)
{facts_c(Co, 'LO.of_octets_valid(o)', 'i1')}
  +vce = LO.to_octets_value({Ye}, {BL_}, c, LT.exp_valid({Co}, e, n), i2)
  +vcy = Equal.trans(Nat, {V(C2)}, {V(Ye)}, {vce_val}, vce, LT.exp_value({Co}, e, n, LO.of_octets_valid(o), he, hn, n0))
  +ltc = {below(C2, 'LO.of_octets_valid(c)', 'vcy', vce_val, (POW(Cm, E_), Nn))}
  +lc = {leneq('c', BL_, f'LO.to_octets_len({Ye}, {BL_}, c, i2)')}
  +vc2 = {crtval(C2, 'LO.of_octets_valid(c)')}
  +vy = {vcc.text}
  +lo = KP.kp.eqt(B.Octets.len(o), {BL_}, i0)
  +ty = Equal.trans({MO}, N.BnNat.to_octets({CR2}, {BL_}), N.BnNat.to_octets({CR2}, B.Octets.len(o)), Some{{o}}, Equal.cong(Nat, {MO}, zz => N.BnNat.to_octets({CR2}, zz), {BL_}, B.Octets.len(o), Equal.sym(Nat, B.Octets.len(o), {BL_}, lo)), LO.to_octets_of_value({CR2}, o, KP.kp.crtk({C2}, p, q, d, t), Equal.sym(Nat, {V(CR2)}, {Cm}, vy)))
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(c), {BL_}), True{{}}, lc) : {EQ(f"Result.bind(&2, &2, R.RsaError, Unit, B.Octets, R.RsaError.check(_, R.RsaOutOfRange{{}}), u => Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, R.Rsa.dp({X}, {C2}), x => R.Rsa.i2osp(x, {BL_})))", 'Done{o}', RO)}
  %Equal.sym(Bool, N.BnNat.is_lt({C2}, n), True{{}}, ltc) : {EQ(f"Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, Result.map(&2, &2, R.RsaError, Unit, N.BnNat, u => {CR2}, R.RsaError.check(_, R.RsaOutOfRange{{}})), x => R.Rsa.i2osp(x, {BL_}))", 'Done{o}', RO)}
  %Equal.sym({MO}, N.BnNat.to_octets({CR2}, {BL_}), Some{{o}}, ty) : {EQ('R.rsa.i2osp.go(_)', 'Done{o}', RO)}
  {{==}}

def kq.de2({PRE}, +o: B.Octets, r: {RO}, +er: {EQ(f'R.Rsa.ep_octets(R.Rsa.public({X}), o)', 'r', RO)}) -> {EQ(f'Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, r, c => R.Rsa.dp_octets({X}, c))', 'Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, c => o, r)', RO)}:
  match r:
    case Fail{{x}}:
      {{==}}
    case Done{{+c}}:
      kq.de3({PREA}, o, c, er)
""")
    # PKCS #1 v1.5
    VF = f"x => P.RsaPkcs1.verify(~digest, prefix, R.Rsa.public({X}), m, x)"
    ENC = f"P.RsaPkcs1.encode(~digest, prefix, m, {BL_})"
    put("# RSASSA-PKCS1-v1_5\n")
    put(f"""def kq.pk2(~digest: B.Octets -> B.Octets, +prefix: B.Octets, +m: B.Octets, {PRE}, +em: B.Octets, +er1: {EQ(ENC, 'Done{em}', RO)}, r: {RO}, +er2: {EQ(f'R.Rsa.dp_octets({X}, em)', 'r', RO)}) -> {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, {VF}, r)', 'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{}, r)', RB)}:
  match r:
    case Fail{{x}}:
      {{==}}
    case Done{{+s}}:
      %Equal.sym({RO}, R.Rsa.ep_octets(R.Rsa.public({X}), s), Done{{em}}, kq.eo3({PREA}, em, s, er2)) : {EQ(f'Done{{P.rsa.pkcs1.check(~digest, _, prefix, m, {BL_})}}', 'Done{True{}}', RB)}
      %Equal.sym({RO}, {ENC}, Done{{em}}, er1) : {EQ('Done{P.rsa.pkcs1.cmp(_, em)}', 'Done{True{}}', RB)}
      %Equal.sym(Bool, B.Octets.is_eq(em, em), True{{}}, BL.octets_is_eq_refl(em)) : {EQ('Done{_}', 'Done{True{}}', RB)}
      {{==}}

def kq.pk1(~digest: B.Octets -> B.Octets, +prefix: B.Octets, +m: B.Octets, {PRE}, r: {RO}, +er1: {EQ(ENC, 'r', RO)}) -> {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, {VF}, Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, r, em => R.Rsa.dp_octets({X}, em)))', f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{{}}, Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, r, em => R.Rsa.dp_octets({X}, em)))', RB)}:
  match r:
    case Fail{{x}}:
      {{==}}
    case Done{{+em}}:
      kq.pk2(~digest, prefix, m, {PREA}, em, er1, R.Rsa.dp_octets({X}, em), {{==}})
""")
    K = f"{OKP}, {OK}, Md.BnMod.inv(q, p), n, e, d, p, q, sk, hk"
    KA = f"n, e, d, p, q, {QI}, KP.kp.kb1({K}), KP.kp.kb2({K}), KP.kp.kmi({K}), hn, he, hd, hp, hq, pp, pq"
    XQ = XK(QI)
    put("# The laws\n")
    put(f"""def Laws.ep_dp_octets(n, e, d, p, q, sk, o, hk, hn, he, hd, hp, hq, pp, pq):
  %KP.kp.ksk({K}) : {EQ('Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, R.Rsa.dp_octets(_, o), s => R.Rsa.ep_octets(R.Rsa.public(_), s))', 'Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, s => o, R.Rsa.dp_octets(_, o))', RO)}
  kq.eo2({KA}, o, R.Rsa.dp_octets({XQ}, o), {{==}})

def Laws.dp_ep_octets(n, e, d, p, q, sk, o, hk, hn, he, hd, hp, hq, pp, pq):
  %KP.kp.ksk({K}) : {EQ('Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, R.Rsa.ep_octets(R.Rsa.public(_), o), c => R.Rsa.dp_octets(_, c))', 'Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, c => o, R.Rsa.ep_octets(R.Rsa.public(_), o))', RO)}
  kq.de2({KA}, o, R.Rsa.ep_octets(R.Rsa.public({XQ}), o), {{==}})

def Laws.pkcs1_sign_verify(digest, prefix, n, e, d, p, q, sk, m, hk, hn, he, hd, hp, hq, pp, pq):
  %KP.kp.ksk({K}) : {EQ('Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => P.RsaPkcs1.verify(~digest, prefix, R.Rsa.public(_), m, x), P.RsaPkcs1.sign(~digest, prefix, _, m))', 'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{}, P.RsaPkcs1.sign(~digest, prefix, _, m))', RB)}
  kq.pk1(~digest, prefix, m, {KA}, P.RsaPkcs1.encode(~digest, prefix, m, {BL_.replace('n)', 'n)')}), {{==}})
""")
    return W.text()


def pss_file():
    NP.OUT.prefix = "kz.r"
    NP.OUT.seen = {}
    W = Out()
    W.flushed = len(NP.OUT.defs)
    put = W.put
    W.out.append(HEAD_PSS)
    EB = "Nat.sub(N.BnNat.bit_len(n), 1n)"
    EL = f"PS.RsaPss.em_len({EB})"
    MH = "digest(m)"
    HL, SL = f"B.Octets.len({MH})", "B.Octets.len(salt)"
    PSN = f"Nat.sub(PS.RsaPss.em_len(embits), Nat.add({SL}, Nat.add({HL}, 2n)))"
    HH = f"digest(PS.rsa.pss.mprime({MH}, salt))"
    DB = f"PS.rsa.pss.db({PSN}, salt)"
    MK = f"mgf({HH}, B.Octets.len({DB}))"
    XR = f"O.RsaOct.xor({DB}, {MK})"
    CL = f"O.RsaOct.clear_left({XR}, PS.rsa.pss.z(embits))"
    TR = f"B.Octets.append({HH}, B.Octets.of_list([188]))"
    EMT = f"B.Octets.append({CL}, {TR})"
    A = f"Nat.add({SL}, Nat.add({HL}, 2n))"
    A2 = f"Nat.add({HL}, Nat.add({SL}, 2n))"
    LE = "PS.RsaPss.em_len(embits)"
    LEN = lambda o: f"B.Octets.len({o})"
    T188 = "B.Octets.of_list([188])"
    T1S = "B.Octets.append(B.Octets.of_list([1]), salt)"
    ZP = f"B.Octets.zeros({PSN})"
    ldb = (f"Equal.trans(Nat, {LEN(DB)}, {ADD(LEN(ZP), LEN(T1S))}, {ADD(PSN, ADD('1n', SL))}, P0.oct_len_app({ZP}, {T1S}), "
           f"Equal.trans(Nat, {ADD(LEN(ZP), LEN(T1S))}, {ADD(PSN, LEN(T1S))}, {ADD(PSN, ADD('1n', SL))}, Equal.cong(Nat, Nat, zz => Nat.add(zz, {LEN(T1S)}), {LEN(ZP)}, {PSN}, BL.octets_len_zeros({PSN})), "
           f"Equal.cong(Nat, Nat, zz => Nat.add({PSN}, zz), {LEN(T1S)}, {ADD('1n', SL)}, P0.oct_len_app(B.Octets.of_list([1]), salt))))")
    T6 = ADD(ADD(PSN, ADD("1n", SL)), ADD(HL, "1n"))
    rg = NP.ring(T6, ADD(PSN, A))
    steps = [
        (ADD(LEN(CL), LEN(TR)), f"P0.oct_len_app({CL}, {TR})"),
        (ADD(LEN(XR), LEN(TR)), f"Equal.cong(Nat, Nat, zz => Nat.add(zz, {LEN(TR)}), {LEN(CL)}, {LEN(XR)}, P0.oct_mask_first_len({XR}, U32.shrn(255, PS.rsa.pss.z(embits))))"),
        (ADD(LEN(DB), LEN(TR)), f"Equal.cong(Nat, Nat, zz => Nat.add(zz, {LEN(TR)}), {LEN(XR)}, {LEN(DB)}, P0.oct_xor_len({DB}, {MK}))"),
        (ADD(LEN(DB), ADD(LEN(HH), "1n")), f"Equal.cong(Nat, Nat, zz => Nat.add({LEN(DB)}, zz), {LEN(TR)}, {ADD(LEN(HH), '1n')}, P0.oct_len_app({HH}, {T188}))"),
        (ADD(LEN(DB), ADD(HL, "1n")), f"Equal.cong(Nat, Nat, zz => Nat.add({LEN(DB)}, Nat.add(zz, 1n)), {LEN(HH)}, {HL}, hdg)"),
        (T6, f"Equal.cong(Nat, Nat, zz => Nat.add(zz, {ADD(HL, '1n')}), {LEN(DB)}, {ADD(PSN, ADD('1n', SL))}, {ldb})"),
        (ADD(PSN, A), rg.text),
        (LE, f"UL.nat_le_witness({A}, {LE}, hle)"),
    ]

    def chain(t0, st):
        if len(st) == 1:
            return st[0][1]
        return f"Equal.trans(Nat, {t0}, {st[0][0]}, {st[-1][0]}, {st[0][1]}, {chain(st[0][0], st[1:])})"

    class _C:
        pass
    ch = _C()
    ch.text = chain(LEN(EMT), steps)
    put("# The length of an EMSA-PSS encoding, for a hash of a fixed length\n")
    put(f"""def kz.rdisc(r: {RO}) -> Type:
  match r:
    case Fail{{x}}:
      Unit
    case Done{{y}}:
      Empty

def kz.fd(x: R.RsaError, y: B.Octets, e: {EQ('Fail{x}', 'Done{y}', RO)}) -> Empty:
  %e : kz.rdisc(_)
  Unit{{}}

def kz.un(r: {RO}, +a: B.Octets) -> B.Octets:
  match r:
    case Fail{{x}}:
      a
    case Done{{y}}:
      y

def kz.dinj(+a: B.Octets, +b: B.Octets, e: {EQ('Done{a}', 'Done{b}', RO)}) -> {EQ('a', 'b', 'B.Octets')}:
  Equal.cong({RO}, B.Octets, zz => kz.un(zz, a), Done{{a}}, Done{{b}}, e)

def kz.ub(r: {RB}) -> Bool:
  match r:
    case Fail{{x}}:
      False{{}}
    case Done{{y}}:
      y

def kz.len2(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, fits: Bool, +m: B.Octets, +salt: B.Octets, +embits: Nat, +em: B.Octets, +ef: {EQ(f'Nat.is_le({A2}, {LE})', 'fits', 'Bool')}, +hdg: {EQ(LEN(HH), HL)}, h: {EQ(f'PS.rsa.pss.enc(~digest, ~mgf, fits, {MH}, salt, embits)', 'Done{em}', RO)}) -> {EQ(LEN('em'), LE)}:
  match fits:
    case False{{}}:
      Empty.absurd({EQ(LEN('em'), LE)}, kz.fd(R.RsaEncodingError{{}}, em, h))
    case True{{}}:
      +hle = Equal.trans(Bool, Nat.is_le({A}, {LE}), Nat.is_le({A2}, {LE}), True{{}}, Equal.cong(Nat, Bool, zz => Nat.is_le(zz, {LE}), {A}, {A2}, {NP.ring(A, A2).text}), ef)
      Equal.trans(Nat, {LEN('em')}, {LEN(EMT)}, {LE}, Equal.cong(B.Octets, Nat, zz => B.Octets.len(zz), em, {EMT}, Equal.sym(B.Octets, {EMT}, em, kz.dinj({EMT}, em, h))), {ch.text})

def kz.len(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +m: B.Octets, +salt: B.Octets, +embits: Nat, +em: B.Octets, +hdg: {EQ(LEN(HH), HL)}, h: {EQ('PS.RsaPss.encode(~digest, ~mgf, m, salt, embits)', 'Done{em}', RO)}) -> {EQ(LEN('em'), LE)}:
  kz.len2(~digest, ~mgf, Nat.is_le({A2}, {LE}), m, salt, embits, em, {{==}}, hdg, h)
""")
    # the scheme
    Co = OF("em")
    Cm = V(Co)
    CR = CRT(Co)
    Y = f"Md.BnMod.exp({OF('s')}, e, n)"
    vy = calc(V(Y),
              (MOD(POW(V(OF("s")), E_), Nn), H(f"LT.exp_value({OF('s')}, e, n, LO.of_octets_valid(s), he, hn, n0)", V(Y), MOD(POW(V(OF("s")), E_), Nn))),
              (MOD(POW(V(OF("s")), E_), PQ), H("vn", Nn, PQ)),
              (MOD(POW(MOD(POW(Cm, D_), PQ), E_), PQ), H("vsc", V(OF("s")), MOD(POW(Cm, D_), PQ))),
              (MOD(POW(POW(Cm, D_), E_), PQ), H(f"LR.nat_pow_mod({POW(Cm, D_)}, {E_}, {PQ}, pq0)", MOD(POW(MOD(POW(Cm, D_), PQ), E_), PQ), MOD(POW(POW(Cm, D_), E_), PQ))),
              (MOD(Cm, PQ), H(f"LR.rsa_nat_rev({P_}, {Q_}, {E_}, {D_}, {Cm}, pp, pq, hpq, hdp, hdq)", MOD(POW(POW(Cm, D_), E_), PQ), MOD(Cm, PQ))),
              (Cm, H(f"LR.nat_mod_small({Cm}, {PQ}, clq)", MOD(Cm, PQ), Cm)))
    ENC = f"PS.RsaPss.encode(~digest, ~mgf, m, salt, {EB})"
    VF = f"x => PS.RsaPss.verify(~digest, ~mgf, R.Rsa.public({X}), m, x, {SL})"
    GO = f"PS.rsa.pss.verify.go(~digest, ~mgf, {{}}, m, {EB}, {SL})"
    SP = f"R.Rsa.sp1({X}, {Co})"
    I2 = f"x => R.Rsa.i2osp(x, {BL_})"
    put("# RSASSA-PSS\n")
    RN = "Result<&2, &2, R.RsaError, N.BnNat>"
    MW = "Result.map(&2, &2, R.RsaError, Unit, N.BnNat, u => w, R.RsaError.check(b1, R.RsaOutOfRange{}))"
    put(f"""def kz.ndisc(r: {RN}) -> Type:
  match r:
    case Fail{{x}}:
      Unit
    case Done{{y}}:
      Empty

def kz.fdn(x: R.RsaError, y: N.BnNat, e: {EQ('Fail{x}', 'Done{y}', RN)}) -> Empty:
  %e : kz.ndisc(_)
  Unit{{}}

def kz.unn(r: {RN}, +a: N.BnNat) -> N.BnNat:
  match r:
    case Fail{{x}}:
      a
    case Done{{y}}:
      y

def kz.si(b1: Bool, +w: N.BnNat, +x: N.BnNat, h: {EQ(MW, 'Done{x}', RN)}) -> {btrue('b1')}:
  match b1:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({btrue('False{}')}, kz.fdn(R.RsaOutOfRange{{}}, x, h))

def kz.sw(b1: Bool, +w: N.BnNat, +x: N.BnNat, h: {EQ(MW, 'Done{x}', RN)}) -> {EQ('w', 'x', 'N.BnNat')}:
  match b1:
    case True{{}}:
      Equal.cong({RN}, N.BnNat, zz => kz.unn(zz, w), Done{{w}}, Done{{x}}, h)
    case False{{}}:
      Empty.absurd({EQ('w', 'x', 'N.BnNat')}, kz.fdn(R.RsaOutOfRange{{}}, x, h))

def kz.p3(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +m: B.Octets, +salt: B.Octets, +hdg: {EQ(f'B.Octets.len(digest(B.Octets.append(B.Octets.zeros(8n), B.Octets.append({MH}, salt))))', HL)}, {PRE}, +em: B.Octets, +er1: {EQ(ENC, 'Done{em}', RO)}, +hlt: {btrue(f'N.BnNat.is_lt({Co}, n)')}, mr: {MO}, +emr: {EQ(f'N.BnNat.to_octets({CR}, {BL_})', 'mr', MO)}) -> {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, {VF}, R.rsa.i2osp.go(mr))', f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{{}}, R.rsa.i2osp.go(mr))', RB)}:
  match mr:
    case None{{}}:
      {{==}}
    case Some{{+s}}:
{ind(FACTS0, 4)}
{ind(facts_c(Co, 'LO.of_octets_valid(em)', 'hlt'), 4)}
      +vc = {crtval(Co, 'LO.of_octets_valid(em)')}
      +vsc = Equal.trans(Nat, {V(OF('s'))}, {V(CR)}, {MOD(POW(Cm, D_), PQ)}, LO.to_octets_value({CR}, {BL_}, s, KP.kp.crtk({Co}, p, q, d, t), emr), vc)
      +lts = {below(OF('s'), 'LO.of_octets_valid(s)', 'vsc', MOD(POW(Cm, D_), PQ), (POW(Cm, D_), PQ))}
      +ls = {leneq('s', BL_, f'LO.to_octets_len({CR}, {BL_}, s, emr)')}
      +vy = {vy.text}
      +le = kz.len(~digest, ~mgf, m, salt, {EB}, em, hdg, er1)
      +ty = Equal.trans({MO}, N.BnNat.to_octets({Y}, {EL}), N.BnNat.to_octets({Y}, B.Octets.len(em)), Some{{em}}, Equal.cong(Nat, {MO}, zz => N.BnNat.to_octets({Y}, zz), {EL}, B.Octets.len(em), Equal.sym(Nat, B.Octets.len(em), {EL}, le)), LO.to_octets_of_value({Y}, em, LT.exp_valid({OF('s')}, e, n), Equal.sym(Nat, {V(Y)}, {Cm}, vy)))
      +hc = Equal.cong({RB}, Bool, zz => kz.ub(zz), Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => PS.RsaPss.check(~digest, ~mgf, m, em2, {EB}, {SL}), Done{{em}}), Done{{True{{}}}}, Equal.trans({RB}, Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => PS.RsaPss.check(~digest, ~mgf, m, em2, {EB}, {SL}), Done{{em}}), Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => PS.RsaPss.check(~digest, ~mgf, m, em2, {EB}, {SL}), {ENC}), Done{{True{{}}}}, Equal.cong({RO}, {RB}, zz => Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => PS.RsaPss.check(~digest, ~mgf, m, em2, {EB}, {SL}), zz), Done{{em}}, {ENC}, Equal.sym({RO}, {ENC}, Done{{em}}, er1)), Equal.trans({RB}, Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => PS.RsaPss.check(~digest, ~mgf, m, em2, {EB}, {SL}), {ENC}), Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => True{{}}, {ENC}), Done{{True{{}}}}, L0.pss_round_trip(~digest, ~mgf, m, salt, {EB}, hdg), Equal.cong({RO}, {RB}, zz => Result.map(&2, &2, R.RsaError, B.Octets, Bool, em2 => True{{}}, zz), {ENC}, Done{{em}}, er1))))
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(s), {BL_}), True{{}}, ls) : {EQ(f"Done{{Bool.and(_, {GO.format(f'PS.rsa.pss.em_of(R.Rsa.vp1(R.RsaPublic{{n, e}}, {OF(chr(115))}), {EL})')})}}", 'Done{True{}}', RB)}
      %Equal.sym(Bool, N.BnNat.is_lt({OF('s')}, n), True{{}}, lts) : {EQ(f"Done{{{GO.format(f'PS.rsa.pss.em_of(Result.map(&2, &2, R.RsaError, Unit, N.BnNat, u => {Y}, R.RsaError.check(_, R.RsaOutOfRange{{}})), {EL})')}}}", 'Done{True{}}', RB)}
      %Equal.sym({MO}, N.BnNat.to_octets({Y}, {EL}), Some{{em}}, ty) : {EQ(f"Done{{{GO.format('_')}}}", 'Done{True{}}', RB)}
      %Equal.sym(Bool, PS.RsaPss.check(~digest, ~mgf, m, em, {EB}, {SL}), True{{}}, hc) : {EQ('Done{_}', 'Done{True{}}', RB)}
      {{==}}

def kz.p2(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +m: B.Octets, +salt: B.Octets, +hdg: {EQ(f'B.Octets.len(digest(B.Octets.append(B.Octets.zeros(8n), B.Octets.append({MH}, salt))))', HL)}, {PRE}, +em: B.Octets, +er1: {EQ(ENC, 'Done{em}', RO)}, r: Result<&2, &2, R.RsaError, N.BnNat>, +er2: {EQ(SP, 'r', 'Result<&2, &2, R.RsaError, N.BnNat>')}) -> {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, {VF}, Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, r, {I2}))', f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{{}}, Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, r, {I2}))', RB)}:
  match r:
    case Fail{{x}}:
      {{==}}
    case Done{{+x}}:
      %kz.sw(N.BnNat.is_lt({Co}, n), {CR}, x, er2) : {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, {VF}, R.Rsa.i2osp(_, {BL_}))', f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{{}}, R.Rsa.i2osp(_, {BL_}))', RB)}
      kz.p3(~digest, ~mgf, m, salt, hdg, {PREA}, em, er1, kz.si(N.BnNat.is_lt({Co}, n), {CR}, x, er2), N.BnNat.to_octets({CR}, {BL_}), {{==}})

def kz.p1(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +m: B.Octets, +salt: B.Octets, +hdg: {EQ(f'B.Octets.len(digest(B.Octets.append(B.Octets.zeros(8n), B.Octets.append({MH}, salt))))', HL)}, {PRE}, r: {RO}, +er1: {EQ(ENC, 'r', RO)}) -> {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, {VF}, Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, r, em => Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, R.Rsa.sp1({X}, N.BnNat.of_octets(em)), {I2})))', f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{{}}, Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, r, em => Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, R.Rsa.sp1({X}, N.BnNat.of_octets(em)), {I2})))', RB)}:
  match r:
    case Fail{{x}}:
      {{==}}
    case Done{{+em}}:
      kz.p2(~digest, ~mgf, m, salt, hdg, {PREA}, em, er1, {SP}, {{==}})
""")
    K = f"{OKP}, {OK}, Md.BnMod.inv(q, p), n, e, d, p, q, sk, hk"
    KA = f"n, e, d, p, q, {QI}, KP.kp.kb1({K}), KP.kp.kb2({K}), KP.kp.kmi({K}), hn, he, hd, hp, hq, pp, pq"
    put("# The law\n")
    put(f"""def Laws.pss_sign_verify(digest, mgf, n, e, d, p, q, sk, m, salt, hdg, hk, hn, he, hd, hp, hq, pp, pq):
  %KP.kp.ksk({K}) : {EQ(f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => PS.RsaPss.verify(~digest, ~mgf, R.Rsa.public(_), m, x, {SL}), PS.RsaPss.sign(~digest, ~mgf, _, m, salt))', f'Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{{}}, PS.RsaPss.sign(~digest, ~mgf, _, m, salt))', RB)}
  kz.p1(~digest, ~mgf, m, salt, hdg, {KA}, {ENC}, {{==}})
""")
    return W.text()


def main():
    global PP_TARGET
    # PROOF_prim's kp.crtv target, as gen/proof_prim.py writes it
    saved = (list(NP.OUT.defs), dict(NP.OUT.seen), NP.OUT.prefix)
    NP.OUT.prefix = "kp.r"
    PP.out.clear()
    PP_TARGET = PP.crtv()
    NP.OUT.defs[:], NP.OUT.seen = saved[0], saved[1]
    NP.OUT.prefix = "kq.r"
    s = sign_file()
    with open(os.path.join(HERE, "..", "PROOF_sign.bend"), "w", newline="\n") as f:
        f.write(s)
    p = pss_file().replace(" kq.eqr(", " KS.kq.eqr(").replace("(kq.eqr(", "(KS.kq.eqr(")
    with open(os.path.join(HERE, "..", "PROOF_pss.bend"), "w", newline="\n") as f:
        f.write(p)


if __name__ == "__main__":
    main()
