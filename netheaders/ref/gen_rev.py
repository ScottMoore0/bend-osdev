# Writes netheaders/PROOF_rev.bend, the proofs of LAWS_rev.bend (run from
# netheaders/):
#   python3 ref/gen_rev.py           rewrite PROOF_rev.bend
#   python3 ref/gen_rev.py --check   only check that it is up to date
# The case analyses and deep patterns are generated; the reasoning is in the
# comments it writes out.
import sys

def pat(n, k):
    """a U32 split into its low k bits (n0 .. n{k-1}) and, if k < 32, the rest."""
    s = "".join("WCon{%s%d, " % (n, i) for i in range(k))
    tail = "WNil{}" if k == 32 else n + "h"
    return "U32{" + s + tail + "}" * k + "}"

def conlist(xs, tail="Nil{}"):
    return "".join("Con{%s, " % x for x in xs) + tail + "}" * len(xs)

L = "List<&2, U32>"
P = []
w = P.append
def res(t): return "Result<&2, &2, N.NetError, %s>" % t

w(f"""# Proofs of LAWS_rev.bend, written by ref/gen_rev.py.
#
# How the proofs go. A law's bytes o are of_list(to_list(o)), so a lemma on
# the list xs = to_list(o) finishes it. The lemma takes xs apart down to the
# bytes the header needs: a shorter xs makes the parse a failure,
# contradicting the hypothesis. With the bytes x0 .. x(n-1) and the rest,
# the hypothesis says h is what the parser read, G (rv.get of the parse);
# the bytes taken from o are of_list of the first n of xs (rv.take_of); and
# two lists with the same bytes (after masking) make the same Octets
# (rv.of_mask). That last equality is a computation on the bytes' bits (a
# deep pattern): every field the parser read is written back bit for bit.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./netheaders.bend as N
import ./ethernet.bend as E
import ./arp.bend as A
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T
import ./proof_ones.bend as S
import ./LAWS_rev.bend as Laws

# Results

def rv.pick(-X: Data, r: {res("X")}, t: Type, f: Type) -> Type:
  match r:
    case Done{{x}}:
      t
    case Fail{{e}}:
      f

def rv.get(-X: Data, r: {res("X")}, +d: X) -> X:
  match r:
    case Done{{x}}:
      x
    case Fail{{e}}:
      d

# Bytes

# the first n bytes of of_list(xs), n <= len(xs), are of_list of the first n
# of xs
def rv.take_of(+n: Nat, +xs: {L}, +h: {{Nat.is_le(n, B.len(xs)) == True{{}} : Bool}}) -> {{B.Octets.take(n, B.Octets.of_list(xs)) == B.Octets.of_list(B.take(n, xs)) : B.Octets}}:
  %BL.take_drop(n, xs) : {{B.Octets.take(n, B.Octets.of_list(_)) == B.Octets.of_list(B.take(n, xs)) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(B.take(n, xs), B.drop(n, xs))), B.Octets.append(B.Octets.of_list(B.take(n, xs)), B.Octets.of_list(B.drop(n, xs))), S.os.of_list_append(B.take(n, xs), B.drop(n, xs))) : {{B.Octets.take(n, _) == B.Octets.of_list(B.take(n, xs)) : B.Octets}}
  %Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.take(n, xs))), B.len(B.take(n, xs)), n, BL.octets_len_of_list(B.take(n, xs)), S.os.len_take(n, xs, h)) : {{B.Octets.take(_, B.Octets.append(B.Octets.of_list(B.take(n, xs)), B.Octets.of_list(B.drop(n, xs)))) == B.Octets.of_list(B.take(n, xs)) : B.Octets}}
  BL.octets_take_append(B.Octets.of_list(B.take(n, xs)), B.Octets.of_list(B.drop(n, xs)))

# two lists with the same bytes are the same Octets
def rv.of_mask(+a: {L}, +b: {L}, +e: {{B.mask(a) == B.mask(b) : {L}}}) -> {{B.Octets.of_list(a) == B.Octets.of_list(b) : B.Octets}}:
  %BL.octets_of_list_idempotent(a) : {{_ == B.Octets.of_list(b) : B.Octets}}
  %Equal.sym({L}, B.Octets.to_list(B.Octets.of_list(a)), B.mask(a), BL.octets_to_of(a)) : {{B.Octets.of_list(_) == B.Octets.of_list(b) : B.Octets}}
  %Equal.sym({L}, B.mask(a), B.mask(b), e) : {{B.Octets.of_list(_) == B.Octets.of_list(b) : B.Octets}}
  %BL.octets_to_of(b) : {{B.Octets.of_list(_) == B.Octets.of_list(b) : B.Octets}}
  BL.octets_of_list_idempotent(b)
""")

def law_simple(law, ty, parse_list, length, n, plen):
    """a header of n bytes, with no condition on them: plen is length(h)"""
    xs = ["x%d" % i for i in range(n)]
    XS = conlist(xs, "rest")
    G = f"rv.get({ty}, {parse_list}({XS}), h)"
    def goal(lst): return f"{{{ty}.build(h) == B.Octets.take({length}(h), B.Octets.of_list({lst})) : B.Octets}}"
    sig = ", ".join("%s: U32" % x for x in xs)
    psig = ", ".join("+%s: U32" % x for x in xs)
    w(f"""
# {law}: the bytes' bits written back
def {law}.masks({sig}, +rest: {L}, +h: {ty}) -> {{B.mask({ty}.build.list({G})) == B.mask(B.take({length}({G}), {XS})) : {L}}}:
  match {" ".join(xs)}:
    case {" ".join(pat(x + "_", 8) for x in xs)}:
      {{==}}

def {law}.full({psig}, +rest: {L}, +h: {ty}, e: {{{parse_list}({XS}) == Done{{h}} : {res(ty)}}}) -> {goal(XS)}:
  %Equal.cong({res(ty)}, {ty}, z => rv.get({ty}, z, h), {parse_list}({XS}), Done{{h}}, e) : {{{ty}.build(_) == B.Octets.take({length}(_), B.Octets.of_list({XS})) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.take({length}({G}), B.Octets.of_list({XS})), B.Octets.of_list(B.take({length}({G}), {XS})), rv.take_of({length}({G}), {XS}, S.os.le_zero(B.len(rest)))) : {{{ty}.build({G}) == _ : B.Octets}}
  rv.of_mask({ty}.build.list({G}), B.take({length}({G}), {XS}), {law}.masks({", ".join(xs)}, rest, h))
""")
    def go(i, ind):
        pad = "  " * ind
        v = "xs" if i == 0 else "t%d" % i
        if i == n:
            return f"{pad}{law}.full({', '.join(xs)}, {v}, h, e)\n"
        cur = conlist(xs[:i], "Nil{}")
        return (f"{pad}match {v}:\n"
                f"{pad}  case Nil{{}}:\n"
                f"{pad}    %e : rv.pick({ty}, _, {goal(cur)}, Unit)\n"
                f"{pad}    Unit{{}}\n"
                f"{pad}  case Con{{+x{i}, +t{i + 1}}}:\n" + go(i + 1, ind + 2))
    w(f"""
def {law}.list(xs: {L}, +h: {ty}, e: {{{parse_list}(xs) == Done{{h}} : {res(ty)}}}) -> {goal("xs")}:
""" + go(0, 1))
    w(f"""
def Laws.{law}(o, h, e):
  %BL.octets_of_to(o) : {{{ty}.build(h) == B.Octets.take({length}(h), _) : B.Octets}}
  {law}.list(B.Octets.to_list(o), h, e)
""")

law_simple("icmp_reverse", "C.IcmpHeader", "C.IcmpHeader.parse.list", "C.IcmpHeader.length", 8, None)
law_simple("udp_reverse", "U.UdpHeader", "U.UdpHeader.parse.list", "U.UdpHeader.header_length", 8, None)

# ---- helpers for headers with conditions
w(f"""
# Maybe, conditions, and equal words

def rv.some(-X: Data, m: Maybe<&2, X>, +d: X) -> X:
  match m:
    case Some{{x}}:
      x
    case None{{}}:
      d

# net.check answered Done{{h}}: its value is h, and its condition held
def rv.check_done(-X: Data, b: Bool, +err: N.NetError, +x: X, +h: X, e: {{N.net.check(X, b, err, x) == Done{{h}} : {res("X")}}}) -> {{x == h : X}}:
  match b:
    case True{{}}:
      Equal.cong({res("X")}, X, z => rv.get(X, z, x), Done{{x}}, Done{{h}}, e)
    case False{{}}:
      %e : rv.pick(X, _, {{x == h : X}}, Unit)
      Unit{{}}

def rv.check_true(-X: Data, b: Bool, +err: N.NetError, +x: X, +h: X, e: {{N.net.check(X, b, err, x) == Done{{h}} : {res("X")}}}) -> {{b == True{{}} : Bool}}:
  match b:
    case True{{}}:
      {{==}}
    case False{{}}:
      %e : rv.pick(X, _, {{False{{}} == True{{}} : Bool}}, Unit)
      Unit{{}}

def rv.and_l(x: Bool, +y: Bool, +e: {{Bool.and(x, y) == True{{}} : Bool}}) -> {{x == True{{}} : Bool}}:
  match x:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({{False{{}} == True{{}} : Bool}}, S.os.ft(e))

def rv.and_r(x: Bool, +y: Bool, +e: {{Bool.and(x, y) == True{{}} : Bool}}) -> {{y == True{{}} : Bool}}:
  match x:
    case True{{}}:
      e
    case False{{}}:
      Empty.absurd({{y == True{{}} : Bool}}, S.os.ft(e))

def rv.nat_eq(x: Nat, y: Nat, +h: {{Nat.is_eq(x, y) == True{{}} : Bool}}) -> {{x == y : Nat}}:
  match x y:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      Empty.absurd({{0n == 1n+q : Nat}}, S.os.ft(h))
    case 1n+p 0n:
      Empty.absurd({{1n+p == 0n : Nat}}, S.os.ft(h))
    case 1n+ +p 1n+ +q:
      S.os.succ_cong(p, q, rv.nat_eq(p, q, h))

def rv.eq_true(+a: U32, +b: U32, +h: {{U32.is_eq(a, b) == True{{}} : Bool}}) -> {{a == b : U32}}:
  UL.u32_value_eq(a, b, rv.nat_eq(U32.to_nat(a), U32.to_nat(b), Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(a, b), True{{}}, Equal.sym(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), UL.u32_eq_value(a, b)), h)))

# net.has(n, xs): xs has at least n bytes
def rv.has_le(n: Nat, xs: {L}, +h: {{N.net.has(n, xs) == True{{}} : Bool}}) -> {{Nat.is_le(n, B.len(xs)) == True{{}} : Bool}}:
  match n:
    case 0n:
      S.os.le_zero(B.len(xs))
    case 1n+ +m:
      match xs:
        case Nil{{}}:
          Empty.absurd({{Nat.is_le(1n+m, 0n) == True{{}} : Bool}}, S.os.ft(h))
        case Con{{x, +t}}:
          rv.has_le(m, t, h)
""")

def split_list(law, ty, parse_list, length, n, full, extra_sig="", extra_args=""):
    """the lemma on lists: xs taken apart down to n bytes, then full(...)"""
    xs = ["x%d" % i for i in range(n)]
    def goal(lst): return f"{{{ty}.build(h) == B.Octets.take({length}(h), B.Octets.of_list({lst})) : B.Octets}}"
    def go(i, ind):
        pad = "  " * ind
        v = "xs" if i == 0 else "t%d" % i
        if i == n:
            return f"{pad}{full}({', '.join(xs)}, {v}, h, e)\n"
        cur = conlist(xs[:i], "Nil{}")
        return (f"{pad}match {v}:\n"
                f"{pad}  case Nil{{}}:\n"
                f"{pad}    %e : rv.pick({ty}, _, {goal(cur)}, Unit)\n"
                f"{pad}    Unit{{}}\n"
                f"{pad}  case Con{{+x{i}, +t{i + 1}}}:\n" + go(i + 1, ind + 2))
    w(f"""
def {law}.list(xs: {L}, +h: {ty}, e: {{{parse_list("xs")} == Done{{h}} : {res(ty)}}}) -> {goal("xs")}:
""" + go(0, 1))
    w(f"""
def Laws.{law}(o, h, e):
  %BL.octets_of_to(o) : {{{ty}.build(h) == B.Octets.take({length}(h), _) : B.Octets}}
  {law}.list(B.Octets.to_list(o), h, e)
""")

def be32(XS, i): return f"rv.some(U32, B.be32_at({XS}, {i}n), 0)"
def be16(XS, i): return f"rv.some(U32, B.be16_at({XS}, {i}n), 0)"
def get(wd, p, k): return f"N.NetField.get({wd}, {p}n, {k}n)"
MZ = "E.MacAddr{0, 0, 0, 0, 0, 0}"
AZ = "I6.Ipv6Addr{0, 0, 0, 0}"

# IPv6: 40 bytes; the version check is net.check's condition
n = 40
xs = ["x%d" % i for i in range(n)]
XS = conlist(xs, "rest")
W0, W1 = be32(XS, 0), be32(XS, 4)
H6 = (f"I6.Ipv6Header{{{get(W0, 28, 4)}, {get(W0, 20, 8)}, {get(W0, 0, 20)}, {get(W1, 16, 16)}, {get(W1, 8, 8)}, {get(W1, 0, 8)}, "
      f"rv.some(I6.Ipv6Addr, I6.Ipv6Addr.at({XS}, 8n), {AZ}), rv.some(I6.Ipv6Addr, I6.Ipv6Addr.at({XS}, 24n), {AZ})}}")
T6 = "I6.Ipv6Header"
w(f"""
# ipv6_reverse: the version is written back as read
def ipv6_reverse.masks({", ".join("%s: U32" % x for x in xs)}, +rest: {L}) -> {{B.mask({T6}.build.list({H6})) == B.mask(B.take({T6}.length({H6}), {XS})) : {L}}}:
  match {" ".join(xs)}:
    case {" ".join(pat(x + "_", 8) for x in xs)}:
      {{==}}

def ipv6_reverse.full({", ".join("+%s: U32" % x for x in xs)}, +rest: {L}, +h: {T6}, e: {{{T6}.parse.list({XS}) == Done{{h}} : {res(T6)}}}) -> {{{T6}.build(h) == B.Octets.take({T6}.length(h), B.Octets.of_list({XS})) : B.Octets}}:
  %rv.check_done({T6}, U32.is_eq({get(W0, 28, 4)}, 6), N.NetBadVersion{{}}, {H6}, h, e) : {{{T6}.build(_) == B.Octets.take({T6}.length(_), B.Octets.of_list({XS})) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.take({T6}.length({H6}), B.Octets.of_list({XS})), B.Octets.of_list(B.take({T6}.length({H6}), {XS})), rv.take_of({T6}.length({H6}), {XS}, S.os.le_zero(B.len(rest)))) : {{{T6}.build({H6}) == _ : B.Octets}}
  rv.of_mask({T6}.build.list({H6}), B.take({T6}.length({H6}), {XS}), ipv6_reverse.masks({", ".join(xs)}, rest))
""")
split_list("ipv6_reverse", T6, lambda x: f"{T6}.parse.list({x})", f"{T6}.length", 40, "ipv6_reverse.full")

# ARP: 28 bytes; the format check (hardware and protocol types and lengths)
n = 28
xs = ["x%d" % i for i in range(n)]
XS = conlist(xs, "rest")
F, LF = be32(XS, 0), be16(XS, 4)
HA = (f"A.ArpPacket{{{be16(XS, 6)}, rv.some(E.MacAddr, E.MacAddr.at({XS}, 8n), {MZ}), {be32(XS, 14)}, "
      f"rv.some(E.MacAddr, E.MacAddr.at({XS}, 18n), {MZ}), {be32(XS, 24)}}}")
TA = "A.ArpPacket"
BA = f"Bool.and(U32.is_eq({F}, 67584), U32.is_eq({LF}, 1540))"
R6 = f"B.drop(6n, B.take(28n, {XS}))"
XSIG = ", ".join("%s: U32" % x for x in xs)
XPAT = " ".join(pat(x + "_", 8) for x in xs)
w(f"""
# arp_reverse: the six bytes the format check reads are the ones written
def arp_reverse.mA({XSIG}, +rest: {L}) -> {{B.mask(B.take(28n, {XS})) == B.mask(B.append(B.be32({F}), B.append(B.be16({LF}), {R6}))) : {L}}}:
  match {" ".join(xs)}:
    case {XPAT}:
      {{==}}

def arp_reverse.mB({XSIG}, +rest: {L}) -> {{B.mask({TA}.build.list({HA})) == B.mask(B.append(B.be32(67584), B.append(B.be16(1540), {R6}))) : {L}}}:
  match {" ".join(xs)}:
    case {XPAT}:
      {{==}}

def arp_reverse.masks({", ".join("+%s: U32" % x for x in xs)}, +rest: {L}, +ef: {{{F} == 67584 : U32}}, +el: {{{LF} == 1540 : U32}}) -> {{B.mask({TA}.build.list({HA})) == B.mask(B.take({TA}.length({HA}), {XS})) : {L}}}:
  %Equal.sym({L}, B.mask(B.take(28n, {XS})), B.mask(B.append(B.be32({F}), B.append(B.be16({LF}), {R6}))), arp_reverse.mA({", ".join(xs)}, rest)) : {{B.mask({TA}.build.list({HA})) == _ : {L}}}
  %Equal.sym(U32, {F}, 67584, ef) : {{B.mask({TA}.build.list({HA})) == B.mask(B.append(B.be32(_), B.append(B.be16({LF}), {R6}))) : {L}}}
  %Equal.sym(U32, {LF}, 1540, el) : {{B.mask({TA}.build.list({HA})) == B.mask(B.append(B.be32(67584), B.append(B.be16(_), {R6}))) : {L}}}
  arp_reverse.mB({", ".join(xs)}, rest)

def arp_reverse.full({", ".join("+%s: U32" % x for x in xs)}, +rest: {L}, +h: {TA}, +e: {{{TA}.parse.list({XS}) == Done{{h}} : {res(TA)}}}) -> {{{TA}.build(h) == B.Octets.take({TA}.length(h), B.Octets.of_list({XS})) : B.Octets}}:
  +eb = rv.check_true({TA}, {BA}, N.NetBadArpFormat{{}}, {HA}, h, e)
  +ef = rv.eq_true({F}, 67584, rv.and_l(U32.is_eq({F}, 67584), U32.is_eq({LF}, 1540), eb))
  +el = rv.eq_true({LF}, 1540, rv.and_r(U32.is_eq({F}, 67584), U32.is_eq({LF}, 1540), eb))
  %rv.check_done({TA}, {BA}, N.NetBadArpFormat{{}}, {HA}, h, e) : {{{TA}.build(_) == B.Octets.take({TA}.length(_), B.Octets.of_list({XS})) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.take({TA}.length({HA}), B.Octets.of_list({XS})), B.Octets.of_list(B.take({TA}.length({HA}), {XS})), rv.take_of({TA}.length({HA}), {XS}, S.os.le_zero(B.len(rest)))) : {{{TA}.build({HA}) == _ : B.Octets}}
  rv.of_mask({TA}.build.list({HA}), B.take({TA}.length({HA}), {XS}), arp_reverse.masks({", ".join(xs)}, rest, ef, el))
""")
split_list("arp_reverse", TA, lambda x: f"{TA}.parse.list({x})", f"{TA}.length", 28, "arp_reverse.full")

# ---- IPv4 and TCP: every header length, options after the fixed part
def bits4lo(v, tail):
    """a U32 whose low 4 bits are v, the rest the Word(28n) tail"""
    s = "".join("WCon{%s, " % ("True{}" if v >> i & 1 else "False{}") for i in range(4))
    return "U32{" + s + tail + "}" * 4 + "}"

def bits4hi(v, lo, tail):
    """a U32 whose bits 0..3 are the variables lo, bits 4..7 are v, the rest
    the Word(24n) tail"""
    s = "".join("WCon{%s, " % b for b in lo) + "".join("WCon{%s, " % ("True{}" if v >> i & 1 else "False{}") for i in range(4))
    return "U32{" + s + tail + "}" * 8 + "}"

w(f"""
# IPv4's checks: version, IHL, and the bytes present
def rv4.done(vok: Bool, +pres: Bool, +x: I4.Ipv4Header, +h: I4.Ipv4Header, e: {{I4.Ipv4Header.check(vok, True{{}}, pres, x) == Done{{h}} : {res("I4.Ipv4Header")}}}) -> {{x == h : I4.Ipv4Header}}:
  match vok:
    case True{{}}:
      rv.check_done(I4.Ipv4Header, pres, N.NetTruncated{{}}, x, h, e)
    case False{{}}:
      %e : rv.pick(I4.Ipv4Header, _, {{x == h : I4.Ipv4Header}}, Unit)
      Unit{{}}

def rv4.pres(vok: Bool, +pres: Bool, +x: I4.Ipv4Header, +h: I4.Ipv4Header, e: {{I4.Ipv4Header.check(vok, True{{}}, pres, x) == Done{{h}} : {res("I4.Ipv4Header")}}}) -> {{pres == True{{}} : Bool}}:
  match vok:
    case True{{}}:
      rv.check_true(I4.Ipv4Header, pres, N.NetTruncated{{}}, x, h, e)
    case False{{}}:
      %e : rv.pick(I4.Ipv4Header, _, {{pres == True{{}} : Bool}}, Unit)
      Unit{{}}

def rv4.no_ihl(vok: Bool, +pres: Bool, +x: I4.Ipv4Header, +h: I4.Ipv4Header, e: {{I4.Ipv4Header.check(vok, False{{}}, pres, x) == Done{{h}} : {res("I4.Ipv4Header")}}}) -> Empty:
  match vok:
    case True{{}}:
      %e : rv.pick(I4.Ipv4Header, _, Empty, Unit)
      Unit{{}}
    case False{{}}:
      %e : rv.pick(I4.Ipv4Header, _, Empty, Unit)
      Unit{{}}
""")

def lengthy_rev(law, ty, lenbyte, hdr, vok, pres_of, cond, m20name):
    """lenbyte: the byte holding the length field (IPv4: byte 0, its low
    nibble; TCP: byte 12, its high nibble); hdr(XS): the header the parser
    reads; vok(XS): the version check (IPv4) or None; pres_of(XS)"""
    n = 20
    xs = ["x%d" % i for i in range(n)]
    XSg = conlist(xs, "rest")
    Hg = hdr(XSg)
    # the fixed 20 bytes, written back bit for bit (any length field)
    w(f"""
# {law}: the fixed 20 bytes written back
def {m20name}({", ".join("%s: U32" % x for x in xs)}, +rest: {L}) -> {{B.mask(B.take(20n, {ty}.build.list({Hg}))) == B.mask({conlist(xs)}) : {L}}}:
  match {" ".join(xs)}:
    case {" ".join(pat(x + "_", 8) for x in xs)}:
      {{==}}
""")
    def goal(lst): return f"{{{ty}.build(h) == B.Octets.take({ty}.length(h), B.Octets.of_list({lst})) : B.Octets}}"
    cases = []
    word = [lenbyte + i for i in range(4)]
    deep = [i for i in word if i != lenbyte]
    def bitargs(i): return ["x%d_%d" % (i, k) for k in range(8)] + ["x%d_h" % i]
    for v in range(16):
        if lenbyte == 0:
            xv = bits4lo(v, "xr")
            vsig, vargs = "+xr: Word(28n), ", "xr, "
        else:
            xv = bits4hi(v, ["xb0", "xb1", "xb2", "xb3"], "xr")
            vsig, vargs = "+xb0: Bool, +xb1: Bool, +xb2: Bool, +xb3: Bool, +xr: Word(24n), ", "xb0, xb1, xb2, xb3, xr, "
        for i in deep:
            vsig += "".join("+x%d_%d: Bool, " % (i, k) for k in range(8)) + "+x%d_h: Word(24n), " % i
            vargs += "".join(a + ", " for a in bitargs(i))
        xsv = [xv if i == lenbyte else (pat("x%d_" % i, 8) if i in deep else x) for i, x in enumerate(xs)]
        others = [x for i, x in enumerate(xs) if i not in word]
        XS = conlist(xsv, "rest")
        H = hdr(XS)
        PRES = pres_of(XS)
        sig = vsig + ", ".join("+%s: U32" % x for x in others) + f", +rest: {L}, +h: {ty}, +e: {{{ty}.parse.list({XS}) == Done{{h}} : {res(ty)}}}"
        args = vargs + ", ".join(others) + ", rest, h, e"
        if v < 5:
            if vok:
                body = f"  Empty.absurd({goal(XS)}, rv4.no_ihl({vok(XS)}, {PRES}, {H}, h, e))\n"
            else:
                body = f"  %e : rv.pick({ty}, _, {goal(XS)}, Unit)\n  Unit{{}}\n"
        else:
            Lv = 4 * v - 20
            if vok:
                eh = f"rv4.done({vok(XS)}, {PRES}, {H}, h, e)"
                ep = f"rv4.pres({vok(XS)}, {PRES}, {H}, h, e)"
            else:
                eh = f"rv.check_done({ty}, {PRES}, N.NetTruncated{{}}, {H}, h, e)"
                ep = f"rv.check_true({ty}, {PRES}, N.NetTruncated{{}}, {H}, h, e)"
            F20 = f"B.take(20n, {ty}.build.list({H}))"
            OPT = cond(XS)
            X20 = conlist(xsv)
            OPTL = OPT[len("B.Octets.of_list("):-1]
            TK = f"B.take({Lv}n, rest)"
            body = (f"  %{eh} : {{{ty}.build(_) == B.Octets.take({ty}.length(_), B.Octets.of_list({XS})) : B.Octets}}\n"
                    f"  %Equal.sym(B.Octets, B.Octets.take({ty}.length({H}), B.Octets.of_list({XS})), B.Octets.of_list(B.take({ty}.length({H}), {XS})), rv.take_of({ty}.length({H}), {XS}, rv.has_le({Lv}n, rest, {ep}))) : {{{ty}.build({H}) == _ : B.Octets}}\n"
                    f"  %Equal.cong({L}, B.Octets, z => B.Octets.of_list(z), B.append({F20}, B.Octets.to_list({OPT})), {ty}.build.list({H}), {{==}}) : {{_ == B.Octets.of_list(B.take({ty}.length({H}), {XS})) : B.Octets}}\n"
                    f"  %S.os.app_of({F20}, {OPT}) : {{_ == B.Octets.of_list(B.take({ty}.length({H}), {XS})) : B.Octets}}\n"
                    f"  %Equal.cong({L}, B.Octets, z => B.Octets.of_list(z), B.append({X20}, {TK}), B.take({ty}.length({H}), {XS}), {{==}}) : {{B.Octets.append(B.Octets.of_list({F20}), {OPT}) == _ : B.Octets}}\n"
                    f"  %Equal.sym(B.Octets, B.Octets.of_list(B.append({X20}, {TK})), B.Octets.append(B.Octets.of_list({X20}), B.Octets.of_list({TK})), S.os.of_list_append({X20}, {TK})) : {{B.Octets.append(B.Octets.of_list({F20}), {OPT}) == _ : B.Octets}}\n"
                    f"  %Equal.cong({L}, B.Octets, z => B.Octets.of_list(z), {TK}, {OPTL}, {{==}}) : {{B.Octets.append(B.Octets.of_list({F20}), _) == B.Octets.append(B.Octets.of_list({X20}), B.Octets.of_list({TK})) : B.Octets}}\n"
                    f"  Equal.cong(B.Octets, B.Octets, z => B.Octets.append(z, B.Octets.of_list({TK})), B.Octets.of_list({F20}), B.Octets.of_list({X20}), rv.of_mask({F20}, {X20}, {m20name}({', '.join(xsv)}, rest)))\n")
        w(f"""
def {law}.v{v}({sig}) -> {goal(XS)}:
{body}""")
        cases.append((" ".join([xv] + [pat("x%d_" % i, 8) for i in deep]), f"{law}.v{v}({args})"))
    # the split on the length field's bits, and the bits of its word
    w(f"""
def {law}.full({", ".join(("%s: U32" if i in word else "+%s: U32") % x for i, x in enumerate(xs))}, +rest: {L}, +h: {ty}, +e: {{{ty}.parse.list({XSg}) == Done{{h}} : {res(ty)}}}) -> {goal(XSg)}:
  match {" ".join(xs[i] for i in word)}:
""" + "".join(f"    case {xv}:\n      {call}\n" for xv, call in cases))
    split_list(law, ty, lambda x: f"{ty}.parse.list({x})", f"{ty}.length", 20, f"{law}.full")

def h4(XS):
    W = [be32(XS, i) for i in (0, 4, 8, 12, 16)]
    hl = f"Nat.mul(4n, U32.to_nat({get(W[0], 24, 4)}))"
    return (f"I4.Ipv4Header{{{get(W[0], 28, 4)}, {get(W[0], 24, 4)}, {get(W[0], 18, 6)}, {get(W[0], 16, 2)}, {get(W[0], 0, 16)}, "
            f"{get(W[1], 16, 16)}, {get(W[1], 13, 3)}, {get(W[1], 0, 13)}, {get(W[2], 24, 8)}, {get(W[2], 16, 8)}, {get(W[2], 0, 16)}, "
            f"{W[3]}, {W[4]}, B.Octets.of_list(B.take(Nat.sub({hl}, 20n), B.drop(20n, {XS})))}}")
def h4opt(XS):
    hl = f"Nat.mul(4n, U32.to_nat({get(be32(XS, 0), 24, 4)}))"
    return f"B.Octets.of_list(B.take(Nat.sub({hl}, 20n), B.drop(20n, {XS})))"
lengthy_rev("ipv4_reverse", "I4.Ipv4Header", 0, h4,
            lambda XS: f"U32.is_eq({get(be32(XS, 0), 28, 4)}, 4)",
            lambda XS: f"N.net.has(Nat.mul(4n, U32.to_nat({get(be32(XS, 0), 24, 4)})), {XS})",
            h4opt, "ipv4_reverse.m20")

def ht(XS):
    W = [be32(XS, i) for i in (0, 4, 8, 12, 16)]
    off = get(W[3], 28, 4)
    hl = f"Nat.mul(4n, U32.to_nat({off}))"
    return (f"T.TcpHeader{{{get(W[0], 16, 16)}, {get(W[0], 0, 16)}, {W[1]}, {W[2]}, {off}, {get(W[3], 24, 4)}, {get(W[3], 16, 8)}, {get(W[3], 0, 16)}, "
            f"{get(W[4], 16, 16)}, {get(W[4], 0, 16)}, B.Octets.of_list(B.take(Nat.sub({hl}, 20n), B.drop(20n, {XS})))}}")
def htopt(XS):
    hl = f"Nat.mul(4n, U32.to_nat({get(be32(XS, 12), 28, 4)}))"
    return f"B.Octets.of_list(B.take(Nat.sub({hl}, 20n), B.drop(20n, {XS})))"
lengthy_rev("tcp_reverse", "T.TcpHeader", 12, ht, None,
            lambda XS: f"N.net.has(Nat.mul(4n, U32.to_nat({get(be32(XS, 12), 28, 4)})), {XS})",
            htopt, "tcp_reverse.m20")

# ---- Ethernet: untagged (14 bytes) or tagged (18), as the tag test says
TE = "E.EthHeader"
TP = "E.EthHeader.TPID_8021Q()"
xs14 = ["x%d" % i for i in range(14)]
xs18 = ["x%d" % i for i in range(18)]
XS14 = conlist(xs14, "rest")
XS18 = conlist(xs18, "rest")
W12a = be16(XS14, 12)
W12b = be16(XS18, 12)
def egoal(lst): return f"{{{TE}.build(h) == B.Octets.take({TE}.length(h), B.Octets.of_list({lst})) : B.Octets}}"
GU = f"rv.get({TE}, {TE}.parse.go(False{{}}, {XS14}), h)"
GT = f"rv.get({TE}, {TE}.parse.go(True{{}}, {XS18}), h)"
R14 = f"B.drop(14n, B.take({TE}.length({GT}), {XS18}))"
w(f"""
# eth_reverse, untagged: the 14 bytes written back
def eth_reverse.masksU({", ".join("%s: U32" % x for x in xs14)}, +rest: {L}, +h: {TE}) -> {{B.mask({TE}.build.list({TP}, {GU})) == B.mask(B.take({TE}.length({GU}), {XS14})) : {L}}}:
  match {" ".join(xs14)}:
    case {" ".join(pat(x + "_", 8) for x in xs14)}:
      {{==}}

def eth_reverse.untagged({", ".join("+%s: U32" % x for x in xs14)}, +rest: {L}, +h: {TE}, e: {{{TE}.parse.go(False{{}}, {XS14}) == Done{{h}} : {res(TE)}}}) -> {egoal(XS14)}:
  %Equal.cong({res(TE)}, {TE}, z => rv.get({TE}, z, h), {TE}.parse.go(False{{}}, {XS14}), Done{{h}}, e) : {{{TE}.build(_) == B.Octets.take({TE}.length(_), B.Octets.of_list({XS14})) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.take({TE}.length({GU}), B.Octets.of_list({XS14})), B.Octets.of_list(B.take({TE}.length({GU}), {XS14})), rv.take_of({TE}.length({GU}), {XS14}, S.os.le_zero(B.len(rest)))) : {{{TE}.build({GU}) == _ : B.Octets}}
  rv.of_mask({TE}.build.list({TP}, {GU}), B.take({TE}.length({GU}), {XS14}), eth_reverse.masksU({", ".join(xs14)}, rest, h))

# tagged: bytes 12 and 13 are the TPID the test found
def eth_reverse.mA({", ".join("%s: U32" % x for x in xs18)}, +rest: {L}, +h: {TE}) -> {{B.mask(B.take({TE}.length({GT}), {XS18})) == B.mask(B.append(B.take(12n, {XS18}), B.append(B.be16({W12b}), {R14}))) : {L}}}:
  match {" ".join(xs18)}:
    case {" ".join(pat(x + "_", 8) for x in xs18)}:
      {{==}}

def eth_reverse.mB({", ".join("%s: U32" % x for x in xs18)}, +rest: {L}, +h: {TE}) -> {{B.mask({TE}.build.list({TP}, {GT})) == B.mask(B.append(B.take(12n, {XS18}), B.append(B.be16(33024), {R14}))) : {L}}}:
  match {" ".join(xs18)}:
    case {" ".join(pat(x + "_", 8) for x in xs18)}:
      {{==}}

def eth_reverse.masksT({", ".join("+%s: U32" % x for x in xs18)}, +rest: {L}, +h: {TE}, +e12: {{{W12b} == 33024 : U32}}) -> {{B.mask({TE}.build.list({TP}, {GT})) == B.mask(B.take({TE}.length({GT}), {XS18})) : {L}}}:
  %Equal.sym({L}, B.mask(B.take({TE}.length({GT}), {XS18})), B.mask(B.append(B.take(12n, {XS18}), B.append(B.be16({W12b}), {R14}))), eth_reverse.mA({", ".join(xs18)}, rest, h)) : {{B.mask({TE}.build.list({TP}, {GT})) == _ : {L}}}
  %Equal.sym(U32, {W12b}, 33024, e12) : {{B.mask({TE}.build.list({TP}, {GT})) == B.mask(B.append(B.take(12n, {XS18}), B.append(B.be16(_), {R14}))) : {L}}}
  eth_reverse.mB({", ".join(xs18)}, rest, h)

def eth_reverse.tfull({", ".join("+%s: U32" % x for x in xs18)}, +rest: {L}, +eb: {{U32.is_eq({W12b}, 33024) == True{{}} : Bool}}, +h: {TE}, e: {{{TE}.parse.go(True{{}}, {XS18}) == Done{{h}} : {res(TE)}}}) -> {egoal(XS18)}:
  %Equal.cong({res(TE)}, {TE}, z => rv.get({TE}, z, h), {TE}.parse.go(True{{}}, {XS18}), Done{{h}}, e) : {{{TE}.build(_) == B.Octets.take({TE}.length(_), B.Octets.of_list({XS18})) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.take({TE}.length({GT}), B.Octets.of_list({XS18})), B.Octets.of_list(B.take({TE}.length({GT}), {XS18})), rv.take_of({TE}.length({GT}), {XS18}, S.os.le_zero(B.len(rest)))) : {{{TE}.build({GT}) == _ : B.Octets}}
  rv.of_mask({TE}.build.list({TP}, {GT}), B.take({TE}.length({GT}), {XS18}), eth_reverse.masksT({", ".join(xs18)}, rest, h, rv.eq_true({W12b}, 33024, eb)))
""")
# the tagged case takes four more bytes apart
def go(i, ind):
    pad = "  " * ind
    v = "rest" if i == 14 else "t%d" % i
    if i == 18:
        return f"{pad}eth_reverse.tfull({', '.join(xs18)}, {v}, eb, h, e)\n"
    cur = conlist(xs18[:i], "Nil{}")
    return (f"{pad}match {v}:\n"
            f"{pad}  case Nil{{}}:\n"
            f"{pad}    %e : rv.pick({TE}, _, {egoal(cur)}, Unit)\n"
            f"{pad}    Unit{{}}\n"
            f"{pad}  case Con{{+x{i}, +t{i + 1}}}:\n" + go(i + 1, ind + 2))
w(f"""
def eth_reverse.tagged({", ".join("+%s: U32" % x for x in xs14)}, rest: {L}, +eb: {{U32.is_eq({W12a}, 33024) == True{{}} : Bool}}, +h: {TE}, e: {{{TE}.parse.go(True{{}}, {XS14}) == Done{{h}} : {res(TE)}}}) -> {egoal(XS14)}:
""" + go(14, 1))
w(f"""
def eth_reverse.split(b: Bool, {", ".join("+%s: U32" % x for x in xs14)}, +rest: {L}, +h: {TE}, +eb: {{U32.is_eq({W12a}, 33024) == b : Bool}}, e: {{{TE}.parse.go(b, {XS14}) == Done{{h}} : {res(TE)}}}) -> {egoal(XS14)}:
  match b:
    case False{{}}:
      eth_reverse.untagged({", ".join(xs14)}, rest, h, e)
    case True{{}}:
      eth_reverse.tagged({", ".join(xs14)}, rest, eb, h, e)

def eth_reverse.full({", ".join("+%s: U32" % x for x in xs14)}, +rest: {L}, +h: {TE}, e: {{{TE}.parse.list({TP}, {XS14}) == Done{{h}} : {res(TE)}}}) -> {egoal(XS14)}:
  eth_reverse.split(U32.is_eq({W12a}, 33024), {", ".join(xs14)}, rest, h, {{==}}, e)
""")
split_list("eth_reverse", TE, lambda x: f"{TE}.parse.list({TP}, {x})", f"{TE}.length", 14, "eth_reverse.full")

# ---- PROOF_revsum.bend: the builders that recompute the checksum
Q = []
q = Q.append
D = "Word.to_nat(16n, Word.not(16n, Word.zero(16n)))"
DA4 = f"{D}, S.os.hd(), S.os.hD(), S.os.hE()"
HD = "+hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}"
HE = "+hE: {U32.to_nat(65535) == d : Nat}"
HDD = "+hd: {Nat.is_le(1n, d) == True{} : Bool}"
DPAR = f"+d: Nat, {HDD}, {HD}, {HE}"
def v(x): return "U32.to_nat(%s)" % x
def le(x, y): return "{Nat.is_le(%s, %s) == True{} : Bool}" % (x, y)
EMP = "B.Octets.empty()"
q(f"""# Proofs of LAWS_revsum.bend, written by ref/gen_rev.py.
#
# How the proofs go. The reverse round trip (LAWS_rev.bend) says the parsed
# header's bytes are the input's first bytes, so the builder is inet_fill (or
# UDP's fill) applied to the input itself. A field c that verifies makes the
# sum with the field 0, s, and c go round to 0xffff: rep(s + c) = d
# (proof_ones.bend: os.verified_sum). When c is not d, s + c = d exactly
# (os.rep_eq_d), so c is the complement of s, the checksum the builder
# writes (os.fill_self), and writing a field's own value back gives the
# bytes back (os.put16_self). UDP's fill writes 0xffff for a computed 0; so
# for a nonzero c the cases c = d, s = 0 or s = d are checked one by one.
import Base
import ../u32/u32.bend as UN
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T
import ./proof_ones.bend as S
import ./PROOF_sum.bend as SP
import ./LAWS_rev.bend as RL
import ./PROOF_rev.bend as RP
import ./LAWS_revsum.bend as Laws

# Lengths

def rs.min_le(n: Nat, +m: Nat) -> {{Nat.is_le(Nat.min(n, m), n) == True{{}} : Bool}}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      match m:
        case 0n:
          {{==}}
        case 1n+ +q:
          rs.min_le(p, q)

def rs.min_le_r(n: Nat, +m: Nat) -> {{Nat.is_le(Nat.min(n, m), m) == True{{}} : Bool}}:
  match n:
    case 0n:
      S.os.le_zero(m)
    case 1n+ +p:
      match m:
        case 0n:
          {{==}}
        case 1n+ +q:
          rs.min_le_r(p, q)

# k bytes in the first n of o: k <= n and k <= len(o)
def rs.take_ge_n(+k: Nat, +n: Nat, +o: B.Octets, +h: {le("k", "B.Octets.len(B.Octets.take(n, o))")}) -> {le("k", "n")}:
  S.os.le_trans(k, Nat.min(n, B.Octets.len(o)), n, Equal.trans(Bool, Nat.is_le(k, Nat.min(n, B.Octets.len(o))), Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(k, z), Nat.min(n, B.Octets.len(o)), B.Octets.len(B.Octets.take(n, o)), Equal.sym(Nat, B.Octets.len(B.Octets.take(n, o)), Nat.min(n, B.Octets.len(o)), BL.octets_len_take(n, o))), h), rs.min_le(n, B.Octets.len(o)))

def rs.take_ge_o(+k: Nat, +n: Nat, +o: B.Octets, +h: {le("k", "B.Octets.len(B.Octets.take(n, o))")}) -> {le("k", "B.Octets.len(o)")}:
  S.os.le_trans(k, Nat.min(n, B.Octets.len(o)), B.Octets.len(o), Equal.trans(Bool, Nat.is_le(k, Nat.min(n, B.Octets.len(o))), Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(k, z), Nat.min(n, B.Octets.len(o)), B.Octets.len(B.Octets.take(n, o)), Equal.sym(Nat, B.Octets.len(B.Octets.take(n, o)), Nat.min(n, B.Octets.len(o)), BL.octets_len_take(n, o))), h), rs.min_le_r(n, B.Octets.len(o)))

# k bytes in the built header, the header the first bytes of o: k <= len(o)
def rs.built_ge(+k: Nat, +n: Nat, +b: B.Octets, +o: B.Octets, +er: {{b == B.Octets.take(n, o) : B.Octets}}, +h: {le("k", "B.Octets.len(b)")}) -> {le("k", "B.Octets.len(o)")}:
  rs.take_ge_o(k, n, o, Equal.trans(Bool, Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), Nat.is_le(k, B.Octets.len(b)), True{{}}, Equal.cong(B.Octets, Bool, z => Nat.is_le(k, B.Octets.len(z)), B.Octets.take(n, o), b, Equal.sym(B.Octets, b, B.Octets.take(n, o), er)), h))

def rs.built_ge_n(+k: Nat, +n: Nat, +b: B.Octets, +o: B.Octets, +er: {{b == B.Octets.take(n, o) : B.Octets}}, +h: {le("k", "B.Octets.len(b)")}) -> {le("k", "n")}:
  rs.take_ge_n(k, n, o, Equal.trans(Bool, Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), Nat.is_le(k, B.Octets.len(b)), True{{}}, Equal.cong(B.Octets, Bool, z => Nat.is_le(k, B.Octets.len(z)), B.Octets.take(n, o), b, Equal.sym(B.Octets, b, B.Octets.take(n, o), er)), h))

# the bytes of a built header: at least its fixed part
def rs.ipv4_lb.m(h: I4.Ipv4Header) -> {le("20n", "B.len(I4.Ipv4Header.build.list(h))")}:
  match h:
    case I4.Ipv4Header{{{", ".join("U32{%s}" % n for n in ["a%d" % i for i in range(13)])}, o}}:
      S.os.le_zero(B.len(B.Octets.to_list(o)))

def rs.tcp_lb.m(h: T.TcpHeader) -> {le("20n", "B.len(T.TcpHeader.build.list(h))")}:
  match h:
    case T.TcpHeader{{{", ".join("U32{%s}" % n for n in ["a%d" % i for i in range(10)])}, o}}:
      S.os.le_zero(B.len(B.Octets.to_list(o)))

def rs.icmp_lb.m(h: C.IcmpHeader) -> {le("8n", "B.len(C.IcmpHeader.build.list(h))")}:
  match h:
    case C.IcmpHeader{{{", ".join("U32{%s}" % n for n in ["a%d" % i for i in range(4)])}}}:
      {{==}}

def rs.udp_lb.m(h: U.UdpHeader) -> {le("8n", "B.len(U.UdpHeader.build.list(h))")}:
  match h:
    case U.UdpHeader{{{", ".join("U32{%s}" % n for n in ["a%d" % i for i in range(4)])}}}:
      {{==}}
""")
for nm, ty, k in [("ipv4", "I4.Ipv4Header", "20n"), ("tcp", "T.TcpHeader", "20n"), ("icmp", "C.IcmpHeader", "8n"), ("udp", "U.UdpHeader", "8n")]:
    q(f"""
def rs.{nm}_lb(+h: {ty}) -> {le(k, f"B.Octets.len({ty}.build(h))")}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list({ty}.build.list(h))), B.len({ty}.build.list(h)), BL.octets_len_of_list({ty}.build.list(h))) : {{Nat.is_le({k}, _) == True{{}} : Bool}}
  rs.{nm}_lb.m(h)
""")
q(f"""
def rs.lower(+a: Nat, +b: Nat, +n: Nat, +h1: {le("a", "b")}, +h2: {le("b", "n")}) -> {le("a", "n")}:
  S.os.le_trans(a, b, n, h1, h2)

# a bytes string is its first n bytes and the rest
def rs.rejoin(+b: B.Octets, +n: Nat, +o: B.Octets, +er: {{b == B.Octets.take(n, o) : B.Octets}}) -> {{B.Octets.append(b, B.Octets.drop(n, o)) == o : B.Octets}}:
  %Equal.sym(B.Octets, b, B.Octets.take(n, o), er) : {{B.Octets.append(_, B.Octets.drop(n, o)) == o : B.Octets}}
  BL.octets_take_drop(n, o)

# UDP's verify: with the field not zero, the sum is checked
def rs.go_s(z: Bool, +ok: Bool, +s: Bool, +ez: {{z == False{{}} : Bool}}, +e: {{U.UdpHeader.verify.go(z, ok, s) == True{{}} : Bool}}) -> {{s == True{{}} : Bool}}:
  match z:
    case True{{}}:
      Empty.absurd({{s == True{{}} : Bool}}, S.os.tf(ez))
    case False{{}}:
      e

def rs.go6_z(z: Bool, +s: Bool, +e: {{U.UdpHeader.verify.go(z, False{{}}, s) == True{{}} : Bool}}) -> {{z == False{{}} : Bool}}:
  match z:
    case True{{}}:
      Empty.absurd({{True{{}} == False{{}} : Bool}}, S.os.ft(e))
    case False{{}}:
      {{==}}

def rs.zf(+o: B.Octets, +c: U32, +hc: {{B.Octets.be16_at(o, 6n) == Some{{c}} : Maybe<&2, U32>}}) -> {{U.UdpHeader.zero_field(B.Octets.be16_at(o, 6n)) == U32.is_eq(c, 0) : Bool}}:
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(o, 6n), Some{{c}}, hc) : {{U.UdpHeader.zero_field(_) == U32.is_eq(c, 0) : Bool}}
  {{==}}

def rs.ne0(x: Nat, +h: {{Nat.is_eq(x, 0n) == False{{}} : Bool}}) -> {le("1n", "x")}:
  match x:
    case 0n:
      Empty.absurd({le("1n", "0n")}, S.os.tf(h))
    case 1n+ +p:
      S.os.le_zero(p)

def rs.add_d_zero(+x: Nat, +d: Nat, +e: {{Nat.add(x, d) == d : Nat}}) -> {{x == 0n : Nat}}:
  S.os.add_cancel_r(x, 0n, d, e)
""")
# UDP's fill with a nonzero verified field
O6 = "o"
S0 = "K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))"
CC = f"K.inet_finish({S0})"
VS0, VC, VCC = v(S0), v("c"), v(CC)
COM = "+f0: " + le(VS0, "d") + ", +fc: " + le(VC, "d") + ", +r2: {S.os.rep(d, Nat.add(" + VS0 + ", " + VC + ")) == d : Nat}, +e2: {Nat.add(" + VCC + ", " + VS0 + ") == d : Nat}"
COMA = "f0, fc, r2, e2"
q(f"""
# the field is not d: CC is c
def rs.nz.ne({DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +hne: {{Nat.is_eq({VC}, d) == False{{}} : Bool}}) -> {{{CC} == c : U32}}:
  UL.u32_value_eq({CC}, c, S.os.add_cancel_r({VCC}, {VC}, {VS0}, Equal.trans(Nat, Nat.add({VCC}, {VS0}), d, Nat.add({VC}, {VS0}), e2, Equal.trans(Nat, d, Nat.add({VS0}, {VC}), Nat.add({VC}, {VS0}), Equal.sym(Nat, Nat.add({VS0}, {VC}), d, S.os.rep_eq_d(d, hd, {VS0}, {VC}, f0, fc, hne, r2)), S.os.add_comm({VS0}, {VC})))))

# the field is d and the sum without it 0: CC is d, which is c
def rs.nz.s0z({DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +es: {{{VS0} == 0n : Nat}}, +ecd: {{{VC} == d : Nat}}, +ez: {{U32.is_eq({CC}, 0) == False{{}} : Bool}}) -> {{{CC} == c : U32}}:
  UL.u32_value_eq({CC}, c, Equal.trans(Nat, {VCC}, d, {VC}, Equal.trans(Nat, {VCC}, Nat.add({VCC}, 0n), d, Equal.sym(Nat, Nat.add({VCC}, 0n), {VCC}, S.os.add_zero({VCC})), Equal.trans(Nat, Nat.add({VCC}, 0n), Nat.add({VCC}, {VS0}), d, Equal.cong(Nat, Nat, z => Nat.add({VCC}, z), 0n, {VS0}, Equal.sym(Nat, {VS0}, 0n, es)), e2)), Equal.sym(Nat, {VC}, d, ecd)))

# the field is d and the sum without it not 0: then it is d, CC is 0
def rs.nz.s0p(+p: Nat, {DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +es: {{{VS0} == 1n+p : Nat}}, +ecd: {{{VC} == d : Nat}}, +ez: {{U32.is_eq({CC}, 0) == False{{}} : Bool}}) -> {{{CC} == c : U32}}:
  +ed = Equal.trans(Nat, {VS0}, S.os.rep(d, {VS0}), d, Equal.sym(Nat, S.os.rep(d, {VS0}), {VS0}, S.os.rep_small(d, {VS0}, f0)), Equal.trans(Nat, S.os.rep(d, {VS0}), S.os.rep(d, Nat.add({VS0}, d)), d, Equal.sym(Nat, S.os.rep(d, Nat.add({VS0}, d)), S.os.rep(d, {VS0}), S.os.rep_period(d, {VS0}, hd, Equal.trans(Bool, Nat.is_le(1n, {VS0}), Nat.is_le(1n, 1n+p), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(1n, z), {VS0}, 1n+p, es), S.os.le_zero(p)))), Equal.trans(Nat, S.os.rep(d, Nat.add({VS0}, d)), S.os.rep(d, Nat.add({VS0}, {VC})), d, Equal.cong(Nat, Nat, z => S.os.rep(d, Nat.add({VS0}, z)), d, {VC}, Equal.sym(Nat, {VC}, d, ecd)), r2)))
  +ec0 = rs.add_d_zero({VCC}, d, Equal.trans(Nat, Nat.add({VCC}, d), Nat.add({VCC}, {VS0}), d, Equal.cong(Nat, Nat, z => Nat.add({VCC}, z), d, {VS0}, Equal.sym(Nat, {VS0}, d, ed)), e2))
  Empty.absurd({{{CC} == c : U32}}, S.os.tf(Equal.trans(Bool, True{{}}, U32.is_eq({CC}, 0), False{{}}, Equal.sym(Bool, U32.is_eq({CC}, 0), True{{}}, Equal.trans(Bool, U32.is_eq({CC}, 0), Nat.is_eq({VCC}, {v("0")}), True{{}}, UL.u32_eq_value({CC}, 0), Equal.trans(Bool, Nat.is_eq({VCC}, {v("0")}), Nat.is_eq(0n, 0n), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, {v("0")}), {VCC}, 0n, ec0), {{==}}))), ez)))

def rs.nz.s0(s: Nat, {DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +es: {{{VS0} == s : Nat}}, +ecd: {{{VC} == d : Nat}}, +ez: {{U32.is_eq({CC}, 0) == False{{}} : Bool}}) -> {{{CC} == c : U32}}:
  match s:
    case 0n:
      rs.nz.s0z(d, hd, hD, hE, pseudo, o, c, {COMA}, es, ecd, ez)
    case 1n+ +p:
      rs.nz.s0p(p, d, hd, hD, hE, pseudo, o, c, {COMA}, es, ecd, ez)

def rs.nz.f(b: Bool, {DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +eb: {{Nat.is_eq({VC}, d) == b : Bool}}, +ez: {{U32.is_eq({CC}, 0) == False{{}} : Bool}}) -> {{{CC} == c : U32}}:
  match b:
    case False{{}}:
      rs.nz.ne(d, hd, hD, hE, pseudo, o, c, {COMA}, eb)
    case True{{}}:
      rs.nz.s0({VS0}, d, hd, hD, hE, pseudo, o, c, {COMA}, {{==}}, S.os.nat_eq({VC}, d, eb), ez)

# CC is 0, so 0xffff is written: then c is d
def rs.nz.t({DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +ez: {{U32.is_eq({CC}, 0) == True{{}} : Bool}}, +hk0: {{U32.is_eq(c, 0) == False{{}} : Bool}}) -> {{c == 65535 : U32}}:
  +ec0 = S.os.nat_eq({VCC}, {v("0")}, Equal.trans(Bool, Nat.is_eq({VCC}, {v("0")}), U32.is_eq({CC}, 0), True{{}}, Equal.sym(Bool, U32.is_eq({CC}, 0), Nat.is_eq({VCC}, {v("0")}), UL.u32_eq_value({CC}, 0)), ez))
  +ed = Equal.trans(Nat, {VS0}, Nat.add({VCC}, {VS0}), d, Equal.cong(Nat, Nat, z => Nat.add(z, {VS0}), 0n, {VCC}, Equal.sym(Nat, {VCC}, 0n, ec0)), e2)
  +h1 = rs.ne0({VC}, Equal.trans(Bool, Nat.is_eq({VC}, 0n), U32.is_eq(c, 0), False{{}}, Equal.sym(Bool, U32.is_eq(c, 0), Nat.is_eq({VC}, {v("0")}), UL.u32_eq_value(c, 0)), hk0))
  +ecd = Equal.trans(Nat, {VC}, S.os.rep(d, {VC}), d, Equal.sym(Nat, S.os.rep(d, {VC}), {VC}, S.os.rep_small(d, {VC}, fc)), Equal.trans(Nat, S.os.rep(d, {VC}), S.os.rep(d, Nat.add({VC}, d)), d, Equal.sym(Nat, S.os.rep(d, Nat.add({VC}, d)), S.os.rep(d, {VC}), S.os.rep_period(d, {VC}, hd, h1)), Equal.trans(Nat, S.os.rep(d, Nat.add({VC}, d)), S.os.rep(d, Nat.add({VS0}, {VC})), d, Equal.cong(Nat, Nat, z => S.os.rep(d, z), Nat.add({VC}, d), Nat.add({VS0}, {VC}), Equal.trans(Nat, Nat.add({VC}, d), Nat.add(d, {VC}), Nat.add({VS0}, {VC}), S.os.add_comm({VC}, d), Equal.cong(Nat, Nat, z => Nat.add(z, {VC}), d, {VS0}, Equal.sym(Nat, {VS0}, d, ed)))), r2)))
  UL.u32_value_eq(c, 65535, Equal.trans(Nat, {VC}, d, {v("65535")}, ecd, Equal.sym(Nat, {v("65535")}, d, hE)))

def rs.nz.go(z: Bool, {DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, {COM}, +ez: {{U32.is_eq({CC}, 0) == z : Bool}}, +es: {{K.inet_put16(o, 6n, c) == o : B.Octets}}, +hk0: {{U32.is_eq(c, 0) == False{{}} : Bool}}) -> {{K.inet_put16(o, 6n, U.UdpHeader.nonzero.go(z, {CC})) == o : B.Octets}}:
  match z:
    case False{{}}:
      %Equal.sym(U32, {CC}, c, rs.nz.f(Nat.is_eq({VC}, d), d, hd, hD, hE, pseudo, o, c, {COMA}, {{==}}, ez)) : {{K.inet_put16(o, 6n, _) == o : B.Octets}}
      es
    case True{{}}:
      %rs.nz.t(d, hd, hD, hE, pseudo, o, c, {COMA}, ez, hk0) : {{K.inet_put16(o, 6n, _) == o : B.Octets}}
      es

# UdpHeader.fill on a datagram verified with a nonzero field gives it back
def rs.fillnz_self({DPAR}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +eP: {{K.inet_even(pseudo) == True{{}} : Bool}}, +eT: {{K.inet_even(B.Octets.take(6n, o)) == True{{}} : Bool}}, +hc: {{B.Octets.be16_at(o, 6n) == Some{{c}} : Maybe<&2, U32>}}, +hl: {le("Nat.add(6n, 2n)", "B.Octets.len(o)")}, +hv: {{K.inet_verify(B.Octets.append(pseudo, o)) == True{{}} : Bool}}, +hk0: {{U32.is_eq(c, 0) == False{{}} : Bool}}) -> {{U.UdpHeader.fill(pseudo, o) == o : B.Octets}}:
  +f0 = S.os.sum0_fits(d, hd, hD, hE, pseudo, o, 6n, eP, eT)
  +fc = S.os.be16_fits(d, hD, o, 6n, c, hc)
  +r2 = S.os.verified_sum(d, hd, hD, hE, pseudo, o, 6n, c, eP, eT, hc, hl, hv)
  +e2 = S.os.finish_value(d, hD, {S0}, f0)
  rs.nz.go(U32.is_eq({CC}, 0), d, hd, hD, hE, pseudo, o, c, {COMA}, {{==}}, S.os.put16_self(o, 6n, c, hc, hl), hk0)
""")

# the laws
B4 = "I4.Ipv4Header.build(h)"
TK4 = "B.Octets.take(I4.Ipv4Header.length(h), o)"
q(f"""
# IPv4: parse_verified answered Done{{h}}: the parse did, and the header verified
def rs.pv_parse(r: Result<&2, &2, N.NetError, I4.Ipv4Header>, +o: B.Octets, +h: I4.Ipv4Header, +er: {{I4.Ipv4Header.parse(o) == r : Result<&2, &2, N.NetError, I4.Ipv4Header>}}, e: {{I4.Ipv4Header.parse_verified.go(r, o) == Done{{h}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}}) -> {{I4.Ipv4Header.parse(o) == Done{{h}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}}:
  match r:
    case Done{{+g}}:
      %RP.rv.check_done(I4.Ipv4Header, K.inet_verify(B.Octets.take(I4.Ipv4Header.length(g), o)), N.NetBadChecksum{{}}, g, h, e) : {{I4.Ipv4Header.parse(o) == Done{{_}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}}
      er
    case Fail{{x}}:
      %e : RP.rv.pick(I4.Ipv4Header, _, {{I4.Ipv4Header.parse(o) == Done{{h}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}}, Unit)
      Unit{{}}

def rs.pv_verify(r: Result<&2, &2, N.NetError, I4.Ipv4Header>, +o: B.Octets, +h: I4.Ipv4Header, +e: {{I4.Ipv4Header.parse_verified.go(r, o) == Done{{h}} : Result<&2, &2, N.NetError, I4.Ipv4Header>}}) -> {{K.inet_verify({TK4}) == True{{}} : Bool}}:
  match r:
    case Done{{+g}}:
      %RP.rv.check_done(I4.Ipv4Header, K.inet_verify(B.Octets.take(I4.Ipv4Header.length(g), o)), N.NetBadChecksum{{}}, g, h, e) : {{K.inet_verify(B.Octets.take(I4.Ipv4Header.length(_), o)) == True{{}} : Bool}}
      RP.rv.check_true(I4.Ipv4Header, K.inet_verify(B.Octets.take(I4.Ipv4Header.length(g), o)), N.NetBadChecksum{{}}, g, h, e)
    case Fail{{x}}:
      %e : RP.rv.pick(I4.Ipv4Header, _, {{K.inet_verify({TK4}) == True{{}} : Bool}}, Unit)
      Unit{{}}

def Laws.ipv4_reverse_checksum(o, h, c, e, hc, hk):
  +ep = rs.pv_parse(I4.Ipv4Header.parse(o), o, h, {{==}}, e)
  +ev = rs.pv_verify(I4.Ipv4Header.parse(o), o, h, e)
  +er = RL.ipv4_reverse(o, h, ep)
  +l20 = rs.ipv4_lb(h)
  +hn = rs.built_ge_n(Nat.add(10n, 2n), I4.Ipv4Header.length(h), {B4}, o, er, rs.lower(Nat.add(10n, 2n), 20n, B.Octets.len({B4}), {{==}}, l20))
  +hcB = Equal.trans(Maybe<&2, U32>, B.Octets.be16_at({B4}, 10n), B.Octets.be16_at({TK4}, 10n), Some{{c}}, Equal.cong(B.Octets, Maybe<&2, U32>, z => B.Octets.be16_at(z, 10n), {B4}, {TK4}, er), Equal.trans(Maybe<&2, U32>, B.Octets.be16_at({TK4}, 10n), B.Octets.be16_at(o, 10n), Some{{c}}, BL.octets_be16_at_take(I4.Ipv4Header.length(h), o, 10n, hn), hc))
  +hvB = Equal.trans(Bool, K.inet_verify(B.Octets.append({EMP}, {B4})), K.inet_verify({TK4}), True{{}}, Equal.cong(B.Octets, Bool, z => K.inet_verify(z), B.Octets.append({EMP}, {B4}), {TK4}, Equal.trans(B.Octets, B.Octets.append({EMP}, {B4}), {B4}, {TK4}, BL.octets_append_empty_l({B4}), er)), ev)
  %er : {{I4.Ipv4Header.build_checksum(h) == _ : B.Octets}}
  S.os.fill_self({DA4}, {EMP}, {B4}, 10n, c, {{==}}, S.os.even_take({B4}, 5n, rs.lower(Nat.double(5n), 20n, B.Octets.len({B4}), {{==}}, l20)), hcB, rs.lower(Nat.add(10n, 2n), 20n, B.Octets.len({B4}), {{==}}, l20), hvB, hk)
""")
BI = "C.IcmpHeader.build(h)"
q(f"""
def Laws.icmp_reverse_checksum(o, h, c, e, ev, hc, hk):
  +er = RL.icmp_reverse(o, h, e)
  +l8 = rs.built_ge(8n, 8n, {BI}, o, er, rs.icmp_lb(h))
  %Equal.sym(B.Octets, B.Octets.append({BI}, B.Octets.drop(8n, o)), o, rs.rejoin({BI}, 8n, o, er)) : {{K.inet_fill({EMP}, _, 2n) == o : B.Octets}}
  S.os.fill_self({DA4}, {EMP}, o, 2n, c, {{==}}, S.os.even_take(o, 1n, rs.lower(Nat.double(1n), 8n, B.Octets.len(o), {{==}}, l8)), hc, rs.lower(Nat.add(2n, 2n), 8n, B.Octets.len(o), {{==}}, l8), Equal.trans(Bool, K.inet_verify(B.Octets.append({EMP}, o)), K.inet_verify(o), True{{}}, Equal.cong(B.Octets, Bool, z => K.inet_verify(z), B.Octets.append({EMP}, o), o, BL.octets_append_empty_l(o)), ev), hk)
""")
BU = "U.UdpHeader.build(h)"
for fam, PS, ver_go in [("4", "I4.ipv4_pseudo(src, dst, 17, N.net.len32(dg))", "4"), ("6", "I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17)", "6")]:
    EVP = (f"SP.h.pseudo4_even(src, dst, 17, U32.from_nat(B.Octets.len(dg)))" if fam == "4"
           else f"SP.h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(dg)), 17)")
    PSX = PS.replace("N.net.len32(dg)", "N.net.len32(_)")
    if fam == "4":
        hk_expr = "hk"
        sz = f"rs.go_s(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), True{{}}, K.inet_verify(B.Octets.append({PS}, dg)), Equal.trans(Bool, U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), U32.is_eq(c, 0), False{{}}, rs.zf(dg, c, hc), hk), ev)"
        args = "src, dst, dg, h, c, e, ev, hc, hk"
        pre = ""
    else:
        pre = f"  +hk = Equal.trans(Bool, U32.is_eq(c, 0), U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), False{{}}, Equal.sym(Bool, U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), U32.is_eq(c, 0), rs.zf(dg, c, hc)), rs.go6_z(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), K.inet_verify(B.Octets.append({PS}, dg)), ev))\n"
        hk_expr = "hk"
        sz = f"rs.go_s(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), False{{}}, K.inet_verify(B.Octets.append({PS}, dg)), rs.go6_z(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), K.inet_verify(B.Octets.append({PS}, dg)), ev), ev)"
        args = "src, dst, dg, h, c, e, ev, hc"
    q(f"""
def Laws.udp_ipv{fam}_reverse_checksum({args}):
  +er = RL.udp_reverse(dg, h, e)
  +l8 = rs.built_ge(8n, 8n, {BU}, dg, er, rs.udp_lb(h))
{pre}  %Equal.sym(B.Octets, B.Octets.append({BU}, B.Octets.drop(8n, dg)), dg, rs.rejoin({BU}, 8n, dg, er)) : {{U.UdpHeader.fill({PSX.replace("_", "_")}, _) == dg : B.Octets}}
  rs.fillnz_self({DA4}, {PS}, dg, c, {EVP}, S.os.even_take(dg, 3n, rs.lower(Nat.double(3n), 8n, B.Octets.len(dg), {{==}}, l8)), hc, rs.lower(Nat.add(6n, 2n), 8n, B.Octets.len(dg), {{==}}, l8), {sz}, {hk_expr})
""")
BT = "T.TcpHeader.build(h)"
for fam, PS in [("4", "I4.ipv4_pseudo(src, dst, 6, N.net.len32(seg))"), ("6", "I6.ipv6_pseudo(src, dst, N.net.len32(seg), 6)")]:
    EVP = (f"SP.h.pseudo4_even(src, dst, 6, U32.from_nat(B.Octets.len(seg)))" if fam == "4"
           else f"SP.h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(seg)), 6)")
    PSX = PS.replace("N.net.len32(seg)", "N.net.len32(_)")
    q(f"""
def Laws.tcp_ipv{fam}_reverse_checksum(src, dst, seg, h, c, e, ev, hc, hk):
  +er = RL.tcp_reverse(seg, h, e)
  +l20 = rs.built_ge(20n, T.TcpHeader.length(h), {BT}, seg, er, rs.tcp_lb(h))
  %Equal.sym(B.Octets, B.Octets.append({BT}, B.Octets.drop(T.TcpHeader.length(h), seg)), seg, rs.rejoin({BT}, T.TcpHeader.length(h), seg, er)) : {{K.inet_fill({PSX}, _, 16n) == seg : B.Octets}}
  S.os.fill_self({DA4}, {PS}, seg, 16n, c, {EVP}, S.os.even_take(seg, 8n, rs.lower(Nat.double(8n), 20n, B.Octets.len(seg), {{==}}, l20)), hc, rs.lower(Nat.add(16n, 2n), 20n, B.Octets.len(seg), {{==}}, l20), ev, hk)
""")

out = "".join(P).rstrip() + chr(10)
outs = {"PROOF_rev.bend": out, "PROOF_revsum.bend": "".join(Q).rstrip() + chr(10)}
if "--check" in sys.argv[1:]:
    stale = [p for p, t in outs.items() if open(p, encoding="utf-8").read() != t]
    if stale:
        print("differ from what ref/gen_rev.py generates: " + " ".join(stale))
        sys.exit(1)
    print("PROOF_rev.bend and PROOF_revsum.bend are up to date")
else:
    for p, t in outs.items():
        with open(p, "w", encoding="utf-8", newline=chr(10)) as f:
            f.write(t)
