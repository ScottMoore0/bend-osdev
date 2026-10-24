# Writes tcpip/PROOF_packet.bend, the proofs of LAWS_packet.bend (run from
# tcpip/):
#   python3 ref/gen_packet.py           rewrite PROOF_packet.bend
#   python3 ref/gen_packet.py --check   only check that it is up to date
# The deep patterns (a word split into its bits) are generated; the
# reasoning is in the comments it writes out.
import sys

def pat(n, k):
    """a U32 split into its low k bits (n0 .. n{k-1}) and, if k < 32, the rest."""
    s = "".join("WCon{%s%d, " % (n, i) for i in range(k))
    tail = "WNil{}" if k == 32 else n + "h"
    return "U32{" + s + tail + "}" * k + "}"

P = []
w = P.append
Z16 = "Word.zero(16n)"
def lo(x): return "tp.lo16(%s)" % x
def mk(a, b): return "tp.mk(%s, %s)" % (a, b)

w(f"""# Proofs of LAWS_packet.bend, written by ref/gen_packet.py.
#
# How the proofs go. The sender's bytes carry a checksum written by
# bend-osdev-netheaders (inet_fill, or UDP's fill); its laws say those bytes
# verify (LAWS_sum.bend: icmp_build_verifies, udp_ipv4_build_verifies), that
# the header parses back with the field written (icmp_put_parse,
# udp_put_parse), and that the bytes past the field, and UDP's payload, read
# back (inet_put16_drop, udp_put_payload). What is left is ICMP's 32-bit
# rest-of-header: the identifier and sequence number are packed as
# (id & 0xffff) << 16 | (seq & 0xffff) and read back with a shift and a mask,
# shown here on the words' halves (tp.rest_form: the packed word is the two
# low halves joined), by computation on their bits.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../netheaders/netheaders.bend as N
import ../netheaders/checksum.bend as K
import ../netheaders/ipv4.bend as I4
import ../netheaders/icmp.bend as NI
import ../netheaders/udp.bend as NU
import ../netheaders/LAWS_sum.bend as NS
import ../netheaders/PROOF_sum.bend as NSP
import ./udp.bend as U
import ./icmp.bend as IC
import ./LAWS_packet.bend as Laws

# Words in 16-bit halves

def tp.lo16(s: U32) -> Word(16n):
  match s:
    case U32{{w}}:
      W.W64.bits.lo(16n, 16n, w)

def tp.mk(a: Word(16n), b: Word(16n)) -> U32:
  U32{{W.W64.bits.cat(16n, 16n, a, b)}}

def tp.and_comm_w(n: Nat, a: Word(n), b: Word(n)) -> {{Word.and(n, a, b) == Word.and(n, b, a) : Word(n)}}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      match a b:
        case WCon{{False{{}}, +at}} WCon{{False{{}}, +bt}}:
          %tp.and_comm_w(p, at, bt) : {{WCon{{False{{}}, Word.and(p, at, bt)}} == WCon{{False{{}}, _}} : Word(1n+p)}}
          {{==}}
        case WCon{{False{{}}, +at}} WCon{{True{{}}, +bt}}:
          %tp.and_comm_w(p, at, bt) : {{WCon{{False{{}}, Word.and(p, at, bt)}} == WCon{{False{{}}, _}} : Word(1n+p)}}
          {{==}}
        case WCon{{True{{}}, +at}} WCon{{False{{}}, +bt}}:
          %tp.and_comm_w(p, at, bt) : {{WCon{{False{{}}, Word.and(p, at, bt)}} == WCon{{False{{}}, _}} : Word(1n+p)}}
          {{==}}
        case WCon{{True{{}}, +at}} WCon{{True{{}}, +bt}}:
          %tp.and_comm_w(p, at, bt) : {{WCon{{True{{}}, Word.and(p, at, bt)}} == WCon{{True{{}}, _}} : Word(1n+p)}}
          {{==}}

def tp.and_comm(a: U32, b: U32) -> {{U32.and(a, b) == U32.and(b, a) : U32}}:
  match a b:
    case U32{{+x}} U32{{+y}}:
      %tp.and_comm_w(32n, x, y) : {{U32{{Word.and(32n, x, y)}} == U32{{_}} : U32}}
      {{==}}

def tp.or_zero_r(n: Nat, a: Word(n)) -> {{Word.or(n, a, Word.zero(n)) == a : Word(n)}}:
  match n:
    case 0n:
      match a:
        case WNil{{}}:
          {{==}}
    case 1n+ +p:
      match a:
        case WCon{{False{{}}, +t}}:
          %Equal.sym(Word(p), Word.or(p, t, Word.zero(p)), t, tp.or_zero_r(p, t)) : {{WCon{{False{{}}, _}} == WCon{{False{{}}, t}} : Word(1n+p)}}
          {{==}}
        case WCon{{True{{}}, +t}}:
          %Equal.sym(Word(p), Word.or(p, t, Word.zero(p)), t, tp.or_zero_r(p, t)) : {{WCon{{True{{}}, _}} == WCon{{True{{}}, t}} : Word(1n+p)}}
          {{==}}

# the or of a high half and a low half is the two halves joined
def tp.or_cat(m: Nat, +n: Nat, +A: Word(n), b: Word(m)) -> {{Word.or(Nat.add(m, n), W.W64.bits.cat(m, n, Word.zero(m), A), W.W64.bits.cat(m, n, b, Word.zero(n))) == W.W64.bits.cat(m, n, b, A) : Word(Nat.add(m, n))}}:
  match m:
    case 0n:
      tp.or_zero_r(n, A)
    case 1n+ +p:
      match b:
        case WCon{{+x, +t}}:
          %Equal.sym(Word(Nat.add(p, n)), Word.or(Nat.add(p, n), W.W64.bits.cat(p, n, Word.zero(p), A), W.W64.bits.cat(p, n, t, Word.zero(n))), W.W64.bits.cat(p, n, t, A), tp.or_cat(p, n, A, t)) : {{WCon{{x, _}} == WCon{{x, W.W64.bits.cat(p, n, t, A)}} : Word(1n+Nat.add(p, n))}}
          {{==}}

def tp.lo_cat(m: Nat, +n: Nat, a: Word(m), +b: Word(n)) -> {{W.W64.bits.lo(m, n, W.W64.bits.cat(m, n, a, b)) == a : Word(m)}}:
  match m:
    case 0n:
      match a:
        case WNil{{}}:
          {{==}}
    case 1n+ +p:
      match a:
        case WCon{{+x, +t}}:
          %Equal.sym(Word(p), W.W64.bits.lo(p, n, W.W64.bits.cat(p, n, t, b)), t, tp.lo_cat(p, n, t, b)) : {{WCon{{x, _}} == WCon{{x, t}} : Word(1n+p)}}
          {{==}}

def tp.lo_mk(+a: Word(16n), +b: Word(16n)) -> {{{lo(mk("a", "b"))} == a : Word(16n)}}:
  tp.lo_cat(16n, 16n, a, b)

def tp.and_mask(x: U32) -> {{U32.and(65535, x) == {mk(lo("x"), Z16)} : U32}}:
  match x:
    case {pat("x", 32)}:
      {{==}}

def tp.and16(+x: U32) -> {{U32.and(x, 65535) == {mk(lo("x"), Z16)} : U32}}:
  %tp.and_comm(65535, x) : {{_ == {mk(lo("x"), Z16)} : U32}}
  tp.and_mask(x)

def tp.shl16(x: U32) -> {{U32.shln({mk(lo("x"), Z16)}, 16n) == {mk(Z16, lo("x"))} : U32}}:
  match x:
    case {pat("x", 16)}:
      {{==}}

def tp.shr_back(x: U32, y: U32) -> {{U32.shrn({mk(lo("x"), lo("y"))}, 16n) == {mk(lo("y"), Z16)} : U32}}:
  match x y:
    case {pat("x", 16)} {pat("y", 16)}:
      {{==}}

def tp.and_back.m(x: U32, y: U32) -> {{U32.and(65535, {mk(lo("x"), lo("y"))}) == {mk(lo("x"), Z16)} : U32}}:
  match x y:
    case {pat("x", 16)} {pat("y", 16)}:
      {{==}}

def tp.and_back(+x: U32, +y: U32) -> {{U32.and({mk(lo("x"), lo("y"))}, 65535) == {mk(lo("x"), Z16)} : U32}}:
  %tp.and_comm(65535, {mk(lo("x"), lo("y"))}) : {{_ == {mk(lo("x"), Z16)} : U32}}
  tp.and_back.m(x, y)

# ICMP's rest-of-header for an echo: the low halves of seq and id, joined
def tp.rest_form(+id: U32, +seq: U32) -> {{IC.Icmp.rest(id, seq) == {mk(lo("seq"), lo("id"))} : U32}}:
  %Equal.sym(U32, U32.and(id, 65535), {mk(lo("id"), Z16)}, tp.and16(id)) : {{U32.or(U32.shln(_, 16n), U32.and(seq, 65535)) == {mk(lo("seq"), lo("id"))} : U32}}
  %Equal.sym(U32, U32.shln({mk(lo("id"), Z16)}, 16n), {mk(Z16, lo("id"))}, tp.shl16(id)) : {{U32.or(_, U32.and(seq, 65535)) == {mk(lo("seq"), lo("id"))} : U32}}
  %Equal.sym(U32, U32.and(seq, 65535), {mk(lo("seq"), Z16)}, tp.and16(seq)) : {{U32.or({mk(Z16, lo("id"))}, _) == {mk(lo("seq"), lo("id"))} : U32}}
  Equal.cong(Word(32n), U32, z => U32{{z}}, Word.or(32n, W.W64.bits.cat(16n, 16n, {Z16}, {lo("id")}), W.W64.bits.cat(16n, 16n, {lo("seq")}, {Z16})), W.W64.bits.cat(16n, 16n, {lo("seq")}, {lo("id")}), tp.or_cat(16n, 16n, {lo("id")}, {lo("seq")}))

def tp.shr_rest(+id: U32, +seq: U32) -> {{U32.shrn(IC.Icmp.rest(id, seq), 16n) == U32.and(id, 65535) : U32}}:
  %Equal.sym(U32, IC.Icmp.rest(id, seq), {mk(lo("seq"), lo("id"))}, tp.rest_form(id, seq)) : {{U32.shrn(_, 16n) == U32.and(id, 65535) : U32}}
  %Equal.sym(U32, U32.and(id, 65535), {mk(lo("id"), Z16)}, tp.and16(id)) : {{U32.shrn({mk(lo("seq"), lo("id"))}, 16n) == _ : U32}}
  tp.shr_back(seq, id)

def tp.and_rest(+id: U32, +seq: U32) -> {{U32.and(IC.Icmp.rest(id, seq), 65535) == U32.and(seq, 65535) : U32}}:
  %Equal.sym(U32, IC.Icmp.rest(id, seq), {mk(lo("seq"), lo("id"))}, tp.rest_form(id, seq)) : {{U32.and(_, 65535) == U32.and(seq, 65535) : U32}}
  %Equal.sym(U32, U32.and(seq, 65535), {mk(lo("seq"), Z16)}, tp.and16(seq)) : {{U32.and({mk(lo("seq"), lo("id"))}, 65535) == _ : U32}}
  tp.and_back(seq, id)

# masking id and seq first packs the same word
def tp.rest_mask(+id: U32, +seq: U32) -> {{IC.Icmp.rest(U32.and(id, 65535), U32.and(seq, 65535)) == IC.Icmp.rest(id, seq) : U32}}:
  %Equal.sym(U32, IC.Icmp.rest(U32.and(id, 65535), U32.and(seq, 65535)), {mk(lo("U32.and(seq, 65535)"), lo("U32.and(id, 65535)"))}, tp.rest_form(U32.and(id, 65535), U32.and(seq, 65535))) : {{_ == IC.Icmp.rest(id, seq) : U32}}
  %Equal.sym(U32, IC.Icmp.rest(id, seq), {mk(lo("seq"), lo("id"))}, tp.rest_form(id, seq)) : {{{mk(lo("U32.and(seq, 65535)"), lo("U32.and(id, 65535)"))} == _ : U32}}
  %Equal.sym(U32, U32.and(seq, 65535), {mk(lo("seq"), Z16)}, tp.and16(seq)) : {{tp.mk(tp.lo16(_), {lo("U32.and(id, 65535)")}) == {mk(lo("seq"), lo("id"))} : U32}}
  %Equal.sym(Word(16n), {lo(mk(lo("seq"), Z16))}, {lo("seq")}, tp.lo_mk({lo("seq")}, {Z16})) : {{tp.mk(_, {lo("U32.and(id, 65535)")}) == {mk(lo("seq"), lo("id"))} : U32}}
  %Equal.sym(U32, U32.and(id, 65535), {mk(lo("id"), Z16)}, tp.and16(id)) : {{tp.mk({lo("seq")}, tp.lo16(_)) == {mk(lo("seq"), lo("id"))} : U32}}
  %Equal.sym(Word(16n), {lo(mk(lo("id"), Z16))}, {lo("id")}, tp.lo_mk({lo("id")}, {Z16})) : {{tp.mk({lo("seq")}, _) == {mk(lo("seq"), lo("id"))} : U32}}
  {{==}}

# Lengths of ICMP headers

def tp.icmp_blen(h: NI.IcmpHeader) -> {{B.len(NI.IcmpHeader.build.list(h)) == 8n : Nat}}:
  match h:
    case NI.IcmpHeader{{U32{{a}}, U32{{b}}, U32{{c}}, U32{{d}}}}:
      {{==}}

def tp.icmp_len_build(+h: NI.IcmpHeader) -> {{B.Octets.len(NI.IcmpHeader.build(h)) == 8n : Nat}}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(NI.IcmpHeader.build.list(h))), B.len(NI.IcmpHeader.build.list(h)), BL.octets_len_of_list(NI.IcmpHeader.build.list(h))) : {{_ == 8n : Nat}}
  tp.icmp_blen(h)

def tp.icmp_mlen(+h: NI.IcmpHeader, +data: B.Octets) -> {{Nat.is_le(Nat.add(2n, 2n), B.Octets.len(B.Octets.append(NI.IcmpHeader.build(h), data))) == True{{}} : Bool}}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(NI.IcmpHeader.build(h), data)), Nat.add(B.Octets.len(NI.IcmpHeader.build(h)), B.Octets.len(data)), BL.octets_len_append(NI.IcmpHeader.build(h), data)) : {{Nat.is_le(Nat.add(2n, 2n), _) == True{{}} : Bool}}
  %Equal.sym(Nat, B.Octets.len(NI.IcmpHeader.build(h)), 8n, tp.icmp_len_build(h)) : {{Nat.is_le(Nat.add(2n, 2n), Nat.add(_, B.Octets.len(data))) == True{{}} : Bool}}
  {{==}}

# the data past the 8-byte header, whatever checksum was written
def tp.icmp_drop8(+h: NI.IcmpHeader, +data: B.Octets, +c: U32) -> {{B.Octets.drop(8n, K.inet_put16(B.Octets.append(NI.IcmpHeader.build(h), data), 2n, c)) == data : B.Octets}}:
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16(B.Octets.append(NI.IcmpHeader.build(h), data), 2n, c)), B.Octets.drop(8n, B.Octets.append(NI.IcmpHeader.build(h), data)), NS.inet_put16_drop(B.Octets.append(NI.IcmpHeader.build(h), data), 2n, c, 8n, {{==}}, tp.icmp_mlen(h, data))) : {{_ == data : B.Octets}}
  %tp.icmp_len_build(h) : {{B.Octets.drop(_, B.Octets.append(NI.IcmpHeader.build(h), data)) == data : B.Octets}}
  BL.octets_drop_append(NI.IcmpHeader.build(h), data)
""")

# ICMP: decoding an echo's bytes
for law, ctor, t in [("icmp_decode_request", "IC.IcmpEchoRequest", "8"), ("icmp_decode_reply", "IC.IcmpEchoReply", "0")]:
    R = "IC.Icmp.rest(id, seq)"
    H = f"NI.IcmpHeader{{{t}, 0, 0, {R}}}"
    M = f"B.Octets.append(NI.IcmpHeader.build({H}), data)"
    CK = f"K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16({M}, 2n, 0)))"
    E = f"IC.Icmp.encode({ctor}{{id, seq, data}})"
    HN = f"NI.IcmpHeader.norm(NI.IcmpHeader{{{t}, 0, {CK}, {R}}})"
    RHS = f"Done{{{ctor}{{U32.and(id, 65535), U32.and(seq, 65535), data}}}}"
    RES = "Result<&2, &2, IC.IcmpError, IC.IcmpMsg>"
    w(f"""
def Laws.{law}(id, seq, data):
  %Equal.sym(Bool, NI.IcmpHeader.verify(NI.IcmpHeader.build_checksum({H}, data)), True{{}}, NS.icmp_build_verifies({H}, data)) : {{IC.Icmp.decode.go(_, NI.IcmpHeader.parse({E}), {E}) == {RHS} : {RES}}}
  %Equal.sym(Result<&2, &2, N.NetError, NI.IcmpHeader>, NI.IcmpHeader.parse(K.inet_put16({M}, 2n, {CK})), Done{{{HN}}}, NS.icmp_put_parse({t}, 0, 0, {R}, data, {CK})) : {{IC.Icmp.decode.go(True{{}}, _, {E}) == {RHS} : {RES}}}
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16({M}, 2n, {CK})), data, tp.icmp_drop8({H}, data, {CK})) : {{Done{{IC.Icmp.of_header({HN}, _)}} == {RHS} : {RES}}}
  %Equal.sym(U32, U32.shrn({R}, 16n), U32.and(id, 65535), tp.shr_rest(id, seq)) : {{Done{{{ctor}{{_, U32.and({R}, 65535), data}}}} == {RHS} : {RES}}}
  %Equal.sym(U32, U32.and({R}, 65535), U32.and(seq, 65535), tp.and_rest(id, seq)) : {{Done{{{ctor}{{U32.and(id, 65535), _, data}}}} == {RHS} : {RES}}}
  {{==}}
""")

ST0 = "IC.IcmpState{IC.IcmpOptions{True{}}}"
REQ = "IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})"
RQD = "Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}}"
LST = "List<&2, IC.IcmpAction>"
BC = lambda r: f"NI.IcmpHeader.build_checksum(NI.IcmpHeader{{0, 0, 0, {r}}}, data)"
w(f"""
# ICMP: an echo request's bytes answered by an echo reply's

def Laws.icmp_echo_packet_answered(src, dst, id, seq, data):
  %Equal.sym(Result<&2, &2, IC.IcmpError, IC.IcmpMsg>, IC.Icmp.decode({REQ}), {RQD}, Laws.icmp_decode_request(id, seq, data)) : {{Pair.snd(IC.IcmpState, {LST}, IC.Icmp.recv({ST0}, src, _)) == [IC.IcmpOut{{src, IC.Icmp.encode(IC.IcmpEchoReply{{id, seq, data}})}}] : {LST}}}
  %Equal.cong(U32, B.Octets, z => {BC("z")}, IC.Icmp.rest(U32.and(id, 65535), U32.and(seq, 65535)), IC.Icmp.rest(id, seq), tp.rest_mask(id, seq)) : {{Pair.snd(IC.IcmpState, {LST}, IC.Icmp.recv({ST0}, src, {RQD})) == [IC.IcmpOut{{src, _}}] : {LST}}}
  {{==}}

def tp.reply_rep(st: IC.IcmpState, +src: U32, +dst: U32, +id: U32, +seq: U32, +data: B.Octets) -> {{Pair.snd(IC.IcmpState, {LST}, IC.Icmp.step(st, IC.IcmpRecv{{src, dst, IC.Icmp.encode(IC.IcmpEchoReply{{id, seq, data}})}})) == [IC.IcmpEchoed{{src, U32.and(id, 65535), U32.and(seq, 65535), data}}] : {LST}}}:
  match st:
    case IC.IcmpState{{IC.IcmpOptions{{ae}}}}:
      %Equal.sym(Result<&2, &2, IC.IcmpError, IC.IcmpMsg>, IC.Icmp.decode(IC.Icmp.encode(IC.IcmpEchoReply{{id, seq, data}})), Done{{IC.IcmpEchoReply{{U32.and(id, 65535), U32.and(seq, 65535), data}}}}, Laws.icmp_decode_reply(id, seq, data)) : {{Pair.snd(IC.IcmpState, {LST}, IC.Icmp.recv(IC.IcmpState{{IC.IcmpOptions{{ae}}}}, src, _)) == [IC.IcmpEchoed{{src, U32.and(id, 65535), U32.and(seq, 65535), data}}] : {LST}}}
      {{==}}

def Laws.icmp_reply_packet_reported(st, src, dst, id, seq, data):
  tp.reply_rep(st, src, dst, id, seq, data)
""")

H = "NU.UdpHeader{sport, dport, length, checksum}"
DG0 = f"B.Octets.append(NU.UdpHeader.build({H}), data)"
PS = f"I4.ipv4_pseudo(src, dst, 17, N.net.len32({DG0}))"
NZ = f"NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append({PS}, K.inet_put16({DG0}, 6n, 0))))"
BUILT = f"NU.UdpHeader.build_ipv4(src, dst, {H}, data)"
HN = f"NU.UdpHeader.norm(NU.UdpHeader{{sport, dport, length, {NZ}}})"
RHS = "U.Udp.receive(st, src, dst, N.NetField.low(16n, sport), N.NetField.low(16n, dport), data)"
UL_ = "List<&2, U.UdpAction>"
w(f"""
# UDP: a datagram's bytes received

def Laws.udp_packet_received(st, src, dst, sport, dport, length, checksum, data, hl):
  %Equal.sym(Bool, NU.UdpHeader.verify_ipv4(src, dst, {BUILT}), True{{}}, NS.udp_ipv4_build_verifies(src, dst, {H}, data)) : {{U.Udp.recv.go(_, st, src, dst, {BUILT}) == {RHS} : {UL_}}}
  %Equal.sym(Result<&2, &2, N.NetError, NU.UdpHeader>, NU.UdpHeader.parse(K.inet_put16({DG0}, 6n, {NZ})), Done{{{HN}}}, NS.udp_put_parse(sport, dport, length, checksum, data, {NZ})) : {{U.Udp.recv.header(_, st, src, dst, {BUILT}) == {RHS} : {UL_}}}
  %Equal.sym(Result<&2, &2, N.NetError, B.Octets>, NU.UdpHeader.payload({HN}, K.inet_put16({DG0}, 6n, {NZ})), Done{{data}}, NS.udp_put_payload(sport, dport, length, checksum, data, {NZ}, hl)) : {{U.Udp.recv.payload(_, st, src, dst, {HN}) == {RHS} : {UL_}}}
  {{==}}

def Laws.udp_packet_received_sat():
  {{==}}
""")

out = "".join(P).rstrip() + chr(10)
if "--check" in sys.argv[1:]:
    if open("PROOF_packet.bend", encoding="utf-8").read() != out:
        print("PROOF_packet.bend differs from what ref/gen_packet.py generates")
        sys.exit(1)
    print("PROOF_packet.bend is up to date")
else:
    with open("PROOF_packet.bend", "w", encoding="utf-8", newline=chr(10)) as f:
        f.write(out)
