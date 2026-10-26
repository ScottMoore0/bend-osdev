# Proofs of LAWS_packet.bend, written by ref/gen_packet.py.
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
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Words in 16-bit halves

def tp.lo16(s: U32) -> Word(16n):
  match s:
    case U32{w}:
      W.W64.bits.lo(16n, 16n, w)

def tp.mk(a: Word(16n), b: Word(16n)) -> U32:
  U32{W.W64.bits.cat(16n, 16n, a, b)}

def tp.or_zero_r(n: Nat, a: Word(n)) -> {Word.or(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+ +p:
      match a:
        case WCon{False{}, +t}:
          %Equal.sym(Word(p), Word.or(p, t, Word.zero(p)), t, tp.or_zero_r(p, t)) : {WCon{False{}, _} == WCon{False{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(p), Word.or(p, t, Word.zero(p)), t, tp.or_zero_r(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}

# the or of a high half and a low half is the two halves joined
def tp.or_cat(m: Nat, +n: Nat, +A: Word(n), b: Word(m)) -> {Word.or(Nat.add(m, n), W.W64.bits.cat(m, n, Word.zero(m), A), W.W64.bits.cat(m, n, b, Word.zero(n))) == W.W64.bits.cat(m, n, b, A) : Word(Nat.add(m, n))}:
  match m:
    case 0n:
      tp.or_zero_r(n, A)
    case 1n+ +p:
      match b:
        case WCon{+x, +t}:
          %Equal.sym(Word(Nat.add(p, n)), Word.or(Nat.add(p, n), W.W64.bits.cat(p, n, Word.zero(p), A), W.W64.bits.cat(p, n, t, Word.zero(n))), W.W64.bits.cat(p, n, t, A), tp.or_cat(p, n, A, t)) : {WCon{x, _} == WCon{x, W.W64.bits.cat(p, n, t, A)} : Word(1n+Nat.add(p, n))}
          {==}

def tp.lo_cat(m: Nat, +n: Nat, a: Word(m), +b: Word(n)) -> {W.W64.bits.lo(m, n, W.W64.bits.cat(m, n, a, b)) == a : Word(m)}:
  match m:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+ +p:
      match a:
        case WCon{+x, +t}:
          %Equal.sym(Word(p), W.W64.bits.lo(p, n, W.W64.bits.cat(p, n, t, b)), t, tp.lo_cat(p, n, t, b)) : {WCon{x, _} == WCon{x, t} : Word(1n+p)}
          {==}

def tp.lo_mk(+a: Word(16n), +b: Word(16n)) -> {tp.lo16(tp.mk(a, b)) == a : Word(16n)}:
  tp.lo_cat(16n, 16n, a, b)

def tp.and_mask(x: U32) -> {U32.and(65535, x) == tp.mk(tp.lo16(x), Word.zero(16n)) : U32}:
  match x:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def tp.and16(+x: U32) -> {U32.and(x, 65535) == tp.mk(tp.lo16(x), Word.zero(16n)) : U32}:
  %UL.u32_and_comm(65535, x) : {_ == tp.mk(tp.lo16(x), Word.zero(16n)) : U32}
  tp.and_mask(x)

def tp.shl16(x: U32) -> {U32.shln(tp.mk(tp.lo16(x), Word.zero(16n)), 16n) == tp.mk(Word.zero(16n), tp.lo16(x)) : U32}:
  match x:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, xh}}}}}}}}}}}}}}}}}:
      {==}

def tp.shr_back(x: U32, y: U32) -> {U32.shrn(tp.mk(tp.lo16(x), tp.lo16(y)), 16n) == tp.mk(tp.lo16(y), Word.zero(16n)) : U32}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, xh}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, yh}}}}}}}}}}}}}}}}}:
      {==}

def tp.and_back.m(x: U32, y: U32) -> {U32.and(65535, tp.mk(tp.lo16(x), tp.lo16(y))) == tp.mk(tp.lo16(x), Word.zero(16n)) : U32}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, xh}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, yh}}}}}}}}}}}}}}}}}:
      {==}

def tp.and_back(+x: U32, +y: U32) -> {U32.and(tp.mk(tp.lo16(x), tp.lo16(y)), 65535) == tp.mk(tp.lo16(x), Word.zero(16n)) : U32}:
  %UL.u32_and_comm(65535, tp.mk(tp.lo16(x), tp.lo16(y))) : {_ == tp.mk(tp.lo16(x), Word.zero(16n)) : U32}
  tp.and_back.m(x, y)

# ICMP's rest-of-header for an echo: the low halves of seq and id, joined
def tp.rest_form(+id: U32, +seq: U32) -> {IC.Icmp.rest(id, seq) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}:
  %Equal.sym(U32, U32.and(id, 65535), tp.mk(tp.lo16(id), Word.zero(16n)), tp.and16(id)) : {U32.or(U32.shln(_, 16n), U32.and(seq, 65535)) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  %Equal.sym(U32, U32.shln(tp.mk(tp.lo16(id), Word.zero(16n)), 16n), tp.mk(Word.zero(16n), tp.lo16(id)), tp.shl16(id)) : {U32.or(_, U32.and(seq, 65535)) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  %Equal.sym(U32, U32.and(seq, 65535), tp.mk(tp.lo16(seq), Word.zero(16n)), tp.and16(seq)) : {U32.or(tp.mk(Word.zero(16n), tp.lo16(id)), _) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  Equal.cong(Word(32n), U32, z => U32{z}, Word.or(32n, W.W64.bits.cat(16n, 16n, Word.zero(16n), tp.lo16(id)), W.W64.bits.cat(16n, 16n, tp.lo16(seq), Word.zero(16n))), W.W64.bits.cat(16n, 16n, tp.lo16(seq), tp.lo16(id)), tp.or_cat(16n, 16n, tp.lo16(id), tp.lo16(seq)))

def tp.shr_rest(+id: U32, +seq: U32) -> {U32.shrn(IC.Icmp.rest(id, seq), 16n) == U32.and(id, 65535) : U32}:
  %Equal.sym(U32, IC.Icmp.rest(id, seq), tp.mk(tp.lo16(seq), tp.lo16(id)), tp.rest_form(id, seq)) : {U32.shrn(_, 16n) == U32.and(id, 65535) : U32}
  %Equal.sym(U32, U32.and(id, 65535), tp.mk(tp.lo16(id), Word.zero(16n)), tp.and16(id)) : {U32.shrn(tp.mk(tp.lo16(seq), tp.lo16(id)), 16n) == _ : U32}
  tp.shr_back(seq, id)

def tp.and_rest(+id: U32, +seq: U32) -> {U32.and(IC.Icmp.rest(id, seq), 65535) == U32.and(seq, 65535) : U32}:
  %Equal.sym(U32, IC.Icmp.rest(id, seq), tp.mk(tp.lo16(seq), tp.lo16(id)), tp.rest_form(id, seq)) : {U32.and(_, 65535) == U32.and(seq, 65535) : U32}
  %Equal.sym(U32, U32.and(seq, 65535), tp.mk(tp.lo16(seq), Word.zero(16n)), tp.and16(seq)) : {U32.and(tp.mk(tp.lo16(seq), tp.lo16(id)), 65535) == _ : U32}
  tp.and_back(seq, id)

# masking id and seq first packs the same word
def tp.rest_mask(+id: U32, +seq: U32) -> {IC.Icmp.rest(U32.and(id, 65535), U32.and(seq, 65535)) == IC.Icmp.rest(id, seq) : U32}:
  %Equal.sym(U32, IC.Icmp.rest(U32.and(id, 65535), U32.and(seq, 65535)), tp.mk(tp.lo16(U32.and(seq, 65535)), tp.lo16(U32.and(id, 65535))), tp.rest_form(U32.and(id, 65535), U32.and(seq, 65535))) : {_ == IC.Icmp.rest(id, seq) : U32}
  %Equal.sym(U32, IC.Icmp.rest(id, seq), tp.mk(tp.lo16(seq), tp.lo16(id)), tp.rest_form(id, seq)) : {tp.mk(tp.lo16(U32.and(seq, 65535)), tp.lo16(U32.and(id, 65535))) == _ : U32}
  %Equal.sym(U32, U32.and(seq, 65535), tp.mk(tp.lo16(seq), Word.zero(16n)), tp.and16(seq)) : {tp.mk(tp.lo16(_), tp.lo16(U32.and(id, 65535))) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  %Equal.sym(Word(16n), tp.lo16(tp.mk(tp.lo16(seq), Word.zero(16n))), tp.lo16(seq), tp.lo_mk(tp.lo16(seq), Word.zero(16n))) : {tp.mk(_, tp.lo16(U32.and(id, 65535))) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  %Equal.sym(U32, U32.and(id, 65535), tp.mk(tp.lo16(id), Word.zero(16n)), tp.and16(id)) : {tp.mk(tp.lo16(seq), tp.lo16(_)) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  %Equal.sym(Word(16n), tp.lo16(tp.mk(tp.lo16(id), Word.zero(16n))), tp.lo16(id), tp.lo_mk(tp.lo16(id), Word.zero(16n))) : {tp.mk(tp.lo16(seq), _) == tp.mk(tp.lo16(seq), tp.lo16(id)) : U32}
  {==}

# Lengths of ICMP headers

def tp.icmp_mlen(+h: NI.IcmpHeader, +data: B.Octets) -> {Nat.is_le(Nat.add(2n, 2n), B.Octets.len(B.Octets.append(NI.IcmpHeader.build(h), data))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(NI.IcmpHeader.build(h), data)), Nat.add(B.Octets.len(NI.IcmpHeader.build(h)), B.Octets.len(data)), BL.octets_len_append(NI.IcmpHeader.build(h), data)) : {Nat.is_le(Nat.add(2n, 2n), _) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(NI.IcmpHeader.build(h)), 8n, NS.icmp_build_length(h)) : {Nat.is_le(Nat.add(2n, 2n), Nat.add(_, B.Octets.len(data))) == True{} : Bool}
  {==}

# the data past the 8-byte header, whatever checksum was written
def tp.icmp_drop8(+h: NI.IcmpHeader, +data: B.Octets, +c: U32) -> {B.Octets.drop(8n, K.inet_put16(B.Octets.append(NI.IcmpHeader.build(h), data), 2n, c)) == data : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16(B.Octets.append(NI.IcmpHeader.build(h), data), 2n, c)), B.Octets.drop(8n, B.Octets.append(NI.IcmpHeader.build(h), data)), NS.inet_put16_drop(B.Octets.append(NI.IcmpHeader.build(h), data), 2n, c, 8n, {==}, tp.icmp_mlen(h, data))) : {_ == data : B.Octets}
  %NS.icmp_build_length(h) : {B.Octets.drop(_, B.Octets.append(NI.IcmpHeader.build(h), data)) == data : B.Octets}
  BL.octets_drop_append(NI.IcmpHeader.build(h), data)

def Laws.icmp_decode_request(id, seq, data):
  %Equal.sym(Bool, NI.IcmpHeader.verify(NI.IcmpHeader.build_checksum(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}, data)), True{}, NS.icmp_build_verifies(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}, data)) : {IC.Icmp.decode.go(_, NI.IcmpHeader.parse(IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})), IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})) == Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(Result<&2, &2, N.NetError, NI.IcmpHeader>, NI.IcmpHeader.parse(K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))), Done{NI.IcmpHeader.norm(NI.IcmpHeader{8, 0, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))), IC.Icmp.rest(id, seq)})}, NS.icmp_put_parse(8, 0, 0, IC.Icmp.rest(id, seq), data, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))) : {IC.Icmp.decode.go(True{}, _, IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})) == Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))), data, tp.icmp_drop8(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}, data, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))) : {Done{IC.Icmp.of_header(NI.IcmpHeader.norm(NI.IcmpHeader{8, 0, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{8, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))), IC.Icmp.rest(id, seq)}), _)} == Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(U32, U32.shrn(IC.Icmp.rest(id, seq), 16n), U32.and(id, 65535), tp.shr_rest(id, seq)) : {Done{IC.IcmpEchoRequest{_, U32.and(IC.Icmp.rest(id, seq), 65535), data}} == Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(U32, U32.and(IC.Icmp.rest(id, seq), 65535), U32.and(seq, 65535), tp.and_rest(id, seq)) : {Done{IC.IcmpEchoRequest{U32.and(id, 65535), _, data}} == Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  {==}

def Laws.icmp_decode_reply(id, seq, data):
  %Equal.sym(Bool, NI.IcmpHeader.verify(NI.IcmpHeader.build_checksum(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}, data)), True{}, NS.icmp_build_verifies(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}, data)) : {IC.Icmp.decode.go(_, NI.IcmpHeader.parse(IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})), IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})) == Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(Result<&2, &2, N.NetError, NI.IcmpHeader>, NI.IcmpHeader.parse(K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))), Done{NI.IcmpHeader.norm(NI.IcmpHeader{0, 0, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))), IC.Icmp.rest(id, seq)})}, NS.icmp_put_parse(0, 0, 0, IC.Icmp.rest(id, seq), data, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))) : {IC.Icmp.decode.go(True{}, _, IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})) == Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))), data, tp.icmp_drop8(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}, data, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))))) : {Done{IC.Icmp.of_header(NI.IcmpHeader.norm(NI.IcmpHeader{0, 0, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(B.Octets.append(NI.IcmpHeader.build(NI.IcmpHeader{0, 0, 0, IC.Icmp.rest(id, seq)}), data), 2n, 0))), IC.Icmp.rest(id, seq)}), _)} == Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(U32, U32.shrn(IC.Icmp.rest(id, seq), 16n), U32.and(id, 65535), tp.shr_rest(id, seq)) : {Done{IC.IcmpEchoReply{_, U32.and(IC.Icmp.rest(id, seq), 65535), data}} == Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  %Equal.sym(U32, U32.and(IC.Icmp.rest(id, seq), 65535), U32.and(seq, 65535), tp.and_rest(id, seq)) : {Done{IC.IcmpEchoReply{U32.and(id, 65535), _, data}} == Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}} : Result<&2, &2, IC.IcmpError, IC.IcmpMsg>}
  {==}

# ICMP: an echo request's bytes answered by an echo reply's

def Laws.icmp_echo_packet_answered(src, dst, id, seq, data):
  %Equal.sym(Result<&2, &2, IC.IcmpError, IC.IcmpMsg>, IC.Icmp.decode(IC.Icmp.encode(IC.IcmpEchoRequest{id, seq, data})), Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}}, Laws.icmp_decode_request(id, seq, data)) : {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.recv(IC.IcmpState{IC.IcmpOptions{True{}}}, src, _)) == [IC.IcmpOut{src, IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})}] : List<&2, IC.IcmpAction>}
  %Equal.cong(U32, B.Octets, z => NI.IcmpHeader.build_checksum(NI.IcmpHeader{0, 0, 0, z}, data), IC.Icmp.rest(U32.and(id, 65535), U32.and(seq, 65535)), IC.Icmp.rest(id, seq), tp.rest_mask(id, seq)) : {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.recv(IC.IcmpState{IC.IcmpOptions{True{}}}, src, Done{IC.IcmpEchoRequest{U32.and(id, 65535), U32.and(seq, 65535), data}})) == [IC.IcmpOut{src, _}] : List<&2, IC.IcmpAction>}
  {==}

def tp.reply_rep(st: IC.IcmpState, +src: U32, +dst: U32, +id: U32, +seq: U32, +data: B.Octets) -> {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.step(st, IC.IcmpRecv{src, dst, IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})})) == [IC.IcmpEchoed{src, U32.and(id, 65535), U32.and(seq, 65535), data}] : List<&2, IC.IcmpAction>}:
  match st:
    case IC.IcmpState{IC.IcmpOptions{ae}}:
      %Equal.sym(Result<&2, &2, IC.IcmpError, IC.IcmpMsg>, IC.Icmp.decode(IC.Icmp.encode(IC.IcmpEchoReply{id, seq, data})), Done{IC.IcmpEchoReply{U32.and(id, 65535), U32.and(seq, 65535), data}}, Laws.icmp_decode_reply(id, seq, data)) : {Pair.snd(IC.IcmpState, List<&2, IC.IcmpAction>, IC.Icmp.recv(IC.IcmpState{IC.IcmpOptions{ae}}, src, _)) == [IC.IcmpEchoed{src, U32.and(id, 65535), U32.and(seq, 65535), data}] : List<&2, IC.IcmpAction>}
      {==}

def Laws.icmp_reply_packet_reported(st, src, dst, id, seq, data):
  tp.reply_rep(st, src, dst, id, seq, data)

# UDP: a datagram's bytes received

def Laws.udp_packet_received(st, src, dst, sport, dport, length, checksum, data, hl):
  %Equal.sym(Bool, NU.UdpHeader.verify_ipv4(src, dst, NU.UdpHeader.build_ipv4(src, dst, NU.UdpHeader{sport, dport, length, checksum}, data)), True{}, NS.udp_ipv4_build_verifies(src, dst, NU.UdpHeader{sport, dport, length, checksum}, data)) : {U.Udp.recv.go(_, st, src, dst, NU.UdpHeader.build_ipv4(src, dst, NU.UdpHeader{sport, dport, length, checksum}, data)) == U.Udp.receive(st, src, dst, N.NetField.low(16n, sport), N.NetField.low(16n, dport), data) : List<&2, U.UdpAction>}
  %Equal.sym(B.Octets, NU.UdpHeader.build_ipv4(src, dst, NU.UdpHeader{sport, dport, length, checksum}, data), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0))))), NS.udp_ipv4_build_fill(src, dst, NU.UdpHeader{sport, dport, length, checksum}, data)) : {U.Udp.recv.go(True{}, st, src, dst, _) == U.Udp.receive(st, src, dst, N.NetField.low(16n, sport), N.NetField.low(16n, dport), data) : List<&2, U.UdpAction>}
  %Equal.sym(Result<&2, &2, N.NetError, NU.UdpHeader>, NU.UdpHeader.parse(K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0)))))), Done{NU.UdpHeader.norm(NU.UdpHeader{sport, dport, length, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0))))})}, NS.udp_put_parse(sport, dport, length, checksum, data, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0)))))) : {U.Udp.recv.header(_, st, src, dst, K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0)))))) == U.Udp.receive(st, src, dst, N.NetField.low(16n, sport), N.NetField.low(16n, dport), data) : List<&2, U.UdpAction>}
  %Equal.sym(Result<&2, &2, N.NetError, B.Octets>, NU.UdpHeader.payload(NU.UdpHeader.norm(NU.UdpHeader{sport, dport, length, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0))))}), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0)))))), Done{data}, NS.udp_put_payload(sport, dport, length, checksum, data, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0)))), hl)) : {U.Udp.recv.payload(_, st, src, dst, NU.UdpHeader.norm(NU.UdpHeader{sport, dport, length, NU.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data)))), K.inet_put16(B.Octets.append(NU.UdpHeader.build(NU.UdpHeader{sport, dport, length, checksum}), data), 6n, 0))))})) == U.Udp.receive(st, src, dst, N.NetField.low(16n, sport), N.NetField.low(16n, dport), data) : List<&2, U.UdpAction>}
  {==}

def Laws.udp_packet_received_sat():
  {==}
