# Proofs of LAWS_sum.bend, written by ref/gen_sum.py. The one's complement
# lemmas are in proof_ones.bend (see its comments); here they are applied to
# the headers: each checksum is inet_fill (or UDP's variant, which sends a
# computed 0 as 0xffff) at an even offset inside the data, after a
# pseudo-header of even length, and writing the field keeps the data's
# length, so the pseudo-header the verifier builds is the one the builder
# summed. The lemmas take d = 2^16 - 1 as a variable; the laws instantiate
# it with S.os.hd, S.os.hD and S.os.hE.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T
import ./proof_ones.bend as S
import ./LAWS_sum.bend as Laws

# The algebra

def Laws.inet_add_comm(a, b):
  S.os.g_add_comm(a, b)

def Laws.inet_add_bound(a, b, ha, hb):
  S.os.g_add_bound(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a, b, ha, hb)

def Laws.inet_add_no_carry(a, b, ha, hb, h):
  S.os.g_no_carry(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a, b, ha, hb, h)

def Laws.inet_add_end_around(a, b, ha, hb, h):
  S.os.g_end_around(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a, b, ha, hb, h)

def Laws.inet_add_zero(a, ha):
  S.os.g_add_zero(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a, ha)

def Laws.inet_add_assoc(a, b, c, ha, hb, hc):
  S.os.g_add_assoc(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a, b, c, ha, hb, hc)

def Laws.inet_add_complement(a, ha):
  S.os.g_complement(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a, ha)

def Laws.inet_finish_bound(a):
  S.os.g_finish_bound(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), a)

def Laws.inet_update_bound(acc, o, ha):
  S.os.g_update_bound(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), acc, o, ha)

def Laws.inet_update_add(acc, w, o, ha, hw):
  S.os.g_update_add(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), acc, w, o, ha, hw)

def Laws.inet_update_comm(acc, x, y, ha):
  S.os.g_update_comm(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), acc, x, y, ha)

def Laws.inet_sum_swap(x, y, ex, ey):
  S.os.g_sum_swap(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), x, y, ex, ey)

def Laws.inet_fill_verifies(pseudo, o, k, ep, hl):
  S.os.fill_verifies(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), pseudo, o, Nat.double(k), ep, S.os.even_take(o, k, hl))

# Pseudo-headers have even lengths

def h.be32_even_cons(v: U32, +rest: List<&2, U32>) -> {K.inet_even.list(B.mask(B.append(B.be32(v), rest))) == K.inet_even.list(B.mask(rest)) : Bool}:
  match v:
    case U32{x}:
      {==}

def h.pseudo4_even.m(src: U32, dst: U32, +p: U32, +len: U32) -> {K.inet_even.list(B.mask(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len)))))) == True{} : Bool}:
  match src dst:
    case U32{a} U32{b}:
      S.os.be16_even.m(len)

def h.pseudo4_even(+src: U32, +dst: U32, +p: U32, +len: U32) -> {K.inet_even(I4.ipv4_pseudo(src, dst, p, len)) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len)))))), B.mask(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len))))), BL.octets_to_of(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len)))))) : {K.inet_even.list(_) == True{} : Bool}
  h.pseudo4_even.m(src, dst, p, len)

def h.pseudo6_even.m(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, +len: U32, +n: U32) -> {K.inet_even.list(B.mask(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)]))))) == True{} : Bool}:
  match src dst:
    case I6.Ipv6Addr{U32{a0}, U32{a1}, U32{a2}, U32{a3}} I6.Ipv6Addr{U32{b0}, U32{b1}, U32{b2}, U32{b3}}:
      h.be32_even_cons(len, [0, 0, 0, B.byte(n)])

def h.pseudo6_even(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +len: U32, +n: U32) -> {K.inet_even(I6.ipv6_pseudo(src, dst, len, n)) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)]))))), B.mask(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)])))), BL.octets_to_of(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)]))))) : {K.inet_even.list(_) == True{} : Bool}
  h.pseudo6_even.m(src, dst, len, n)

def h.icmp_len.m(h: C.IcmpHeader, +data: B.Octets) -> {Nat.is_le(8n, Nat.add(B.len(C.IcmpHeader.build.list(h)), B.Octets.len(data))) == True{} : Bool}:
  match h:
    case C.IcmpHeader{U32{t}, U32{c}, U32{k}, U32{r}}:
      S.os.le_zero(B.Octets.len(data))

def h.icmp_len(+h: C.IcmpHeader, +data: B.Octets) -> {Nat.is_le(8n, B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data)), Nat.add(B.Octets.len(C.IcmpHeader.build(h)), B.Octets.len(data)), BL.octets_len_append(C.IcmpHeader.build(h), data)) : {Nat.is_le(8n, _) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(C.IcmpHeader.build.list(h))), B.len(C.IcmpHeader.build.list(h)), BL.octets_len_of_list(C.IcmpHeader.build.list(h))) : {Nat.is_le(8n, Nat.add(_, B.Octets.len(data))) == True{} : Bool}
  h.icmp_len.m(h, data)

def h.udp_len.m(h: U.UdpHeader, +payload: B.Octets) -> {Nat.is_le(8n, Nat.add(B.len(U.UdpHeader.build.list(h)), B.Octets.len(payload))) == True{} : Bool}:
  match h:
    case U.UdpHeader{U32{a}, U32{b}, U32{c}, U32{e}}:
      S.os.le_zero(B.Octets.len(payload))

def h.udp_len(+h: U.UdpHeader, +payload: B.Octets) -> {Nat.is_le(8n, B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), Nat.add(B.Octets.len(U.UdpHeader.build(h)), B.Octets.len(payload)), BL.octets_len_append(U.UdpHeader.build(h), payload)) : {Nat.is_le(8n, _) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(U.UdpHeader.build.list(h))), B.len(U.UdpHeader.build.list(h)), BL.octets_len_of_list(U.UdpHeader.build.list(h))) : {Nat.is_le(8n, Nat.add(_, B.Octets.len(payload))) == True{} : Bool}
  h.udp_len.m(h, payload)

def h.tcp_len.m(h: T.TcpHeader, +payload: B.Octets) -> {Nat.is_le(20n, Nat.add(B.len(T.TcpHeader.build.list(h)), B.Octets.len(payload))) == True{} : Bool}:
  match h:
    case T.TcpHeader{U32{a}, U32{b}, U32{sq}, U32{ak}, U32{off}, U32{rs}, U32{fl}, U32{win}, U32{ck}, U32{ur}, o}:
      S.os.le_zero(Nat.add(B.len(B.Octets.to_list(o)), B.Octets.len(payload)))

def h.tcp_len(+h: T.TcpHeader, +payload: B.Octets) -> {Nat.is_le(20n, B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), Nat.add(B.Octets.len(T.TcpHeader.build(h)), B.Octets.len(payload)), BL.octets_len_append(T.TcpHeader.build(h), payload)) : {Nat.is_le(20n, _) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(T.TcpHeader.build.list(h))), B.len(T.TcpHeader.build.list(h)), BL.octets_len_of_list(T.TcpHeader.build.list(h))) : {Nat.is_le(20n, Nat.add(_, B.Octets.len(payload))) == True{} : Bool}
  h.tcp_len.m(h, payload)

def h.le_trans(+x: Nat, +y: Nat, +z: Nat, +h1: {Nat.is_le(x, y) == True{} : Bool}, +h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  S.os.le_trans(x, y, z, h1, h2)

# ICMP

def Laws.icmp_build_verifies(h, data):
  %BL.octets_append_empty_l(K.inet_fill(B.Octets.empty(), B.Octets.append(C.IcmpHeader.build(h), data), 2n)) : {K.inet_verify(_) == True{} : Bool}
  S.os.fill_verifies(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), B.Octets.empty(), B.Octets.append(C.IcmpHeader.build(h), data), 2n, {==}, S.os.even_take(B.Octets.append(C.IcmpHeader.build(h), data), 1n, h.le_trans(2n, 8n, B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data)), {==}, h.icmp_len(h, data))))

def h.icmp6(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +h: C.IcmpHeader, +data: B.Octets) -> {K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(C.IcmpHeader.build_ipv6(src, dst, h, data))), 58), C.IcmpHeader.build_ipv6(src, dst, h, data))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(C.IcmpHeader.build(h), data), 2n, K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data))), 58), K.inet_put16(B.Octets.append(C.IcmpHeader.build(h), data), 2n, 0))))), B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data)), S.os.len_put16(B.Octets.append(C.IcmpHeader.build(h), data), 2n, K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data))), 58), K.inet_put16(B.Octets.append(C.IcmpHeader.build(h), data), 2n, 0))), h.le_trans(Nat.add(2n, 2n), 8n, B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data)), {==}, h.icmp_len(h, data)))) : {K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(_), 58), C.IcmpHeader.build_ipv6(src, dst, h, data))) == True{} : Bool}
  S.os.fill_verifies(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data))), 58), B.Octets.append(C.IcmpHeader.build(h), data), 2n, h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data))), 58), S.os.even_take(B.Octets.append(C.IcmpHeader.build(h), data), 1n, h.le_trans(2n, 8n, B.Octets.len(B.Octets.append(C.IcmpHeader.build(h), data)), {==}, h.icmp_len(h, data))))

def Laws.icmp6_build_verifies(src, dst, h, data):
  h.icmp6(src, dst, h, data)

def h.tcp4(+src: U32, +dst: U32, +h: T.TcpHeader, +payload: B.Octets) -> {K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 6, U32.from_nat(B.Octets.len(T.TcpHeader.build_ipv4(src, dst, h, payload)))), T.TcpHeader.build_ipv4(src, dst, h, payload))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 6, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)))), K.inet_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, 0))))), B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), S.os.len_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 6, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)))), K.inet_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, 0))), h.le_trans(Nat.add(16n, 2n), 20n, B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), {==}, h.tcp_len(h, payload)))) : {K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 6, U32.from_nat(_)), T.TcpHeader.build_ipv4(src, dst, h, payload))) == True{} : Bool}
  S.os.fill_verifies(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I4.ipv4_pseudo(src, dst, 6, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)))), B.Octets.append(T.TcpHeader.build(h), payload), 16n, h.pseudo4_even(src, dst, 6, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)))), S.os.even_take(B.Octets.append(T.TcpHeader.build(h), payload), 8n, h.le_trans(16n, 20n, B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), {==}, h.tcp_len(h, payload))))

def Laws.tcp_ipv4_build_verifies(src, dst, h, payload):
  h.tcp4(src, dst, h, payload)

def h.tcp6(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +h: T.TcpHeader, +payload: B.Octets) -> {K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(T.TcpHeader.build_ipv6(src, dst, h, payload))), 6), T.TcpHeader.build_ipv6(src, dst, h, payload))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload))), 6), K.inet_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, 0))))), B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), S.os.len_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload))), 6), K.inet_put16(B.Octets.append(T.TcpHeader.build(h), payload), 16n, 0))), h.le_trans(Nat.add(16n, 2n), 20n, B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), {==}, h.tcp_len(h, payload)))) : {K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(_), 6), T.TcpHeader.build_ipv6(src, dst, h, payload))) == True{} : Bool}
  S.os.fill_verifies(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload))), 6), B.Octets.append(T.TcpHeader.build(h), payload), 16n, h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload))), 6), S.os.even_take(B.Octets.append(T.TcpHeader.build(h), payload), 8n, h.le_trans(16n, 20n, B.Octets.len(B.Octets.append(T.TcpHeader.build(h), payload)), {==}, h.tcp_len(h, payload))))

def Laws.tcp_ipv6_build_verifies(src, dst, h, payload):
  h.tcp6(src, dst, h, payload)

# the field written by UdpHeader.fill verifies, in both cases of nonzero
def h.udp_nz(z: Bool, +pseudo: B.Octets, +o: B.Octets, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(6n, o)) == True{} : Bool}, +ez: {U32.is_eq(K.inet_checksum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))), 0) == z : Bool}) -> {K.inet_verify(B.Octets.append(pseudo, K.inet_put16(o, 6n, U.UdpHeader.nonzero.go(z, K.inet_checksum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))))) == True{} : Bool}:
  match z:
    case True{}:
      S.os.verify_put(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), pseudo, o, 6n, eP, eT, 65535, S.os.fit65535(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hE()), S.os.allones_sum(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), pseudo, o, 6n, eP, eT, ez))
    case False{}:
      S.os.verify_put(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), pseudo, o, 6n, eP, eT, K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), S.os.finish_fits(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hD(), K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), S.os.fill_sum(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), pseudo, o, 6n, eP, eT))

# the field read back: nonzero(c) is never 0
def h.nz_low(z: Bool, +c: U32, +hc: {Nat.is_le(U32.to_nat(c), Word.to_nat(16n, Word.not(16n, Word.zero(16n)))) == True{} : Bool}, +ez: {U32.is_eq(c, 0) == z : Bool}) -> {U32.is_eq(B.low16(U.UdpHeader.nonzero.go(z, c)), 0) == False{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(U32, B.low16(c), c, S.os.low16_fit(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hD(), c, hc)) : {U32.is_eq(_, 0) == False{} : Bool}
      ez

def h.be16_2(+x: U32) -> {Nat.is_le(Nat.add(0n, 2n), B.Octets.len(B.Octets.be16(x))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.be16(x)), 2n, BL.octets_len_be16(x)) : {Nat.is_le(Nat.add(0n, 2n), _) == True{} : Bool}
  {==}

# the 16-bit field at offset 6 of o with x written there reads x's low 16 bits
def h.zf(+o: B.Octets, +x: U32, +h8: {Nat.is_le(8n, B.Octets.len(o)) == True{} : Bool}) -> {U.UdpHeader.zero_field(B.Octets.be16_at(K.inet_put16(o, 6n, x), 6n)) == U32.is_eq(B.low16(x), 0) : Bool}:
  %Equal.cong(Nat, Nat, z => Nat.add(z, 0n), B.Octets.len(B.Octets.take(6n, o)), 6n, BL.octets_len_take_le(6n, o, h.le_trans(6n, 8n, B.Octets.len(o), {==}, h8))) : {U.UdpHeader.zero_field(B.Octets.be16_at(B.Octets.append(B.Octets.take(6n, o), B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(6n, 2n), o))), _)) == U32.is_eq(B.low16(x), 0) : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.take(6n, o), B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(6n, 2n), o))), Nat.add(B.Octets.len(B.Octets.take(6n, o)), 0n)), B.Octets.be16_at(B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(6n, 2n), o)), 0n), BL.octets_be16_at_append_add(B.Octets.take(6n, o), B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(6n, 2n), o)), 0n)) : {U.UdpHeader.zero_field(_) == U32.is_eq(B.low16(x), 0) : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(6n, 2n), o)), 0n), B.Octets.be16_at(B.Octets.be16(x), 0n), BL.octets_be16_at_append_le(B.Octets.be16(x), B.Octets.drop(Nat.add(6n, 2n), o), 0n, h.be16_2(x))) : {U.UdpHeader.zero_field(_) == U32.is_eq(B.low16(x), 0) : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.be16(x), 0n), Some{B.low16(x)}, BL.octets_be16_round_trip(x)) : {U.UdpHeader.zero_field(_) == U32.is_eq(B.low16(x), 0) : Bool}
  {==}

def h.go_true(z: Bool, +s: Bool, +hs: {s == True{} : Bool}) -> {U.UdpHeader.verify.go(z, True{}, s) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      hs

def h.go_false(z: Bool, +s: Bool, +ez: {z == False{} : Bool}, +hs: {s == True{} : Bool}) -> {U.UdpHeader.verify.go(z, False{}, s) == True{} : Bool}:
  match z:
    case True{}:
      Empty.absurd({U.UdpHeader.verify.go(True{}, False{}, s) == True{} : Bool}, S.os.tf(ez))
    case False{}:
      hs

def h.udp4.sum(+src: U32, +dst: U32, +h: U.UdpHeader, +payload: B.Octets) -> {K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(U.UdpHeader.build_ipv4(src, dst, h, payload)))), U.UdpHeader.build_ipv4(src, dst, h, payload))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)))), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))))), B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), S.os.len_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)))), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), h.le_trans(Nat.add(6n, 2n), 8n, B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), {==}, h.udp_len(h, payload)))) : {K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(_)), U.UdpHeader.build_ipv4(src, dst, h, payload))) == True{} : Bool}
  h.udp_nz(U32.is_eq(K.inet_checksum(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)))), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0))), 0), I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)))), B.Octets.append(U.UdpHeader.build(h), payload), h.pseudo4_even(src, dst, 17, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)))), S.os.even_take(B.Octets.append(U.UdpHeader.build(h), payload), 3n, h.le_trans(6n, 8n, B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), {==}, h.udp_len(h, payload))), {==})

def h.udp6.sum(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +h: U.UdpHeader, +payload: B.Octets) -> {K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(U.UdpHeader.build_ipv6(src, dst, h, payload))), 17), U.UdpHeader.build_ipv6(src, dst, h, payload))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))))), B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), S.os.len_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), h.le_trans(Nat.add(6n, 2n), 8n, B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), {==}, h.udp_len(h, payload)))) : {K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(_), 17), U.UdpHeader.build_ipv6(src, dst, h, payload))) == True{} : Bool}
  h.udp_nz(U32.is_eq(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0))), 0), I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), B.Octets.append(U.UdpHeader.build(h), payload), h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), S.os.even_take(B.Octets.append(U.UdpHeader.build(h), payload), 3n, h.le_trans(6n, 8n, B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload)), {==}, h.udp_len(h, payload))), {==})

def Laws.udp_ipv4_build_verifies(src, dst, h, payload):
  h.go_true(U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv4(src, dst, h, payload), 6n)), K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat(B.Octets.len(U.UdpHeader.build_ipv4(src, dst, h, payload)))), U.UdpHeader.build_ipv4(src, dst, h, payload))), h.udp4.sum(src, dst, h, payload))

def h.udp6.zero(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +h: U.UdpHeader, +payload: B.Octets) -> {U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv6(src, dst, h, payload), 6n)) == False{} : Bool}:
  Equal.trans(Bool, U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv6(src, dst, h, payload), 6n)), U32.is_eq(B.low16(U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0))))), 0), False{}, h.zf(B.Octets.append(U.UdpHeader.build(h), payload), U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), h.udp_len(h, payload)), h.nz_low(U32.is_eq(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0))), 0), K.inet_finish(K.inet_sum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), S.os.finish_fits(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hD(), K.inet_sum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), {==}))

def Laws.udp_ipv6_build_verifies(src, dst, h, payload):
  h.go_false(U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv6(src, dst, h, payload), 6n)), K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(U.UdpHeader.build_ipv6(src, dst, h, payload))), 17), U.UdpHeader.build_ipv6(src, dst, h, payload))), h.udp6.zero(src, dst, h, payload), h.udp6.sum(src, dst, h, payload))

# Satisfiability and the vector

def Laws.inet_sum_sat():
  {==}

def Laws.inet_add_vector():
  {==}
