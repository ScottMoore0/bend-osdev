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
import ./netheaders.bend as N
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

# Writing a 16-bit field

def Laws.inet_put16_len(o, off, v, h):
  S.os.len_put16(o, off, v, h)

def Laws.inet_put16_drop(o, off, v, n, h1, h2):
  %S.os.add_sub(Nat.add(off, 2n), n, h1) : {B.Octets.drop(_, K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}
  %Equal.sym(Nat, Nat.add(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n))), Nat.add(off, Nat.add(2n, Nat.sub(n, Nat.add(off, 2n)))), S.os.add_assoc(off, 2n, Nat.sub(n, Nat.add(off, 2n)))) : {B.Octets.drop(_, K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}
  %BL.octets_len_take_le(off, o, S.os.le_trans(off, Nat.add(off, 2n), B.Octets.len(o), S.os.le_add_r(off, 2n), h2)) : {B.Octets.drop(Nat.add(_, Nat.add(2n, Nat.sub(n, Nat.add(off, 2n)))), K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(B.Octets.take(off, o)), Nat.add(2n, Nat.sub(n, Nat.add(off, 2n)))), B.Octets.append(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o)))), B.Octets.drop(Nat.add(2n, Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o))), BL.octets_drop_append_add(B.Octets.take(off, o), Nat.add(2n, Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o)))) : {_ == B.Octets.drop(n, o) : B.Octets}
  %BL.octets_len_be16(v) : {B.Octets.drop(Nat.add(_, Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o))) == B.Octets.drop(n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(B.Octets.be16(v)), Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o))), B.Octets.drop(Nat.sub(n, Nat.add(off, 2n)), B.Octets.drop(Nat.add(off, 2n), o)), BL.octets_drop_append_add(B.Octets.be16(v), Nat.sub(n, Nat.add(off, 2n)), B.Octets.drop(Nat.add(off, 2n), o))) : {_ == B.Octets.drop(n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.sub(n, Nat.add(off, 2n)), B.Octets.drop(Nat.add(off, 2n), o)), B.Octets.drop(Nat.add(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n))), o), BL.octets_drop_drop(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n)), o)) : {_ == B.Octets.drop(n, o) : B.Octets}
  %Equal.sym(Nat, Nat.add(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n))), n, S.os.add_sub(Nat.add(off, 2n), n, h1)) : {B.Octets.drop(_, o) == B.Octets.drop(n, o) : B.Octets}
  {==}

def h.icmp_put_parse.m(msg_type: U32, code: U32, checksum: U32, rest: U32, +data: B.Octets, c: U32) -> {C.IcmpHeader.parse.list(B.append(B.mask(B.take(2n, B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data)))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(2n, 2n), B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data))))))) == Done{C.IcmpHeader.norm(C.IcmpHeader{msg_type, code, c, rest})} : Result<&2, &2, N.NetError, C.IcmpHeader>}:
  match msg_type code checksum rest c:
    case U32{WCon{msg_type_0, WCon{msg_type_1, WCon{msg_type_2, WCon{msg_type_3, WCon{msg_type_4, WCon{msg_type_5, WCon{msg_type_6, WCon{msg_type_7, msg_type_h}}}}}}}}} U32{WCon{code_0, WCon{code_1, WCon{code_2, WCon{code_3, WCon{code_4, WCon{code_5, WCon{code_6, WCon{code_7, code_h}}}}}}}}} U32{WCon{checksum_0, WCon{checksum_1, WCon{checksum_2, WCon{checksum_3, WCon{checksum_4, WCon{checksum_5, WCon{checksum_6, WCon{checksum_7, WCon{checksum_8, WCon{checksum_9, WCon{checksum_10, WCon{checksum_11, WCon{checksum_12, WCon{checksum_13, WCon{checksum_14, WCon{checksum_15, checksum_h}}}}}}}}}}}}}}}}} U32{WCon{rest_0, WCon{rest_1, WCon{rest_2, WCon{rest_3, WCon{rest_4, WCon{rest_5, WCon{rest_6, WCon{rest_7, WCon{rest_8, WCon{rest_9, WCon{rest_10, WCon{rest_11, WCon{rest_12, WCon{rest_13, WCon{rest_14, WCon{rest_15, WCon{rest_16, WCon{rest_17, WCon{rest_18, WCon{rest_19, WCon{rest_20, WCon{rest_21, WCon{rest_22, WCon{rest_23, WCon{rest_24, WCon{rest_25, WCon{rest_26, WCon{rest_27, WCon{rest_28, WCon{rest_29, WCon{rest_30, WCon{rest_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c_0, WCon{c_1, WCon{c_2, WCon{c_3, WCon{c_4, WCon{c_5, WCon{c_6, WCon{c_7, WCon{c_8, WCon{c_9, WCon{c_10, WCon{c_11, WCon{c_12, WCon{c_13, WCon{c_14, WCon{c_15, c_h}}}}}}}}}}}}}}}}}:
      {==}

def h.icmp_put_parse.len.m(msg_type: U32, code: U32, checksum: U32, rest: U32, +data: B.Octets) -> {Nat.is_le(Nat.add(2n, 2n), B.len(B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data)))) == True{} : Bool}:
  match msg_type code checksum rest:
    case U32{msg_type_} U32{code_} U32{checksum_} U32{rest_}:
      S.os.le_zero(Nat.add(4n, B.len(B.Octets.to_list(data))))

def Laws.icmp_put_parse(msg_type, code, checksum, rest, data, c):
  %Equal.sym(B.Octets, B.Octets.append(C.IcmpHeader.build(C.IcmpHeader{msg_type, code, checksum, rest}), data), B.Octets.of_list(B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data))), S.os.app_of(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), data)) : {C.IcmpHeader.parse(K.inet_put16(_, 2n, c)) == Done{C.IcmpHeader.norm(C.IcmpHeader{msg_type, code, c, rest})} : Result<&2, &2, N.NetError, C.IcmpHeader>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(K.inet_put16(B.Octets.of_list(B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data))), 2n, c)), B.append(B.mask(B.take(2n, B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data)))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(2n, 2n), B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data)))))), S.os.put16_list(B.append(C.IcmpHeader.build.list(C.IcmpHeader{msg_type, code, checksum, rest}), B.Octets.to_list(data)), 2n, c, h.icmp_put_parse.len.m(msg_type, code, checksum, rest, data))) : {C.IcmpHeader.parse.list(_) == Done{C.IcmpHeader.norm(C.IcmpHeader{msg_type, code, c, rest})} : Result<&2, &2, N.NetError, C.IcmpHeader>}
  h.icmp_put_parse.m(msg_type, code, checksum, rest, data, c)

def h.udp_put_parse.m(src_port: U32, dst_port: U32, length: U32, checksum: U32, +payload: B.Octets, c: U32) -> {U.UdpHeader.parse.list(B.append(B.mask(B.take(6n, B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload)))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(6n, 2n), B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload))))))) == Done{U.UdpHeader.norm(U.UdpHeader{src_port, dst_port, length, c})} : Result<&2, &2, N.NetError, U.UdpHeader>}:
  match src_port dst_port length checksum c:
    case U32{WCon{src_port_0, WCon{src_port_1, WCon{src_port_2, WCon{src_port_3, WCon{src_port_4, WCon{src_port_5, WCon{src_port_6, WCon{src_port_7, WCon{src_port_8, WCon{src_port_9, WCon{src_port_10, WCon{src_port_11, WCon{src_port_12, WCon{src_port_13, WCon{src_port_14, WCon{src_port_15, src_port_h}}}}}}}}}}}}}}}}} U32{WCon{dst_port_0, WCon{dst_port_1, WCon{dst_port_2, WCon{dst_port_3, WCon{dst_port_4, WCon{dst_port_5, WCon{dst_port_6, WCon{dst_port_7, WCon{dst_port_8, WCon{dst_port_9, WCon{dst_port_10, WCon{dst_port_11, WCon{dst_port_12, WCon{dst_port_13, WCon{dst_port_14, WCon{dst_port_15, dst_port_h}}}}}}}}}}}}}}}}} U32{WCon{length_0, WCon{length_1, WCon{length_2, WCon{length_3, WCon{length_4, WCon{length_5, WCon{length_6, WCon{length_7, WCon{length_8, WCon{length_9, WCon{length_10, WCon{length_11, WCon{length_12, WCon{length_13, WCon{length_14, WCon{length_15, length_h}}}}}}}}}}}}}}}}} U32{checksum_} U32{WCon{c_0, WCon{c_1, WCon{c_2, WCon{c_3, WCon{c_4, WCon{c_5, WCon{c_6, WCon{c_7, WCon{c_8, WCon{c_9, WCon{c_10, WCon{c_11, WCon{c_12, WCon{c_13, WCon{c_14, WCon{c_15, c_h}}}}}}}}}}}}}}}}}:
      {==}

def h.udp_put_parse.len.m(src_port: U32, dst_port: U32, length: U32, checksum: U32, +payload: B.Octets) -> {Nat.is_le(Nat.add(6n, 2n), B.len(B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload)))) == True{} : Bool}:
  match src_port dst_port length checksum:
    case U32{src_port_} U32{dst_port_} U32{length_} U32{checksum_}:
      S.os.le_zero(B.len(B.Octets.to_list(payload)))

def Laws.udp_put_parse(src_port, dst_port, length, checksum, payload, c):
  %Equal.sym(B.Octets, B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), B.Octets.of_list(B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload))), S.os.app_of(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), payload)) : {U.UdpHeader.parse(K.inet_put16(_, 6n, c)) == Done{U.UdpHeader.norm(U.UdpHeader{src_port, dst_port, length, c})} : Result<&2, &2, N.NetError, U.UdpHeader>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(K.inet_put16(B.Octets.of_list(B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload))), 6n, c)), B.append(B.mask(B.take(6n, B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload)))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(6n, 2n), B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload)))))), S.os.put16_list(B.append(U.UdpHeader.build.list(U.UdpHeader{src_port, dst_port, length, checksum}), B.Octets.to_list(payload)), 6n, c, h.udp_put_parse.len.m(src_port, dst_port, length, checksum, payload))) : {U.UdpHeader.parse.list(_) == Done{U.UdpHeader.norm(U.UdpHeader{src_port, dst_port, length, c})} : Result<&2, &2, N.NetError, U.UdpHeader>}
  h.udp_put_parse.m(src_port, dst_port, length, checksum, payload, c)

def h.low_low16(l: U32) -> {N.NetField.low(16n, N.NetField.low(16n, l)) == N.NetField.low(16n, l) : U32}:
  match l:
    case U32{WCon{l_0, WCon{l_1, WCon{l_2, WCon{l_3, WCon{l_4, WCon{l_5, WCon{l_6, WCon{l_7, WCon{l_8, WCon{l_9, WCon{l_10, WCon{l_11, WCon{l_12, WCon{l_13, WCon{l_14, WCon{l_15, l_h}}}}}}}}}}}}}}}}}:
      {==}

def h.udp_blen(a: U32, b: U32, l: U32, k: U32) -> {B.len(U.UdpHeader.build.list(U.UdpHeader{a, b, l, k})) == 8n : Nat}:
  match a b l k:
    case U32{a_} U32{b_} U32{l_} U32{k_}:
      {==}

def h.udp_len_build(+a: U32, +b: U32, +l: U32, +k: U32) -> {B.Octets.len(U.UdpHeader.build(U.UdpHeader{a, b, l, k})) == 8n : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(U.UdpHeader.build.list(U.UdpHeader{a, b, l, k}))), B.len(U.UdpHeader.build.list(U.UdpHeader{a, b, l, k})), BL.octets_len_of_list(U.UdpHeader.build.list(U.UdpHeader{a, b, l, k}))) : {_ == 8n : Nat}
  h.udp_blen(a, b, l, k)

def h.udp_dg_len(+src_port: U32, +dst_port: U32, +length: U32, +checksum: U32, +payload: B.Octets, +c: U32) -> {B.Octets.len(K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == Nat.add(8n, B.Octets.len(payload)) : Nat}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)), B.Octets.len(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload)), S.os.len_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c, h.udp_len(U.UdpHeader{src_port, dst_port, length, checksum}, payload))) : {_ == Nat.add(8n, B.Octets.len(payload)) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload)), Nat.add(B.Octets.len(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum})), B.Octets.len(payload)), BL.octets_len_append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload)) : {_ == Nat.add(8n, B.Octets.len(payload)) : Nat}
  %Equal.sym(Nat, B.Octets.len(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum})), 8n, h.udp_len_build(src_port, dst_port, length, checksum)) : {Nat.add(_, B.Octets.len(payload)) == Nat.add(8n, B.Octets.len(payload)) : Nat}
  {==}

def h.udp_drop8(+src_port: U32, +dst_port: U32, +length: U32, +checksum: U32, +payload: B.Octets, +c: U32) -> {B.Octets.drop(8n, K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == payload : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)), B.Octets.drop(8n, B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload)), Laws.inet_put16_drop(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c, 8n, {==}, h.udp_len(U.UdpHeader{src_port, dst_port, length, checksum}, payload))) : {_ == payload : B.Octets}
  %h.udp_len_build(src_port, dst_port, length, checksum) : {B.Octets.drop(_, B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload)) == payload : B.Octets}
  BL.octets_drop_append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload)

def h.sub8(x: Nat) -> {Nat.sub(Nat.add(8n, x), 8n) == x : Nat}:
  S.os.sub_zero(x)

def h.ge8(x: Nat) -> {Nat.is_ge(Nat.add(8n, x), 8n) == True{} : Bool}:
  S.os.ge_zero(x)

def Laws.udp_put_payload(src_port, dst_port, length, checksum, payload, c, hl):
  %Equal.sym(Nat, U32.to_nat(N.NetField.low(16n, N.NetField.low(16n, length))), Nat.add(8n, B.Octets.len(payload)), Equal.trans(Nat, U32.to_nat(N.NetField.low(16n, N.NetField.low(16n, length))), U32.to_nat(N.NetField.low(16n, length)), Nat.add(8n, B.Octets.len(payload)), Equal.cong(U32, Nat, z => U32.to_nat(z), N.NetField.low(16n, N.NetField.low(16n, length)), N.NetField.low(16n, length), h.low_low16(length)), hl)) : {U.UdpHeader.payload.go(Nat.is_ge(_, 8n), Nat.sub(_, 8n), K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  %Equal.sym(Bool, Nat.is_ge(Nat.add(8n, B.Octets.len(payload)), 8n), True{}, h.ge8(B.Octets.len(payload))) : {U.UdpHeader.payload.go(_, Nat.sub(Nat.add(8n, B.Octets.len(payload)), 8n), K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  %Equal.sym(Nat, Nat.sub(Nat.add(8n, B.Octets.len(payload)), 8n), B.Octets.len(payload), h.sub8(B.Octets.len(payload))) : {U.UdpHeader.payload.go(True{}, _, K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)) == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)), Nat.add(8n, B.Octets.len(payload)), h.udp_dg_len(src_port, dst_port, length, checksum, payload, c)) : {N.net.check(B.Octets, Nat.is_le(Nat.add(8n, B.Octets.len(payload)), _), N.NetTruncated{}, B.Octets.slice(8n, B.Octets.len(payload), K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c))) == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(8n, B.Octets.len(payload)), Nat.add(8n, B.Octets.len(payload))), True{}, S.os.le_refl(Nat.add(8n, B.Octets.len(payload)))) : {N.net.check(B.Octets, _, N.NetTruncated{}, B.Octets.slice(8n, B.Octets.len(payload), K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c))) == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.drop(8n, K.inet_put16(B.Octets.append(U.UdpHeader.build(U.UdpHeader{src_port, dst_port, length, checksum}), payload), 6n, c)), payload, h.udp_drop8(src_port, dst_port, length, checksum, payload, c)) : {Done{B.Octets.take(B.Octets.len(payload), _)} == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(payload), payload), payload, BL.octets_take_len(payload)) : {Done{_} == Done{payload} : Result<&2, &2, N.NetError, B.Octets>}
  {==}

def h.udp6.zero(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +h: U.UdpHeader, +payload: B.Octets) -> {U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv6(src, dst, h, payload), 6n)) == False{} : Bool}:
  Equal.trans(Bool, U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv6(src, dst, h, payload), 6n)), U32.is_eq(B.low16(U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0))))), 0), False{}, h.zf(B.Octets.append(U.UdpHeader.build(h), payload), U.UdpHeader.nonzero(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), h.udp_len(h, payload)), h.nz_low(U32.is_eq(K.inet_checksum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0))), 0), K.inet_finish(K.inet_sum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), S.os.finish_fits(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hD(), K.inet_sum(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(B.Octets.append(U.UdpHeader.build(h), payload))), 17), K.inet_put16(B.Octets.append(U.UdpHeader.build(h), payload), 6n, 0)))), {==}))

def Laws.udp_ipv6_build_verifies(src, dst, h, payload):
  h.go_false(U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv6(src, dst, h, payload), 6n)), K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat(B.Octets.len(U.UdpHeader.build_ipv6(src, dst, h, payload))), 17), U.UdpHeader.build_ipv6(src, dst, h, payload))), h.udp6.zero(src, dst, h, payload), h.udp6.sum(src, dst, h, payload))

# Satisfiability and the vector

def Laws.inet_sum_sat():
  {==}

def Laws.inet_add_vector():
  {==}
