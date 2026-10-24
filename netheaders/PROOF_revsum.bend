# Proofs of LAWS_revsum.bend, written by ref/gen_rev.py.
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
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP
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

def rs.min_le(n: Nat, +m: Nat) -> {Nat.is_le(Nat.min(n, m), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match m:
        case 0n:
          {==}
        case 1n+ +q:
          rs.min_le(p, q)

def rs.min_le_r(n: Nat, +m: Nat) -> {Nat.is_le(Nat.min(n, m), m) == True{} : Bool}:
  match n:
    case 0n:
      S.os.le_zero(m)
    case 1n+ +p:
      match m:
        case 0n:
          {==}
        case 1n+ +q:
          rs.min_le_r(p, q)

# k bytes in the first n of o: k <= n and k <= len(o)
def rs.take_ge_n(+k: Nat, +n: Nat, +o: B.Octets, +h: {Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))) == True{} : Bool}) -> {Nat.is_le(k, n) == True{} : Bool}:
  UO.nat_le_trans(k, Nat.min(n, B.Octets.len(o)), n, Equal.trans(Bool, Nat.is_le(k, Nat.min(n, B.Octets.len(o))), Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(k, z), Nat.min(n, B.Octets.len(o)), B.Octets.len(B.Octets.take(n, o)), Equal.sym(Nat, B.Octets.len(B.Octets.take(n, o)), Nat.min(n, B.Octets.len(o)), BL.octets_len_take(n, o))), h), rs.min_le(n, B.Octets.len(o)))

def rs.take_ge_o(+k: Nat, +n: Nat, +o: B.Octets, +h: {Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))) == True{} : Bool}) -> {Nat.is_le(k, B.Octets.len(o)) == True{} : Bool}:
  UO.nat_le_trans(k, Nat.min(n, B.Octets.len(o)), B.Octets.len(o), Equal.trans(Bool, Nat.is_le(k, Nat.min(n, B.Octets.len(o))), Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(k, z), Nat.min(n, B.Octets.len(o)), B.Octets.len(B.Octets.take(n, o)), Equal.sym(Nat, B.Octets.len(B.Octets.take(n, o)), Nat.min(n, B.Octets.len(o)), BL.octets_len_take(n, o))), h), rs.min_le_r(n, B.Octets.len(o)))

# k bytes in the built header, the header the first bytes of o: k <= len(o)
def rs.built_ge(+k: Nat, +n: Nat, +b: B.Octets, +o: B.Octets, +er: {b == B.Octets.take(n, o) : B.Octets}, +h: {Nat.is_le(k, B.Octets.len(b)) == True{} : Bool}) -> {Nat.is_le(k, B.Octets.len(o)) == True{} : Bool}:
  rs.take_ge_o(k, n, o, Equal.trans(Bool, Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), Nat.is_le(k, B.Octets.len(b)), True{}, Equal.cong(B.Octets, Bool, z => Nat.is_le(k, B.Octets.len(z)), B.Octets.take(n, o), b, Equal.sym(B.Octets, b, B.Octets.take(n, o), er)), h))

def rs.built_ge_n(+k: Nat, +n: Nat, +b: B.Octets, +o: B.Octets, +er: {b == B.Octets.take(n, o) : B.Octets}, +h: {Nat.is_le(k, B.Octets.len(b)) == True{} : Bool}) -> {Nat.is_le(k, n) == True{} : Bool}:
  rs.take_ge_n(k, n, o, Equal.trans(Bool, Nat.is_le(k, B.Octets.len(B.Octets.take(n, o))), Nat.is_le(k, B.Octets.len(b)), True{}, Equal.cong(B.Octets, Bool, z => Nat.is_le(k, B.Octets.len(z)), B.Octets.take(n, o), b, Equal.sym(B.Octets, b, B.Octets.take(n, o), er)), h))

# the bytes of a built header: at least its fixed part
def rs.ipv4_lb.m(h: I4.Ipv4Header) -> {Nat.is_le(20n, B.len(I4.Ipv4Header.build.list(h))) == True{} : Bool}:
  match h:
    case I4.Ipv4Header{U32{a0}, U32{a1}, U32{a2}, U32{a3}, U32{a4}, U32{a5}, U32{a6}, U32{a7}, U32{a8}, U32{a9}, U32{a10}, U32{a11}, U32{a12}, o}:
      S.os.le_zero(B.len(B.Octets.to_list(o)))

def rs.tcp_lb.m(h: T.TcpHeader) -> {Nat.is_le(20n, B.len(T.TcpHeader.build.list(h))) == True{} : Bool}:
  match h:
    case T.TcpHeader{U32{a0}, U32{a1}, U32{a2}, U32{a3}, U32{a4}, U32{a5}, U32{a6}, U32{a7}, U32{a8}, U32{a9}, o}:
      S.os.le_zero(B.len(B.Octets.to_list(o)))

def rs.icmp_lb.m(h: C.IcmpHeader) -> {Nat.is_le(8n, B.len(C.IcmpHeader.build.list(h))) == True{} : Bool}:
  match h:
    case C.IcmpHeader{U32{a0}, U32{a1}, U32{a2}, U32{a3}}:
      {==}

def rs.udp_lb.m(h: U.UdpHeader) -> {Nat.is_le(8n, B.len(U.UdpHeader.build.list(h))) == True{} : Bool}:
  match h:
    case U.UdpHeader{U32{a0}, U32{a1}, U32{a2}, U32{a3}}:
      {==}

def rs.ipv4_lb(+h: I4.Ipv4Header) -> {Nat.is_le(20n, B.Octets.len(I4.Ipv4Header.build(h))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(I4.Ipv4Header.build.list(h))), B.len(I4.Ipv4Header.build.list(h)), BL.octets_len_of_list(I4.Ipv4Header.build.list(h))) : {Nat.is_le(20n, _) == True{} : Bool}
  rs.ipv4_lb.m(h)

def rs.tcp_lb(+h: T.TcpHeader) -> {Nat.is_le(20n, B.Octets.len(T.TcpHeader.build(h))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(T.TcpHeader.build.list(h))), B.len(T.TcpHeader.build.list(h)), BL.octets_len_of_list(T.TcpHeader.build.list(h))) : {Nat.is_le(20n, _) == True{} : Bool}
  rs.tcp_lb.m(h)

def rs.icmp_lb(+h: C.IcmpHeader) -> {Nat.is_le(8n, B.Octets.len(C.IcmpHeader.build(h))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(C.IcmpHeader.build.list(h))), B.len(C.IcmpHeader.build.list(h)), BL.octets_len_of_list(C.IcmpHeader.build.list(h))) : {Nat.is_le(8n, _) == True{} : Bool}
  rs.icmp_lb.m(h)

def rs.udp_lb(+h: U.UdpHeader) -> {Nat.is_le(8n, B.Octets.len(U.UdpHeader.build(h))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(U.UdpHeader.build.list(h))), B.len(U.UdpHeader.build.list(h)), BL.octets_len_of_list(U.UdpHeader.build.list(h))) : {Nat.is_le(8n, _) == True{} : Bool}
  rs.udp_lb.m(h)

# a bytes string is its first n bytes and the rest
def rs.rejoin(+b: B.Octets, +n: Nat, +o: B.Octets, +er: {b == B.Octets.take(n, o) : B.Octets}) -> {B.Octets.append(b, B.Octets.drop(n, o)) == o : B.Octets}:
  %Equal.sym(B.Octets, b, B.Octets.take(n, o), er) : {B.Octets.append(_, B.Octets.drop(n, o)) == o : B.Octets}
  BL.octets_take_drop(n, o)

# UDP's verify: with the field not zero, the sum is checked
def rs.go_s(z: Bool, +ok: Bool, +s: Bool, +ez: {z == False{} : Bool}, +e: {U.UdpHeader.verify.go(z, ok, s) == True{} : Bool}) -> {s == True{} : Bool}:
  match z:
    case True{}:
      Empty.absurd({s == True{} : Bool}, S.os.tf(ez))
    case False{}:
      e

def rs.go6_z(z: Bool, +s: Bool, +e: {U.UdpHeader.verify.go(z, False{}, s) == True{} : Bool}) -> {z == False{} : Bool}:
  match z:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.os.ft(e))
    case False{}:
      {==}

def rs.zf(+o: B.Octets, +c: U32, +hc: {B.Octets.be16_at(o, 6n) == Some{c} : Maybe<&2, U32>}) -> {U.UdpHeader.zero_field(B.Octets.be16_at(o, 6n)) == U32.is_eq(c, 0) : Bool}:
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(o, 6n), Some{c}, hc) : {U.UdpHeader.zero_field(_) == U32.is_eq(c, 0) : Bool}
  {==}

def rs.ne0(x: Nat, +h: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_le(1n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, S.os.tf(h))
    case 1n+ +p:
      S.os.le_zero(p)

def rs.add_d_zero(+x: Nat, +d: Nat, +e: {Nat.add(x, d) == d : Nat}) -> {x == 0n : Nat}:
  S.os.add_cancel_r(x, 0n, d, e)

# the field is not d: CC is c
def rs.nz.ne(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +hne: {Nat.is_eq(U32.to_nat(c), d) == False{} : Bool}) -> {K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == c : U32}:
  UL.u32_value_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), c, S.os.add_cancel_r(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(c), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), Equal.trans(Nat, Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, Nat.add(U32.to_nat(c), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), e2, Equal.trans(Nat, d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c)), Nat.add(U32.to_nat(c), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), Equal.sym(Nat, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c)), d, S.os.rep_eq_d(d, hd, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c), f0, fc, hne, r2)), UL.nat_add_comm(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))))))

# the field is d and the sum without it 0: CC is d, which is c
def rs.nz.s0z(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +es: {U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == 0n : Nat}, +ecd: {U32.to_nat(c) == d : Nat}, +ez: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0) == False{} : Bool}) -> {K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == c : U32}:
  UL.u32_value_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), c, Equal.trans(Nat, U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, U32.to_nat(c), Equal.trans(Nat, U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), 0n), d, Equal.sym(Nat, Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), 0n), U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), UL.nat_add_zero(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))))), Equal.trans(Nat, Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), 0n), Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), z), 0n, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0n, es)), e2)), Equal.sym(Nat, U32.to_nat(c), d, ecd)))

# the field is d and the sum without it not 0: then it is d, CC is 0
def rs.nz.s0p(+p: Nat, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +es: {U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == 1n+p : Nat}, +ecd: {U32.to_nat(c) == d : Nat}, +ez: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0) == False{} : Bool}) -> {K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == c : U32}:
  +ed = Equal.trans(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), S.os.rep(d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, Equal.sym(Nat, S.os.rep(d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), S.os.rep_small(d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), f0)), Equal.trans(Nat, S.os.rep(d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d)), d, Equal.sym(Nat, S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d)), S.os.rep(d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), S.os.rep_period(d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), hd, Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), Nat.is_le(1n, 1n+p), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n, z), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 1n+p, es), S.os.le_zero(p)))), Equal.trans(Nat, S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d)), S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))), d, Equal.cong(Nat, Nat, z => S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), z)), d, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), d, ecd)), r2)))
  +ec0 = rs.add_d_zero(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, Equal.trans(Nat, Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d), Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), z), d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d, ed)), e2))
  Empty.absurd({K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == c : U32}, S.os.tf(Equal.trans(Bool, True{}, U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), False{}, Equal.sym(Bool, U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), True{}, Equal.trans(Bool, U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), Nat.is_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(0)), True{}, UL.u32_eq_value(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), Equal.trans(Bool, Nat.is_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(0)), Nat.is_eq(0n, 0n), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, U32.to_nat(0)), U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), 0n, ec0), {==}))), ez)))

def rs.nz.s0(s: Nat, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +es: {U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == s : Nat}, +ecd: {U32.to_nat(c) == d : Nat}, +ez: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0) == False{} : Bool}) -> {K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == c : U32}:
  match s:
    case 0n:
      rs.nz.s0z(d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, es, ecd, ez)
    case 1n+ +p:
      rs.nz.s0p(p, d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, es, ecd, ez)

def rs.nz.f(b: Bool, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +eb: {Nat.is_eq(U32.to_nat(c), d) == b : Bool}, +ez: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0) == False{} : Bool}) -> {K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))) == c : U32}:
  match b:
    case False{}:
      rs.nz.ne(d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, eb)
    case True{}:
      rs.nz.s0(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, {==}, S.os.nat_eq(U32.to_nat(c), d, eb), ez)

# CC is 0, so 0xffff is written: then c is d
def rs.nz.t(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +ez: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0) == True{} : Bool}, +hk0: {U32.is_eq(c, 0) == False{} : Bool}) -> {c == 65535 : U32}:
  +ec0 = S.os.nat_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(0), Equal.trans(Bool, Nat.is_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(0)), U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), True{}, Equal.sym(Bool, U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), Nat.is_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(0)), UL.u32_eq_value(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0)), ez))
  +ed = Equal.trans(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), d, Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), 0n, U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), Equal.sym(Nat, U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), 0n, ec0)), e2)
  +h1 = rs.ne0(U32.to_nat(c), Equal.trans(Bool, Nat.is_eq(U32.to_nat(c), 0n), U32.is_eq(c, 0), False{}, Equal.sym(Bool, U32.is_eq(c, 0), Nat.is_eq(U32.to_nat(c), U32.to_nat(0)), UL.u32_eq_value(c, 0)), hk0))
  +ecd = Equal.trans(Nat, U32.to_nat(c), S.os.rep(d, U32.to_nat(c)), d, Equal.sym(Nat, S.os.rep(d, U32.to_nat(c)), U32.to_nat(c), S.os.rep_small(d, U32.to_nat(c), fc)), Equal.trans(Nat, S.os.rep(d, U32.to_nat(c)), S.os.rep(d, Nat.add(U32.to_nat(c), d)), d, Equal.sym(Nat, S.os.rep(d, Nat.add(U32.to_nat(c), d)), S.os.rep(d, U32.to_nat(c)), S.os.rep_period(d, U32.to_nat(c), hd, h1)), Equal.trans(Nat, S.os.rep(d, Nat.add(U32.to_nat(c), d)), S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))), d, Equal.cong(Nat, Nat, z => S.os.rep(d, z), Nat.add(U32.to_nat(c), d), Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c)), Equal.trans(Nat, Nat.add(U32.to_nat(c), d), Nat.add(d, U32.to_nat(c)), Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c)), UL.nat_add_comm(U32.to_nat(c), d), Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(c)), d, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d, ed)))), r2)))
  UL.u32_value_eq(c, 65535, Equal.trans(Nat, U32.to_nat(c), d, U32.to_nat(65535), ecd, Equal.sym(Nat, U32.to_nat(65535), d, hE)))

def rs.nz.go(z: Bool, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +f0: {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), d) == True{} : Bool}, +fc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}, +r2: {S.os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), U32.to_nat(c))) == d : Nat}, +e2: {Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))))) == d : Nat}, +ez: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0) == z : Bool}, +es: {K.inet_put16(o, 6n, c) == o : B.Octets}, +hk0: {U32.is_eq(c, 0) == False{} : Bool}) -> {K.inet_put16(o, 6n, U.UdpHeader.nonzero.go(z, K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))))) == o : B.Octets}:
  match z:
    case False{}:
      %Equal.sym(U32, K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), c, rs.nz.f(Nat.is_eq(U32.to_nat(c), d), d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, {==}, ez)) : {K.inet_put16(o, 6n, _) == o : B.Octets}
      es
    case True{}:
      %rs.nz.t(d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, ez, hk0) : {K.inet_put16(o, 6n, _) == o : B.Octets}
      es

# UdpHeader.fill on a datagram verified with a nonzero field gives it back
def rs.fillnz_self(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +c: U32, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(6n, o)) == True{} : Bool}, +hc: {B.Octets.be16_at(o, 6n) == Some{c} : Maybe<&2, U32>}, +hl: {Nat.is_le(Nat.add(6n, 2n), B.Octets.len(o)) == True{} : Bool}, +hv: {K.inet_verify(B.Octets.append(pseudo, o)) == True{} : Bool}, +hk0: {U32.is_eq(c, 0) == False{} : Bool}) -> {U.UdpHeader.fill(pseudo, o) == o : B.Octets}:
  +f0 = S.os.sum0_fits(d, hd, hD, hE, pseudo, o, 6n, eP, eT)
  +fc = S.os.be16_fits(d, hD, o, 6n, c, hc)
  +r2 = S.os.verified_sum(d, hd, hD, hE, pseudo, o, 6n, c, eP, eT, hc, hl, hv)
  +e2 = S.os.finish_value(d, hD, K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0))), f0)
  rs.nz.go(U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, 6n, 0)))), 0), d, hd, hD, hE, pseudo, o, c, f0, fc, r2, e2, {==}, S.os.put16_self(o, 6n, c, hc, hl), hk0)

# IPv4: parse_verified answered Done{h}: the parse did, and the header verified
def rs.pv_parse(r: Result<&2, &2, N.NetError, I4.Ipv4Header>, +o: B.Octets, +h: I4.Ipv4Header, +er: {I4.Ipv4Header.parse(o) == r : Result<&2, &2, N.NetError, I4.Ipv4Header>}, e: {I4.Ipv4Header.parse_verified.go(r, o) == Done{h} : Result<&2, &2, N.NetError, I4.Ipv4Header>}) -> {I4.Ipv4Header.parse(o) == Done{h} : Result<&2, &2, N.NetError, I4.Ipv4Header>}:
  match r:
    case Done{+g}:
      %RP.rv.check_done(I4.Ipv4Header, K.inet_verify(B.Octets.take(I4.Ipv4Header.length(g), o)), N.NetBadChecksum{}, g, h, e) : {I4.Ipv4Header.parse(o) == Done{_} : Result<&2, &2, N.NetError, I4.Ipv4Header>}
      er
    case Fail{x}:
      %e : RP.rv.pick(I4.Ipv4Header, _, {I4.Ipv4Header.parse(o) == Done{h} : Result<&2, &2, N.NetError, I4.Ipv4Header>}, Unit)
      Unit{}

def rs.pv_verify(r: Result<&2, &2, N.NetError, I4.Ipv4Header>, +o: B.Octets, +h: I4.Ipv4Header, +e: {I4.Ipv4Header.parse_verified.go(r, o) == Done{h} : Result<&2, &2, N.NetError, I4.Ipv4Header>}) -> {K.inet_verify(B.Octets.take(I4.Ipv4Header.length(h), o)) == True{} : Bool}:
  match r:
    case Done{+g}:
      %RP.rv.check_done(I4.Ipv4Header, K.inet_verify(B.Octets.take(I4.Ipv4Header.length(g), o)), N.NetBadChecksum{}, g, h, e) : {K.inet_verify(B.Octets.take(I4.Ipv4Header.length(_), o)) == True{} : Bool}
      RP.rv.check_true(I4.Ipv4Header, K.inet_verify(B.Octets.take(I4.Ipv4Header.length(g), o)), N.NetBadChecksum{}, g, h, e)
    case Fail{x}:
      %e : RP.rv.pick(I4.Ipv4Header, _, {K.inet_verify(B.Octets.take(I4.Ipv4Header.length(h), o)) == True{} : Bool}, Unit)
      Unit{}

def Laws.ipv4_reverse_checksum(o, h, c, e, hc, hk):
  +ep = rs.pv_parse(I4.Ipv4Header.parse(o), o, h, {==}, e)
  +ev = rs.pv_verify(I4.Ipv4Header.parse(o), o, h, e)
  +er = RL.ipv4_reverse(o, h, ep)
  +l20 = rs.ipv4_lb(h)
  +hn = rs.built_ge_n(Nat.add(10n, 2n), I4.Ipv4Header.length(h), I4.Ipv4Header.build(h), o, er, UO.nat_le_trans(Nat.add(10n, 2n), 20n, B.Octets.len(I4.Ipv4Header.build(h)), {==}, l20))
  +hcB = Equal.trans(Maybe<&2, U32>, B.Octets.be16_at(I4.Ipv4Header.build(h), 10n), B.Octets.be16_at(B.Octets.take(I4.Ipv4Header.length(h), o), 10n), Some{c}, Equal.cong(B.Octets, Maybe<&2, U32>, z => B.Octets.be16_at(z, 10n), I4.Ipv4Header.build(h), B.Octets.take(I4.Ipv4Header.length(h), o), er), Equal.trans(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.take(I4.Ipv4Header.length(h), o), 10n), B.Octets.be16_at(o, 10n), Some{c}, BL.octets_be16_at_take(I4.Ipv4Header.length(h), o, 10n, hn), hc))
  +hvB = Equal.trans(Bool, K.inet_verify(B.Octets.append(B.Octets.empty(), I4.Ipv4Header.build(h))), K.inet_verify(B.Octets.take(I4.Ipv4Header.length(h), o)), True{}, Equal.cong(B.Octets, Bool, z => K.inet_verify(z), B.Octets.append(B.Octets.empty(), I4.Ipv4Header.build(h)), B.Octets.take(I4.Ipv4Header.length(h), o), Equal.trans(B.Octets, B.Octets.append(B.Octets.empty(), I4.Ipv4Header.build(h)), I4.Ipv4Header.build(h), B.Octets.take(I4.Ipv4Header.length(h), o), BL.octets_append_empty_l(I4.Ipv4Header.build(h)), er)), ev)
  %er : {I4.Ipv4Header.build_checksum(h) == _ : B.Octets}
  S.os.fill_self(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), B.Octets.empty(), I4.Ipv4Header.build(h), 10n, c, {==}, S.os.even_take(I4.Ipv4Header.build(h), 5n, UO.nat_le_trans(Nat.double(5n), 20n, B.Octets.len(I4.Ipv4Header.build(h)), {==}, l20)), hcB, UO.nat_le_trans(Nat.add(10n, 2n), 20n, B.Octets.len(I4.Ipv4Header.build(h)), {==}, l20), hvB, hk)

def Laws.icmp_reverse_checksum(o, h, c, e, ev, hc, hk):
  +er = RL.icmp_reverse(o, h, e)
  +l8 = rs.built_ge(8n, 8n, C.IcmpHeader.build(h), o, er, rs.icmp_lb(h))
  %Equal.sym(B.Octets, B.Octets.append(C.IcmpHeader.build(h), B.Octets.drop(8n, o)), o, rs.rejoin(C.IcmpHeader.build(h), 8n, o, er)) : {K.inet_fill(B.Octets.empty(), _, 2n) == o : B.Octets}
  S.os.fill_self(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), B.Octets.empty(), o, 2n, c, {==}, S.os.even_take(o, 1n, UO.nat_le_trans(Nat.double(1n), 8n, B.Octets.len(o), {==}, l8)), hc, UO.nat_le_trans(Nat.add(2n, 2n), 8n, B.Octets.len(o), {==}, l8), Equal.trans(Bool, K.inet_verify(B.Octets.append(B.Octets.empty(), o)), K.inet_verify(o), True{}, Equal.cong(B.Octets, Bool, z => K.inet_verify(z), B.Octets.append(B.Octets.empty(), o), o, BL.octets_append_empty_l(o)), ev), hk)

def Laws.udp_ipv4_reverse_checksum(src, dst, dg, h, c, e, ev, hc, hk):
  +er = RL.udp_reverse(dg, h, e)
  +l8 = rs.built_ge(8n, 8n, U.UdpHeader.build(h), dg, er, rs.udp_lb(h))
  %Equal.sym(B.Octets, B.Octets.append(U.UdpHeader.build(h), B.Octets.drop(8n, dg)), dg, rs.rejoin(U.UdpHeader.build(h), 8n, dg, er)) : {U.UdpHeader.fill(I4.ipv4_pseudo(src, dst, 17, N.net.len32(_)), _) == dg : B.Octets}
  rs.fillnz_self(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I4.ipv4_pseudo(src, dst, 17, N.net.len32(dg)), dg, c, SP.h.pseudo4_even(src, dst, 17, U32.from_nat(B.Octets.len(dg))), S.os.even_take(dg, 3n, UO.nat_le_trans(Nat.double(3n), 8n, B.Octets.len(dg), {==}, l8)), hc, UO.nat_le_trans(Nat.add(6n, 2n), 8n, B.Octets.len(dg), {==}, l8), rs.go_s(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), True{}, K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, N.net.len32(dg)), dg)), Equal.trans(Bool, U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), U32.is_eq(c, 0), False{}, rs.zf(dg, c, hc), hk), ev), hk)

def Laws.udp_ipv6_reverse_checksum(src, dst, dg, h, c, e, ev, hc):
  +er = RL.udp_reverse(dg, h, e)
  +l8 = rs.built_ge(8n, 8n, U.UdpHeader.build(h), dg, er, rs.udp_lb(h))
  +hk = Equal.trans(Bool, U32.is_eq(c, 0), U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), False{}, Equal.sym(Bool, U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), U32.is_eq(c, 0), rs.zf(dg, c, hc)), rs.go6_z(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17), dg)), ev))
  %Equal.sym(B.Octets, B.Octets.append(U.UdpHeader.build(h), B.Octets.drop(8n, dg)), dg, rs.rejoin(U.UdpHeader.build(h), 8n, dg, er)) : {U.UdpHeader.fill(I6.ipv6_pseudo(src, dst, N.net.len32(_), 17), _) == dg : B.Octets}
  rs.fillnz_self(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17), dg, c, SP.h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(dg)), 17), S.os.even_take(dg, 3n, UO.nat_le_trans(Nat.double(3n), 8n, B.Octets.len(dg), {==}, l8)), hc, UO.nat_le_trans(Nat.add(6n, 2n), 8n, B.Octets.len(dg), {==}, l8), rs.go_s(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), False{}, K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17), dg)), rs.go6_z(U.UdpHeader.zero_field(B.Octets.be16_at(dg, 6n)), K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, N.net.len32(dg), 17), dg)), ev), ev), hk)

def Laws.tcp_ipv4_reverse_checksum(src, dst, seg, h, c, e, ev, hc, hk):
  +er = RL.tcp_reverse(seg, h, e)
  +l20 = rs.built_ge(20n, T.TcpHeader.length(h), T.TcpHeader.build(h), seg, er, rs.tcp_lb(h))
  %Equal.sym(B.Octets, B.Octets.append(T.TcpHeader.build(h), B.Octets.drop(T.TcpHeader.length(h), seg)), seg, rs.rejoin(T.TcpHeader.build(h), T.TcpHeader.length(h), seg, er)) : {K.inet_fill(I4.ipv4_pseudo(src, dst, 6, N.net.len32(_)), _, 16n) == seg : B.Octets}
  S.os.fill_self(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I4.ipv4_pseudo(src, dst, 6, N.net.len32(seg)), seg, 16n, c, SP.h.pseudo4_even(src, dst, 6, U32.from_nat(B.Octets.len(seg))), S.os.even_take(seg, 8n, UO.nat_le_trans(Nat.double(8n), 20n, B.Octets.len(seg), {==}, l20)), hc, UO.nat_le_trans(Nat.add(16n, 2n), 20n, B.Octets.len(seg), {==}, l20), ev, hk)

def Laws.tcp_ipv6_reverse_checksum(src, dst, seg, h, c, e, ev, hc, hk):
  +er = RL.tcp_reverse(seg, h, e)
  +l20 = rs.built_ge(20n, T.TcpHeader.length(h), T.TcpHeader.build(h), seg, er, rs.tcp_lb(h))
  %Equal.sym(B.Octets, B.Octets.append(T.TcpHeader.build(h), B.Octets.drop(T.TcpHeader.length(h), seg)), seg, rs.rejoin(T.TcpHeader.build(h), T.TcpHeader.length(h), seg, er)) : {K.inet_fill(I6.ipv6_pseudo(src, dst, N.net.len32(_), 6), _, 16n) == seg : B.Octets}
  S.os.fill_self(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), S.os.hd(), S.os.hD(), S.os.hE(), I6.ipv6_pseudo(src, dst, N.net.len32(seg), 6), seg, 16n, c, SP.h.pseudo6_even(src, dst, U32.from_nat(B.Octets.len(seg)), 6), S.os.even_take(seg, 8n, UO.nat_le_trans(Nat.double(8n), 20n, B.Octets.len(seg), {==}, l20)), hc, UO.nat_le_trans(Nat.add(16n, 2n), 20n, B.Octets.len(seg), {==}, l20), ev, hk)
