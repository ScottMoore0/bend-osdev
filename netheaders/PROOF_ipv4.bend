# Proof of LAWS_ipv4.bend, written by ref/gen_sum.py. The bytes that
# build_checksum writes are those of the header with its checksum field set
# to the checksum (h4.eq, by computation on the bits of the fields the
# checksum word shares, TTL and protocol, and of the two checksums); so the
# parser reads them back by the round trip (LAWS.bend), the length it reads
# is the bytes' length (h4.len, case by case on the IHL), and the bytes
# verify by inet_fill_verifies (LAWS_sum.bend).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./LAWS.bend as NL
import ./PROOF.bend as NP
import ./LAWS_sum.bend as SL
import ./PROOF_sum.bend as SP
import ./proof_ones.bend as S
import ./LAWS_ipv4.bend as Laws

# The built bytes, with c written into the checksum field, are the header's
# with checksum c
def h4.eq.list(ihl: U32, dscp: U32, ecn: U32, tl: U32, id: U32, fl: U32, fo: U32, ttl: U32, pr: U32, ck: U32, src: U32, dst: U32, +options: List<&2, U32>, c: U32) -> {B.append(B.mask(B.take(10n, I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(10n, 2n), I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))))) == B.mask(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) : List<&2, U32>}:
  match ihl dscp ecn tl id fl fo ttl pr ck src dst c:
    case U32{ihl_} U32{dscp_} U32{ecn_} U32{tl_} U32{id_} U32{fl_} U32{fo_} U32{WCon{ttl_0, WCon{ttl_1, WCon{ttl_2, WCon{ttl_3, WCon{ttl_4, WCon{ttl_5, WCon{ttl_6, WCon{ttl_7, ttl_h}}}}}}}}} U32{WCon{pr_0, WCon{pr_1, WCon{pr_2, WCon{pr_3, WCon{pr_4, WCon{pr_5, WCon{pr_6, WCon{pr_7, pr_h}}}}}}}}} U32{WCon{ck_0, WCon{ck_1, WCon{ck_2, WCon{ck_3, WCon{ck_4, WCon{ck_5, WCon{ck_6, WCon{ck_7, WCon{ck_8, WCon{ck_9, WCon{ck_10, WCon{ck_11, WCon{ck_12, WCon{ck_13, WCon{ck_14, WCon{ck_15, ck_h}}}}}}}}}}}}}}}}} U32{src_} U32{dst_} U32{WCon{c_0, WCon{c_1, WCon{c_2, WCon{c_3, WCon{c_4, WCon{c_5, WCon{c_6, WCon{c_7, WCon{c_8, WCon{c_9, WCon{c_10, WCon{c_11, WCon{c_12, WCon{c_13, WCon{c_14, WCon{c_15, c_h}}}}}}}}}}}}}}}}}:
      {==}

def h4.len.m(ihl: U32, dscp: U32, ecn: U32, tl: U32, id: U32, fl: U32, fo: U32, ttl: U32, pr: U32, ck: U32, src: U32, dst: U32, +options: List<&2, U32>) -> {B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(B.Octets.to_list(B.Octets.of_list(options)))) : Nat}:
  match ihl dscp ecn tl id fl fo ttl pr ck src dst:
    case U32{ihl_} U32{dscp_} U32{ecn_} U32{tl_} U32{id_} U32{fl_} U32{fo_} U32{ttl_} U32{pr_} U32{ck_} U32{src_} U32{dst_}:
      {==}

def h4.len12.m(ihl: U32, dscp: U32, ecn: U32, tl: U32, id: U32, fl: U32, fo: U32, ttl: U32, pr: U32, ck: U32, src: U32, dst: U32, +options: List<&2, U32>) -> {Nat.is_le(Nat.add(10n, 2n), B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) == True{} : Bool}:
  match ihl dscp ecn tl id fl fo ttl pr ck src dst:
    case U32{ihl_} U32{dscp_} U32{ecn_} U32{tl_} U32{id_} U32{fl_} U32{fo_} U32{ttl_} U32{pr_} U32{ck_} U32{src_} U32{dst_}:
      {==}

def h4.len10.m(ihl: U32, dscp: U32, ecn: U32, tl: U32, id: U32, fl: U32, fo: U32, ttl: U32, pr: U32, ck: U32, src: U32, dst: U32, +options: List<&2, U32>) -> {Nat.is_le(Nat.double(5n), B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) == True{} : Bool}:
  match ihl dscp ecn tl id fl fo ttl pr ck src dst:
    case U32{ihl_} U32{dscp_} U32{ecn_} U32{tl_} U32{id_} U32{fl_} U32{fo_} U32{ttl_} U32{pr_} U32{ck_} U32{src_} U32{dst_}:
      {==}

def h4.len10(+ihl: U32, +dscp: U32, +ecn: U32, +tl: U32, +id: U32, +fl: U32, +fo: U32, +ttl: U32, +pr: U32, +ck: U32, +src: U32, +dst: U32, +options: List<&2, U32>) -> {Nat.is_le(Nat.double(5n), B.Octets.len(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))), B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), BL.octets_len_of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) : {Nat.is_le(Nat.double(5n), _) == True{} : Bool}
  h4.len10.m(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options)

def h4.len12(+ihl: U32, +dscp: U32, +ecn: U32, +tl: U32, +id: U32, +fl: U32, +fo: U32, +ttl: U32, +pr: U32, +ck: U32, +src: U32, +dst: U32, +options: List<&2, U32>) -> {Nat.is_le(Nat.add(10n, 2n), B.Octets.len(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))), B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), BL.octets_len_of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) : {Nat.is_le(Nat.add(10n, 2n), _) == True{} : Bool}
  h4.len12.m(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options)

def h4.eq(+ihl: U32, +dscp: U32, +ecn: U32, +tl: U32, +id: U32, +fl: U32, +fo: U32, +ttl: U32, +pr: U32, +ck: U32, +src: U32, +dst: U32, +options: List<&2, U32>, +c: U32) -> {K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, c) == I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)}) : B.Octets}:
  %BL.octets_of_to(K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, c)) : {_ == I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)}) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(K.inet_put16(B.Octets.of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), 10n, c)), B.append(B.mask(B.take(10n, I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(10n, 2n), I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))))), S.os.put16_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, c, h4.len12.m(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options))) : {B.Octets.of_list(_) == I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)}) : B.Octets}
  %Equal.sym(List<&2, U32>, B.append(B.mask(B.take(10n, I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(10n, 2n), I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))))), B.mask(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})), h4.eq.list(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options, c)) : {B.Octets.of_list(_) == I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)}) : B.Octets}
  %BL.octets_to_of(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) : {B.Octets.of_list(_) == I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)}) : B.Octets}
  BL.octets_of_list_idempotent(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)}))

# the length of the bytes build_checksum writes: 20 bytes and the options
def h4.lenR(+ihl: U32, +dscp: U32, +ecn: U32, +tl: U32, +id: U32, +fl: U32, +fo: U32, +ttl: U32, +pr: U32, +ck: U32, +src: U32, +dst: U32, +options: List<&2, U32>) -> {B.Octets.len(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))))), B.Octets.len(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), S.os.len_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), h4.len12(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options))) : {_ == Nat.add(20n, B.len(options)) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))), B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), BL.octets_len_of_list(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) : {_ == Nat.add(20n, B.len(options)) : Nat}
  %Equal.sym(Nat, B.len(I4.Ipv4Header.build.list(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), Nat.add(20n, B.len(B.Octets.to_list(B.Octets.of_list(options)))), h4.len.m(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options)) : {_ == Nat.add(20n, B.len(options)) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(options)), B.mask(options), BL.octets_to_of(options)) : {Nat.add(20n, B.len(_)) == Nat.add(20n, B.len(options)) : Nat}
  %Equal.sym(Nat, B.len(B.mask(options)), B.len(options), S.os.len_mask(options)) : {Nat.add(20n, _) == Nat.add(20n, B.len(options)) : Nat}
  {==}

def h4.len(ihl: U32, +e1: {U32.is_ge(N.NetField.low(4n, ihl), 5) == True{} : Bool}, +dscp: U32, +ecn: U32, +tl: U32, +id: U32, +fl: U32, +fo: U32, +ttl: U32, +pr: U32, +ck: U32, +src: U32, +dst: U32, +options: List<&2, U32>, +c: U32, +e2: {B.len(options) == Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n) : Nat}) -> {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}:
  match ihl:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, ih}}}}}:
      Empty.absurd({I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}, S.os.ft(e1))
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, ih}}}}}:
      Empty.absurd({I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}, S.os.ft(e1))
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, ih}}}}}:
      Empty.absurd({I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}, S.os.ft(e1))
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, ih}}}}}:
      Empty.absurd({I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}, S.os.ft(e1))
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, ih}}}}}:
      Empty.absurd({I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, B.len(options)) : Nat}, S.os.ft(e1))
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, ih}}}}}:
      %Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, c, src, dst, B.Octets.of_list(options)})) == Nat.add(20n, _) : Nat}
      {==}

def Laws.ipv4_build_verifies(ihl, e1, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options, e2):
  %Equal.sym(B.Octets, K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0)))), I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, B.Octets.of_list(options)}), h4.eq(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))))) : {I4.Ipv4Header.verify.go(I4.Ipv4Header.parse(_), I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})) == True{} : Bool}
  %BL.octets_append_empty_r(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, B.Octets.of_list(options)})) : {I4.Ipv4Header.verify.go(I4.Ipv4Header.parse(_), I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})) == True{} : Bool}
  %Equal.sym(Result<&2, &2, N.NetError, I4.Ipv4Header>, I4.Ipv4Header.parse(B.Octets.append(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, B.Octets.of_list(options)}), B.Octets.empty())), Done{I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, B.Octets.of_list(options)})}, NL.ipv4_round_trip(ihl, e1, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, options, e2, B.Octets.empty())) : {I4.Ipv4Header.verify.go(_, I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})) == True{} : Bool}
  %Equal.sym(Nat, I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, B.Octets.of_list(options)})), B.Octets.len(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), Equal.trans(Nat, I4.Ipv4Header.length(I4.Ipv4Header.norm(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), src, dst, B.Octets.of_list(options)})), Nat.add(20n, B.len(options)), B.Octets.len(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), h4.len(ihl, e1, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options, K.inet_checksum(B.Octets.append(B.Octets.empty(), K.inet_put16(I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 10n, 0))), e2), Equal.sym(Nat, B.Octets.len(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), Nat.add(20n, B.len(options)), h4.lenR(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options)))) : {K.inet_verify(B.Octets.take(_, I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})), I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), BL.octets_take_len(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}))) : {K.inet_verify(_) == True{} : Bool}
  %BL.octets_append_empty_l(I4.Ipv4Header.build_checksum(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)})) : {K.inet_verify(_) == True{} : Bool}
  SL.inet_fill_verifies(B.Octets.empty(), I4.Ipv4Header.build(I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, B.Octets.of_list(options)}), 5n, {==}, h4.len10(ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options))

def Laws.ipv4_build_verifies_sat():
  {==}
