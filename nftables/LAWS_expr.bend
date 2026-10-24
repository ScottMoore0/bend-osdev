# What the expressions mean, for every input:
# * payload loads (NftSrcPayload{base, offset, len}) are byte reads at
#   offsets: the load is the len bytes at the offset of the base's bytes
#   (the headers from that layer on, as netheaders builds them, then the
#   data), and its byte i is the base's byte at offset + i; a load that
#   would run past the end, or from a layer the packet does not have, gives
#   nothing (and so matches nothing);
# * comparisons are the key order on Octets (sets.bend: byte by byte, most
#   significant first): == holds exactly for the value itself, != is its
#   negation, < <= > >= are NftKey.lt and NftKey.le one way or the other
#   round; a range test is an element's interval test; in and not in are
#   set membership; one-byte keys compare as their numbers;
# * limits: the first packet through a limit with no bucket yet conforms
#   exactly when its cost (unit_ms, per byte if bytes) is at most the
#   bucket's capacity (burst tokens, rate if burst is 0, of unit_ms each);
#   `over` only inverts the match: the buckets evolve the same.
#
# Not stated here: the refill arithmetic (the credit after elapsed ms is
# min(capacity, credit + elapsed * rate)), which rests on 64-bit
# multiplication and division, for which bend-osdev-word64 has no value
# laws yet.
#
# A pair of its own (PROOF_expr.bend): the proofs rest on PROOF_map.bend's
# key order lemmas and on bend-osdev-bytes', -u32's and -word64's laws.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../netheaders/udp.bend as NU
import ./sets.bend as S
import ./expr.bend as X

# whether an expression let the rule go on
def expr_ok(o: X.NftExprOut) -> Bool:
  match o:
    case X.NftExprOk{env}:
      True{}
    case X.NftExprFail{env}:
      False{}
    case X.NftExprVerdict{v, env}:
      False{}

# the packet, state and time an expression leaves
def expr_env(o: X.NftExprOut) -> X.NftEnv:
  match o:
    case X.NftExprOk{env}:
      env
    case X.NftExprFail{env}:
      env
    case X.NftExprVerdict{v, env}:
      env

# byte i of a loaded value
def load_at(m: Maybe<&2, B.Octets>, +i: Nat) -> Maybe<&2, U32>:
  match m:
    case Some{v}:
      B.Octets.at(v, i)
    case None{}:
      None{}

# a limit's bucket: burst tokens (rate if burst is 0) of unit_ms each
def limit_tokens(z: Bool, burst: U32, rate: U32) -> U32:
  match z:
    case True{}:
      rate
    case False{}:
      burst

def limit_cap(+rate: U32, unit: U32, +burst: U32) -> W.W64:
  W.W64.mul(W.W64.from_u32(limit_tokens(U32.is_eq(burst, 0), burst, rate)), W.W64.from_u32(unit))

# what a packet of len bytes costs: unit_ms, per byte when the limit counts
# bytes
def limit_cost(bytes: Bool, +unit: U32, len: U32) -> W.W64:
  match bytes:
    case True{}:
      W.W64.mul(W.W64.from_u32(len), W.W64.from_u32(unit))
    case False{}:
      W.W64.from_u32(unit)

# Payload loads

law payload_load:
  for +b: X.NftPayloadBase
  for +off: Nat
  for +len: Nat
  for +sets: List<&2, S.NftNamedSet>
  for +p: X.NftPacket
  for +o: B.Octets
  for h: {X.NftPacket.base(b, p) == Some{o} : Maybe<&2, B.Octets>}
  for hf: {Nat.is_le(Nat.add(off, len), B.Octets.len(o)) == True{} : Bool}
  {X.NftSrc.load(X.NftSrcPayload{b, off, len}, sets, p) == Some{B.Octets.slice(off, len, o)} : Maybe<&2, B.Octets>}

law payload_at:
  for +b: X.NftPayloadBase
  for +off: Nat
  for +len: Nat
  for +i: Nat
  for +sets: List<&2, S.NftNamedSet>
  for +p: X.NftPacket
  for +o: B.Octets
  for h: {X.NftPacket.base(b, p) == Some{o} : Maybe<&2, B.Octets>}
  for hf: {Nat.is_le(Nat.add(off, len), B.Octets.len(o)) == True{} : Bool}
  for hi: {Nat.is_lt(i, len) == True{} : Bool}
  {load_at(X.NftSrc.load(X.NftSrcPayload{b, off, len}, sets, p), i) == B.Octets.at(o, Nat.add(off, i)) : Maybe<&2, U32>}

law payload_short:
  for +b: X.NftPayloadBase
  for +off: Nat
  for +len: Nat
  for +sets: List<&2, S.NftNamedSet>
  for +p: X.NftPacket
  for +o: B.Octets
  for h: {X.NftPacket.base(b, p) == Some{o} : Maybe<&2, B.Octets>}
  for hf: {Nat.is_le(Nat.add(off, len), B.Octets.len(o)) == False{} : Bool}
  {X.NftSrc.load(X.NftSrcPayload{b, off, len}, sets, p) == None{} : Maybe<&2, B.Octets>}

law payload_no_base:
  for +b: X.NftPayloadBase
  for +off: Nat
  for +len: Nat
  for +sets: List<&2, S.NftNamedSet>
  for +p: X.NftPacket
  for h: {X.NftPacket.base(b, p) == None{} : Maybe<&2, B.Octets>}
  {X.NftSrc.load(X.NftSrcPayload{b, off, len}, sets, p) == None{} : Maybe<&2, B.Octets>}

# Comparisons

law cmp_eq_holds:
  for +v: B.Octets
  for +w: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  for h: {X.NftTest.check(X.NftCmp{X.NftOpEq{}, w}, v, sets) == True{} : Bool}
  {v == w : B.Octets}

law cmp_eq_refl:
  for +v: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftCmp{X.NftOpEq{}, v}, v, sets) == True{} : Bool}

law cmp_ne:
  for +v: B.Octets
  for +w: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftCmp{X.NftOpNe{}, w}, v, sets) == Bool.not(X.NftTest.check(X.NftCmp{X.NftOpEq{}, w}, v, sets)) : Bool}

law cmp_lt:
  for +v: B.Octets
  for +w: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftCmp{X.NftOpLt{}, w}, v, sets) == S.NftKey.lt(v, w) : Bool}

law cmp_le:
  for +v: B.Octets
  for +w: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftCmp{X.NftOpLe{}, w}, v, sets) == S.NftKey.le(v, w) : Bool}

law cmp_gt:
  for +v: B.Octets
  for +w: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftCmp{X.NftOpGt{}, w}, v, sets) == S.NftKey.lt(w, v) : Bool}

law cmp_ge:
  for +v: B.Octets
  for +w: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftCmp{X.NftOpGe{}, w}, v, sets) == S.NftKey.le(w, v) : Bool}

law range_contains:
  for +lo: B.Octets
  for +hi: B.Octets
  for +v: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftRange{lo, hi}, v, sets) == S.NftElem.contains(S.NftElem.range(lo, hi), v) : Bool}

law not_range_contains:
  for +lo: B.Octets
  for +hi: B.Octets
  for +v: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftNotRange{lo, hi}, v, sets) == Bool.not(S.NftElem.contains(S.NftElem.range(lo, hi), v)) : Bool}

law in_set_mem:
  for +s: S.NftSet
  for +v: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftIn{X.NftSetAnon{s}}, v, sets) == S.NftSet.mem(s, v) : Bool}

law not_in_set_mem:
  for +s: S.NftSet
  for +v: B.Octets
  for +sets: List<&2, S.NftNamedSet>
  {X.NftTest.check(X.NftNotIn{X.NftSetAnon{s}}, v, sets) == Bool.not(S.NftSet.mem(s, v)) : Bool}

# one-byte keys compare as the numbers (bytes) they hold
law key_u8_cmp:
  for +a: U32
  for +b: U32
  {S.NftKey.cmp(S.NftKey.u8(a), S.NftKey.u8(b)) == U32.cmp(B.byte(a), B.byte(b)) : Cmp}

# Limits

law limit_fresh:
  for +id: U32
  for +rate: U32
  for +unit: U32
  for +burst: U32
  for +bytes: Bool
  for +over: Bool
  for +sets: List<&2, S.NftNamedSet>
  for +p: X.NftPacket
  for +cs: List<&2, X.NftCounterVal>
  for +now: W.W64
  {expr_ok(X.NftExpr.eval(X.NftLimit{id, X.NftLimitSpec{rate, unit, burst, bytes, over}}, sets, X.NftEnv{p, X.NftState{cs, Nil{}}, now})) == Bool.xor(W.W64.is_ge(limit_cap(rate, unit, burst), limit_cost(bytes, unit, X.NftPacket.length(p))), over) : Bool}

law limit_over:
  for +id: U32
  for +rate: U32
  for +unit: U32
  for +burst: U32
  for +bytes: Bool
  for +sets: List<&2, S.NftNamedSet>
  for +env: X.NftEnv
  {expr_ok(X.NftExpr.eval(X.NftLimit{id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}}, sets, env)) == Bool.not(expr_ok(X.NftExpr.eval(X.NftLimit{id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}}, sets, env))) : Bool}

law limit_over_env:
  for +id: U32
  for +rate: U32
  for +unit: U32
  for +burst: U32
  for +bytes: Bool
  for +sets: List<&2, S.NftNamedSet>
  for +env: X.NftEnv
  {expr_env(X.NftExpr.eval(X.NftLimit{id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}}, sets, env)) == expr_env(X.NftExpr.eval(X.NftLimit{id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}}, sets, env)) : X.NftEnv}

# Vectors

# a UDP datagram from port 5353 to port 53, with no network layer
def vec_pkt() -> X.NftPacket:
  X.NftPacket{X.NftMeta{1, 2, 0, 17, 100, 2}, X.NftCt{0, 0}, X.NftL2None{}, X.NftL3None{}, X.NftL4Udp{NU.UdpHeader{5353, 53, 8, 0}}, B.Octets.empty()}

# th dport reads bytes 2 and 3 of the UDP header; 4 bytes at offset 6 run
# past its 8; there is no network layer to load from
law payload_vec:
  {(X.NftSrc.load(X.NftField.th_dport(), Nil{}, vec_pkt()), X.NftSrc.load(X.NftSrcPayload{X.NftBaseTh{}, 6n, 4n}, Nil{}, vec_pkt()), X.NftSrc.load(X.NftField.ip_protocol(), Nil{}, vec_pkt())) == (Some{S.NftKey.u16(53)}, None{}, None{}) : Maybe<&2, B.Octets> & Maybe<&2, B.Octets> & Maybe<&2, B.Octets>}

# the hypotheses of the payload laws hold: the transport base of vec_pkt,
# a load that fits, a byte inside it, one that does not fit, a missing base
law payload_sat:
  {(X.NftPacket.base(X.NftBaseTh{}, vec_pkt()), Nat.is_le(Nat.add(2n, 2n), B.Octets.len(B.Octets.of_list([20, 233, 0, 53, 0, 8, 0, 0]))), Nat.is_lt(1n, 2n), Nat.is_le(Nat.add(6n, 4n), B.Octets.len(B.Octets.of_list([20, 233, 0, 53, 0, 8, 0, 0]))), X.NftPacket.base(X.NftBaseNh{}, vec_pkt())) == (Some{B.Octets.of_list([20, 233, 0, 53, 0, 8, 0, 0])}, True{}, True{}, False{}, None{}) : Maybe<&2, B.Octets> & Bool & Bool & Bool & Maybe<&2, B.Octets>}

# ports compared as keys; a range; a set; the hypothesis of cmp_eq_holds
# holds for a value and itself (cmp_eq_refl), and fails for another
law cmp_vec:
  {(X.NftTest.check(X.NftCmp{X.NftOpGt{}, S.NftKey.u16(1024)}, S.NftKey.u16(8080), Nil{}), X.NftTest.check(X.NftCmp{X.NftOpEq{}, S.NftKey.u16(80)}, S.NftKey.u16(443), Nil{}), X.NftTest.check(X.NftRange{S.NftKey.u16(1000), S.NftKey.u16(2000)}, S.NftKey.u16(1500), Nil{}), X.NftTest.check(X.NftIn{X.NftSetAnon{S.NftSet{[S.NftElem.single(S.NftKey.u16(22))]}}}, S.NftKey.u16(22), Nil{})) == (True{}, False{}, True{}, True{}) : Bool & Bool & Bool & Bool}

# limit 1 packet per second, burst 1: a packet passes at 0 ms, the next at
# 0 ms does not, one at 1000 ms does
def vec_lim() -> X.NftExpr:
  X.NftLimit{7, X.NftLimitSpec{1, 1000, 1, False{}, False{}}}

def vec_at.env(e: X.NftEnv, now: W.W64) -> X.NftEnv:
  match e:
    case X.NftEnv{p, st, t}:
      X.NftEnv{p, st, now}

def vec_at(o: X.NftExprOut, now: W.W64) -> X.NftEnv:
  vec_at.env(expr_env(o), now)

def vec_lim1() -> X.NftExprOut:
  X.NftExpr.eval(vec_lim(), Nil{}, X.NftEnv{vec_pkt(), X.NftState.empty(), W.W64.zero()})

def vec_lim2() -> X.NftExprOut:
  X.NftExpr.eval(vec_lim(), Nil{}, vec_at(vec_lim1(), W.W64.zero()))

def vec_lim3() -> X.NftExprOut:
  X.NftExpr.eval(vec_lim(), Nil{}, vec_at(vec_lim2(), W.W64.from_u32(1000)))

law limit_vec:
  {(expr_ok(vec_lim1()), expr_ok(vec_lim2()), expr_ok(vec_lim3())) == (True{}, False{}, True{}) : Bool & Bool & Bool}
