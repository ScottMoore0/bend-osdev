import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./family.bend as F
import ./verdict.bend as V
import ./sets.bend as S
import ./expr.bend as X
import ./chains.bend as C
import ./nftables.bend as N

def src4(far: Bool, s: U32) -> List<&2, U32>:
  match far:
    case True{}:
      [192, 168, 1, s]
    case False{}:
      [10, 0, 0, s]

# An IPv4 TCP SYN from 10.0.0.s (or 192.168.1.s if far) to 10.0.0.2, port
# dport, as bytes (RFC 791, RFC 9293)
def tcp4(far: Bool, s: U32, dport: U32) -> B.Octets:
  B.Octets.of_list(B.append([69, 0, 0, 40, 0, 1, 0, 0, 64, 6, 0, 0], B.append(src4(far, s), B.append([10, 0, 0, 2, 48, 57], B.append(B.be16(dport), [0, 0, 0, 1, 0, 0, 0, 0, 80, 2, 255, 255, 0, 0, 0, 0])))))

# An IPv6 UDP datagram to port dport (RFC 8200, RFC 768)
def udp6(dport: U32) -> B.Octets:
  B.Octets.of_list(B.append([96, 0, 0, 0, 0, 8, 17, 64], B.append(B.zeros(15n), B.append([1], B.append(B.zeros(15n), B.append([2, 4, 0], B.append(B.be16(dport), [0, 8, 0, 0])))))))

def ct0() -> X.NftCt:
  X.NftCt{X.NftCt.NEW(), 0}

def pkt_or(r: Result<&2, &2, F.NftError, X.NftPacket>) -> X.NftPacket:
  match r:
    case Done{p}:
      p
    case Fail{e}:
      X.NftPacket{X.NftMeta{0, 0, 0, 0, 0, 0}, ct0(), X.NftL2None{}, X.NftL3None{}, X.NftL4None{}, B.Octets.empty()}

def syn(far: Bool, s: U32, dport: U32) -> X.NftPacket:
  pkt_or(X.NftPacket.of_ip(1, 0, 0, ct0(), tcp4(far, s, dport)))

def est(dport: U32) -> X.NftPacket:
  pkt_or(X.NftPacket.of_ip(1, 0, 0, X.NftCt{X.NftCt.ESTABLISHED(), 0}, tcp4(False{}, 1, dport)))

def v6(dport: U32) -> X.NftPacket:
  pkt_or(X.NftPacket.of_ip(1, 0, 0, ct0(), udp6(dport)))

def base(h: F.NftHook, prio: U32, pol: V.NftPolicy) -> Maybe<&2, C.NftBaseSpec>:
  Some{C.NftBaseSpec{h, prio, pol}}

def rule(xs: List<&2, X.NftExpr>) -> X.NftRule:
  X.NftRule{xs}

def verd(v: V.NftVerdict) -> X.NftRule:
  X.NftRule{[X.NftVerdictStmt{v}]}

def dport(p: U32, v: V.NftVerdict) -> X.NftRule:
  X.NftRule{[X.NftExpr.needs_l4proto(6), X.NftExpr.eq(X.NftField.th_dport(), S.NftKey.u16(p)), X.NftVerdictStmt{v}]}

def set_of(r: Result<&2, &2, F.NftError, S.NftSet>) -> S.NftSet:
  match r:
    case Done{s}:
      s
    case Fail{e}:
      S.NftSet.empty()

def web_ports() -> S.NftSet:
  set_of(S.NftSet.of_list([S.NftElem.single(S.NftKey.u16(80)), S.NftElem.single(S.NftKey.u16(443))]))

# table inet filter: input, policy drop: established accept, ssh accept,
# web ports jump web; web: count, 10.0.0.0/8 accept
def filter() -> C.NftRuleset:
  C.NftRuleset{[C.NftTable{"filter", F.NftInet{}, [C.NftChain{"input", base(F.NftInput{}, F.NftPrio.filter(), V.NftPolicyDrop{}), [rule([X.NftExpr.ct_state(U32.or(X.NftCt.ESTABLISHED(), X.NftCt.RELATED())), X.NftVerdictStmt{V.NftAccept{}}]), dport(22, V.NftAccept{}), rule([X.NftExpr.needs_l4proto(6), X.NftExpr.in_set(X.NftField.th_dport(), X.NftSetNamed{"web_ports"}), X.NftVerdictStmt{V.NftJump{"web"}}])]}, C.NftChain{"web", None{}, [rule([X.NftCount{1}]), rule([X.NftExpr.in_set(X.NftField.ip_saddr(), X.NftSetAnon{set_of(S.NftSet.of_list([S.NftElem.prefix(S.NftKey.ipv4(10, 0, 0, 0), 8n)]))}), X.NftVerdictStmt{V.NftAccept{}}])]}], [S.NftNamedSet{"web_ports", web_ports()}]}]}

def run(rs: C.NftRuleset, p: X.NftPacket) -> String:
  N.NftResult.show(N.Nft.eval_default(rs, F.NftProtoIpv4{}, F.NftInput{}, W.W64.zero(), p, X.NftState.empty()))

def run6(rs: C.NftRuleset, p: X.NftPacket) -> String:
  N.NftResult.show(N.Nft.eval_default(rs, F.NftProtoIpv6{}, F.NftInput{}, W.W64.zero(), p, X.NftState.empty()))

def one(name: String, f: F.NftFamily, h: F.NftHook, prio: U32, pol: V.NftPolicy, rules: List<&2, X.NftRule>) -> C.NftTable:
  C.NftTable{name, f, [C.NftChain{"c", base(h, prio, pol), rules}], Nil{}}

def calls.a(goto_b: Bool) -> X.NftRule:
  match goto_b:
    case True{}:
      verd(V.NftGoto{"b"})
    case False{}:
      verd(V.NftJump{"b"})

# chains a, b: base jumps to a, a goes to b, b returns: back after the jump
def calls(goto_b: Bool) -> C.NftRuleset:
  C.NftRuleset{[C.NftTable{"t", F.NftIp{}, [C.NftChain{"in", base(F.NftInput{}, 0, V.NftPolicyDrop{}), [verd(V.NftJump{"a"}), rule([X.NftCount{7}, X.NftVerdictStmt{V.NftAccept{}}])]}, C.NftChain{"a", None{}, [calls.a(goto_b), rule([X.NftCount{8}, X.NftVerdictStmt{V.NftDrop{}}])]}, C.NftChain{"b", None{}, [rule([X.NftCount{9}]), verd(V.NftReturn{})]}], Nil{}}]}

# a chain that jumps to itself
def loop() -> C.NftRuleset:
  C.NftRuleset{[C.NftTable{"t", F.NftIp{}, [C.NftChain{"in", base(F.NftInput{}, 0, V.NftPolicyAccept{}), [verd(V.NftJump{"a"})]}, C.NftChain{"a", None{}, [verd(V.NftJump{"a"})]}], Nil{}}]}

# a verdict map on the destination port, and a mark from a map on the source
def vmap() -> C.NftRuleset:
  +m = set_of(S.NftSet.of_list([S.NftElem.to(S.NftElem.prefix(S.NftKey.ipv4(10, 0, 0, 0), 8n), S.NftDataValue{S.NftKey.u32(1)}), S.NftElem.to(S.NftElem.prefix(S.NftKey.ipv4(192, 168, 0, 0), 16n), S.NftDataValue{S.NftKey.u32(2)})]))
  +vm = set_of(S.NftSet.of_list([S.NftElem.to(S.NftElem.single(S.NftKey.u16(22)), S.NftDataVerdict{V.NftAccept{}}), S.NftElem.to(S.NftElem.range(S.NftKey.u16(8000), S.NftKey.u16(8999)), S.NftDataVerdict{V.NftReject{V.NftRejectTcpReset{}}}), S.NftElem.to(S.NftElem.single(S.NftKey.u16(9)), S.NftDataVerdict{V.NftQueue{3, True{}}})]))
  C.NftRuleset{[C.NftTable{"t", F.NftIp{}, [C.NftChain{"in", base(F.NftInput{}, 0, V.NftPolicyAccept{}), [rule([X.NftMarkSet{X.NftSrcMap{X.NftField.ip_saddr(), X.NftSetAnon{m}}}]), rule([X.NftExpr.eq(X.NftField.meta(X.NftMetaMark{}), S.NftKey.u32(2)), X.NftVerdictStmt{V.NftDrop{}}]), rule([X.NftVmap{X.NftField.th_dport(), X.NftSetAnon{vm}}])]}], Nil{}}]}

# two base chains at input: ip (priority 10) accepts, inet (priority -5)
# counts; then drop in the ip one for port 23
def two() -> C.NftRuleset:
  C.NftRuleset{[one("a", F.NftIp{}, F.NftInput{}, 10, V.NftPolicyAccept{}, [dport(23, V.NftDrop{}), rule([X.NftCount{2}, X.NftVerdictStmt{V.NftAccept{}}])]), one("b", F.NftInet{}, F.NftInput{}, F.NftPrio.of(True{}, 5), V.NftPolicyAccept{}, [rule([X.NftCount{1}, X.NftVerdictStmt{V.NftAccept{}}])]), one("c", F.NftIp6{}, F.NftInput{}, 0, V.NftPolicyDrop{}, Nil{})]}

# limit rate 2/second burst 2, then drop
def limited() -> C.NftRuleset:
  C.NftRuleset{[one("t", F.NftIp{}, F.NftInput{}, 0, V.NftPolicyDrop{}, [rule([X.NftLimit{1, X.NftLimitSpec{2, X.NftLimitSpec.second(), 2, False{}, False{}}}, X.NftVerdictStmt{V.NftAccept{}}])])]}

def lim(r: N.NftResult) -> X.NftState:
  N.NftResult.st(r)

def at(ms: U32, st: X.NftState) -> N.NftResult:
  N.Nft.eval_default(limited(), F.NftProtoIpv4{}, F.NftInput{}, W.W64.from_u32(ms), syn(False{}, 1, 80), st)

def err(r: Result<&2, &2, F.NftError, C.NftRuleset>) -> String:
  match r:
    case Done{x}:
      "ok"
    case Fail{e}:
      match e:
        case F.NftErrBadHook{}:
          "bad hook"
        case F.NftErrNoChain{}:
          "no chain"
        case F.NftErrSetOverlap{}:
          "overlap"
        case F.NftErrExists{}:
          "exists"
        case _:
          "other"

def built() -> Result<&2, &2, F.NftError, C.NftRuleset>:
  +rs = C.NftRuleset.add_table(C.NftRuleset.empty(), F.NftIp{}, "f")
  +rs2 = C.NftRuleset.then(rs, F.NftIp{}, "f", C.NftEditChain{"in", base(F.NftInput{}, 0, V.NftPolicyDrop{})})
  +rs3 = C.NftRuleset.then(rs2, F.NftIp{}, "f", C.NftEditRule{"in", dport(22, V.NftAccept{})})
  +rs4 = C.NftRuleset.then(rs3, F.NftIp{}, "f", C.NftEditSet{"s", S.NftSet.empty()})
  C.NftRuleset.then(rs4, F.NftIp{}, "f", C.NftEditElem{"s", S.NftElem.range(S.NftKey.u16(1), S.NftKey.u16(10))})

def built_or(r: Result<&2, &2, F.NftError, C.NftRuleset>) -> C.NftRuleset:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      C.NftRuleset.empty()

def show_basics() -> IO(Unit):
  do IO<Unit>:
    IO.print(run(C.NftRuleset.empty(), syn(False{}, 1, 22)))
    IO.print(run(C.NftRuleset.without_rules(filter()), syn(False{}, 1, 22)))
    IO.print(run(filter(), syn(False{}, 1, 22)))
    IO.print(run(filter(), syn(False{}, 1, 23)))
    IO.print(run(filter(), syn(False{}, 1, 443)))
    IO.print(run(filter(), syn(True{}, 1, 443)))
    IO.print(run(filter(), est(23)))
    IO.print(run6(filter(), v6(53)))
    IO.print(run(calls(False{}), syn(False{}, 1, 22)))
    IO.print(run(calls(True{}), syn(False{}, 1, 22)))

def show_calls() -> IO(Unit):
  do IO<Unit>:
    IO.print(run(loop(), syn(False{}, 1, 22)))
    IO.print(run(vmap(), syn(False{}, 1, 22)))
    IO.print(run(vmap(), syn(True{}, 1, 22)))
    IO.print(run(vmap(), syn(False{}, 1, 8080)))
    IO.print(run(vmap(), syn(False{}, 1, 9)))
    IO.print(run(vmap(), syn(False{}, 1, 10)))
    IO.print(run(two(), syn(False{}, 1, 22)))
    IO.print(run(two(), syn(False{}, 1, 23)))
    IO.print(run6(two(), v6(22)))

# the limit's packets at the times ts, one after another, the state carried
def lim_seq(ts: List<&2, U32>, +r: N.NftResult, acc: String) -> String:
  match ts:
    case Nil{}:
      acc ++ N.NftResult.show(r)
    case Con{t, rest}:
      lim_seq(rest, at(t, N.NftResult.st(r)), acc ++ N.NftResult.show(r) ++ "
")

def show_limits() -> IO(Unit):
  do IO<Unit>:
    IO.print(lim_seq([0, 0, 500, 600], at(0, X.NftState.empty()), ""))

def show_building() -> IO(Unit):
  do IO<Unit>:
    IO.print(err(built()))
    IO.print(run(built_or(built()), syn(False{}, 1, 22)))
    IO.print(err(C.NftRuleset.add_chain(built_or(built()), F.NftIp{}, "f", "in", None{})))
    IO.print(err(C.NftRuleset.add_rule(built_or(built()), F.NftIp{}, "f", "nope", verd(V.NftAccept{}))))
    IO.print(err(C.NftRuleset.add_element(built_or(built()), F.NftIp{}, "f", "s", S.NftElem.single(S.NftKey.u16(10)))))
    IO.print(err(C.NftRuleset.then(C.NftRuleset.add_table(C.NftRuleset.empty(), F.NftArp{}, "a"), F.NftArp{}, "a", C.NftEditChain{"c", base(F.NftForward{}, 0, V.NftPolicyAccept{})})))

def main() -> IO(Unit):
  do IO<Unit>:
    show_basics()
    show_calls()
    show_limits()
    show_building()

#|accept mark=0 ctmark=0 depth=0
#|drop mark=0 ctmark=0 depth=0
#|accept mark=0 ctmark=0 depth=0
#|drop mark=0 ctmark=0 depth=0
#|accept mark=0 ctmark=0 depth=1 c1=1/40
#|drop mark=0 ctmark=0 depth=1 c1=1/40
#|accept mark=0 ctmark=0 depth=0
#|drop mark=0 ctmark=0 depth=0
#|drop mark=0 ctmark=0 depth=2 c9=1/40 c8=1/40
#|accept mark=0 ctmark=0 depth=2 c9=1/40 c7=1/40
#|drop mark=0 ctmark=0 depth=16
#|accept mark=1 ctmark=0 depth=0
#|drop mark=2 ctmark=0 depth=0
#|reject with tcp reset mark=1 ctmark=0 depth=0
#|queue num 3 bypass mark=1 ctmark=0 depth=0
#|accept mark=1 ctmark=0 depth=0
#|accept mark=0 ctmark=0 depth=0 c1=1/40 c2=1/40
#|drop mark=0 ctmark=0 depth=0 c1=1/40
#|drop mark=0 ctmark=0 depth=0 c1=1/48
#|accept mark=0 ctmark=0 depth=0
#|accept mark=0 ctmark=0 depth=0
#|drop mark=0 ctmark=0 depth=0
#|accept mark=0 ctmark=0 depth=0
#|drop mark=0 ctmark=0 depth=0
#|ok
#|accept mark=0 ctmark=0 depth=0
#|exists
#|no chain
#|overlap
#|bad hook
