# Properties, for every input:
#   * evaluation stays within the jump-depth bound: the deepest level of
#     chains a chain's evaluation enters is at most its fuel, and a hook's
#     at most the options' max_depth, for every rule set and packet (that it
#     terminates at all, Bend's checker guarantees for every def);
#   * drop is final: a rule that drops ends its chain whatever follows; a
#     jump or goto to a chain that drops ends the caller with drop; and a
#     base chain that drops ends the hook, whatever base chains follow,
#     with the packet and state as that chain left them;
#   * a rule set with no rules gives the base chains' policies: the hook
#     drops if some base chain the packet meets has policy drop, and accepts
#     otherwise, leaving packet and state unchanged (for every rule set rs,
#     NftRuleset.without_rules(rs) is rs with no rules; every rule set with
#     no rules is one of these);
#   * jump and goto keep the call stack: when a jumped-to chain returns, the
#     rest of the current chain runs, from the packet and state it left;
#     when a gone-to chain returns, the current chain returns with it (to
#     the chain that jumped to the current one), the rest of it skipped;
#   * set membership agrees with the list model: after inserting e, a key is
#     in the set if e holds it or the set held it, and the set built from a
#     list of elements holds exactly the keys some element of the list holds;
#     a map's lookup finds an element exactly when the key is in the map;
#   * interval sets never overlap after insertion: insertion keeps the
#     invariant (every element valid, each one's high end below the next
#     one's low end), and every set built from a list has it.
#
# Vectors: the depth limit reached by a chain that jumps to itself; jump
# then return, and goto then return; accept passing a packet on to a later
# base chain that drops it; queue as a verdict; and a witness for each
# hypothesis.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./family.bend as F
import ./verdict.bend as V
import ./sets.bend as S
import ./expr.bend as X
import ./chains.bend as C
import ./eval.bend as E
import ./nftables.bend as N

# The list models

# some element of es holds x
def list_mem(es: List<&2, S.NftElem>, +x: B.Octets) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, t}:
      Bool.or(S.NftElem.contains(e, x), list_mem(t, x))

def is_some(m: Maybe<&2, S.NftData>) -> Bool:
  match m:
    case Some{d}:
      True{}
    case None{}:
      False{}

# whether a chain is a base chain at hook with policy drop
def model.chain(c: C.NftChain, +hook: F.NftHook) -> Bool:
  match c:
    case C.NftChain{n, b, rs}:
      match b:
        case None{}:
          False{}
        case Some{spec}:
          match spec:
            case C.NftBaseSpec{h, p, pol}:
              Bool.and(F.NftHook.is_eq(h, hook), Bool.not(V.NftPolicy.accepts(pol)))

def model.chains(cs: List<&2, C.NftChain>, +hook: F.NftHook) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Bool.or(model.chain(c, hook), model.chains(t, hook))

def model.tables(ts: List<&2, C.NftTable>, +proto: F.NftProto, +hook: F.NftHook) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, rest}:
      match t:
        case C.NftTable{n, f, cs, ss}:
          Bool.or(Bool.and(F.NftFamily.sees(f, proto), model.chains(cs, hook)), model.tables(rest, proto, hook))

def model.final(drops: Bool) -> V.NftFinal:
  match drops:
    case True{}:
      V.NftFinalDrop{}
    case False{}:
      V.NftFinalAccept{}

# what a hook does with a packet when no chain has rules: drop if some base
# chain the packet meets there has policy drop
def policy_model(rs: C.NftRuleset, +proto: F.NftProto, +hook: F.NftHook) -> V.NftFinal:
  match rs:
    case C.NftRuleset{ts}:
      model.final(model.tables(ts, proto, hook))

# Depth

law chain_depth_bound:
  for +opts: E.NftOptions
  for +fuel: Nat
  for +tbl: C.NftTable
  for rules: List<&2, X.NftRule>
  for env: X.NftEnv
  {Nat.is_le(E.NftRun.depth(E.Nft.run_chain(opts, fuel, tbl, rules, env)), fuel) == True{} : Bool}

law eval_depth_bound:
  for +opts: E.NftOptions
  for rs: C.NftRuleset
  for +proto: F.NftProto
  for +hook: F.NftHook
  for now: W.W64
  for pkt: X.NftPacket
  for st: X.NftState
  {Nat.is_le(N.NftResult.depth(N.Nft.eval(opts, rs, proto, hook, now, pkt, st)), E.NftOptions.max_depth(opts)) == True{} : Bool}

# Drop is final

law drop_rule_final:
  for +opts: E.NftOptions
  for +fuel: Nat
  for +tbl: C.NftTable
  for r: X.NftRule
  for rest: List<&2, X.NftRule>
  for env: X.NftEnv
  for env2: X.NftEnv
  for drops: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftDrop{}, env2} : X.NftRuleOut}
  {E.NftRun.result(E.Nft.run_chain(opts, fuel, tbl, Con{r, rest}, env)) == E.NftChainStop{V.NftFinalDrop{}} : E.NftChainRes}

law drop_through_jump:
  for +opts: E.NftOptions
  for +q: Nat
  for +tbl: C.NftTable
  for r: X.NftRule
  for rest: List<&2, X.NftRule>
  for env: X.NftEnv
  for +c: String
  for +env2: X.NftEnv
  for jumps: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftJump{c}, env2} : X.NftRuleOut}
  for found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}
  for drops: {E.NftRun.result(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) == E.NftChainStop{V.NftFinalDrop{}} : E.NftChainRes}
  {E.NftRun.result(E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env)) == E.NftChainStop{V.NftFinalDrop{}} : E.NftChainRes}

law drop_through_goto:
  for +opts: E.NftOptions
  for +q: Nat
  for +tbl: C.NftTable
  for r: X.NftRule
  for rest: List<&2, X.NftRule>
  for env: X.NftEnv
  for +c: String
  for +env2: X.NftEnv
  for goes: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftGoto{c}, env2} : X.NftRuleOut}
  for found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}
  for drops: {E.NftRun.result(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) == E.NftChainStop{V.NftFinalDrop{}} : E.NftChainRes}
  {E.NftRun.result(E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env)) == E.NftChainStop{V.NftFinalDrop{}} : E.NftChainRes}

law drop_ends_hook:
  for +opts: E.NftOptions
  for +h: C.NftHooked
  for rest: List<&2, C.NftHooked>
  for +env: X.NftEnv
  for drops: {E.NftOut.final(E.Nft.run_base(opts, h, env)) == Some{V.NftFinalDrop{}} : Maybe<&2, V.NftFinal>}
  {E.Nft.run_hook(opts, Con{h, rest}, env) == E.NftOut{Some{V.NftFinalDrop{}}, E.NftOut.env(E.Nft.run_base(opts, h, env)), E.NftOut.depth(E.Nft.run_base(opts, h, env))} : E.NftOut}

# Jump keeps the call stack: when the jumped-to chain returns, the
# evaluation goes on with the rest of the current chain, from the packet and
# state the jumped-to chain left (compared without the depth, which counts
# the levels entered)

def view(+r: E.NftRun) -> E.NftChainRes & X.NftEnv:
  (E.NftRun.result(r), E.NftRun.env(r))

law jump_returns:
  for +opts: E.NftOptions
  for +q: Nat
  for +tbl: C.NftTable
  for r: X.NftRule
  for +rest: List<&2, X.NftRule>
  for env: X.NftEnv
  for +c: String
  for +env2: X.NftEnv
  for jumps: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftJump{c}, env2} : X.NftRuleOut}
  for found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}
  for returns: {E.NftRun.result(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) == E.NftChainReturn{} : E.NftChainRes}
  {view(E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env)) == view(E.Nft.run_chain(opts, 1n+q, tbl, rest, E.NftRun.env(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)))) : E.NftChainRes & X.NftEnv}

# Goto keeps the call stack: the gone-to chain's return is the current
# chain's return, with the gone-to chain's packet and state

law goto_returns:
  for +opts: E.NftOptions
  for +q: Nat
  for +tbl: C.NftTable
  for r: X.NftRule
  for rest: List<&2, X.NftRule>
  for env: X.NftEnv
  for +c: String
  for +env2: X.NftEnv
  for goes: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftGoto{c}, env2} : X.NftRuleOut}
  for found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}
  {E.NftRun.env(E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env)) == E.NftRun.env(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) : X.NftEnv}

law goto_result:
  for +opts: E.NftOptions
  for +q: Nat
  for +tbl: C.NftTable
  for r: X.NftRule
  for rest: List<&2, X.NftRule>
  for env: X.NftEnv
  for +c: String
  for +env2: X.NftEnv
  for goes: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftGoto{c}, env2} : X.NftRuleOut}
  for found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}
  {E.NftRun.result(E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env)) == E.NftRun.result(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) : E.NftChainRes}

# No rules: the policies

law no_rules_policy:
  for +opts: E.NftOptions
  for +rs: C.NftRuleset
  for +proto: F.NftProto
  for +hook: F.NftHook
  for now: W.W64
  for pkt: X.NftPacket
  for st: X.NftState
  {N.Nft.eval(opts, C.NftRuleset.without_rules(rs), proto, hook, now, pkt, st) == N.NftResult{policy_model(rs, proto, hook), pkt, st, 0n} : N.NftResult}

# Sets

law set_mem_insert:
  for s: S.NftSet
  for +e: S.NftElem
  for +x: B.Octets
  for s2: S.NftSet
  for ok: {S.NftSet.insert(s, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}
  {S.NftSet.mem(s2, x) == Bool.or(S.NftElem.contains(e, x), S.NftSet.mem(s, x)) : Bool}

law set_mem_of_list:
  for +es: List<&2, S.NftElem>
  for s: S.NftSet
  for +x: B.Octets
  for ok: {S.NftSet.of_list(es) == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}
  {S.NftSet.mem(s, x) == list_mem(es, x) : Bool}

law map_lookup_mem:
  for s: S.NftSet
  for +x: B.Octets
  {is_some(S.NftSet.lookup(s, x)) == S.NftSet.mem(s, x) : Bool}

law set_wf_insert:
  for s: S.NftSet
  for +e: S.NftElem
  for s2: S.NftSet
  for wf: {S.NftSet.wf(s) == True{} : Bool}
  for ok: {S.NftSet.insert(s, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}
  {S.NftSet.wf(s2) == True{} : Bool}

law set_wf_of_list:
  for +es: List<&2, S.NftElem>
  for s: S.NftSet
  for ok: {S.NftSet.of_list(es) == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}
  {S.NftSet.wf(s) == True{} : Bool}

law set_empty_wf:
  {S.NftSet.wf(S.NftSet.empty()) == True{} : Bool}

# Vectors

def pkt() -> X.NftPacket:
  X.NftPacket{X.NftMeta{1, 0, 0, 6, 40, 2}, X.NftCt{X.NftCt.NEW(), 0}, X.NftL2None{}, X.NftL3None{}, X.NftL4None{}, B.Octets.empty()}

def env() -> X.NftEnv:
  X.NftEnv{pkt(), X.NftState.empty(), W.W64.zero()}

def verd(v: V.NftVerdict) -> X.NftRule:
  X.NftRule{[X.NftVerdictStmt{v}]}

def mark(k: U32) -> X.NftRule:
  X.NftRule{[X.NftMarkSet{X.NftSrcImm{S.NftKey.u32(k)}}]}

def base(prio: U32, pol: V.NftPolicy) -> Maybe<&2, C.NftBaseSpec>:
  Some{C.NftBaseSpec{F.NftInput{}, prio, pol}}

def table(cs: List<&2, C.NftChain>) -> C.NftTable:
  C.NftTable{"t", F.NftIp{}, cs, Nil{}}

def ev(rs: C.NftRuleset) -> N.NftResult:
  N.Nft.eval_default(rs, F.NftProtoIpv4{}, F.NftInput{}, W.W64.zero(), pkt(), X.NftState.empty())

def marked(k: U32) -> X.NftPacket:
  X.NftPacket.set_mark(pkt(), k)

# a chain that jumps to itself: 16 levels, then the depth limit's drop
def loop() -> C.NftRuleset:
  C.NftRuleset{[table([C.NftChain{"in", base(0, V.NftPolicyAccept{}), [verd(V.NftJump{"a"})]}, C.NftChain{"a", None{}, [verd(V.NftJump{"a"})]}])]}

law vec_depth_limit:
  {ev(loop()) == N.NftResult{V.NftFinalDrop{}, pkt(), X.NftState.empty(), 16n} : N.NftResult}

def calls.a(go: Bool) -> X.NftRule:
  match go:
    case True{}:
      verd(V.NftGoto{"b"})
    case False{}:
      verd(V.NftJump{"b"})

# in: jump a, then accept; a: jump (or goto) b, then mark 2 and drop;
# b: mark 1, return
def calls(go: Bool) -> C.NftRuleset:
  C.NftRuleset{[table([C.NftChain{"in", base(0, V.NftPolicyDrop{}), [verd(V.NftJump{"a"}), verd(V.NftAccept{})]}, C.NftChain{"a", None{}, [calls.a(go), mark(2), verd(V.NftDrop{})]}, C.NftChain{"b", None{}, [mark(1), verd(V.NftReturn{})]}])]}

# jump: b returns to a, which marks 2 and drops
law vec_jump_return:
  {ev(calls(False{})) == N.NftResult{V.NftFinalDrop{}, marked(2), X.NftState.empty(), 2n} : N.NftResult}

# goto: b returns to in, past the rest of a, and in accepts
law vec_goto_return:
  {ev(calls(True{})) == N.NftResult{V.NftFinalAccept{}, marked(1), X.NftState.empty(), 2n} : N.NftResult}

# accept ends a base chain, not the hook: a later base chain drops
def two() -> C.NftRuleset:
  C.NftRuleset{[C.NftTable{"a", F.NftIp{}, [C.NftChain{"c", base(10, V.NftPolicyAccept{}), [mark(5), verd(V.NftDrop{})]}], Nil{}}, C.NftTable{"b", F.NftInet{}, [C.NftChain{"c", base(F.NftPrio.of(True{}, 5), V.NftPolicyDrop{}), [mark(4), verd(V.NftAccept{})]}], Nil{}}]}

law vec_accept_passes_on:
  {ev(two()) == N.NftResult{V.NftFinalDrop{}, marked(5), X.NftState.empty(), 0n} : N.NftResult}

law vec_queue:
  {ev(C.NftRuleset{[table([C.NftChain{"in", base(0, V.NftPolicyAccept{}), [verd(V.NftQueue{7, False{}}), verd(V.NftDrop{})]}])]}) == N.NftResult{V.NftFinalQueue{7, False{}}, pkt(), X.NftState.empty(), 0n} : N.NftResult}

# an overlapping interval is refused
law vec_overlap:
  {S.NftSet.of_list([S.NftElem.range(S.NftKey.u16(10), S.NftKey.u16(20)), S.NftElem.range(S.NftKey.u16(20), S.NftKey.u16(30))]) == Fail{F.NftErrSetOverlap{}} : Result<&2, &2, F.NftError, S.NftSet>}

law vec_bad_interval:
  {S.NftSet.of_list([S.NftElem.range(S.NftKey.u16(30), S.NftKey.u16(20))]) == Fail{F.NftErrBadInterval{}} : Result<&2, &2, F.NftError, S.NftSet>}

# Witnesses: each hypothesis above holds for some input

def dtable() -> C.NftTable:
  table([C.NftChain{"d", None{}, [verd(V.NftDrop{})]}])

# drop_rule_final: a drop rule
law witness_drops:
  {X.NftRule.eval(verd(V.NftDrop{}), C.NftTable.sets(dtable()), env()) == X.NftRuleVerdict{V.NftDrop{}, env()} : X.NftRuleOut}

# drop_through_jump: a jump to chain d, which exists and drops
law witness_jumps:
  {X.NftRule.eval(verd(V.NftJump{"d"}), C.NftTable.sets(dtable()), env()) == X.NftRuleVerdict{V.NftJump{"d"}, env()} : X.NftRuleOut}

law witness_found:
  {C.NftTable.has_chain(dtable(), "d") == True{} : Bool}

law witness_callee_drops:
  {E.NftRun.result(E.Nft.run_chain(E.NftOptions.default(), 3n, dtable(), C.NftTable.rules(dtable(), "d"), env())) == E.NftChainStop{V.NftFinalDrop{}} : E.NftChainRes}

# jump_returns: chain r, which returns
def rtable() -> C.NftTable:
  table([C.NftChain{"r", None{}, [mark(3), verd(V.NftReturn{})]}])

law witness_callee_returns:
  {E.NftRun.result(E.Nft.run_chain(E.NftOptions.default(), 3n, rtable(), C.NftTable.rules(rtable(), "r"), env())) == E.NftChainReturn{} : E.NftChainRes}

law witness_jumps_r:
  {X.NftRule.eval(verd(V.NftJump{"r"}), C.NftTable.sets(rtable()), env()) == X.NftRuleVerdict{V.NftJump{"r"}, env()} : X.NftRuleOut}

law witness_found_r:
  {C.NftTable.has_chain(rtable(), "r") == True{} : Bool}

# drop_through_goto, goto_returns, goto_result: a goto to chain d
law witness_goes:
  {X.NftRule.eval(verd(V.NftGoto{"d"}), C.NftTable.sets(dtable()), env()) == X.NftRuleVerdict{V.NftGoto{"d"}, env()} : X.NftRuleOut}

# drop_ends_hook: a base chain that drops
law witness_base_drops:
  {E.NftOut.final(E.Nft.run_base(E.NftOptions.default(), C.NftHooked{dtable(), [verd(V.NftDrop{})], 0, V.NftPolicyAccept{}}, env())) == Some{V.NftFinalDrop{}} : Maybe<&2, V.NftFinal>}

def two_elems() -> List<&2, S.NftElem>:
  [S.NftElem.prefix(S.NftKey.ipv4(10, 0, 0, 0), 8n), S.NftElem.single(S.NftKey.ipv4(192, 168, 1, 1))]

def two_set() -> S.NftSet:
  S.NftSet{[S.NftElem{S.NftKey.ipv4(10, 0, 0, 0), S.NftKey.ipv4(10, 255, 255, 255), S.NftNoData{}}, S.NftElem{S.NftKey.ipv4(192, 168, 1, 1), S.NftKey.ipv4(192, 168, 1, 1), S.NftNoData{}}]}

# set_mem_of_list, set_wf_of_list: a list that builds a set
law witness_of_list:
  {S.NftSet.of_list(two_elems()) == Done{two_set()} : Result<&2, &2, F.NftError, S.NftSet>}

# set_wf_insert: a set with the invariant, and an insertion that succeeds
law witness_wf:
  {S.NftSet.wf(two_set()) == True{} : Bool}

law witness_insert:
  {S.NftSet.insert(two_set(), S.NftElem.single(S.NftKey.ipv4(127, 0, 0, 1))) == Done{S.NftSet{[S.NftElem{S.NftKey.ipv4(10, 0, 0, 0), S.NftKey.ipv4(10, 255, 255, 255), S.NftNoData{}}, S.NftElem{S.NftKey.ipv4(127, 0, 0, 1), S.NftKey.ipv4(127, 0, 0, 1), S.NftNoData{}}, S.NftElem{S.NftKey.ipv4(192, 168, 1, 1), S.NftKey.ipv4(192, 168, 1, 1), S.NftNoData{}}]}} : Result<&2, &2, F.NftError, S.NftSet>}
