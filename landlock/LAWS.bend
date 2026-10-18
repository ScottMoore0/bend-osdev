# Properties, for every input (every domain, ruleset, path, port, right,
# operation, ABI version and option):
#   restriction is monotone: adding a layer never allows an operation the
#     domain refused before (for every operation: open, exec, create, remove,
#     rename, link, bind, connect, signal, abstract-socket connect), whether
#     the layer is pushed or enforced through landlock_restrict_self;
#   a ruleset handling nothing changes nothing, and restrict_self with one
#     leaves the domain as it is;
#   a right a layer does not handle is never refused by that layer (for
#     filesystem rights, with REFER handled by any ruleset that handles a
#     filesystem right, as landlock(7) says; for network rights; for scoped
#     actions); and REFER is refused by a ruleset that handles filesystem
#     rights but not REFER itself;
#   path-beneath rules are inherited: a rule added on q allows its rights on
#     every path beneath q, and anything a domain allows on a path it allows
#     on every path beneath it; a net-port rule allows its rights on its port;
#   rename and link within one directory need only the REMOVE_* and MAKE_*
#     rights there; across directories a layer that handles filesystem rights
#     but not REFER refuses them (ABI 1); and an allowed reparenting never
#     lets the file gain a right it did not have in its old directory;
#   ABI: a later version knows every right an earlier one does; strict mode
#     refuses a right the ABI lacks; best effort never refuses and handles
#     exactly the rights asked for that the ABI knows;
#   the layer limit: restrict_self keeps a domain within the limit, and
#     refuses a new layer at the limit;
#   scoping: a process may always signal or connect to its own domain and
#     to domains nested in it, and a scoping layer refuses a process outside.
#
# Witnesses: every law with a hypothesis has a witness law below it showing
# an input for which all the hypotheses hold.
#
# Vectors: the ABI masks (landlock(7)'s table), the landlock(7) example, and
# rename and link cases checked on Linux 6.6 (ABI 3).
import Base
import ../word64/word64.bend as W
import ./error.bend as E
import ./path.bend as P
import ./rights.bend as R
import ./net.bend as N
import ./scope.bend as S
import ./abi.bend as A
import ./ruleset.bend as RS
import ./domain.bend as D
import ./refer.bend as F
import ./landlock.bend as L

# Examples, built from the public interface

def ex.p(s: String) -> P.LandlockPath:
  P.LandlockPath.of_string(s)

# landlock(7)'s example: the ABI 3 rights handled, /usr readable
def ex.usr_rights() -> R.LandlockFs:
  R.LandlockFs.of_list([R.LandlockExecute{}, R.LandlockReadFile{}, R.LandlockReadDir{}])

def ex.usr() -> RS.LandlockRuleset:
  RS.LandlockRuleset.with_path(RS.LandlockRuleset.make(A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none()), ex.p("/usr"), ex.usr_rights())

def ex.usr_domain() -> D.LandlockDomain:
  D.LandlockDomain.push(D.LandlockDomain.none(), 1, ex.usr())

# a ruleset of ABI 1: the thirteen first rights, all allowed on /
def ex.v1() -> RS.LandlockRuleset:
  RS.LandlockRuleset.with_path(RS.LandlockRuleset.make(A.LandlockAbi.fs(1n), N.LandlockNet.none(), S.LandlockScope.none()), P.LandlockPath.root(), A.LandlockAbi.fs(1n))

# /a and /b, both with REFER, MAKE_REG and REMOVE_FILE, and /b with READ_FILE
# too
def ex.rmr() -> R.LandlockFs:
  R.LandlockFs.of_list([R.LandlockRefer{}, R.LandlockMakeReg{}, R.LandlockRemoveFile{}])

def ex.gain() -> D.LandlockDomain:
  D.LandlockDomain.push(D.LandlockDomain.none(), 1, RS.LandlockRuleset.with_path(RS.LandlockRuleset.with_path(RS.LandlockRuleset.make(A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none()), ex.p("/a"), ex.rmr()), ex.p("/b"), R.LandlockFs.add(ex.rmr(), R.LandlockReadFile{})))

# /a with REFER, MAKE_REG, REMOVE_FILE and READ_FILE; /b with EXECUTE too
def ex.lose() -> D.LandlockDomain:
  D.LandlockDomain.push(D.LandlockDomain.none(), 1, RS.LandlockRuleset.with_path(RS.LandlockRuleset.with_path(RS.LandlockRuleset.make(A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none()), ex.p("/a"), R.LandlockFs.add(ex.rmr(), R.LandlockReadFile{})), ex.p("/b"), R.LandlockFs.add(R.LandlockFs.add(ex.rmr(), R.LandlockReadFile{}), R.LandlockExecute{})))

# Restriction is monotone

law push_monotone:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +op: L.LandlockOp
  for h: {F.LandlockDecision.is_allowed(L.Landlock.check(D.LandlockDomain.push(d, id, rs), op)) == True{} : Bool}
  {F.LandlockDecision.is_allowed(L.Landlock.check(d, op)) == True{} : Bool}

law witness_push_monotone:
  {F.LandlockDecision.is_allowed(L.Landlock.check(D.LandlockDomain.push(D.LandlockDomain.none(), 1, ex.usr()), L.LandlockOpOpen{ex.p("/usr/bin/env"), True{}, False{}, False{}})) == True{} : Bool}

law restrict_monotone:
  for +o: L.LandlockOptions
  for +t: L.LandlockThread
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +t2: L.LandlockThread
  for +op: L.LandlockOp
  for h1: {L.Landlock.restrict_self(o, t, id, rs) == Done{t2} : Result<&2, &2, E.LandlockError, L.LandlockThread>}
  for h2: {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(t2), op)) == True{} : Bool}
  {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(t), op)) == True{} : Bool}

law witness_restrict_monotone:
  {L.Landlock.restrict_self(L.LandlockOptions.default(), L.LandlockThread.new(), 1, ex.usr()) == Done{L.LandlockThread{ex.usr_domain(), True{}, False{}}} : Result<&2, &2, E.LandlockError, L.LandlockThread>}

law witness_restrict_monotone_allowed:
  {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(L.LandlockThread{ex.usr_domain(), True{}, False{}}), L.LandlockOpExec{ex.p("/usr/bin/env")})) == True{} : Bool}

# A ruleset that handles nothing changes nothing

law empty_changes_nothing:
  for +d: D.LandlockDomain
  for +id: U32
  for +op: L.LandlockOp
  {L.Landlock.check(D.LandlockDomain.push(d, id, RS.LandlockRuleset.none()), op) == L.Landlock.check(d, op) : F.LandlockDecision}

law empty_restrict_unchanged:
  for +max: Nat
  for +d: D.LandlockDomain
  for +id: U32
  {D.LandlockDomain.restrict(max, d, id, RS.LandlockRuleset.none()) == Done{d} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}

# A right a layer does not handle is never refused by that layer

law unhandled_fs_not_refused:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +p: P.LandlockPath
  for +r: R.LandlockFsRight
  for h: {RS.LandlockRuleset.handles(rs, r) == False{} : Bool}
  {D.LandlockDomain.allows(D.LandlockDomain.push(d, id, rs), p, [r]) == D.LandlockDomain.allows(d, p, [r]) : Bool}

law witness_unhandled_fs:
  {RS.LandlockRuleset.handles(RS.LandlockRuleset.make(R.LandlockFs.single(R.LandlockReadFile{}), N.LandlockNet.none(), S.LandlockScope.none()), R.LandlockWriteFile{}) == False{} : Bool}

law unhandled_net_not_refused:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +port: U32
  for +r: N.LandlockNetRight
  for h: {RS.LandlockRuleset.handles_net(rs, r) == False{} : Bool}
  {D.LandlockDomain.allows_net(D.LandlockDomain.push(d, id, rs), port, r) == D.LandlockDomain.allows_net(d, port, r) : Bool}

law witness_unhandled_net:
  {RS.LandlockRuleset.handles_net(RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.single(N.LandlockBindTcp{}), S.LandlockScope.none()), N.LandlockConnectTcp{}) == False{} : Bool}

law unscoped_not_refused:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +target: D.LandlockDomain
  for +x: S.LandlockScopeRight
  for h: {RS.LandlockRuleset.scopes(rs, x) == False{} : Bool}
  {D.LandlockDomain.allows_scope(D.LandlockDomain.push(d, id, rs), target, x) == D.LandlockDomain.allows_scope(d, target, x) : Bool}

law witness_unscoped:
  {RS.LandlockRuleset.scopes(RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.none(), S.LandlockScope.single(S.LandlockScopeSignal{})), S.LandlockScopeAbstractUnix{}) == False{} : Bool}

# REFER: handled by every ruleset that handles a filesystem right, and then
# granted only by a rule allowing it, which needs REFER handled explicitly

law refer_always_handled:
  for +rs: RS.LandlockRuleset
  for h: {R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(rs)) == False{} : Bool}
  {RS.LandlockRuleset.handles(rs, R.LandlockRefer{}) == True{} : Bool}

law refer_refused_unless_handled:
  for +rs: RS.LandlockRuleset
  for +p: P.LandlockPath
  for h1: {R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(rs)) == False{} : Bool}
  for h2: {R.LandlockFs.has(RS.LandlockRuleset.handled_fs(rs), R.LandlockRefer{}) == False{} : Bool}
  {RS.LandlockRuleset.allows(rs, p, R.LandlockRefer{}) == False{} : Bool}

law witness_refer:
  {Bool.and(Bool.not(R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(ex.v1()))), Bool.not(R.LandlockFs.has(RS.LandlockRuleset.handled_fs(ex.v1()), R.LandlockRefer{}))) == True{} : Bool}

# Path-beneath rules are inherited by descendants

law rule_applies_beneath:
  for +rs: RS.LandlockRuleset
  for +q: P.LandlockPath
  for +is_dir: Bool
  for +a: R.LandlockFs
  for +rs2: RS.LandlockRuleset
  for +s: P.LandlockPath
  for +r: R.LandlockFsRight
  for h1: {RS.LandlockRuleset.add_path(rs, q, is_dir, a) == Done{rs2} : Result<&2, &2, E.LandlockError, RS.LandlockRuleset>}
  for h2: {R.LandlockFs.has(a, r) == True{} : Bool}
  {RS.LandlockRuleset.allows(rs2, P.LandlockPath.join(q, s), r) == True{} : Bool}

law witness_rule_applies_beneath:
  {RS.LandlockRuleset.add_path(RS.LandlockRuleset.make(A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none()), ex.p("/usr"), True{}, ex.usr_rights()) == Done{ex.usr()} : Result<&2, &2, E.LandlockError, RS.LandlockRuleset>}

law witness_rule_applies_beneath_right:
  {R.LandlockFs.has(ex.usr_rights(), R.LandlockReadDir{}) == True{} : Bool}

law allowed_inherited:
  for +d: D.LandlockDomain
  for +q: P.LandlockPath
  for +s: P.LandlockPath
  for +req: List<&2, R.LandlockFsRight>
  for h: {D.LandlockDomain.allows(d, q, req) == True{} : Bool}
  {D.LandlockDomain.allows(d, P.LandlockPath.join(q, s), req) == True{} : Bool}

law witness_allowed_inherited:
  {D.LandlockDomain.allows(ex.usr_domain(), ex.p("/usr"), [R.LandlockReadDir{}, R.LandlockExecute{}]) == True{} : Bool}

law port_rule_applies:
  for +rs: RS.LandlockRuleset
  for +port: U32
  for +a: N.LandlockNet
  for +rs2: RS.LandlockRuleset
  for +r: N.LandlockNetRight
  for h1: {RS.LandlockRuleset.add_port(rs, port, a) == Done{rs2} : Result<&2, &2, E.LandlockError, RS.LandlockRuleset>}
  for h2: {N.LandlockNet.has(a, r) == True{} : Bool}
  {RS.LandlockRuleset.allows_net(rs2, port, r) == True{} : Bool}

law witness_port_rule:
  {RS.LandlockRuleset.add_port(RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.all(), S.LandlockScope.none()), 443, N.LandlockNet.single(N.LandlockConnectTcp{})) == Done{RS.LandlockRuleset.with_port(RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.all(), S.LandlockScope.none()), 443, N.LandlockNet.single(N.LandlockConnectTcp{}))} : Result<&2, &2, E.LandlockError, RS.LandlockRuleset>}

law witness_port_rule_right:
  {N.LandlockNet.has(N.LandlockNet.single(N.LandlockConnectTcp{}), N.LandlockConnectTcp{}) == True{} : Bool}

# Rename and link

law rename_same_dir:
  for +d: D.LandlockDomain
  for +p: P.LandlockPath
  for +k: R.LandlockFileKind
  {F.LandlockRefer.rename(d, p, p, k) == F.LandlockDecision.of_bool(D.LandlockDomain.allows(d, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}

law link_same_dir:
  for +d: D.LandlockDomain
  for +p: P.LandlockPath
  for +k: R.LandlockFileKind
  {F.LandlockRefer.link(d, p, p, k) == F.LandlockDecision.of_bool(D.LandlockDomain.allows(d, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}

law reparent_needs_refer_rename:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +src: P.LandlockPath
  for +dst: P.LandlockPath
  for +k: R.LandlockFileKind
  for h1: {R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(rs)) == False{} : Bool}
  for h2: {R.LandlockFs.has(RS.LandlockRuleset.handled_fs(rs), R.LandlockRefer{}) == False{} : Bool}
  for h3: {P.LandlockPath.is_eq(src, dst) == False{} : Bool}
  {F.LandlockDecision.is_allowed(F.LandlockRefer.rename(D.LandlockDomain.push(d, id, rs), src, dst, k)) == False{} : Bool}

law reparent_needs_refer_link:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +src: P.LandlockPath
  for +dst: P.LandlockPath
  for +k: R.LandlockFileKind
  for h1: {R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(rs)) == False{} : Bool}
  for h2: {R.LandlockFs.has(RS.LandlockRuleset.handled_fs(rs), R.LandlockRefer{}) == False{} : Bool}
  for h3: {P.LandlockPath.is_eq(src, dst) == False{} : Bool}
  {F.LandlockDecision.is_allowed(F.LandlockRefer.link(D.LandlockDomain.push(d, id, rs), src, dst, k)) == False{} : Bool}

law witness_reparent_needs_refer:
  {Bool.and(Bool.not(R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(ex.v1()))), Bool.and(Bool.not(R.LandlockFs.has(RS.LandlockRuleset.handled_fs(ex.v1()), R.LandlockRefer{})), Bool.not(P.LandlockPath.is_eq(ex.p("/a"), ex.p("/b"))))) == True{} : Bool}

law reparent_no_gain_rename:
  for +d: D.LandlockDomain
  for +src: P.LandlockPath
  for +dst: P.LandlockPath
  for +k: R.LandlockFileKind
  for +r: R.LandlockFsRight
  for h1: {P.LandlockPath.is_eq(src, dst) == False{} : Bool}
  for h2: {F.LandlockDecision.is_allowed(F.LandlockRefer.rename(d, src, dst, k)) == True{} : Bool}
  for h3: {R.LandlockFs.has(R.LandlockFileKind.carried(k), r) == True{} : Bool}
  for h4: {D.LandlockDomain.allows(d, dst, [r]) == True{} : Bool}
  {D.LandlockDomain.allows(d, src, [r]) == True{} : Bool}

law reparent_no_gain_link:
  for +d: D.LandlockDomain
  for +src: P.LandlockPath
  for +dst: P.LandlockPath
  for +k: R.LandlockFileKind
  for +r: R.LandlockFsRight
  for h1: {P.LandlockPath.is_eq(src, dst) == False{} : Bool}
  for h2: {F.LandlockDecision.is_allowed(F.LandlockRefer.link(d, src, dst, k)) == True{} : Bool}
  for h3: {R.LandlockFs.has(R.LandlockFileKind.carried(k), r) == True{} : Bool}
  for h4: {D.LandlockDomain.allows(d, dst, [r]) == True{} : Bool}
  {D.LandlockDomain.allows(d, src, [r]) == True{} : Bool}

# moving a regular file from /b to /a (ex.lose): it loses EXECUTE, which is
# allowed, and keeps READ_FILE
law witness_reparent_no_gain:
  {Bool.and(Bool.not(P.LandlockPath.is_eq(ex.p("/b"), ex.p("/a"))), Bool.and(F.LandlockDecision.is_allowed(F.LandlockRefer.rename(ex.lose(), ex.p("/b"), ex.p("/a"), R.LandlockReg{})), Bool.and(F.LandlockDecision.is_allowed(F.LandlockRefer.link(ex.lose(), ex.p("/b"), ex.p("/a"), R.LandlockReg{})), Bool.and(R.LandlockFs.has(R.LandlockFileKind.carried(R.LandlockReg{}), R.LandlockReadFile{}), D.LandlockDomain.allows(ex.lose(), ex.p("/a"), [R.LandlockReadFile{}]))))) == True{} : Bool}

# ABI versions

law abi_later_knows_fs:
  for +v: Nat
  for +r: R.LandlockFsRight
  for h: {A.LandlockAbi.knows_fs(v, r) == True{} : Bool}
  {A.LandlockAbi.knows_fs(1n+v, r) == True{} : Bool}

law abi_later_knows_net:
  for +v: Nat
  for +r: N.LandlockNetRight
  for h: {A.LandlockAbi.knows_net(v, r) == True{} : Bool}
  {A.LandlockAbi.knows_net(1n+v, r) == True{} : Bool}

law abi_later_knows_scope:
  for +v: Nat
  for +r: S.LandlockScopeRight
  for h: {A.LandlockAbi.knows_scope(v, r) == True{} : Bool}
  {A.LandlockAbi.knows_scope(1n+v, r) == True{} : Bool}

law witness_abi_knows:
  {Bool.and(A.LandlockAbi.knows_fs(3n, R.LandlockTruncate{}), Bool.and(A.LandlockAbi.knows_net(4n, N.LandlockBindTcp{}), A.LandlockAbi.knows_scope(6n, S.LandlockScopeSignal{}))) == True{} : Bool}

law strict_refuses_unknown_fs:
  for +v: Nat
  for +m: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  for +r: R.LandlockFsRight
  for h1: {R.LandlockFs.has(f, r) == True{} : Bool}
  for h2: {A.LandlockAbi.knows_fs(v, r) == False{} : Bool}
  {L.Landlock.ok(L.Landlock.create_ruleset(L.LandlockOptions{v, A.LandlockStrict{}, m}, f, n, s)) == False{} : Bool}

law strict_refuses_unknown_net:
  for +v: Nat
  for +m: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  for +r: N.LandlockNetRight
  for h1: {N.LandlockNet.has(n, r) == True{} : Bool}
  for h2: {A.LandlockAbi.knows_net(v, r) == False{} : Bool}
  {L.Landlock.ok(L.Landlock.create_ruleset(L.LandlockOptions{v, A.LandlockStrict{}, m}, f, n, s)) == False{} : Bool}

law strict_refuses_unknown_scope:
  for +v: Nat
  for +m: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  for +r: S.LandlockScopeRight
  for h1: {S.LandlockScope.has(s, r) == True{} : Bool}
  for h2: {A.LandlockAbi.knows_scope(v, r) == False{} : Bool}
  {L.Landlock.ok(L.Landlock.create_ruleset(L.LandlockOptions{v, A.LandlockStrict{}, m}, f, n, s)) == False{} : Bool}

# IOCTL_DEV on ABI 3, BIND_TCP on ABI 3, SIGNAL on ABI 5
law witness_strict_refuses:
  {Bool.and(Bool.and(R.LandlockFs.has(R.LandlockFs.single(R.LandlockIoctlDev{}), R.LandlockIoctlDev{}), Bool.not(A.LandlockAbi.knows_fs(3n, R.LandlockIoctlDev{}))), Bool.and(Bool.and(N.LandlockNet.has(N.LandlockNet.single(N.LandlockBindTcp{}), N.LandlockBindTcp{}), Bool.not(A.LandlockAbi.knows_net(3n, N.LandlockBindTcp{}))), Bool.and(S.LandlockScope.has(S.LandlockScope.single(S.LandlockScopeSignal{}), S.LandlockScopeSignal{}), Bool.not(A.LandlockAbi.knows_scope(5n, S.LandlockScopeSignal{}))))) == True{} : Bool}

law best_effort_never_refuses:
  for +v: Nat
  for +m: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  {L.Landlock.ok(L.Landlock.create_ruleset(L.LandlockOptions{v, A.LandlockBestEffort{}, m}, f, n, s)) == True{} : Bool}

law best_effort_keeps_known_fs:
  for +v: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  for +r: R.LandlockFsRight
  {R.LandlockFs.has(RS.LandlockRuleset.handled_fs(L.Landlock.best_effort(v, f, n, s)), r) == Bool.and(R.LandlockFs.has(f, r), A.LandlockAbi.knows_fs(v, r)) : Bool}

law best_effort_keeps_known_net:
  for +v: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  for +r: N.LandlockNetRight
  {N.LandlockNet.has(RS.LandlockRuleset.handled_net(L.Landlock.best_effort(v, f, n, s)), r) == Bool.and(N.LandlockNet.has(n, r), A.LandlockAbi.knows_net(v, r)) : Bool}

law best_effort_keeps_known_scope:
  for +v: Nat
  for +f: R.LandlockFs
  for +n: N.LandlockNet
  for +s: S.LandlockScope
  for +r: S.LandlockScopeRight
  {S.LandlockScope.has(RS.LandlockRuleset.scoped(L.Landlock.best_effort(v, f, n, s)), r) == Bool.and(S.LandlockScope.has(s, r), A.LandlockAbi.knows_scope(v, r)) : Bool}

# The layer limit

law restrict_bounded:
  for +max: Nat
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +d2: D.LandlockDomain
  for h1: {Nat.is_le(D.LandlockDomain.depth(d), max) == True{} : Bool}
  for h2: {D.LandlockDomain.restrict(max, d, id, rs) == Done{d2} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}
  {Nat.is_le(D.LandlockDomain.depth(d2), max) == True{} : Bool}

law witness_restrict_bounded:
  {D.LandlockDomain.restrict(16n, D.LandlockDomain.none(), 1, ex.usr()) == Done{ex.usr_domain()} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}

law witness_restrict_bounded_depth:
  {Nat.is_le(D.LandlockDomain.depth(D.LandlockDomain.none()), 16n) == True{} : Bool}

law restrict_full_refused:
  for +max: Nat
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for h1: {RS.LandlockRuleset.is_none(rs) == False{} : Bool}
  for h2: {Nat.is_lt(D.LandlockDomain.depth(d), max) == False{} : Bool}
  {D.LandlockDomain.restrict(max, d, id, rs) == Fail{E.LandlockTooManyLayers{}} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}

law witness_restrict_full:
  {Bool.and(Bool.not(RS.LandlockRuleset.is_none(ex.usr())), Bool.not(Nat.is_lt(D.LandlockDomain.depth(ex.usr_domain()), 1n))) == True{} : Bool}

# Scoping

law scope_same_domain:
  for +d: D.LandlockDomain
  for +x: S.LandlockScopeRight
  {D.LandlockDomain.allows_scope(d, d, x) == True{} : Bool}

law scope_nested_allowed:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +x: S.LandlockScopeRight
  {D.LandlockDomain.allows_scope(d, D.LandlockDomain.push(d, id, rs), x) == True{} : Bool}

law scope_refuses_outside:
  for +d: D.LandlockDomain
  for +id: U32
  for +rs: RS.LandlockRuleset
  for +x: S.LandlockScopeRight
  for h: {RS.LandlockRuleset.scopes(rs, x) == True{} : Bool}
  {D.LandlockDomain.allows_scope(D.LandlockDomain.push(d, id, rs), D.LandlockDomain.none(), x) == False{} : Bool}

law witness_scope_refuses:
  {RS.LandlockRuleset.scopes(RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.none(), S.LandlockScope.all()), S.LandlockScopeSignal{}) == True{} : Bool}

# Vectors

# landlock(7), VERSIONS and EXAMPLES: (MAKE_SYM << 1) - 1, (REFER << 1) - 1,
# (TRUNCATE << 1) - 1; IOCTL_DEV is bit 15
law mask_abi1:
  {R.LandlockFs.to_u32(A.LandlockAbi.fs(1n)) == 8191 : U32}

law mask_abi2:
  {R.LandlockFs.to_u32(A.LandlockAbi.fs(2n)) == 16383 : U32}

law mask_abi3:
  {R.LandlockFs.to_u32(A.LandlockAbi.fs(3n)) == 32767 : U32}

law mask_abi5:
  {R.LandlockFs.to_u32(A.LandlockAbi.fs(5n)) == 65535 : U32}

law mask_abi4_net:
  {N.LandlockNet.to_u32(A.LandlockAbi.net(4n)) == 3 : U32}

law mask_abi6_scope:
  {S.LandlockScope.to_u32(A.LandlockAbi.scope(6n)) == 3 : U32}

law mask_abi0:
  {R.LandlockFs.to_u32(A.LandlockAbi.fs(0n)) == 0 : U32}

law mask_round_trip:
  {R.LandlockFs.of_mask(R.LandlockFs.to_mask(ex.usr_rights())) == Done{ex.usr_rights()} : Result<&2, &2, E.LandlockError, R.LandlockFs>}

law mask_unknown_bit:
  {R.LandlockFs.of_mask(W.W64.from_u32(65536)) == Fail{E.LandlockUnknownAccess{}} : Result<&2, &2, E.LandlockError, R.LandlockFs>}

# landlock(7)'s example: /usr readable, everything else refused
law example_read_usr:
  {L.Landlock.check(ex.usr_domain(), L.LandlockOpOpen{ex.p("/usr/lib/libc.so"), True{}, False{}, False{}}) == F.LandlockAllowed{} : F.LandlockDecision}

law example_write_usr:
  {L.Landlock.check(ex.usr_domain(), L.LandlockOpOpen{ex.p("/usr/lib/libc.so"), True{}, True{}, False{}}) == F.LandlockDeniedAccess{} : F.LandlockDecision}

law example_read_etc:
  {L.Landlock.check(ex.usr_domain(), L.LandlockOpOpen{ex.p("/etc/passwd"), True{}, False{}, False{}}) == F.LandlockDeniedAccess{} : F.LandlockDecision}

law example_mkdir_usr:
  {L.Landlock.check(ex.usr_domain(), L.LandlockOpCreate{ex.p("/usr"), R.LandlockDir{}}) == F.LandlockDeniedAccess{} : F.LandlockDecision}

# Linux 6.6: an ABI 1 ruleset allowing everything still refuses reparenting
# (EXDEV), but not a rename within one directory
law example_v1_reparent:
  {F.LandlockRefer.rename(D.LandlockDomain.push(D.LandlockDomain.none(), 1, ex.v1()), ex.p("/a"), ex.p("/b"), R.LandlockReg{}) == F.LandlockDeniedReparent{} : F.LandlockDecision}

law example_v1_same_dir:
  {F.LandlockRefer.rename(D.LandlockDomain.push(D.LandlockDomain.none(), 1, ex.v1()), ex.p("/a"), ex.p("/a"), R.LandlockReg{}) == F.LandlockAllowed{} : F.LandlockDecision}

# Linux 6.6: moving a regular file from /a to /b would gain READ_FILE (EXDEV)
law example_gain:
  {F.LandlockRefer.rename(ex.gain(), ex.p("/a"), ex.p("/b"), R.LandlockReg{}) == F.LandlockDeniedReparent{} : F.LandlockDecision}

# ... and a directory moved there would too (MAKE_DIR, REMOVE_DIR missing
# first: EACCES)
law example_gain_dir:
  {F.LandlockRefer.rename(ex.gain(), ex.p("/a"), ex.p("/b"), R.LandlockDir{}) == F.LandlockDeniedAccess{} : F.LandlockDecision}

law example_lose:
  {F.LandlockRefer.rename(ex.gain(), ex.p("/b"), ex.p("/a"), R.LandlockReg{}) == F.LandlockAllowed{} : F.LandlockDecision}

law example_link_gain:
  {F.LandlockRefer.link(ex.gain(), ex.p("/a"), ex.p("/b"), R.LandlockReg{}) == F.LandlockDeniedReparent{} : F.LandlockDecision}
