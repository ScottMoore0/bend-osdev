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

def p(s: String) -> P.LandlockPath:
  P.LandlockPath.of_string(s)

def show_rs(r: Result<&2, &2, E.LandlockError, RS.LandlockRuleset>) -> String:
  match r:
    case Fail{+e}:
      E.LandlockError.name(e) ++ " (" ++ E.LandlockError.errno(e) ++ ")"
    case Done{+rs}:
      "fs " ++ R.LandlockFs.show(RS.LandlockRuleset.handled_fs(rs)) ++ ", net " ++ N.LandlockNet.show(RS.LandlockRuleset.handled_net(rs)) ++ ", scope " ++ S.LandlockScope.show(RS.LandlockRuleset.scoped(rs)) ++ ", " ++ Nat.show(List.length(&2, RS.LandlockPathRule, RS.LandlockRuleset.paths(rs))) ++ " path rules"

def show_d(r: Result<&2, &2, E.LandlockError, D.LandlockDomain>) -> String:
  match r:
    case Fail{+e}:
      E.LandlockError.name(e) ++ " (" ++ E.LandlockError.errno(e) ++ ")"
    case Done{d}:
      Nat.show(D.LandlockDomain.depth(d)) ++ " layers"

def or_none(r: Result<&2, &2, E.LandlockError, RS.LandlockRuleset>) -> RS.LandlockRuleset:
  match r:
    case Fail{e}:
      RS.LandlockRuleset.none()
    case Done{rs}:
      rs

def dom_or_none(r: Result<&2, &2, E.LandlockError, L.LandlockThread>) -> D.LandlockDomain:
  match r:
    case Fail{e}:
      D.LandlockDomain.none()
    case Done{t}:
      L.LandlockThread.domain(t)

# landlock(7)'s example, through the API: handle the ABI 3 filesystem rights,
# allow reading /usr, enforce
def example(+o: L.LandlockOptions) -> D.LandlockDomain:
  +rs0 = or_none(L.Landlock.create_ruleset(o, A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none()))
  +rs = or_none(L.Landlock.add_path(o, rs0, p("/usr"), True{}, R.LandlockFs.of_list([R.LandlockExecute{}, R.LandlockReadFile{}, R.LandlockReadDir{}])))
  dom_or_none(L.Landlock.restrict_self(o, L.LandlockThread.new(), 1, rs))

def ck(+d: D.LandlockDomain, op: L.LandlockOp) -> String:
  F.LandlockDecision.show(L.Landlock.check(d, op))

# n more layers, each handling READ_FILE with no rule
def stack(n: Nat, r: Result<&2, &2, E.LandlockError, D.LandlockDomain>) -> Result<&2, &2, E.LandlockError, D.LandlockDomain>:
  match n:
    case 0n:
      r
    case 1n+(+k):
      match r:
        case Fail{e}:
          Fail{e}
        case Done{d}:
          stack(k, D.LandlockDomain.restrict(16n, d, U32.from_nat(k), RS.LandlockRuleset.make(R.LandlockFs.single(R.LandlockReadFile{}), N.LandlockNet.none(), S.LandlockScope.none())))

def main() -> IO(Unit):
  +o = L.LandlockOptions.default()
  +strict3 = L.LandlockOptions.with_compat(L.LandlockOptions.with_abi(o, 3n), A.LandlockStrict{})
  +best3 = L.LandlockOptions.with_abi(o, 3n)
  +d = example(o)
  +rmr = R.LandlockFs.of_list([R.LandlockRefer{}, R.LandlockMakeReg{}, R.LandlockRemoveFile{}])
  +base = RS.LandlockRuleset.make(A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none())
  +g = D.LandlockDomain.push(D.LandlockDomain.none(), 1, RS.LandlockRuleset.with_path(RS.LandlockRuleset.with_path(base, p("/a"), rmr), p("/b"), R.LandlockFs.add(rmr, R.LandlockReadFile{})))
  +v1 = D.LandlockDomain.push(D.LandlockDomain.none(), 1, RS.LandlockRuleset.with_path(RS.LandlockRuleset.make(A.LandlockAbi.fs(1n), N.LandlockNet.none(), S.LandlockScope.none()), P.LandlockPath.root(), A.LandlockAbi.fs(1n)))
  +web = or_none(L.Landlock.add_port(o, or_none(L.Landlock.create_ruleset(o, R.LandlockFs.none(), N.LandlockNet.all(), S.LandlockScope.none())), 443, N.LandlockNet.single(N.LandlockConnectTcp{})))
  +nd = D.LandlockDomain.push(D.LandlockDomain.none(), 7, web)
  +sc = D.LandlockDomain.push(D.LandlockDomain.none(), 9, RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.none(), S.LandlockScope.all()))
  do IO<Unit>:
    IO.print("abi masks")
    IO.print(W.W64.show_hex(R.LandlockFs.to_mask(A.LandlockAbi.fs(1n))))
    IO.print(W.W64.show_hex(R.LandlockFs.to_mask(A.LandlockAbi.fs(2n))))
    IO.print(W.W64.show_hex(R.LandlockFs.to_mask(A.LandlockAbi.fs(3n))))
    IO.print(W.W64.show_hex(R.LandlockFs.to_mask(A.LandlockAbi.fs(5n))))
    IO.print(N.LandlockNet.show(A.LandlockAbi.net(4n)) ++ " " ++ S.LandlockScope.show(A.LandlockAbi.scope(6n)))
    IO.print("create")
    IO.print(show_rs(L.Landlock.create_ruleset(strict3, A.LandlockAbi.fs(3n), N.LandlockNet.none(), S.LandlockScope.none())))
    IO.print(show_rs(L.Landlock.create_ruleset(strict3, R.LandlockFs.all(), N.LandlockNet.none(), S.LandlockScope.none())))
    IO.print(show_rs(L.Landlock.create_ruleset(best3, R.LandlockFs.all(), N.LandlockNet.all(), S.LandlockScope.all())))
    IO.print(show_rs(L.Landlock.create_ruleset(strict3, R.LandlockFs.none(), N.LandlockNet.none(), S.LandlockScope.none())))
    IO.print(show_rs(L.Landlock.create_ruleset(L.LandlockOptions.with_abi(strict3, 0n), A.LandlockAbi.fs(1n), N.LandlockNet.none(), S.LandlockScope.none())))
    IO.print("add_rule")
    IO.print(show_rs(L.Landlock.add_path(strict3, base, p("/usr"), True{}, R.LandlockFs.single(R.LandlockReadDir{}))))
    IO.print(show_rs(L.Landlock.add_path(strict3, base, p("/usr"), True{}, R.LandlockFs.none())))
    IO.print(show_rs(L.Landlock.add_path(strict3, base, p("/usr"), True{}, R.LandlockFs.single(R.LandlockIoctlDev{}))))
    IO.print(show_rs(L.Landlock.add_path(best3, base, p("/usr"), True{}, R.LandlockFs.single(R.LandlockIoctlDev{}))))
    IO.print(show_rs(L.Landlock.add_path(strict3, base, p("/etc/passwd"), False{}, R.LandlockFs.single(R.LandlockReadDir{}))))
    IO.print(show_rs(L.Landlock.add_path(strict3, base, p("/etc/passwd"), False{}, R.LandlockFs.single(R.LandlockReadFile{}))))
    IO.print(show_rs(L.Landlock.add_port(o, RS.LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.all(), S.LandlockScope.none()), 65536, N.LandlockNet.all())))
    IO.print("landlock(7) example")
    IO.print(ck(d, L.LandlockOpOpen{p("/usr/lib/libc.so.6"), True{}, False{}, False{}}))
    IO.print(ck(d, L.LandlockOpExec{p("/usr/bin/env")}))
    IO.print(ck(d, L.LandlockOpReadDir{p("/usr/share")}))
    IO.print(ck(d, L.LandlockOpOpen{p("/usr/lib/libc.so.6"), True{}, True{}, False{}}))
    IO.print(ck(d, L.LandlockOpOpen{p("/etc/passwd"), True{}, False{}, False{}}))
    IO.print(ck(d, L.LandlockOpCreate{p("/tmp"), R.LandlockReg{}}))
    IO.print(ck(d, L.LandlockOpBind{8080}))
    IO.print("rename and link")
    IO.print(ck(g, L.LandlockOpRename{p("/a"), p("/b"), R.LandlockReg{}}))
    IO.print(ck(g, L.LandlockOpRename{p("/b"), p("/a"), R.LandlockReg{}}))
    IO.print(ck(g, L.LandlockOpRename{p("/a"), p("/a"), R.LandlockReg{}}))
    IO.print(ck(g, L.LandlockOpRename{p("/a"), p("/b"), R.LandlockDir{}}))
    IO.print(ck(g, L.LandlockOpLink{p("/b"), p("/a"), R.LandlockReg{}}))
    IO.print(ck(v1, L.LandlockOpRename{p("/a"), p("/b"), R.LandlockReg{}}))
    IO.print(ck(v1, L.LandlockOpRename{p("/a"), p("/a"), R.LandlockReg{}}))
    IO.print("net")
    IO.print(ck(nd, L.LandlockOpConnect{443}))
    IO.print(ck(nd, L.LandlockOpConnect{80}))
    IO.print(ck(nd, L.LandlockOpBind{443}))
    IO.print(ck(nd, L.LandlockOpOpen{p("/etc/passwd"), True{}, True{}, True{}}))
    IO.print("scope")
    IO.print(ck(sc, L.LandlockOpSignal{sc}))
    IO.print(ck(sc, L.LandlockOpSignal{D.LandlockDomain.push(sc, 10, RS.LandlockRuleset.none())}))
    IO.print(ck(sc, L.LandlockOpSignal{D.LandlockDomain.none()}))
    IO.print(ck(sc, L.LandlockOpConnectAbstract{nd}))
    IO.print(ck(nd, L.LandlockOpSignal{D.LandlockDomain.none()}))
    IO.print("layers")
    IO.print(show_d(stack(16n, Done{D.LandlockDomain.none()})))
    IO.print(show_d(stack(17n, Done{D.LandlockDomain.none()})))
    IO.print(show_d(D.LandlockDomain.restrict(16n, D.LandlockDomain.none(), 1, RS.LandlockRuleset.none())))
    IO.print("paths")
    IO.print(P.LandlockPath.show(P.LandlockPath.parent(p("/usr/lib/"))) ++ " " ++ P.LandlockPath.show(P.LandlockPath.join(p("/usr"), p("lib/x"))))

#|abi masks
#|0000000000001fff
#|0000000000003fff
#|0000000000007fff
#|000000000000ffff
#|BIND_TCP|CONNECT_TCP ABSTRACT_UNIX_SOCKET|SIGNAL
#|create
#|fs EXECUTE|WRITE_FILE|READ_FILE|READ_DIR|REMOVE_DIR|REMOVE_FILE|MAKE_CHAR|MAKE_DIR|MAKE_REG|MAKE_SOCK|MAKE_FIFO|MAKE_BLOCK|MAKE_SYM|REFER|TRUNCATE, net 0, scope 0, 0 path rules
#|LandlockUnknownAccess (EINVAL)
#|fs EXECUTE|WRITE_FILE|READ_FILE|READ_DIR|REMOVE_DIR|REMOVE_FILE|MAKE_CHAR|MAKE_DIR|MAKE_REG|MAKE_SOCK|MAKE_FIFO|MAKE_BLOCK|MAKE_SYM|REFER|TRUNCATE, net 0, scope 0, 0 path rules
#|LandlockEmptyRuleset (ENOMSG)
#|LandlockNotSupported (EOPNOTSUPP)
#|add_rule
#|fs EXECUTE|WRITE_FILE|READ_FILE|READ_DIR|REMOVE_DIR|REMOVE_FILE|MAKE_CHAR|MAKE_DIR|MAKE_REG|MAKE_SOCK|MAKE_FIFO|MAKE_BLOCK|MAKE_SYM|REFER|TRUNCATE, net 0, scope 0, 1 path rules
#|LandlockEmptyRule (ENOMSG)
#|LandlockRuleNotHandled (EINVAL)
#|fs EXECUTE|WRITE_FILE|READ_FILE|READ_DIR|REMOVE_DIR|REMOVE_FILE|MAKE_CHAR|MAKE_DIR|MAKE_REG|MAKE_SOCK|MAKE_FIFO|MAKE_BLOCK|MAKE_SYM|REFER|TRUNCATE, net 0, scope 0, 0 path rules
#|LandlockDirRightOnFile (EINVAL)
#|fs EXECUTE|WRITE_FILE|READ_FILE|READ_DIR|REMOVE_DIR|REMOVE_FILE|MAKE_CHAR|MAKE_DIR|MAKE_REG|MAKE_SOCK|MAKE_FIFO|MAKE_BLOCK|MAKE_SYM|REFER|TRUNCATE, net 0, scope 0, 1 path rules
#|LandlockBadPort (EINVAL)
#|landlock(7) example
#|OK
#|OK
#|OK
#|EACCES
#|EACCES
#|EACCES
#|OK
#|rename and link
#|EXDEV
#|OK
#|OK
#|EACCES
#|OK
#|EXDEV
#|OK
#|net
#|OK
#|EACCES
#|EACCES
#|OK
#|scope
#|OK
#|OK
#|EPERM
#|EPERM
#|OK
#|layers
#|16 layers
#|LandlockTooManyLayers (E2BIG)
#|0 layers
#|paths
#|/usr /usr/lib/x
