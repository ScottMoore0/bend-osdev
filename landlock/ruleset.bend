# bend-osdev-landlock: rulesets (landlock_create_ruleset(2),
# landlock_add_rule(2)) and what one ruleset, as one layer of a domain,
# allows.
#
# A ruleset handles some filesystem rights, some network rights and some
# scoped actions, and holds path-beneath rules (rights allowed on a path and
# everything beneath it) and net-port rules (rights allowed on a TCP port).
# As a layer it refuses a handled right unless a rule on the path or one of
# its ancestors allows it (landlock(7): "One policy layer grants access to a
# file path if at least one of its rules encountered on the path grants the
# access"), and never refuses a right it does not handle.
#
# FS_REFER is the one exception landlock(7) names: it "is denied by default
# by any ruleset, even if the right is not specified as handled". So a ruleset
# that handles any filesystem right handles REFER too (LandlockRuleset.handles),
# and only a rule allowing REFER, which needs REFER explicitly handled, grants
# it. A ruleset handling no filesystem right does not restrict the
# filesystem at all.
import Base
import ./error.bend as E
import ./path.bend as P
import ./rights.bend as R
import ./net.bend as N
import ./scope.bend as S
import ./abi.bend as A

type LandlockPathRule is Data:
  LandlockPathRule{beneath: P.LandlockPath, allowed: R.LandlockFs}

type LandlockRuleset is Data:
  LandlockRuleset{handled_fs: R.LandlockFs, handled_net: N.LandlockNet, scoped: S.LandlockScope, paths: List<&2, LandlockPathRule>, ports: List<&2, N.LandlockNetRule>}

def LandlockRuleset.handled_fs(rs: LandlockRuleset) -> R.LandlockFs:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      f

def LandlockRuleset.handled_net(rs: LandlockRuleset) -> N.LandlockNet:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      n

def LandlockRuleset.scoped(rs: LandlockRuleset) -> S.LandlockScope:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      s

def LandlockRuleset.paths(rs: LandlockRuleset) -> List<&2, LandlockPathRule>:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      ps

def LandlockRuleset.ports(rs: LandlockRuleset) -> List<&2, N.LandlockNetRule>:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      qs

# a ruleset with these handled sets and no rules (not checked against an ABI)
def LandlockRuleset.make(f: R.LandlockFs, n: N.LandlockNet, s: S.LandlockScope) -> LandlockRuleset:
  LandlockRuleset{f, n, s, Nil{}, Nil{}}

# the ruleset that handles nothing (the kernel refuses to create it, ENOMSG;
# best effort answers it when the ABI knows none of the rights asked for)
def LandlockRuleset.none() -> LandlockRuleset:
  LandlockRuleset.make(R.LandlockFs.none(), N.LandlockNet.none(), S.LandlockScope.none())

# handles no right and scopes no action
def LandlockRuleset.is_none(rs: LandlockRuleset) -> Bool:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      Bool.and(R.LandlockFs.is_empty(f), Bool.and(N.LandlockNet.is_empty(n), S.LandlockScope.is_empty(s)))

# landlock_create_ruleset(2)

def LandlockRuleset.create.go(known: Bool, empty: Bool, f: R.LandlockFs, n: N.LandlockNet, s: S.LandlockScope) -> Result<&2, &2, E.LandlockError, LandlockRuleset>:
  match known:
    case False{}:
      Fail{E.LandlockUnknownAccess{}}
    case True{}:
      match empty:
        case True{}:
          Fail{E.LandlockEmptyRuleset{}}
        case False{}:
          Done{LandlockRuleset.make(f, n, s)}

# a new ruleset on a kernel of ABI version v: EOPNOTSUPP without Landlock,
# EINVAL for a right v does not know, ENOMSG when nothing is handled
def LandlockRuleset.create(v: Nat, +f: R.LandlockFs, +n: N.LandlockNet, +s: S.LandlockScope) -> Result<&2, &2, E.LandlockError, LandlockRuleset>:
  match v:
    case 0n:
      Fail{E.LandlockNotSupported{}}
    case 1n+(+p):
      LandlockRuleset.create.go(Bool.and(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p)))), Bool.and(R.LandlockFs.is_empty(f), Bool.and(N.LandlockNet.is_empty(n), S.LandlockScope.is_empty(s))), f, n, s)

# What one ruleset allows

def LandlockRuleset.handles.go(refer: Bool, +h: R.LandlockFs, r: R.LandlockFsRight) -> Bool:
  match refer:
    case True{}:
      Bool.not(R.LandlockFs.is_empty(h))
    case False{}:
      R.LandlockFs.has(h, r)

def LandlockRuleset.is_refer(r: R.LandlockFsRight) -> Bool:
  match r:
    case R.LandlockRefer{}:
      True{}
    case _:
      False{}

# the ruleset restricts this filesystem right: it handles it, or it is REFER
# and the ruleset handles any filesystem right
def LandlockRuleset.handles(rs: LandlockRuleset, +r: R.LandlockFsRight) -> Bool:
  LandlockRuleset.handles.go(LandlockRuleset.is_refer(r), LandlockRuleset.handled_fs(rs), r)

def LandlockRuleset.beneath.pick(hit: Bool, a: R.LandlockFs) -> R.LandlockFs:
  match hit:
    case True{}:
      a
    case False{}:
      R.LandlockFs.none()

# the union of the rights the rules on p or an ancestor of p allow
def LandlockRuleset.beneath(rules: List<&2, LandlockPathRule>, +p: P.LandlockPath) -> R.LandlockFs:
  match rules:
    case Nil{}:
      R.LandlockFs.none()
    case Con{LandlockPathRule{q, a}, t}:
      R.LandlockFs.union(LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(p, q), a), LandlockRuleset.beneath(t, p))

# the handled rights granted on p
def LandlockRuleset.granted(rs: LandlockRuleset, +p: P.LandlockPath) -> R.LandlockFs:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      R.LandlockFs.inter(f, LandlockRuleset.beneath(ps, p))

# the ruleset, as a layer, allows right r on path p
def LandlockRuleset.allows(+rs: LandlockRuleset, p: P.LandlockPath, +r: R.LandlockFsRight) -> Bool:
  R.LandlockBits.imp(LandlockRuleset.handles(rs, r), R.LandlockFs.has(LandlockRuleset.granted(rs, p), r))

# every right of a request
def LandlockRuleset.allows_all(req: List<&2, R.LandlockFsRight>, +rs: LandlockRuleset, +p: P.LandlockPath) -> Bool:
  match req:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(LandlockRuleset.allows(rs, p, r), LandlockRuleset.allows_all(t, rs, p))

def LandlockRuleset.handles_net(rs: LandlockRuleset, r: N.LandlockNetRight) -> Bool:
  N.LandlockNet.has(LandlockRuleset.handled_net(rs), r)

def LandlockRuleset.granted_net(rs: LandlockRuleset, +port: U32) -> N.LandlockNet:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      N.LandlockNet.inter(n, N.LandlockNet.granted(qs, port))

def LandlockRuleset.allows_net(+rs: LandlockRuleset, port: U32, +r: N.LandlockNetRight) -> Bool:
  R.LandlockBits.imp(LandlockRuleset.handles_net(rs, r), N.LandlockNet.has(LandlockRuleset.granted_net(rs, port), r))

def LandlockRuleset.scopes(rs: LandlockRuleset, x: S.LandlockScopeRight) -> Bool:
  S.LandlockScope.has(LandlockRuleset.scoped(rs), x)

# landlock_add_rule(2)

# the rule added without checks
def LandlockRuleset.with_path(rs: LandlockRuleset, q: P.LandlockPath, a: R.LandlockFs) -> LandlockRuleset:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      LandlockRuleset{f, n, s, Con{LandlockPathRule{q, a}, ps}, qs}

def LandlockRuleset.with_port(rs: LandlockRuleset, port: U32, a: N.LandlockNet) -> LandlockRuleset:
  match rs:
    case LandlockRuleset{f, n, s, ps, qs}:
      LandlockRuleset{f, n, s, ps, Con{N.LandlockNetRule{port, a}, qs}}

def LandlockRuleset.add_path.go(empty: Bool, handled: Bool, fits: Bool, rs: LandlockRuleset, q: P.LandlockPath, a: R.LandlockFs) -> Result<&2, &2, E.LandlockError, LandlockRuleset>:
  match empty:
    case True{}:
      Fail{E.LandlockEmptyRule{}}
    case False{}:
      match handled:
        case False{}:
          Fail{E.LandlockRuleNotHandled{}}
        case True{}:
          match fits:
            case False{}:
              Fail{E.LandlockDirRightOnFile{}}
            case True{}:
              Done{LandlockRuleset.with_path(rs, q, a)}

# a path-beneath rule allowing a on the hierarchy q (a directory, or a file
# when is_dir is False): ENOMSG for no right, EINVAL for a right the ruleset
# does not handle or, on a file, a right a file cannot receive
def LandlockRuleset.add_path(+rs: LandlockRuleset, q: P.LandlockPath, is_dir: Bool, +a: R.LandlockFs) -> Result<&2, &2, E.LandlockError, LandlockRuleset>:
  LandlockRuleset.add_path.go(R.LandlockFs.is_empty(a), R.LandlockFs.subset(a, LandlockRuleset.handled_fs(rs)), Bool.or(is_dir, R.LandlockFs.subset(a, R.LandlockFs.file_rights())), rs, q, a)

def LandlockRuleset.add_port.go(empty: Bool, handled: Bool, fits: Bool, rs: LandlockRuleset, port: U32, a: N.LandlockNet) -> Result<&2, &2, E.LandlockError, LandlockRuleset>:
  match empty:
    case True{}:
      Fail{E.LandlockEmptyRule{}}
    case False{}:
      match handled:
        case False{}:
          Fail{E.LandlockRuleNotHandled{}}
        case True{}:
          match fits:
            case False{}:
              Fail{E.LandlockBadPort{}}
            case True{}:
              Done{LandlockRuleset.with_port(rs, port, a)}

# a net-port rule allowing a on a TCP port: ENOMSG for no right, EINVAL for a
# right the ruleset does not handle or a port above 65535
def LandlockRuleset.add_port(+rs: LandlockRuleset, +port: U32, +a: N.LandlockNet) -> Result<&2, &2, E.LandlockError, LandlockRuleset>:
  LandlockRuleset.add_port.go(N.LandlockNet.is_empty(a), N.LandlockNet.subset(a, LandlockRuleset.handled_net(rs)), U32.is_le(port, N.LandlockNet.max_port()), rs, port, a)
