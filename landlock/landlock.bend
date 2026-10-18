# bend-osdev-landlock: Landlock rule evaluation, from Landlock's documented
# user API (landlock(7), landlock_create_ruleset(2), landlock_add_rule(2),
# landlock_restrict_self(2), and the kernel's userspace-api/landlock
# document). This file is the entry: the choices (LandlockOptions), the
# three system calls as a program makes them, and the answer to an operation
# (LandlockOp) under a domain.
#
# The other files: path.bend (the hierarchy), rights.bend (filesystem rights
# and sets), net.bend (network rights, net-port rules), scope.bend (IPC
# scoping), abi.bend (ABI versions), ruleset.bend (rulesets, one layer's
# answer), domain.bend (stacked layers), refer.bend (rename and link),
# error.bend (the errors).
import Base
import ./error.bend as E
import ./path.bend as P
import ./rights.bend as R
import ./net.bend as N
import ./scope.bend as S
import ./abi.bend as A
import ./ruleset.bend as RS
import ./domain.bend as D
import ./refer.bend as F

# The choices

type LandlockOptions is Data:
  # abi: the kernel's ABI version (0: no Landlock); compat: what to do with a
  # right it lacks; max_layers: the most layers a domain may have
  LandlockOptions{abi: Nat, compat: A.LandlockCompat, max_layers: Nat}

# the newest ABI, best effort, 16 layers
def LandlockOptions.default() -> LandlockOptions:
  LandlockOptions{A.LandlockAbi.latest(), A.LandlockBestEffort{}, 16n}

def LandlockOptions.abi(o: LandlockOptions) -> Nat:
  match o:
    case LandlockOptions{v, c, m}:
      v

def LandlockOptions.compat(o: LandlockOptions) -> A.LandlockCompat:
  match o:
    case LandlockOptions{v, c, m}:
      c

def LandlockOptions.max_layers(o: LandlockOptions) -> Nat:
  match o:
    case LandlockOptions{v, c, m}:
      m

def LandlockOptions.with_abi(o: LandlockOptions, v: Nat) -> LandlockOptions:
  match o:
    case LandlockOptions{w, c, m}:
      LandlockOptions{v, c, m}

def LandlockOptions.with_compat(o: LandlockOptions, c: A.LandlockCompat) -> LandlockOptions:
  match o:
    case LandlockOptions{v, d, m}:
      LandlockOptions{v, c, m}

def LandlockOptions.with_max_layers(o: LandlockOptions, m: Nat) -> LandlockOptions:
  match o:
    case LandlockOptions{v, c, n}:
      LandlockOptions{v, c, m}

# Creating a ruleset

# best effort: the rights the ABI knows, of those asked for (handling nothing
# when it knows none of them)
def Landlock.best_effort(+v: Nat, f: R.LandlockFs, n: N.LandlockNet, s: S.LandlockScope) -> RS.LandlockRuleset:
  RS.LandlockRuleset.make(A.LandlockAbi.clip_fs(v, f), A.LandlockAbi.clip_net(v, n), A.LandlockAbi.clip_scope(v, s))

def Landlock.create_ruleset.go(c: A.LandlockCompat, +v: Nat, +f: R.LandlockFs, +n: N.LandlockNet, +s: S.LandlockScope) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match c:
    case A.LandlockBestEffort{}:
      Done{Landlock.best_effort(v, f, n, s)}
    case A.LandlockStrict{}:
      RS.LandlockRuleset.create(v, f, n, s)

# landlock_create_ruleset: handling filesystem rights f, network rights n
# and scoping s
def Landlock.create_ruleset(o: LandlockOptions, f: R.LandlockFs, n: N.LandlockNet, s: S.LandlockScope) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match o:
    case LandlockOptions{v, c, m}:
      Landlock.create_ruleset.go(c, v, f, n, s)

# the call succeeded
def Landlock.ok(r: Result<&2, &2, E.LandlockError, RS.LandlockRuleset>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

# Adding rules

def Landlock.skip_or.fs(skip: Bool, +rs: RS.LandlockRuleset, q: P.LandlockPath, is_dir: Bool, a: R.LandlockFs) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match skip:
    case True{}:
      Done{rs}
    case False{}:
      RS.LandlockRuleset.add_path(rs, q, is_dir, a)

def Landlock.add_path.go(c: A.LandlockCompat, +v: Nat, rs: RS.LandlockRuleset, q: P.LandlockPath, is_dir: Bool, +a: R.LandlockFs) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match c:
    case A.LandlockBestEffort{}:
      +b = A.LandlockAbi.clip_fs(v, a)
      Landlock.skip_or.fs(Bool.and(R.LandlockFs.is_empty(b), Bool.not(R.LandlockFs.is_empty(a))), rs, q, is_dir, b)
    case A.LandlockStrict{}:
      RS.LandlockRuleset.add_path(rs, q, is_dir, a)

# landlock_add_rule with a path-beneath rule; best effort drops the rights
# the ABI lacks, and the whole rule when that is all of them
def Landlock.add_path(o: LandlockOptions, rs: RS.LandlockRuleset, q: P.LandlockPath, is_dir: Bool, a: R.LandlockFs) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match o:
    case LandlockOptions{v, c, m}:
      Landlock.add_path.go(c, v, rs, q, is_dir, a)

def Landlock.skip_or.net(skip: Bool, +rs: RS.LandlockRuleset, port: U32, a: N.LandlockNet) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match skip:
    case True{}:
      Done{rs}
    case False{}:
      RS.LandlockRuleset.add_port(rs, port, a)

def Landlock.add_port.go(c: A.LandlockCompat, +v: Nat, rs: RS.LandlockRuleset, port: U32, +a: N.LandlockNet) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match c:
    case A.LandlockBestEffort{}:
      +b = A.LandlockAbi.clip_net(v, a)
      Landlock.skip_or.net(Bool.and(N.LandlockNet.is_empty(b), Bool.not(N.LandlockNet.is_empty(a))), rs, port, b)
    case A.LandlockStrict{}:
      RS.LandlockRuleset.add_port(rs, port, a)

# landlock_add_rule with a net-port rule
def Landlock.add_port(o: LandlockOptions, rs: RS.LandlockRuleset, port: U32, a: N.LandlockNet) -> Result<&2, &2, E.LandlockError, RS.LandlockRuleset>:
  match o:
    case LandlockOptions{v, c, m}:
      Landlock.add_port.go(c, v, rs, port, a)

# Enforcing a ruleset

type LandlockThread is Data:
  LandlockThread{domain: D.LandlockDomain, no_new_privs: Bool, cap_sys_admin: Bool}

def LandlockThread.domain(t: LandlockThread) -> D.LandlockDomain:
  match t:
    case LandlockThread{d, nnp, cap}:
      d

# a thread that never restricted itself, with no_new_privs set
def LandlockThread.new() -> LandlockThread:
  LandlockThread{D.LandlockDomain.none(), True{}, False{}}

def Landlock.restrict_self.wrap(r: Result<&2, &2, E.LandlockError, D.LandlockDomain>, nnp: Bool, cap: Bool) -> Result<&2, &2, E.LandlockError, LandlockThread>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{d}:
      Done{LandlockThread{d, nnp, cap}}

def Landlock.restrict_self.go(may: Bool, max: Nat, d: D.LandlockDomain, nnp: Bool, cap: Bool, id: U32, rs: RS.LandlockRuleset) -> Result<&2, &2, E.LandlockError, LandlockThread>:
  match may:
    case False{}:
      Fail{E.LandlockNoNewPrivs{}}
    case True{}:
      Landlock.restrict_self.wrap(D.LandlockDomain.restrict(max, d, id, rs), nnp, cap)

# landlock_restrict_self: EPERM without no_new_privs or CAP_SYS_ADMIN; the
# new layer is named id (scope.bend)
def Landlock.restrict_self(o: LandlockOptions, t: LandlockThread, id: U32, rs: RS.LandlockRuleset) -> Result<&2, &2, E.LandlockError, LandlockThread>:
  match t:
    case LandlockThread{d, +nnp, +cap}:
      Landlock.restrict_self.go(Bool.or(nnp, cap), LandlockOptions.max_layers(o), d, nnp, cap, id, rs)

# Operations

type LandlockOp is Data:
  # open(2) of a file, for reading, writing, and with O_TRUNC
  LandlockOpOpen{path: P.LandlockPath, read: Bool, write: Bool, truncate: Bool}
  # opening or listing a directory
  LandlockOpReadDir{path: P.LandlockPath}
  # execve(2): EXECUTE, and READ_FILE, since the kernel opens the file to
  # read it (observed on Linux 6.6: with READ_FILE handled and not granted,
  # execve fails with EACCES)
  LandlockOpExec{path: P.LandlockPath}
  # truncate(2)
  LandlockOpTruncate{path: P.LandlockPath}
  # ioctl(2) on a device file
  LandlockOpIoctl{path: P.LandlockPath}
  # creating a file of this kind in a directory (mkdir, mknod, mkfifo,
  # symlink, bind of a UNIX socket, O_CREAT)
  LandlockOpCreate{dir: P.LandlockPath, kind: R.LandlockFileKind}
  # unlink(2), rmdir(2)
  LandlockOpRemove{dir: P.LandlockPath, kind: R.LandlockFileKind}
  # rename(2), from directory src to directory dst
  LandlockOpRename{src: P.LandlockPath, dst: P.LandlockPath, kind: R.LandlockFileKind}
  # link(2)
  LandlockOpLink{src: P.LandlockPath, dst: P.LandlockPath, kind: R.LandlockFileKind}
  # bind(2), connect(2) of a TCP socket
  LandlockOpBind{port: U32}
  LandlockOpConnect{port: U32}
  # kill(2) to, or connect(2) to an abstract UNIX socket of, a process of
  # domain target
  LandlockOpSignal{target: D.LandlockDomain}
  LandlockOpConnectAbstract{target: D.LandlockDomain}

def Landlock.when(b: Bool, r: R.LandlockFsRight, rest: List<&2, R.LandlockFsRight>) -> List<&2, R.LandlockFsRight>:
  match b:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

# the filesystem rights open(2) needs
def Landlock.open_rights(read: Bool, write: Bool, truncate: Bool) -> List<&2, R.LandlockFsRight>:
  Landlock.when(read, R.LandlockReadFile{}, Landlock.when(write, R.LandlockWriteFile{}, Landlock.when(truncate, R.LandlockTruncate{}, Nil{})))

def Landlock.fs(+d: D.LandlockDomain, p: P.LandlockPath, req: List<&2, R.LandlockFsRight>) -> F.LandlockDecision:
  F.LandlockDecision.of_bool(D.LandlockDomain.allows(d, p, req), F.LandlockDeniedAccess{})

# what the domain answers to an operation
def Landlock.check(+d: D.LandlockDomain, op: LandlockOp) -> F.LandlockDecision:
  match op:
    case LandlockOpOpen{p, r, w, t}:
      Landlock.fs(d, p, Landlock.open_rights(r, w, t))
    case LandlockOpReadDir{p}:
      Landlock.fs(d, p, [R.LandlockReadDir{}])
    case LandlockOpExec{p}:
      Landlock.fs(d, p, [R.LandlockExecute{}, R.LandlockReadFile{}])
    case LandlockOpTruncate{p}:
      Landlock.fs(d, p, [R.LandlockTruncate{}])
    case LandlockOpIoctl{p}:
      Landlock.fs(d, p, [R.LandlockIoctlDev{}])
    case LandlockOpCreate{p, k}:
      Landlock.fs(d, p, [R.LandlockFileKind.make_right(k)])
    case LandlockOpRemove{p, k}:
      Landlock.fs(d, p, [R.LandlockFileKind.remove_right(k)])
    case LandlockOpRename{a, b, k}:
      F.LandlockRefer.rename(d, a, b, k)
    case LandlockOpLink{a, b, k}:
      F.LandlockRefer.link(d, a, b, k)
    case LandlockOpBind{port}:
      F.LandlockDecision.of_bool(D.LandlockDomain.allows_net(d, port, N.LandlockBindTcp{}), F.LandlockDeniedAccess{})
    case LandlockOpConnect{port}:
      F.LandlockDecision.of_bool(D.LandlockDomain.allows_net(d, port, N.LandlockConnectTcp{}), F.LandlockDeniedAccess{})
    case LandlockOpSignal{t}:
      F.LandlockDecision.of_bool(D.LandlockDomain.allows_scope(d, t, S.LandlockScopeSignal{}), F.LandlockDeniedScope{})
    case LandlockOpConnectAbstract{t}:
      F.LandlockDecision.of_bool(D.LandlockDomain.allows_scope(d, t, S.LandlockScopeAbstractUnix{}), F.LandlockDeniedScope{})
