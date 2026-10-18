import Base
import ../../word64/word64.bend as W
import ../error.bend as E
import ../path.bend as P
import ../rights.bend as R
import ../net.bend as N
import ../scope.bend as S
import ../abi.bend as A
import ../ruleset.bend as RS
import ../domain.bend as D
import ../refer.bend as F
import ../landlock.bend as L

# The helpers every generated case file starts with (gen.py copies this file
# to the head of each cases-NN.bend)

def pp(s: String) -> P.LandlockPath:
  P.LandlockPath.of_string(s)

def fsm.ok(r: Result<&2, &2, E.LandlockError, R.LandlockFs>) -> R.LandlockFs:
  match r:
    case Fail{e}:
      R.LandlockFs.none()
    case Done{s}:
      s

def fsm(m: U32) -> R.LandlockFs:
  fsm.ok(R.LandlockFs.of_mask(W.W64.from_u32(m)))

def netm.ok(r: Result<&2, &2, E.LandlockError, N.LandlockNet>) -> N.LandlockNet:
  match r:
    case Fail{e}:
      N.LandlockNet.none()
    case Done{s}:
      s

def netm(m: U32) -> N.LandlockNet:
  netm.ok(N.LandlockNet.of_mask(W.W64.from_u32(m)))

def scm.ok(r: Result<&2, &2, E.LandlockError, S.LandlockScope>) -> S.LandlockScope:
  match r:
    case Fail{e}:
      S.LandlockScope.none()
    case Done{s}:
      s

def scm(m: U32) -> S.LandlockScope:
  scm.ok(S.LandlockScope.of_mask(W.W64.from_u32(m)))

def rs.paths(xs: List<&1, String & U32>, r: RS.LandlockRuleset) -> RS.LandlockRuleset:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      (s, m) = h
      rs.paths(t, RS.LandlockRuleset.with_path(r, pp(s), fsm(m)))

def rs.ports(xs: List<&1, U32 & U32>, r: RS.LandlockRuleset) -> RS.LandlockRuleset:
  match xs:
    case Nil{}:
      r
    case Con{h, t}:
      (p, m) = h
      rs.ports(t, RS.LandlockRuleset.with_port(r, p, netm(m)))

# a ruleset: handled masks, path rules, port rules
def rs(f: U32, n: U32, s: U32, ps: List<&1, String & U32>, qs: List<&1, U32 & U32>) -> RS.LandlockRuleset:
  rs.ports(qs, rs.paths(ps, RS.LandlockRuleset.make(fsm(f), netm(n), scm(s))))

def dm.go(xs: List<&2, RS.LandlockRuleset>, +i: U32, d: D.LandlockDomain) -> D.LandlockDomain:
  match xs:
    case Nil{}:
      d
    case Con{r, t}:
      dm.go(t, U32.add(i, 1), D.LandlockDomain.push(d, i, r))

# a domain of these layers, named 1, 2, ...
def dm(xs: List<&2, RS.LandlockRuleset>) -> D.LandlockDomain:
  dm.go(xs, 1, D.LandlockDomain.none())

def tg.go(xs: List<&2, U32>, d: D.LandlockDomain) -> D.LandlockDomain:
  match xs:
    case Nil{}:
      d
    case Con{i, t}:
      tg.go(t, D.LandlockDomain.push(d, i, RS.LandlockRuleset.none()))

# a target process's domain, by its layers' names
def tg(xs: List<&2, U32>) -> D.LandlockDomain:
  tg.go(xs, D.LandlockDomain.none())

def kd(n: Nat) -> R.LandlockFileKind:
  match n:
    case 0n:
      R.LandlockReg{}
    case 1n:
      R.LandlockDir{}
    case 2n:
      R.LandlockChr{}
    case 3n:
      R.LandlockBlk{}
    case 4n:
      R.LandlockFifo{}
    case 5n:
      R.LandlockSock{}
    case _:
      R.LandlockSym{}

def ck(label: String, s: String) -> String:
  label ++ " " ++ s

def compat(strict: Bool) -> A.LandlockCompat:
  match strict:
    case True{}:
      A.LandlockStrict{}
    case False{}:
      A.LandlockBestEffort{}

def opts(abi: Nat, strict: Bool) -> L.LandlockOptions:
  L.LandlockOptions{abi, compat(strict), 16n}

def show_create(r: Result<&2, &2, E.LandlockError, RS.LandlockRuleset>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.LandlockError.name(e)
    case Done{+x}:
      "ok " ++ U32.show(R.LandlockFs.to_u32(RS.LandlockRuleset.handled_fs(x))) ++ " " ++ U32.show(N.LandlockNet.to_u32(RS.LandlockRuleset.handled_net(x))) ++ " " ++ U32.show(S.LandlockScope.to_u32(RS.LandlockRuleset.scoped(x)))

def show_add(r: Result<&2, &2, E.LandlockError, RS.LandlockRuleset>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.LandlockError.name(e)
    case Done{+x}:
      "ok " ++ Nat.show(Nat.add(List.length(&2, RS.LandlockPathRule, RS.LandlockRuleset.paths(x)), List.length(&2, N.LandlockNetRule, RS.LandlockRuleset.ports(x))))

def cr(abi: Nat, strict: Bool, f: U32, n: U32, s: U32) -> String:
  show_create(L.Landlock.create_ruleset(opts(abi, strict), fsm(f), netm(n), scm(s)))

def ap(abi: Nat, strict: Bool, h: U32, q: String, is_dir: Bool, a: U32) -> String:
  show_add(L.Landlock.add_path(opts(abi, strict), RS.LandlockRuleset.make(fsm(h), N.LandlockNet.none(), S.LandlockScope.none()), pp(q), is_dir, fsm(a)))

def ao(abi: Nat, strict: Bool, h: U32, port: U32, a: U32) -> String:
  show_add(L.Landlock.add_port(opts(abi, strict), RS.LandlockRuleset.make(R.LandlockFs.none(), netm(h), S.LandlockScope.none()), port, netm(a)))

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

def ly.show(r: Result<&2, &2, E.LandlockError, D.LandlockDomain>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ E.LandlockError.name(e)
    case Done{d}:
      "ok " ++ Nat.show(D.LandlockDomain.depth(d))

# n landlock_restrict_self calls in a row
def ly(n: Nat) -> String:
  ly.show(stack(n, Done{D.LandlockDomain.none()}))

def out(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      do IO<Unit>:
        IO.print(h)
        out(t)
