# bend-osdev-landlock: domains (landlock_restrict_self(2), landlock(7)
# "Layers of file path access rights"). A domain is a stack of layers, the
# newest first; each layer is a ruleset as it was enforced, with an identity
# (scope.bend). An access is allowed only when every layer allows it, so a
# new layer can only take accesses away.
#
# The number of layers is limited: 16 in the kernel's documentation and on
# the kernels tested (a 17th landlock_restrict_self fails with E2BIG); the
# man page (man-pages 6.7) says 64. The limit is a parameter.
import Base
import ./error.bend as E
import ./path.bend as P
import ./rights.bend as R
import ./net.bend as N
import ./scope.bend as S
import ./ruleset.bend as RS

type LandlockLayer is Data:
  LandlockLayer{id: U32, ruleset: RS.LandlockRuleset}

type LandlockDomain is Data:
  LandlockDomain{layers: List<&2, LandlockLayer>}

# the domain of a process that never restricted itself
def LandlockDomain.none() -> LandlockDomain:
  LandlockDomain{Nil{}}

def LandlockDomain.layers(d: LandlockDomain) -> List<&2, LandlockLayer>:
  match d:
    case LandlockDomain{ls}:
      ls

# the domain with one more layer, unchecked
def LandlockDomain.push(d: LandlockDomain, id: U32, rs: RS.LandlockRuleset) -> LandlockDomain:
  match d:
    case LandlockDomain{ls}:
      LandlockDomain{Con{LandlockLayer{id, rs}, ls}}

def LandlockDomain.depth(d: LandlockDomain) -> Nat:
  List.length(&2, LandlockLayer, LandlockDomain.layers(d))

def LandlockDomain.ids.go(ls: List<&2, LandlockLayer>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{LandlockLayer{id, rs}, t}:
      Con{id, LandlockDomain.ids.go(t)}

# the identities of the domain's layers
def LandlockDomain.ids(d: LandlockDomain) -> List<&2, U32>:
  LandlockDomain.ids.go(LandlockDomain.layers(d))

def LandlockDomain.restrict.go(nothing: Bool, room: Bool, d: LandlockDomain, id: U32, rs: RS.LandlockRuleset) -> Result<&2, &2, E.LandlockError, LandlockDomain>:
  match nothing:
    case True{}:
      Done{d}
    case False{}:
      match room:
        case False{}:
          Fail{E.LandlockTooManyLayers{}}
        case True{}:
          Done{LandlockDomain.push(d, id, rs)}

# landlock_restrict_self: the domain with the ruleset as a new layer named id;
# E2BIG when it already has max layers. A ruleset that handles nothing
# (best effort on a kernel that knows none of the rights asked for) leaves
# the domain as it is.
def LandlockDomain.restrict(max: Nat, +d: LandlockDomain, id: U32, +rs: RS.LandlockRuleset) -> Result<&2, &2, E.LandlockError, LandlockDomain>:
  LandlockDomain.restrict.go(RS.LandlockRuleset.is_none(rs), Nat.is_lt(LandlockDomain.depth(d), max), d, id, rs)

# Access checks: every layer must allow

def LandlockDomain.allows.go(ls: List<&2, LandlockLayer>, +p: P.LandlockPath, +req: List<&2, R.LandlockFsRight>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{LandlockLayer{id, rs}, t}:
      Bool.and(RS.LandlockRuleset.allows_all(req, rs, p), LandlockDomain.allows.go(t, p, req))

# every right of req on path p
def LandlockDomain.allows(d: LandlockDomain, p: P.LandlockPath, req: List<&2, R.LandlockFsRight>) -> Bool:
  LandlockDomain.allows.go(LandlockDomain.layers(d), p, req)

def LandlockDomain.allows_net.go(ls: List<&2, LandlockLayer>, +port: U32, +r: N.LandlockNetRight) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{LandlockLayer{id, rs}, t}:
      Bool.and(RS.LandlockRuleset.allows_net(rs, port, r), LandlockDomain.allows_net.go(t, port, r))

# the network right r on a TCP port
def LandlockDomain.allows_net(d: LandlockDomain, port: U32, r: N.LandlockNetRight) -> Bool:
  LandlockDomain.allows_net.go(LandlockDomain.layers(d), port, r)

def LandlockDomain.allows_scope.go(ls: List<&2, LandlockLayer>, +target: List<&2, U32>, +x: S.LandlockScopeRight) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{LandlockLayer{id, rs}, t}:
      Bool.and(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(rs), id, target, x), LandlockDomain.allows_scope.go(t, target, x))

# a process of domain d may do x (signal, connect to an abstract UNIX socket)
# to a process of domain target
def LandlockDomain.allows_scope(d: LandlockDomain, target: LandlockDomain, x: S.LandlockScopeRight) -> Bool:
  LandlockDomain.allows_scope.go(LandlockDomain.layers(d), LandlockDomain.ids(target), x)
