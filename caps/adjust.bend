# bend-osdev-caps, adjust.bend: changing a thread's capability sets.
# capset(2) under the rules of capabilities(7) ("Programmatically adjusting
# capability sets"), and the prctl(2) operations PR_CAPBSET_READ,
# PR_CAPBSET_DROP and PR_CAP_AMBIENT.
import Base
import ./caps.bend as C

# capset(2)

# the new sets; ambient capabilities no longer both permitted and
# inheritable are lowered (capabilities(7), "Ambient")
def CapAdjust.set_pie(s: C.CapState, +p: C.CapSet(), +i: C.CapSet(), e: C.CapSet()) -> C.CapState:
  match s:
    case C.CapState{op, oi, oe, b, a}:
      C.CapState{p, i, e, b, C.CapSet.inter(C.CapSet.inter(a, p), i)}

def CapAdjust.capset.done(+c: C.CapCred, e: C.CapSet(), p: C.CapSet(), i: C.CapSet()) -> Result<&2, &2, C.CapsError, C.CapCred>:
  Done{C.CapCred.with_sets(c, CapAdjust.set_pie(C.CapCred.sets(c), p, i, e))}

# without CAP_SETPCAP in the effective set: the new inheritable set must be
# within the old inheritable and permitted sets
def CapAdjust.capset.r4(setpcap: Bool, inh_ok: Bool, +c: C.CapCred, e: C.CapSet(), p: C.CapSet(), i: C.CapSet()) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match setpcap:
    case True{}:
      CapAdjust.capset.done(c, e, p, i)
    case False{}:
      match inh_ok:
        case False{}:
          Fail{C.CapsInheritableNotPermitted{}}
        case True{}:
          CapAdjust.capset.done(c, e, p, i)

# the new inheritable set must be within the old inheritable and bounding sets
def CapAdjust.capset.r3(ok: Bool, +c: C.CapCred, e: C.CapSet(), p: C.CapSet(), +i: C.CapSet()) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match ok:
    case False{}:
      Fail{C.CapsInheritableNotBounded{}}
    case True{}:
      +s = C.CapCred.sets(c)
      CapAdjust.capset.r4(C.CapSet.has(C.CapState.effective(s), C.Cap.setpcap()), C.CapSet.subset(i, C.CapSet.union(C.CapState.inheritable(s), C.CapState.permitted(s))), c, e, p, i)

# the new effective set must be within the new permitted set
def CapAdjust.capset.r2(ok: Bool, +c: C.CapCred, e: C.CapSet(), p: C.CapSet(), +i: C.CapSet()) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match ok:
    case False{}:
      Fail{C.CapsEffectiveNotPermitted{}}
    case True{}:
      +s = C.CapCred.sets(c)
      CapAdjust.capset.r3(C.CapSet.subset(i, C.CapSet.union(C.CapState.inheritable(s), C.CapState.bounding(s))), c, e, p, i)

# the new permitted set must be within the old one
def CapAdjust.capset.r1(ok: Bool, +c: C.CapCred, +e: C.CapSet(), +p: C.CapSet(), i: C.CapSet()) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match ok:
    case False{}:
      Fail{C.CapsPermittedGrows{}}
    case True{}:
      CapAdjust.capset.r2(C.CapSet.subset(e, p), c, e, p, i)

# capset(2) with new effective e, permitted p and inheritable i. The rules
# are checked in this order, and the first that fails names the error.
def Caps.capset(+c: C.CapCred, e: C.CapSet(), +p: C.CapSet(), i: C.CapSet()) -> Result<&2, &2, C.CapsError, C.CapCred>:
  CapAdjust.capset.r1(C.CapSet.subset(p, C.CapState.permitted(C.CapCred.sets(c))), c, e, p, i)

# prctl(2) PR_CAPBSET_READ and PR_CAPBSET_DROP

def CapAdjust.bset_drop.go(v: Bool, setpcap: Bool, +c: C.CapCred, x: U32) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match v:
    case False{}:
      Fail{C.CapsInvalidCap{}}
    case True{}:
      match setpcap:
        case False{}:
          Fail{C.CapsNoSetpcap{}}
        case True{}:
          +s = C.CapCred.sets(c)
          Done{C.CapCred.with_sets(c, C.CapState.with_bounding(s, C.CapSet.del(C.CapState.bounding(s), x)))}

# drop capability x from the bounding set: CapsInvalidCap (EINVAL) if the
# kernel does not support x, CapsNoSetpcap (EPERM) without CAP_SETPCAP in the
# effective set
def Caps.bset_drop(k: C.CapsKernel, +c: C.CapCred, +x: U32) -> Result<&2, &2, C.CapsError, C.CapCred>:
  CapAdjust.bset_drop.go(C.CapsKernel.valid(k, x), C.CapSet.has(C.CapState.effective(C.CapCred.sets(c)), C.Cap.setpcap()), c, x)

def CapAdjust.bset_read.go(v: Bool, c: C.CapCred, x: U32) -> Result<&2, &2, C.CapsError, Bool>:
  match v:
    case False{}:
      Fail{C.CapsInvalidCap{}}
    case True{}:
      Done{C.CapSet.has(C.CapState.bounding(C.CapCred.sets(c)), x)}

# whether x is in the bounding set
def Caps.bset_read(k: C.CapsKernel, c: C.CapCred, +x: U32) -> Result<&2, &2, C.CapsError, Bool>:
  CapAdjust.bset_read.go(C.CapsKernel.valid(k, x), c, x)

# prctl(2) PR_CAP_AMBIENT

def CapAdjust.ambient.allowed(c: C.CapCred, +x: U32) -> Bool:
  +s = C.CapCred.sets(c)
  Bool.and(C.CapSet.has(C.CapState.permitted(s), x), C.CapSet.has(C.CapState.inheritable(s), x))

def CapAdjust.ambient_raise.go(v: Bool, locked: Bool, allowed: Bool, +c: C.CapCred, x: U32) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match v:
    case False{}:
      Fail{C.CapsInvalidCap{}}
    case True{}:
      match locked:
        case True{}:
          Fail{C.CapsAmbientRaiseLocked{}}
        case False{}:
          match allowed:
            case False{}:
              Fail{C.CapsAmbientNotAllowed{}}
            case True{}:
              +s = C.CapCred.sets(c)
              Done{C.CapCred.with_sets(c, C.CapState.with_ambient(s, C.CapSet.add(C.CapState.ambient(s), x)))}

# PR_CAP_AMBIENT_RAISE: x must be both permitted and inheritable
# (CapsAmbientNotAllowed), and SECBIT_NO_CAP_AMBIENT_RAISE clear
# (CapsAmbientRaiseLocked)
def Caps.ambient_raise(k: C.CapsKernel, +c: C.CapCred, +x: U32) -> Result<&2, &2, C.CapsError, C.CapCred>:
  CapAdjust.ambient_raise.go(C.CapsKernel.valid(k, x), C.CapCred.no_ambient_raise(c), CapAdjust.ambient.allowed(c, x), c, x)

def CapAdjust.ambient_lower.go(v: Bool, +c: C.CapCred, x: U32) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match v:
    case False{}:
      Fail{C.CapsInvalidCap{}}
    case True{}:
      +s = C.CapCred.sets(c)
      Done{C.CapCred.with_sets(c, C.CapState.with_ambient(s, C.CapSet.del(C.CapState.ambient(s), x)))}

# PR_CAP_AMBIENT_LOWER
def Caps.ambient_lower(k: C.CapsKernel, +c: C.CapCred, +x: U32) -> Result<&2, &2, C.CapsError, C.CapCred>:
  CapAdjust.ambient_lower.go(C.CapsKernel.valid(k, x), c, x)

def CapAdjust.ambient_is_set.go(v: Bool, c: C.CapCred, x: U32) -> Result<&2, &2, C.CapsError, Bool>:
  match v:
    case False{}:
      Fail{C.CapsInvalidCap{}}
    case True{}:
      Done{C.CapSet.has(C.CapState.ambient(C.CapCred.sets(c)), x)}

# PR_CAP_AMBIENT_IS_SET
def Caps.ambient_is_set(k: C.CapsKernel, c: C.CapCred, +x: U32) -> Result<&2, &2, C.CapsError, Bool>:
  CapAdjust.ambient_is_set.go(C.CapsKernel.valid(k, x), c, x)

# PR_CAP_AMBIENT_CLEAR_ALL
def Caps.ambient_clear_all(+c: C.CapCred) -> C.CapCred:
  C.CapCred.with_sets(c, C.CapState.with_ambient(C.CapCred.sets(c), C.CapSet.empty()))
