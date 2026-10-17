# bend-osdev-caps, exec.bend: the transformation of a thread's capability
# sets during execve(2), as capabilities(7) documents it ("Transformation of
# capabilities during execve()", "Safety checking for capability-dumb
# binaries", "Capabilities and execution of programs by root") and execve(2)
# (set-user-ID, and when set-ID bits and file capabilities are ignored).
import Base
import ./caps.bend as C

# The file's sets as the transformation uses them (the notional all-ones sets
# of the root rules, or the file's own), the notional effective bit, and
# whether the file is privileged (set-user-ID, set-group-ID, or with
# capabilities).
type CapExecFlags is Data:
  CapExecFlags{privileged: Bool, effective: Bool, permitted: C.CapSet(), inheritable: C.CapSet()}

def CapExec.ambient(privileged: Bool, a: C.CapSet()) -> C.CapSet():
  match privileged:
    case True{}:
      C.CapSet.empty()
    case False{}:
      a

def CapExec.effective(effective: Bool, p: C.CapSet(), a: C.CapSet()) -> C.CapSet():
  match effective:
    case True{}:
      p
    case False{}:
      a

# capabilities(7):
#   P'(ambient)     = (file is privileged) ? 0 : P(ambient)
#   P'(permitted)   = (P(inheritable) & F(inheritable)) |
#                     (F(permitted) & P(bounding)) | P'(ambient)
#   P'(effective)   = F(effective) ? P'(permitted) : P'(ambient)
#   P'(inheritable) = P(inheritable)
#   P'(bounding)    = P(bounding)
def CapExec.sets(fl: CapExecFlags, s: C.CapState) -> C.CapState:
  match fl s:
    case CapExecFlags{priv, feff, fp, fi} C.CapState{p, +i, e, +b, a}:
      +a2 = CapExec.ambient(priv, a)
      +p2 = C.CapSet.union(C.CapSet.union(C.CapSet.inter(i, fi), C.CapSet.inter(fp, b)), a2)
      C.CapState{p2, i, CapExec.effective(feff, p2, a2), b, a2}

# the effective user ID after execve: the file's owner if it is
# set-user-ID, unless set-ID bits are ignored
def CapExec.euid(ign: Bool, setuid: Bool, owner: U32, euid: U32) -> U32:
  match ign:
    case True{}:
      euid
    case False{}:
      match setuid:
        case True{}:
          owner
        case False{}:
          euid

# the file's capabilities, unless they are ignored
def CapExec.fcaps(ign: Bool, fc: Maybe<&2, C.CapFileSets>) -> Maybe<&2, C.CapFileSets>:
  match ign:
    case True{}:
      None{}
    case False{}:
      fc

def CapExec.has_caps(fc: Maybe<&2, C.CapFileSets>) -> Bool:
  match fc:
    case None{}:
      False{}
    case Some{x}:
      True{}

# a privileged file: set-user-ID, set-group-ID, or with capabilities
def CapExec.privileged(ign: Bool, setuid: Bool, setgid: Bool, fc: Maybe<&2, C.CapFileSets>) -> Bool:
  match ign:
    case True{}:
      CapExec.has_caps(fc)
    case False{}:
      Bool.or(setuid, Bool.or(setgid, CapExec.has_caps(fc)))

# the file's own sets (empty when it has none); effective is the notional
# effective bit of the root rules, ORed with the file's own
def CapExec.flags.file(priv: Bool, effective: Bool, fc: Maybe<&2, C.CapFileSets>) -> CapExecFlags:
  match fc:
    case None{}:
      CapExecFlags{priv, effective, C.CapSet.empty(), C.CapSet.empty()}
    case Some{C.CapFileSets{fp, fi, fe}}:
      CapExecFlags{priv, Bool.or(effective, fe), fp, fi}

# effective UID 0 but real UID not: the file's sets are all ones, unless the
# file has capabilities (a set-user-ID-root program with file capabilities)
def CapExec.flags.suid_root(priv: Bool, fc: Maybe<&2, C.CapFileSets>) -> CapExecFlags:
  match fc:
    case None{}:
      CapExecFlags{priv, True{}, C.CapSet.full(), C.CapSet.full()}
    case Some{C.CapFileSets{fp, fi, fe}}:
      CapExecFlags{priv, True{}, fp, fi}

def CapExec.fc_effective(fc: Maybe<&2, C.CapFileSets>) -> Bool:
  match fc:
    case None{}:
      False{}
    case Some{C.CapFileSets{fp, fi, fe}}:
      fe

# "Capabilities and execution of programs by root": with r0 (real UID 0)
# and e0 (effective UID 0, after the set-user-ID bit), unless SECBIT_NOROOT:
#   (1) the file's inheritable and permitted sets are all ones (but a
#       set-user-ID-root program with capabilities run by a non-root real
#       UID keeps its own);
#   (2) if e0, the file effective bit is one.
def CapExec.flags.go(noroot: Bool, r0: Bool, e0: Bool, priv: Bool, fc: Maybe<&2, C.CapFileSets>) -> CapExecFlags:
  match noroot:
    case True{}:
      CapExec.flags.file(priv, False{}, fc)
    case False{}:
      match r0:
        case True{}:
          CapExecFlags{priv, Bool.or(e0, CapExec.fc_effective(fc)), C.CapSet.full(), C.CapSet.full()}
        case False{}:
          match e0:
            case True{}:
              CapExec.flags.suid_root(priv, fc)
            case False{}:
              CapExec.flags.file(priv, False{}, fc)

# the file's capabilities as execve sees them: none if ign, or if the kernel
# has file capabilities off
def CapExec.file_caps(k: C.CapsKernel, f: C.CapFile, ign: Bool) -> Maybe<&2, C.CapFileSets>:
  match f:
    case C.CapFile{u, su, sg, fc}:
      CapExec.fcaps(Bool.or(ign, Bool.not(C.CapsKernel.file_caps(k))), fc)

def CapExec.flags.mk(+fc2: Maybe<&2, C.CapFileSets>, c: C.CapCred, f: C.CapFile, +ign: Bool) -> CapExecFlags:
  match c f:
    case C.CapCred{r, e, s, nr, na, st} C.CapFile{u, +su, sg, fc}:
      CapExec.flags.go(nr, U32.is_eq(r, 0), U32.is_eq(CapExec.euid(ign, su, u, e), 0), CapExec.privileged(ign, su, sg, fc2), fc2)

def CapExec.flags(k: C.CapsKernel, c: C.CapCred, +f: C.CapFile, +ign: Bool) -> CapExecFlags:
  CapExec.flags.mk(CapExec.file_caps(k, f, ign), c, f, ign)

# The thread's sets after it executes f. ign: the set-user-ID and
# set-group-ID bits and the file capabilities are ignored (no_new_privs, a
# nosuid mount, or a ptraced caller: execve(2)).
def Caps.execve.sets(k: C.CapsKernel, +c: C.CapCred, f: C.CapFile, ign: Bool) -> C.CapState:
  CapExec.sets(CapExec.flags(k, c, f, ign), C.CapCred.sets(c))

# "Safety checking for capability-dumb binaries": a file with capabilities
# and the effective bit must grant all of its permitted set
def CapExec.dumb_ok(fc: Maybe<&2, C.CapFileSets>, p: C.CapSet()) -> Bool:
  match fc:
    case None{}:
      True{}
    case Some{C.CapFileSets{fp, fi, fe}}:
      match fe:
        case False{}:
          True{}
        case True{}:
          C.CapSet.subset(fp, p)

def CapExec.fin(ok: Bool, c: C.CapCred, +euid: U32, s: C.CapState) -> Result<&2, &2, C.CapsError, C.CapCred>:
  match ok:
    case False{}:
      Fail{C.CapsCapabilityDumb{}}
    case True{}:
      match c:
        case C.CapCred{r, e, sv, nr, na, st}:
          Done{C.CapCred{r, euid, euid, nr, na, s}}

def CapExec.new_euid(c: C.CapCred, f: C.CapFile, ign: Bool) -> U32:
  match c f:
    case C.CapCred{r, e, s, nr, na, st} C.CapFile{u, su, sg, fc}:
      CapExec.euid(ign, su, u, e)

# execve(2) of f: the new credentials (the effective user ID changes for a
# set-user-ID file, and the saved set-user-ID becomes the effective one), or
# CapsCapabilityDumb (EPERM)
def Caps.execve(+k: C.CapsKernel, +c: C.CapCred, +f: C.CapFile, +ign: Bool) -> Result<&2, &2, C.CapsError, C.CapCred>:
  +s = Caps.execve.sets(k, c, f, ign)
  CapExec.fin(CapExec.dumb_ok(CapExec.file_caps(k, f, ign), C.CapState.permitted(s)), c, CapExec.new_euid(c, f, ign), s)
