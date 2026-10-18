# bend-osdev-landlock: renaming and linking (landlock(7), FS_REFER).
#
# Within one directory, a rename needs the REMOVE_* right for the file's type
# on the directory and the MAKE_* right for it there too; a link needs the
# MAKE_* right. Across directories (reparenting), landlock(7) adds:
#
#   * REFER on the source and the destination directories;
#   * "The reparented file may not gain more access rights in the destination
#     directory than it previously had in the source directory" (EXDEV);
#   * the MAKE_* right on the destination and, for a rename, the REMOVE_*
#     right on the source (EACCES);
#   * "If multiple requirements are not met, the EACCES error code takes
#     precedence over EXDEV."
#
# What landlock(7) leaves open, settled by experiment on Linux 6.6 (ABI 3):
# a missing REFER is EXDEV; the rights compared for "gain" are, for a
# directory, every handled right, and for any other file only the rights a
# file can receive (EXECUTE, WRITE_FILE, READ_FILE, TRUNCATE, IOCTL_DEV: a
# regular file moved where MAKE_DIR or READ_DIR is granted gains nothing);
# the comparison is made in each layer, on the rights each layer grants on
# the two directories; and EACCES takes precedence across layers too.
import Base
import ./path.bend as P
import ./rights.bend as R
import ./ruleset.bend as RS
import ./domain.bend as D

type LandlockDecision is Data:
  LandlockAllowed{}
  # EACCES
  LandlockDeniedAccess{}
  # EXDEV: a reparenting refused
  LandlockDeniedReparent{}
  # EPERM: refused by IPC scoping
  LandlockDeniedScope{}

def LandlockDecision.is_allowed(d: LandlockDecision) -> Bool:
  match d:
    case LandlockAllowed{}:
      True{}
    case _:
      False{}

# the errno a refused system call sets
def LandlockDecision.show(d: LandlockDecision) -> String:
  match d:
    case LandlockAllowed{}:
      "OK"
    case LandlockDeniedAccess{}:
      "EACCES"
    case LandlockDeniedReparent{}:
      "EXDEV"
    case LandlockDeniedScope{}:
      "EPERM"

def LandlockDecision.of_bool(ok: Bool, deny: LandlockDecision) -> LandlockDecision:
  match ok:
    case True{}:
      LandlockAllowed{}
    case False{}:
      deny

# two layers' answers together: EACCES before EXDEV before allowed
def LandlockDecision.worse(a: LandlockDecision, b: LandlockDecision) -> LandlockDecision:
  match a:
    case LandlockAllowed{}:
      b
    case LandlockDeniedAccess{}:
      LandlockDeniedAccess{}
    case LandlockDeniedReparent{}:
      match b:
        case LandlockDeniedAccess{}:
          LandlockDeniedAccess{}
        case LandlockDeniedScope{}:
          LandlockDeniedScope{}
        case _:
          LandlockDeniedReparent{}
    case LandlockDeniedScope{}:
      LandlockDeniedScope{}

# One layer

def LandlockRefer.decide(access: Bool, reparent: Bool) -> LandlockDecision:
  match access:
    case False{}:
      LandlockDeniedAccess{}
    case True{}:
      LandlockDecision.of_bool(reparent, LandlockDeniedReparent{})

# the file gains nothing: what the layer grants on dst, of the rights a file
# of this kind carries, it grants on src
def LandlockRefer.no_gain(+rs: RS.LandlockRuleset, src: P.LandlockPath, dst: P.LandlockPath, k: R.LandlockFileKind) -> Bool:
  R.LandlockFs.subset(R.LandlockFs.inter(RS.LandlockRuleset.granted(rs, dst), R.LandlockFileKind.carried(k)), RS.LandlockRuleset.granted(rs, src))

# REFER on both directories, and no gain
def LandlockRefer.reparent_ok(+rs: RS.LandlockRuleset, +src: P.LandlockPath, +dst: P.LandlockPath, k: R.LandlockFileKind) -> Bool:
  Bool.and(RS.LandlockRuleset.allows(rs, src, R.LandlockRefer{}), Bool.and(RS.LandlockRuleset.allows(rs, dst, R.LandlockRefer{}), LandlockRefer.no_gain(rs, src, dst, k)))

# one layer's answer to moving (rename: remove is True) or linking a file of
# kind k from directory src to directory dst; same: src and dst are one
# directory
def LandlockRefer.layer(+rs: RS.LandlockRuleset, +src: P.LandlockPath, +dst: P.LandlockPath, +k: R.LandlockFileKind, same: Bool, remove: Bool) -> LandlockDecision:
  LandlockRefer.decide(Bool.and(R.LandlockBits.imp(remove, RS.LandlockRuleset.allows(rs, src, R.LandlockFileKind.remove_right(k))), RS.LandlockRuleset.allows(rs, dst, R.LandlockFileKind.make_right(k))), Bool.or(same, LandlockRefer.reparent_ok(rs, src, dst, k)))

# The domain: every layer's answer, the worst of them

def LandlockRefer.go(ls: List<&2, D.LandlockLayer>, +src: P.LandlockPath, +dst: P.LandlockPath, +k: R.LandlockFileKind, +same: Bool, +remove: Bool) -> LandlockDecision:
  match ls:
    case Nil{}:
      LandlockAllowed{}
    case Con{D.LandlockLayer{id, rs}, t}:
      LandlockDecision.worse(LandlockRefer.layer(rs, src, dst, k, same, remove), LandlockRefer.go(t, src, dst, k, same, remove))

# rename(2) of a file of kind k from directory src to directory dst (to a
# name not in use there)
def LandlockRefer.rename(d: D.LandlockDomain, +src: P.LandlockPath, +dst: P.LandlockPath, k: R.LandlockFileKind) -> LandlockDecision:
  LandlockRefer.go(D.LandlockDomain.layers(d), src, dst, k, P.LandlockPath.is_eq(src, dst), True{})

# link(2) of a file of kind k in directory src into directory dst
def LandlockRefer.link(d: D.LandlockDomain, +src: P.LandlockPath, +dst: P.LandlockPath, k: R.LandlockFileKind) -> LandlockDecision:
  LandlockRefer.go(D.LandlockDomain.layers(d), src, dst, k, P.LandlockPath.is_eq(src, dst), False{})
