# bend-osdev-landlock: the errors the Landlock system calls answer, one
# constructor per documented failure, with the errno each one is.
import Base

type LandlockError is Data:
  # Landlock is not available (ABI version 0: an old kernel, or Landlock
  # disabled at boot): EOPNOTSUPP
  LandlockNotSupported{}
  # a right, or a mask bit, the ABI does not know: EINVAL
  LandlockUnknownAccess{}
  # landlock_create_ruleset with nothing handled: ENOMSG
  LandlockEmptyRuleset{}
  # landlock_add_rule with no allowed right: ENOMSG
  LandlockEmptyRule{}
  # a rule allows a right its ruleset does not handle: EINVAL
  LandlockRuleNotHandled{}
  # a path-beneath rule on a file (not a directory) allows a directory right: EINVAL
  LandlockDirRightOnFile{}
  # a net-port rule's port is above 65535: EINVAL
  LandlockBadPort{}
  # landlock_restrict_self with the layer limit reached: E2BIG
  LandlockTooManyLayers{}
  # landlock_restrict_self without no_new_privs or CAP_SYS_ADMIN: EPERM
  LandlockNoNewPrivs{}

def LandlockError.name(e: LandlockError) -> String:
  match e:
    case LandlockNotSupported{}:
      "LandlockNotSupported"
    case LandlockUnknownAccess{}:
      "LandlockUnknownAccess"
    case LandlockEmptyRuleset{}:
      "LandlockEmptyRuleset"
    case LandlockEmptyRule{}:
      "LandlockEmptyRule"
    case LandlockRuleNotHandled{}:
      "LandlockRuleNotHandled"
    case LandlockDirRightOnFile{}:
      "LandlockDirRightOnFile"
    case LandlockBadPort{}:
      "LandlockBadPort"
    case LandlockTooManyLayers{}:
      "LandlockTooManyLayers"
    case LandlockNoNewPrivs{}:
      "LandlockNoNewPrivs"

# the errno name the system call sets
def LandlockError.errno(e: LandlockError) -> String:
  match e:
    case LandlockNotSupported{}:
      "EOPNOTSUPP"
    case LandlockUnknownAccess{}:
      "EINVAL"
    case LandlockEmptyRuleset{}:
      "ENOMSG"
    case LandlockEmptyRule{}:
      "ENOMSG"
    case LandlockRuleNotHandled{}:
      "EINVAL"
    case LandlockDirRightOnFile{}:
      "EINVAL"
    case LandlockBadPort{}:
      "EINVAL"
    case LandlockTooManyLayers{}:
      "E2BIG"
    case LandlockNoNewPrivs{}:
      "EPERM"
