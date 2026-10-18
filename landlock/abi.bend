# bend-osdev-landlock: the Landlock ABI versions and the rights each knows
# (landlock(7), VERSIONS; the kernel's userspace-api/landlock document):
#
#   1  Linux 5.13  the thirteen filesystem rights EXECUTE ... MAKE_SYM
#   2  Linux 5.19  FS_REFER
#   3  Linux 6.2   FS_TRUNCATE
#   4  Linux 6.7   NET_BIND_TCP, NET_CONNECT_TCP (and net-port rules)
#   5  Linux 6.10  FS_IOCTL_DEV
#   6  Linux 6.12  SCOPE_ABSTRACT_UNIX_SOCKET, SCOPE_SIGNAL
#
# Version 0 stands for no Landlock (landlock_create_ruleset with the version
# flag fails). A version knows every right introduced at or before it, so a
# later version knows everything an earlier one does.
#
# What to do with a right the ABI lacks is the caller's choice
# (LandlockCompat): refuse the request, as the kernel does (EINVAL), or drop
# the right, the best-effort approach landlock(7) recommends.
import Base
import ./rights.bend as R
import ./net.bend as N
import ./scope.bend as S

type LandlockCompat is Data:
  # drop what the ABI lacks (the default)
  LandlockBestEffort{}
  # refuse it, as the kernel does
  LandlockStrict{}

# the newest version this package knows
def LandlockAbi.latest() -> Nat:
  6n

# The version each right first appears in

def LandlockAbi.fs_since(r: R.LandlockFsRight) -> Nat:
  match r:
    case R.LandlockRefer{}:
      2n
    case R.LandlockTruncate{}:
      3n
    case R.LandlockIoctlDev{}:
      5n
    case _:
      1n

def LandlockAbi.net_since(r: N.LandlockNetRight) -> Nat:
  4n

def LandlockAbi.scope_since(r: S.LandlockScopeRight) -> Nat:
  6n

def LandlockAbi.knows_fs(+v: Nat, r: R.LandlockFsRight) -> Bool:
  Nat.is_le(LandlockAbi.fs_since(r), v)

def LandlockAbi.knows_net(+v: Nat, r: N.LandlockNetRight) -> Bool:
  Nat.is_le(LandlockAbi.net_since(r), v)

def LandlockAbi.knows_scope(+v: Nat, r: S.LandlockScopeRight) -> Bool:
  Nat.is_le(LandlockAbi.scope_since(r), v)

# The sets each version knows

def LandlockAbi.fs(+v: Nat) -> R.LandlockFs:
  +one = Nat.is_le(1n, v)
  R.LandlockFs{one, one, one, one, one, one, one, one, one, one, one, one, one, Nat.is_le(2n, v), Nat.is_le(3n, v), Nat.is_le(5n, v)}

def LandlockAbi.net(+v: Nat) -> N.LandlockNet:
  +four = Nat.is_le(4n, v)
  N.LandlockNet{four, four}

def LandlockAbi.scope(+v: Nat) -> S.LandlockScope:
  +six = Nat.is_le(6n, v)
  S.LandlockScope{six, six}

# net-port rules exist from version 4
def LandlockAbi.has_net_rules(v: Nat) -> Bool:
  Nat.is_le(4n, v)

# Best effort: the part of a request this version knows

def LandlockAbi.clip_fs(+v: Nat, s: R.LandlockFs) -> R.LandlockFs:
  R.LandlockFs.inter(s, LandlockAbi.fs(v))

def LandlockAbi.clip_net(+v: Nat, s: N.LandlockNet) -> N.LandlockNet:
  N.LandlockNet.inter(s, LandlockAbi.net(v))

def LandlockAbi.clip_scope(+v: Nat, s: S.LandlockScope) -> S.LandlockScope:
  S.LandlockScope.inter(s, LandlockAbi.scope(v))
