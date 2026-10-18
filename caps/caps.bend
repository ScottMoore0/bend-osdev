# bend-osdev-caps: Linux capability sets, as capabilities(7) documents them.
# This file: capability numbers, sets, and the thread's and file's sets.
# exec.bend: the transformation during execve(2). adjust.bend: capset(2) and
# the prctl(2) bounding-set and ambient operations.
#
# A capability set holds bit k for capability k, from CAP_CHOWN (0) to
# CAP_CHECKPOINT_RESTORE (40): bits 0 to 31 in a native U32, bits 32 to 40 in
# a Word(9n) (CapSetW, internal). The set operations work bit by bit; the
# width-n forms (CapBits) are what the laws are proved by induction on, for
# both parts.
#
# A thread has five sets (CapState): permitted, inheritable, effective,
# bounding and ambient. A file has a permitted and an inheritable set and an
# effective bit (CapFileSets). execve, capset, and the prctl(2) bounding-set
# and ambient operations are modelled on a credential (CapCred): the sets, the
# real, effective and saved user IDs, and the securebits SECBIT_NOROOT and
# SECBIT_NO_CAP_AMBIENT_RAISE.
import Base
import ../word64/word64.bend as W

# Capability numbers

def Cap.chown() -> U32:
  0

def Cap.dac_override() -> U32:
  1

def Cap.dac_read_search() -> U32:
  2

def Cap.fowner() -> U32:
  3

def Cap.fsetid() -> U32:
  4

def Cap.kill() -> U32:
  5

def Cap.setgid() -> U32:
  6

def Cap.setuid() -> U32:
  7

def Cap.setpcap() -> U32:
  8

def Cap.linux_immutable() -> U32:
  9

def Cap.net_bind_service() -> U32:
  10

def Cap.net_broadcast() -> U32:
  11

def Cap.net_admin() -> U32:
  12

def Cap.net_raw() -> U32:
  13

def Cap.ipc_lock() -> U32:
  14

def Cap.ipc_owner() -> U32:
  15

def Cap.sys_module() -> U32:
  16

def Cap.sys_rawio() -> U32:
  17

def Cap.sys_chroot() -> U32:
  18

def Cap.sys_ptrace() -> U32:
  19

def Cap.sys_pacct() -> U32:
  20

def Cap.sys_admin() -> U32:
  21

def Cap.sys_boot() -> U32:
  22

def Cap.sys_nice() -> U32:
  23

def Cap.sys_resource() -> U32:
  24

def Cap.sys_time() -> U32:
  25

def Cap.sys_tty_config() -> U32:
  26

def Cap.mknod() -> U32:
  27

def Cap.lease() -> U32:
  28

def Cap.audit_write() -> U32:
  29

def Cap.audit_control() -> U32:
  30

def Cap.setfcap() -> U32:
  31

def Cap.mac_override() -> U32:
  32

def Cap.mac_admin() -> U32:
  33

def Cap.syslog() -> U32:
  34

def Cap.wake_alarm() -> U32:
  35

def Cap.block_suspend() -> U32:
  36

def Cap.audit_read() -> U32:
  37

def Cap.perfmon() -> U32:
  38

def Cap.bpf() -> U32:
  39

def Cap.checkpoint_restore() -> U32:
  40
def Cap.count() -> U32:
  41

def Cap.names() -> List<&2, String>:
  ["CAP_CHOWN", "CAP_DAC_OVERRIDE", "CAP_DAC_READ_SEARCH", "CAP_FOWNER", "CAP_FSETID", "CAP_KILL", "CAP_SETGID", "CAP_SETUID", "CAP_SETPCAP", "CAP_LINUX_IMMUTABLE", "CAP_NET_BIND_SERVICE", "CAP_NET_BROADCAST", "CAP_NET_ADMIN", "CAP_NET_RAW", "CAP_IPC_LOCK", "CAP_IPC_OWNER", "CAP_SYS_MODULE", "CAP_SYS_RAWIO", "CAP_SYS_CHROOT", "CAP_SYS_PTRACE", "CAP_SYS_PACCT", "CAP_SYS_ADMIN", "CAP_SYS_BOOT", "CAP_SYS_NICE", "CAP_SYS_RESOURCE", "CAP_SYS_TIME", "CAP_SYS_TTY_CONFIG", "CAP_MKNOD", "CAP_LEASE", "CAP_AUDIT_WRITE", "CAP_AUDIT_CONTROL", "CAP_SETFCAP", "CAP_MAC_OVERRIDE", "CAP_MAC_ADMIN", "CAP_SYSLOG", "CAP_WAKE_ALARM", "CAP_BLOCK_SUSPEND", "CAP_AUDIT_READ", "CAP_PERFMON", "CAP_BPF", "CAP_CHECKPOINT_RESTORE"]

# whether k names a capability (0 to 40)
def Cap.valid(k: U32) -> Bool:
  U32.is_lt(k, 41)

def Cap.name.go(v: Bool, k: U32) -> Maybe<&2, String>:
  match v:
    case False{}:
      None{}
    case True{}:
      List.get(&2, String, Cap.names(), U32.to_nat(k))

# the name of capability k, such as "CAP_CHOWN"
def Cap.name(+k: U32) -> Maybe<&2, String>:
  Cap.name.go(Cap.valid(k), k)

def Cap.of_name.hit(hit: Bool, k: U32, rest: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      rest

def Cap.of_name.go(xs: List<&2, String>, +s: String, +k: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Cap.of_name.hit(String.eq(h, s), k, Cap.of_name.go(t, s, U32.add(k, 1)))

# the number of the capability named s
def Cap.of_name(s: String) -> Maybe<&2, U32>:
  Cap.of_name.go(Cap.names(), s, 0)

# Sets of capabilities, for every width n

# the set of every capability below n
def CapBits.all(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, CapBits.all(p)}

# one bit of a subset test: a bit in a must be in b; r is the rest
def CapBits.sub.bit(a: Bool, b: Bool, r: Bool) -> Bool:
  match a:
    case False{}:
      r
    case True{}:
      match b:
        case False{}:
          False{}
        case True{}:
          r

# every capability in a is in b
def CapBits.subset(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          CapBits.sub.bit(ah, bh, CapBits.subset(p, at, bt))

# the set holding capability k alone (empty if k >= n)
def CapBits.single(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{True{}, Word.zero(p)}
        case 1n+j:
          WCon{False{}, CapBits.single(p, j)}

# whether capability k is in s
def CapBits.has(n: Nat, s: Word(n), k: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match s k:
        case WCon{h, t} 0n:
          h
        case WCon{h, t} 1n+j:
          CapBits.has(p, t, j)

# the capabilities in s, in increasing order, numbered from k
def CapBits.to_list(n: Nat, s: Word(n), +k: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match s:
        case WCon{True{}, t}:
          Con{k, CapBits.to_list(p, t, U32.add(k, 1))}
        case WCon{False{}, t}:
          CapBits.to_list(p, t, U32.add(k, 1))

# Capability sets

# A set is two words: capabilities 0 to 31 are the bits of a native U32 (bit
# k is capability k), and capabilities 32 to 40 a Word(9n) (bit j is
# capability 32 + j). Ten machine words, where a Word(41n) cost forty-one
# (and a CapState of five of them was more than Bend's C backend compiles:
# bendlang/bend#1069). The high part is exactly nine bits, so every value of
# the type is a set of capabilities 0 to 40, with one representation each.
# Internal: use the CapSet defs.
type CapSetW is Data:
  CapSetW{lo: U32, hi: Word(9n)}

def CapSet() -> Data:
  CapSetW

def CapSet.empty() -> CapSet():
  CapSetW{0, Word.zero(9n)}

def CapSet.full() -> CapSet():
  CapSetW{4294967295, CapBits.all(9n)}

def CapSet.union(a: CapSet(), b: CapSet()) -> CapSet():
  match a b:
    case CapSetW{al, ah} CapSetW{bl, bh}:
      CapSetW{U32.or(al, bl), Word.or(9n, ah, bh)}

def CapSet.inter(a: CapSet(), b: CapSet()) -> CapSet():
  match a b:
    case CapSetW{al, ah} CapSetW{bl, bh}:
      CapSetW{U32.and(al, bl), Word.and(9n, ah, bh)}

# the capabilities of a not in b
def CapSet.minus(a: CapSet(), b: CapSet()) -> CapSet():
  match a b:
    case CapSetW{al, ah} CapSetW{bl, bh}:
      CapSetW{U32.and(al, U32.not(bl)), Word.and(9n, ah, Word.not(9n, bh))}

# a within b: no bit of a outside b (on the low word, a & ~b == 0)
def CapSet.subset(a: CapSet(), b: CapSet()) -> Bool:
  match a b:
    case CapSetW{al, ah} CapSetW{bl, bh}:
      Bool.and(U32.is_eq(U32.and(al, U32.not(bl)), 0), CapBits.subset(9n, ah, bh))

def CapSet.is_eq(a: CapSet(), b: CapSet()) -> Bool:
  match a b:
    case CapSetW{al, ah} CapSetW{bl, bh}:
      Bool.and(U32.is_eq(al, bl), Cmp.is_eq(Word.cmp(9n, ah, bh)))

def CapSetW.single.go(low: Bool, +k: U32) -> CapSet():
  match low:
    case True{}:
      CapSetW{U32.shln(1, U32.to_nat(k)), Word.zero(9n)}
    case False{}:
      CapSetW{0, CapBits.single(9n, U32.to_nat(U32.sub(k, 32)))}

# the set holding capability k alone (k is 0 to 40)
def CapSetW.single(+k: U32) -> CapSet():
  CapSetW.single.go(U32.is_lt(k, 32), k)

def CapSet.of.go(v: Bool, k: U32) -> CapSet():
  match v:
    case False{}:
      CapSet.empty()
    case True{}:
      CapSetW.single(k)

# the set holding capability k alone (empty if k is not a capability)
def CapSet.of(+k: U32) -> CapSet():
  CapSet.of.go(Cap.valid(k), k)

def CapSet.has.go(v: Bool, s: CapSet(), k: U32) -> Bool:
  match v:
    case False{}:
      False{}
    case True{}:
      CapSet.subset(CapSetW.single(k), s)

# whether capability k is in s
def CapSet.has(s: CapSet(), +k: U32) -> Bool:
  CapSet.has.go(Cap.valid(k), s, k)

def CapSet.add(s: CapSet(), k: U32) -> CapSet():
  CapSet.union(s, CapSet.of(k))

def CapSet.del(s: CapSet(), k: U32) -> CapSet():
  CapSet.minus(s, CapSet.of(k))

def CapSet.from_list(xs: List<&2, U32>) -> CapSet():
  match xs:
    case Nil{}:
      CapSet.empty()
    case Con{h, t}:
      CapSet.add(CapSet.from_list(t), h)

def CapSetW.push(b: Bool, k: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      Con{k, rest}
    case False{}:
      rest

# the capabilities among the low n bits of w, numbered from k, then rest
def CapSetW.lo_list(n: Nat, +w: U32, +k: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+p:
      CapSetW.push(U32.is_eq(U32.and(w, 1), 1), k, CapSetW.lo_list(p, U32.shr(w), U32.add(k, 1), rest))

def CapSet.to_list(s: CapSet()) -> List<&2, U32>:
  match s:
    case CapSetW{l, h}:
      CapSetW.lo_list(32n, l, 0, CapBits.to_list(9n, h, 32))

def CapSetW.bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# the value of the n bits of w, and the n low bits of a, as native words
def CapSetW.word_u32(n: Nat, w: Word(n)) -> U32:
  match n:
    case 0n:
      0
    case 1n+p:
      match w:
        case WCon{b, t}:
          U32.or(CapSetW.bit(b), U32.shl(CapSetW.word_u32(p, t)))

def CapSetW.u32_word(n: Nat, +a: U32) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{U32.is_eq(U32.and(a, 1), 1), CapSetW.u32_word(p, U32.shr(a))}

# the 64-bit mask of a set, as capget(2) and /proc/<pid>/status show it
def CapSet.to_w64(s: CapSet()) -> W.W64:
  match s:
    case CapSetW{l, h}:
      W.W64.from_parts(CapSetW.word_u32(9n, h), l)

# the set of the low 41 bits of a 64-bit mask
def CapSet.from_w64(+v: W.W64) -> CapSet():
  CapSetW{W.W64.lo(v), CapSetW.u32_word(9n, W.W64.hi(v))}

# 16 hex digits, as the CapEff line of /proc/<pid>/status
def CapSet.show(s: CapSet()) -> String:
  W.W64.show_hex(CapSet.to_w64(s))

# Thread and file capability sets

type CapState is Data:
  CapState{permitted: CapSet(), inheritable: CapSet(), effective: CapSet(), bounding: CapSet(), ambient: CapSet()}

def CapState.permitted(s: CapState) -> CapSet():
  match s:
    case CapState{p, i, e, b, a}:
      p

def CapState.inheritable(s: CapState) -> CapSet():
  match s:
    case CapState{p, i, e, b, a}:
      i

def CapState.effective(s: CapState) -> CapSet():
  match s:
    case CapState{p, i, e, b, a}:
      e

def CapState.bounding(s: CapState) -> CapSet():
  match s:
    case CapState{p, i, e, b, a}:
      b

def CapState.ambient(s: CapState) -> CapSet():
  match s:
    case CapState{p, i, e, b, a}:
      a

def CapState.with_bounding(s: CapState, b: CapSet()) -> CapState:
  match s:
    case CapState{p, i, e, x, a}:
      CapState{p, i, e, b, a}

def CapState.with_ambient(s: CapState, a: CapSet()) -> CapState:
  match s:
    case CapState{p, i, e, b, x}:
      CapState{p, i, e, b, a}

# capabilities(7)'s invariants: effective within permitted, and no capability
# ambient unless it is both permitted and inheritable
def CapState.valid(s: CapState) -> Bool:
  match s:
    case CapState{+p, +i, e, b, +a}:
      Bool.and(CapSet.subset(e, p), Bool.and(CapSet.subset(a, p), CapSet.subset(a, i)))

# A thread's credentials: real, effective and saved set-user-ID, the
# securebits SECBIT_NOROOT and SECBIT_NO_CAP_AMBIENT_RAISE, and the sets.
type CapCred is Data:
  CapCred{ruid: U32, euid: U32, suid: U32, noroot: Bool, no_ambient_raise: Bool, sets: CapState}

def CapCred.ruid(c: CapCred) -> U32:
  match c:
    case CapCred{r, e, s, nr, na, st}:
      r

def CapCred.euid(c: CapCred) -> U32:
  match c:
    case CapCred{r, e, s, nr, na, st}:
      e

def CapCred.suid(c: CapCred) -> U32:
  match c:
    case CapCred{r, e, s, nr, na, st}:
      s

def CapCred.no_ambient_raise(c: CapCred) -> Bool:
  match c:
    case CapCred{r, e, s, nr, na, st}:
      na

def CapCred.sets(c: CapCred) -> CapState:
  match c:
    case CapCred{r, e, s, nr, na, st}:
      st

def CapCred.with_sets(c: CapCred, st: CapState) -> CapCred:
  match c:
    case CapCred{r, e, s, nr, na, x}:
      CapCred{r, e, s, nr, na, st}

# A file's capabilities (the security.capability attribute)
type CapFileSets is Data:
  CapFileSets{permitted: CapSet(), inheritable: CapSet(), effective: Bool}

# An executable: its owner, its set-user-ID and set-group-ID bits, and its
# capabilities, if it has any
type CapFile is Data:
  CapFile{uid: U32, setuid: Bool, setgid: Bool, caps: Maybe<&2, CapFileSets>}

# The kernel's choices: the highest capability it supports
# (/proc/sys/kernel/cap_last_cap; at most 40 here) and whether file
# capabilities are on (off when booted with no_file_caps)
type CapsKernel is Data:
  CapsKernel{last_cap: U32, file_caps: Bool}

# Linux since 5.9: capabilities 0 to 40, file capabilities on
def CapsKernel.linux() -> CapsKernel:
  CapsKernel{40, True{}}

def CapsKernel.file_caps(k: CapsKernel) -> Bool:
  match k:
    case CapsKernel{l, f}:
      f

# whether c names a capability this kernel supports
def CapsKernel.valid(k: CapsKernel, +c: U32) -> Bool:
  match k:
    case CapsKernel{l, f}:
      Bool.and(Cap.valid(c), U32.is_le(c, l))

# Why a call fails
type CapsError is Data:
  CapsInvalidCap{}
  CapsPermittedGrows{}
  CapsEffectiveNotPermitted{}
  CapsInheritableNotBounded{}
  CapsInheritableNotPermitted{}
  CapsNoSetpcap{}
  CapsAmbientRaiseLocked{}
  CapsAmbientNotAllowed{}
  CapsCapabilityDumb{}

# the errno the kernel answers: EINVAL (22) for a capability it does not
# support, EPERM (1) otherwise
def CapsError.errno(e: CapsError) -> U32:
  match e:
    case CapsInvalidCap{}:
      22
    case CapsPermittedGrows{}:
      1
    case CapsEffectiveNotPermitted{}:
      1
    case CapsInheritableNotBounded{}:
      1
    case CapsInheritableNotPermitted{}:
      1
    case CapsNoSetpcap{}:
      1
    case CapsAmbientRaiseLocked{}:
      1
    case CapsAmbientNotAllowed{}:
      1
    case CapsCapabilityDumb{}:
      1

# the credentials after a call: the new ones, or c if it failed
def Caps.or(r: Result<&2, &2, CapsError, CapCred>, c: CapCred) -> CapCred:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      c

# the sets after a call, or s if it failed
def Caps.sets_or(r: Result<&2, &2, CapsError, CapCred>, s: CapState) -> CapState:
  match r:
    case Done{x}:
      CapCred.sets(x)
    case Fail{e}:
      s
