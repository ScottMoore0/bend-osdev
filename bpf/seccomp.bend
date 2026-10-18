# bend-osdev-bpf: seccomp filters (the seccomp(2) manual page).
#
# A seccomp filter is a classic BPF program run over struct seccomp_data:
#   int nr; __u32 arch; __u64 instruction_pointer; __u64 args[6];
# 64 bytes, in the host's byte order, which is also the order of the
# filter's loads (little-endian on x86-64 and arm64). Its answer is a
# SECCOMP_RET_* value: the action in the high 16 bits, data in the low 16.
# With several filters installed, every one runs, the most recently
# installed first, and the answer is the first-seen action of the highest
# precedence, with its data: KILL_PROCESS, KILL_THREAD, TRAP, ERRNO,
# USER_NOTIF, TRACE, LOG, ALLOW, in decreasing order. An action value the
# manual page does not name is treated as KILL_PROCESS.
#
# A seccomp filter loads only 32-bit words at aligned offsets inside
# seccomp_data (BPF_LD | BPF_W | BPF_ABS), and Linux refuses BPF_MOD in a
# seccomp filter (observed on the running kernel: the manual page does not
# list the instructions); seccomp_validate adds those rules to
# bpf_validate's. BPF_LEN loads give 64, the size of seccomp_data.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./insn.bend as I
import ./validate.bend as V
import ./bpf.bend as R

# The input

type SeccompData is Data:
  SeccompData{nr: U32, arch: U32, ip: W.W64, a0: W.W64, a1: W.W64, a2: W.W64, a3: W.W64, a4: W.W64, a5: W.W64}

def SeccompData.field32(order: I.BpfOrder, v: U32) -> B.Octets:
  match order:
    case I.BpfLittle{}:
      B.Octets.le32(v)
    case I.BpfBig{}:
      B.Octets.be32(v)

def SeccompData.field64(order: I.BpfOrder, v: W.W64) -> B.Octets:
  match order:
    case I.BpfLittle{}:
      B.Octets.le64(v)
    case I.BpfBig{}:
      B.Octets.be64(v)

# the 64 bytes of struct seccomp_data, in the given byte order
def SeccompData.to_octets(+order: I.BpfOrder, d: SeccompData) -> B.Octets:
  match d:
    case SeccompData{nr, arch, ip, a0, a1, a2, a3, a4, a5}:
      B.Octets.concat([SeccompData.field32(order, nr), SeccompData.field32(order, arch), SeccompData.field64(order, ip), SeccompData.field64(order, a0), SeccompData.field64(order, a1), SeccompData.field64(order, a2), SeccompData.field64(order, a3), SeccompData.field64(order, a4), SeccompData.field64(order, a5)])

def SeccompData.input(+order: I.BpfOrder, d: SeccompData) -> R.BpfInput:
  R.BpfInput{order, SeccompData.to_octets(order, d)}

# the byte order of x86-64 and arm64, the usual hosts
def seccomp_order() -> I.BpfOrder:
  I.BpfLittle{}

def seccomp_data_size() -> U32:
  64

# AUDIT_ARCH_* values for seccomp_data.arch, and the x32 system call bit
def seccomp_arch_x86_64() -> U32:
  3221225534

def seccomp_arch_i386() -> U32:
  1073741827

def seccomp_arch_aarch64() -> U32:
  3221225655

def seccomp_x32_syscall_bit() -> U32:
  1073741824

# Actions

type SeccompAction is Data:
  SeccompKillProcess{}
  SeccompKillThread{}
  SeccompTrap{data: U32}
  SeccompErrno{data: U32}
  SeccompUserNotif{}
  SeccompTrace{data: U32}
  SeccompLog{}
  SeccompAllow{}

def SeccompAction.pick(hit: Bool, a: SeccompAction, rest: SeccompAction) -> SeccompAction:
  match hit:
    case True{}:
      a
    case False{}:
      rest

# the action of a SECCOMP_RET_* value: SECCOMP_RET_ACTION_FULL (0xffff0000)
# selects the action, SECCOMP_RET_DATA (0xffff) the data
def SeccompAction.of_u32(+v: U32) -> SeccompAction:
  +act = U32.and(4294901760, v)
  +d = U32.and(65535, v)
  SeccompAction.pick(U32.is_eq(act, 2147483648), SeccompKillProcess{},
    SeccompAction.pick(U32.is_eq(act, 0), SeccompKillThread{},
    SeccompAction.pick(U32.is_eq(act, 196608), SeccompTrap{d},
    SeccompAction.pick(U32.is_eq(act, 327680), SeccompErrno{d},
    SeccompAction.pick(U32.is_eq(act, 2143289344), SeccompUserNotif{},
    SeccompAction.pick(U32.is_eq(act, 2146435072), SeccompTrace{d},
    SeccompAction.pick(U32.is_eq(act, 2147221504), SeccompLog{},
    SeccompAction.pick(U32.is_eq(act, 2147418112), SeccompAllow{},
    SeccompKillProcess{}))))))))

# the SECCOMP_RET_* value of an action, with the low 16 bits of its data
def SeccompAction.to_u32(a: SeccompAction) -> U32:
  match a:
    case SeccompKillProcess{}:
      2147483648
    case SeccompKillThread{}:
      0
    case SeccompTrap{d}:
      U32.or(196608, U32.and(65535, d))
    case SeccompErrno{d}:
      U32.or(327680, U32.and(65535, d))
    case SeccompUserNotif{}:
      2143289344
    case SeccompTrace{d}:
      U32.or(2146435072, U32.and(65535, d))
    case SeccompLog{}:
      2147221504
    case SeccompAllow{}:
      2147418112

# the same action with its data cut to the 16 bits a return value holds
def SeccompAction.clip(a: SeccompAction) -> SeccompAction:
  match a:
    case SeccompTrap{d}:
      SeccompTrap{U32.and(65535, d)}
    case SeccompErrno{d}:
      SeccompErrno{U32.and(65535, d)}
    case SeccompTrace{d}:
      SeccompTrace{U32.and(65535, d)}
    case other:
      other

# the precedence: 0 for KILL_PROCESS, the most restrictive, to 7 for ALLOW
def SeccompAction.rank(a: SeccompAction) -> Nat:
  match a:
    case SeccompKillProcess{}:
      0n
    case SeccompKillThread{}:
      1n
    case SeccompTrap{d}:
      2n
    case SeccompErrno{d}:
      3n
    case SeccompUserNotif{}:
      4n
    case SeccompTrace{d}:
      5n
    case SeccompLog{}:
      6n
    case SeccompAllow{}:
      7n

def SeccompAction.show(a: SeccompAction) -> String:
  match a:
    case SeccompKillProcess{}:
      "KILL_PROCESS"
    case SeccompKillThread{}:
      "KILL_THREAD"
    case SeccompTrap{d}:
      "TRAP(" ++ U32.show(d) ++ ")"
    case SeccompErrno{d}:
      "ERRNO(" ++ U32.show(d) ++ ")"
    case SeccompUserNotif{}:
      "USER_NOTIF"
    case SeccompTrace{d}:
      "TRACE(" ++ U32.show(d) ++ ")"
    case SeccompLog{}:
      "LOG"
    case SeccompAllow{}:
      "ALLOW"

def seccomp_combine.pick(newer_wins: Bool, newer: SeccompAction, older: SeccompAction) -> SeccompAction:
  match newer_wins:
    case True{}:
      newer
    case False{}:
      older

# the answer of two filters, given each one's: the higher precedence, and on
# a tie the newer filter's action (with its data)
def seccomp_combine(+newer: SeccompAction, +older: SeccompAction) -> SeccompAction:
  seccomp_combine.pick(Nat.is_le(SeccompAction.rank(newer), SeccompAction.rank(older)), newer, older)

# Validation

def seccomp_check.word(+k: U32, +pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  V.bpf_chk(Bool.and(U32.is_eq(U32.and(k, 3), 0), U32.is_lt(k, seccomp_data_size())), I.BpfErrSeccompLoad{pc})

def seccomp_check.abs(size: I.BpfSize, +k: U32, +pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match size:
    case I.BpfW{}:
      seccomp_check.word(k, pc)
    case other:
      Fail{I.BpfErrSeccompLoad{pc}}

def seccomp_check.alu(o: I.BpfAluOp, pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match o:
    case I.BpfMod{}:
      Fail{I.BpfErrSeccompInsn{pc}}
    case other:
      Done{Unit{}}

def seccomp_check.op(op: I.BpfOp, +pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match op:
    case I.BpfLdAbs{size, k}:
      seccomp_check.abs(size, k, pc)
    case I.BpfLdInd{size, k}:
      Fail{I.BpfErrSeccompLoad{pc}}
    case I.BpfLdxMsh{k}:
      Fail{I.BpfErrSeccompLoad{pc}}
    case I.BpfAlu{o, src}:
      seccomp_check.alu(o, pc)
    case other:
      Done{Unit{}}

# ok is the verdict so far; the loop stops at the instruction after a failure
def seccomp_check.go(xs: List<&2, I.BpfOp>, +pc: Nat, ok: Result<&2, &2, I.BpfError, Unit>) -> Result<&2, &2, I.BpfError, Unit>:
  match xs:
    case Nil{}:
      ok
    case Con{op, t}:
      match ok:
        case Fail{e}:
          Fail{e}
        case Done{u}:
          seccomp_check.go(t, 1n+pc, seccomp_check.op(op, pc))

def seccomp_validate.go(v: Result<&2, &2, I.BpfError, Unit>, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      seccomp_check.go(prog, 0n, Done{Unit{}})

# bpf_validate's rules, only aligned 32-bit loads inside seccomp_data, and
# no BPF_MOD (checked once bpf_validate's rules hold)
def seccomp_validate_with(opts: V.BpfValidateOptions, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  seccomp_validate.go(V.bpf_validate_with(opts, prog), prog)

# the default options (what Linux checks), with this instruction limit
def seccomp_validate(limit: Nat, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  seccomp_validate_with(V.BpfValidateOptions{limit, True{}}, prog)

# Running

def seccomp_run.fin(r: Result<&2, &2, I.BpfError, U32>) -> Result<&2, &2, I.BpfError, SeccompAction>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{SeccompAction.of_u32(v)}

# one filter's action for a system call
def seccomp_run(+order: I.BpfOrder, prog: List<&2, I.BpfOp>, d: SeccompData) -> Result<&2, &2, I.BpfError, SeccompAction>:
  seccomp_run.fin(R.bpf_run(SeccompData.input(order, d), prog))

def seccomp_eval.join(r: Result<&2, &2, I.BpfError, SeccompAction>, s: Result<&2, &2, I.BpfError, SeccompAction>) -> Result<&2, &2, I.BpfError, SeccompAction>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      match s:
        case Fail{e}:
          Fail{e}
        case Done{b}:
          Done{seccomp_combine(a, b)}

# the action of a stack of filters, the most recently installed first; with
# no filter, ALLOW
def seccomp_eval(stack: List<&2, List<&2, I.BpfOp>>, +order: I.BpfOrder, +d: SeccompData) -> Result<&2, &2, I.BpfError, SeccompAction>:
  match stack:
    case Nil{}:
      Done{SeccompAllow{}}
    case Con{f, rest}:
      seccomp_eval.join(seccomp_run(order, f, d), seccomp_eval(rest, order, d))

# Installing

# the limits on one filter (BPF_MAXINSNS) and on all the filters of a
# thread together (MAX_INSNS_PER_PATH), where each filter already installed
# counts 4 instructions more than its length
type SeccompLimits is Data:
  SeccompLimits{filter: Nat, path: Nat}

def seccomp_limits() -> SeccompLimits:
  SeccompLimits{V.bpf_maxinsns(), 32768n}

def seccomp_path_len(stack: List<&2, List<&2, I.BpfOp>>) -> Nat:
  match stack:
    case Nil{}:
      0n
    case Con{f, rest}:
      Nat.add(Nat.add(V.bpf_count(f), 4n), seccomp_path_len(rest))

def seccomp_install.fit(fits: Bool, total: Nat, ops: List<&2, I.BpfOp>, stack: List<&2, List<&2, I.BpfOp>>) -> Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>:
  match fits:
    case True{}:
      Done{Con{ops, stack}}
    case False{}:
      Fail{I.BpfErrPathTooLong{total}}

def seccomp_install.ok(v: Result<&2, &2, I.BpfError, Unit>, path: Nat, +ops: List<&2, I.BpfOp>, +stack: List<&2, List<&2, I.BpfOp>>) -> Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      +total = Nat.add(V.bpf_count(ops), seccomp_path_len(stack))
      seccomp_install.fit(Nat.is_le(total, path), total, ops, stack)

def seccomp_install.go(lim: SeccompLimits, d: Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>, stack: List<&2, List<&2, I.BpfOp>>) -> Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>:
  match lim:
    case SeccompLimits{filter, path}:
      match d:
        case Fail{e}:
          Fail{e}
        case Done{+ops}:
          seccomp_install.ok(seccomp_validate(filter, ops), path, ops, stack)

# decode a stored filter, validate it for seccomp, and put it on top of the
# stack, as SECCOMP_SET_MODE_FILTER does
def seccomp_install(lim: SeccompLimits, stack: List<&2, List<&2, I.BpfOp>>, rs: List<&2, I.BpfRaw>) -> Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>:
  seccomp_install.go(lim, I.bpf_decode(rs), stack)
