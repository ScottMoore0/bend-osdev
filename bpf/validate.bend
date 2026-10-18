# bend-osdev-bpf: validating a classic BPF program before it runs.
#
# The rules of the BSD bpf(4) manual page and McCanne and Jacobson (1993):
#   * the program is not empty, and has at most limit instructions
#     (BPF_MAXINSNS, 4096, by default);
#   * every jump lands on an instruction of the program (jumps only move
#     forward: their offsets are unsigned), and a conditional jump's offsets
#     fit their 8-bit fields;
#   * no instruction but a return or a jump can be the last, so the program
#     ends in a return;
#   * scratch memory indices are below BPF_MEMWORDS (16);
#   * no division or modulo by a constant zero;
#   * optionally (BpfValidateOptions.require_mem_init, on by default, as
#     Linux checks socket filters and seccomp filters alike): a scratch slot
#     is read only after every path from the start to the read has written
#     it, where the instruction after a return counts as reached from the
#     return (as Linux counts it: observed on the running kernel).
# The opcodes themselves are checked when a program is decoded
# (bpf_decode); bpf_prepare decodes and validates in one step.
import Base
import ./insn.bend as I

# BPF_MAXINSNS: the usual instruction limit
def bpf_maxinsns() -> Nat:
  4096n

# the choices validation offers: the instruction limit, and whether every
# scratch read must follow a write on every path
type BpfValidateOptions is Data:
  BpfValidateOptions{max_insns: Nat, require_mem_init: Bool}

# what Linux checks: at most 4096 instructions, scratch written before read
def BpfValidateOptions.default() -> BpfValidateOptions:
  BpfValidateOptions{bpf_maxinsns(), True{}}

# the rules of bpf(4) alone: scratch memory may be read before it is written
def BpfValidateOptions.permissive() -> BpfValidateOptions:
  BpfValidateOptions{bpf_maxinsns(), False{}}

def bpf_chk(ok: Bool, e: I.BpfError) -> Result<&2, &2, I.BpfError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def bpf_both(r: Result<&2, &2, I.BpfError, Unit>, s: Result<&2, &2, I.BpfError, Unit>) -> Result<&2, &2, I.BpfError, Unit>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      s

# an instruction that goes on to the next one must not be the last
def bpf_check.next(pc: Nat, r: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  bpf_chk(Nat.is_lt(0n, r), I.BpfErrNoReturn{pc})

def bpf_check.k_div(src: I.BpfSrc, pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match src:
    case I.BpfK{k}:
      bpf_chk(Bool.not(U32.is_zero(k)), I.BpfErrDivZero{pc})
    case I.BpfX{}:
      Done{Unit{}}

def bpf_check.div(o: I.BpfAluOp, src: I.BpfSrc, pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match o:
    case I.BpfDiv{}:
      bpf_check.k_div(src, pc)
    case I.BpfMod{}:
      bpf_check.k_div(src, pc)
    case other:
      Done{Unit{}}

def bpf_check.mem(+k: U32, +pc: Nat, r: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  bpf_both(bpf_chk(U32.is_lt(k, I.bpf_memwords()), I.BpfErrScratch{pc}), bpf_check.next(pc, r))

def bpf_check.jmp(+jt: U32, +jf: U32, +pc: Nat, +r: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  bpf_both(bpf_chk(U32.is_lt(jt, 256), I.BpfErrJumpField{pc}), bpf_both(bpf_chk(U32.is_lt(jf, 256), I.BpfErrJumpField{pc}), bpf_both(bpf_chk(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}), bpf_chk(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc}))))

# the checks of one instruction at index pc, with r instructions after it
def bpf_check.op(op: I.BpfOp, +pc: Nat, +r: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match op:
    case I.BpfLdMem{k}:
      bpf_check.mem(k, pc, r)
    case I.BpfLdxMem{k}:
      bpf_check.mem(k, pc, r)
    case I.BpfSt{k}:
      bpf_check.mem(k, pc, r)
    case I.BpfStx{k}:
      bpf_check.mem(k, pc, r)
    case I.BpfAlu{o, src}:
      bpf_both(bpf_check.div(o, src, pc), bpf_check.next(pc, r))
    case I.BpfJa{k}:
      bpf_chk(Nat.is_lt(U32.to_nat(k), r), I.BpfErrJump{pc})
    case I.BpfJmp{c, src, jt, jf}:
      bpf_check.jmp(jt, jf, pc, r)
    case I.BpfRet{v}:
      Done{Unit{}}
    case other:
      bpf_check.next(pc, r)

# the instructions' own checks, structurally: the reference the proofs
# reason about (PROOF.bend: F_check ties bpf_check.go to it)
def bpf_check.all(xs: List<&2, I.BpfOp>, +pc: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match xs:
    case Nil{}:
      Done{Unit{}}
    case Con{op, +t}:
      bpf_both(bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), bpf_check.all(t, 1n+pc))

# the same as a tail call: ok is the verdict so far, and n counts the
# instructions from pc on; the loop stops at the instruction after a failure
def bpf_check.go(xs: List<&2, I.BpfOp>, +pc: Nat, ok: Result<&2, &2, I.BpfError, Unit>, n: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  match xs:
    case Nil{}:
      ok
    case Con{op, t}:
      match ok:
        case Fail{e}:
          Fail{e}
        case Done{u}:
          match n:
            case 0n:
              bpf_check.go(t, 1n+pc, bpf_check.op(op, pc, 0n), 0n)
            case 1n+(+r):
              bpf_check.go(t, 1n+pc, bpf_check.op(op, pc, r), r)

# the number of instructions, as a tail call (PROOF.bend: F_count)
def bpf_count.go(xs: List<&2, I.BpfOp>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      bpf_count.go(t, 1n+n)

def bpf_count(xs: List<&2, I.BpfOp>) -> Nat:
  bpf_count.go(xs, 0n)

def bpf_check.len(+n: Nat, limit: Nat) -> Result<&2, &2, I.BpfError, Unit>:
  bpf_both(bpf_chk(Nat.is_lt(0n, n), I.BpfErrEmpty{}), bpf_chk(Nat.is_le(n, limit), I.BpfErrTooLong{n}))

# Scratch memory written before it is read. One pass over the instructions
# keeps, for each instruction still ahead, the slots written on every jump to
# it so far (a 16-bit mask, 65535 while no jump reaches it), and the slots
# written on the path falling into the next one.

def bpf_mem.bit.go(small: Bool, k: U32) -> U32:
  match small:
    case True{}:
      U32.shln(1, U32.to_nat(k))
    case False{}:
      0

def bpf_mem.bit(+k: U32) -> U32:
  bpf_mem.bit.go(U32.is_lt(k, I.bpf_memwords()), k)

# meet the n-th mask ahead with m (acc: the masks before it, last first)
def bpf_mem.meet.go(ahead: List<&2, U32>, n: Nat, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ahead:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{h, t}:
      match n:
        case 0n:
          List.reverse.go(&2, U32, acc, Con{U32.and(h, m), t})
        case 1n+p:
          bpf_mem.meet.go(t, p, m, Con{h, acc})

def bpf_mem.meet(ahead: List<&2, U32>, n: Nat, +m: U32) -> List<&2, U32>:
  bpf_mem.meet.go(ahead, n, m, Nil{})

type BpfInitStep is Data:
  BpfInitStep{ok: Result<&2, &2, I.BpfError, Unit>, fall: U32, ahead: List<&2, U32>}

def bpf_mem.read(+pc: Nat, +now: U32, +k: U32, ahead: List<&2, U32>) -> BpfInitStep:
  BpfInitStep{bpf_chk(Bool.not(U32.is_zero(U32.and(now, bpf_mem.bit(k)))), I.BpfErrMemInit{pc}), now, ahead}

# one instruction, given the slots written on every path to it
def bpf_mem.step(op: I.BpfOp, +pc: Nat, +now: U32, ahead: List<&2, U32>) -> BpfInitStep:
  match op:
    case I.BpfLdMem{k}:
      bpf_mem.read(pc, now, k, ahead)
    case I.BpfLdxMem{k}:
      bpf_mem.read(pc, now, k, ahead)
    case I.BpfSt{k}:
      BpfInitStep{Done{Unit{}}, U32.or(now, bpf_mem.bit(k)), ahead}
    case I.BpfStx{k}:
      BpfInitStep{Done{Unit{}}, U32.or(now, bpf_mem.bit(k)), ahead}
    case I.BpfJa{k}:
      BpfInitStep{Done{Unit{}}, 65535, bpf_mem.meet(ahead, U32.to_nat(k), now)}
    case I.BpfJmp{c, src, jt, jf}:
      BpfInitStep{Done{Unit{}}, 65535, bpf_mem.meet(bpf_mem.meet(ahead, U32.to_nat(jt), now), U32.to_nat(jf), now)}
    case other:
      BpfInitStep{Done{Unit{}}, now, ahead}

def bpf_mem.head(ahead: List<&2, U32>) -> U32:
  match ahead:
    case Nil{}:
      65535
    case Con{h, t}:
      h

def bpf_mem.tail(ahead: List<&2, U32>) -> List<&2, U32>:
  match ahead:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def bpf_mem.go(xs: List<&2, I.BpfOp>, +pc: Nat, st: BpfInitStep) -> Result<&2, &2, I.BpfError, Unit>:
  match xs:
    case Nil{}:
      match st:
        case BpfInitStep{ok, fall, ahead}:
          ok
    case Con{op, t}:
      match st:
        case BpfInitStep{ok, fall, +ahead}:
          match ok:
            case Fail{e}:
              Fail{e}
            case Done{u}:
              bpf_mem.go(t, 1n+pc, bpf_mem.step(op, pc, U32.and(fall, bpf_mem.head(ahead)), bpf_mem.tail(ahead)))

# n masks of 65535: no jump reaches any instruction yet
def bpf_mem.none(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      bpf_mem.none(p, Con{65535, acc})

def bpf_check.mem_init(need: Bool, n: Nat, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  match need:
    case False{}:
      Done{Unit{}}
    case True{}:
      bpf_mem.go(prog, 0n, BpfInitStep{Done{Unit{}}, 0, bpf_mem.none(n, Nil{})})

# The rules in order, each pass only once the ones before it hold: the
# length, the instructions' own rules, then scratch memory

def bpf_validate.mem(v: Result<&2, &2, I.BpfError, Unit>, need: Bool, n: Nat, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      bpf_check.mem_init(need, n, prog)

def bpf_validate.ops(v: Result<&2, &2, I.BpfError, Unit>, +n: Nat, need: Bool, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      bpf_validate.mem(bpf_check.go(prog, 0n, Done{Unit{}}, n), need, n, prog)

# Done{Unit{}} if the program may run, or the first rule it breaks: the
# length, then each instruction's own rules in order, then scratch memory
def bpf_validate_with(opts: BpfValidateOptions, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  match opts:
    case BpfValidateOptions{max, need}:
      +n = bpf_count(prog)
      bpf_validate.ops(bpf_check.len(n, max), n, need, prog)

# the default options, with this instruction limit
def bpf_validate(limit: Nat, +prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, Unit>:
  bpf_validate_with(BpfValidateOptions{limit, True{}}, prog)

def bpf_prepare.ok(v: Result<&2, &2, I.BpfError, Unit>, ops: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{ops}

def bpf_prepare.go(opts: BpfValidateOptions, d: Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>) -> Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>:
  match d:
    case Fail{e}:
      Fail{e}
    case Done{+ops}:
      bpf_prepare.ok(bpf_validate_with(opts, ops), ops)

# decode a stored program and validate it: the instructions, ready to run
def bpf_prepare_with(opts: BpfValidateOptions, rs: List<&2, I.BpfRaw>) -> Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>:
  bpf_prepare.go(opts, I.bpf_decode(rs))

# the same, with the default options and this instruction limit
def bpf_prepare(limit: Nat, rs: List<&2, I.BpfRaw>) -> Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>:
  bpf_prepare_with(BpfValidateOptions{limit, True{}}, rs)
