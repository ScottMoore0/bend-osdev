# bend-osdev-ebpf: the interpreter (RFC 9669, "BPF Instruction Set
# Architecture (ISA)").
#
# The machine has eleven 64-bit registers (R0 to R10), a 512-byte stack per
# call frame, and a program counter into the slots. R10 is a read-only
# pointer to the top of the current frame's stack; R1 holds a pointer to the
# context at entry (so does a BPF-to-BPF callee's R1 to R5, which the caller
# sets). Instructions step the state; a jump adds its offset to the pc; CALL
# to a helper runs ~helpers; CALL to a local function pushes a frame; EXIT
# returns R0 to the caller, or ends the program from the outermost frame.
#
# Every memory access is bounds checked (memory.bend), so a step never reads
# or writes outside a region (a law). Arithmetic wraps; division and modulo
# by zero follow RFC 9669 (alu.bend). The run has a step limit; errors are
# EbpfError, each carrying the pc. The helper table ~helpers and its id type
# are template arguments, so the interpreter is specialised to its platform.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bpf/insn.bend as C
import ./insn.bend as I
import ./alu.bend as A
import ./memory.bend as M
import ./helpers.bend as H

# The registers of one frame: R0 to R9 are values, R10 the frame pointer
type EbpfRegs is Data:
  EbpfRegs{r: List<&2, M.EbpfValue>}

# R0 undefined, R1 the context pointer, R2 to R9 undefined, R10 the frame
# pointer (RFC 9669: R1 holds the context at program entry)
def ebpf_regs.init(depth: Nat, ctx: M.EbpfValue) -> EbpfRegs:
  EbpfRegs{[M.EbpfUndef{}, ctx, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfPtr{M.EbpfRgnStack{depth}, W.W64.from_u32(M.ebpf_stack_size())}]}

def EbpfRegs.get(rs: EbpfRegs, reg: I.EbpfReg) -> M.EbpfValue:
  match rs:
    case EbpfRegs{r}:
      Maybe.default(&2, M.EbpfValue, List.get(&2, M.EbpfValue, r, U32.to_nat(I.EbpfReg.num(reg))), M.EbpfUndef{})

def EbpfRegs.set(rs: EbpfRegs, reg: I.EbpfReg, v: M.EbpfValue) -> EbpfRegs:
  match rs:
    case EbpfRegs{r}:
      EbpfRegs{List.set(&2, M.EbpfValue, r, U32.to_nat(I.EbpfReg.num(reg)), v)}

def EbpfValue.scalar(v: M.EbpfValue) -> W.W64:
  match v:
    case M.EbpfScalar{x}:
      x
    case other:
      W.W64.zero()

def EbpfRegs.scalar(rs: EbpfRegs, reg: I.EbpfReg) -> W.W64:
  EbpfValue.scalar(EbpfRegs.get(rs, reg))

# A call frame: its registers and the slot to return to (the caller's pc + 1)
type EbpfFrame is Data:
  EbpfFrame{regs: EbpfRegs, ret_pc: Nat, ret_reg: I.EbpfReg}

# The machine: the current frame's registers and pc, the stack of callers
# (innermost first), the memory, and steps taken
type EbpfMachine is Data:
  EbpfMachine{regs: EbpfRegs, pc: Nat, callers: List<&2, EbpfFrame>, +mem: M.EbpfMem, steps: Nat}

# What a step leads to: go to a pc, end the program with R0, or fault
type EbpfStep is Data:
  EbpfGoto{m: EbpfMachine}
  EbpfReturn{v: W.W64}
  EbpfFault{e: I.EbpfError}

def EbpfMachine.regs(m: EbpfMachine) -> EbpfRegs:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      regs

def EbpfMachine.pc(m: EbpfMachine) -> Nat:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      pc

def EbpfMachine.mem(m: EbpfMachine) -> M.EbpfMem:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      mem

def EbpfMachine.depth(m: EbpfMachine) -> Nat:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      List.length(&2, EbpfFrame, callers)

# the pc advanced by delta (a jump's signed offset) plus one
def ebpf_target(pc: Nat, off: W.W64) -> Nat:
  U32.to_nat(U32.add(U32.add(U32.from_nat(pc), W.W64.lo(off)), 1))

# Signed offset of an instruction, as a Nat index relative math
def ebpf_pc_add(pc: Nat, off: U32) -> Nat:
  U32.to_nat(U32.add(U32.from_nat(pc), off))

# Source operand of an ALU/JMP instruction, as a 64-bit value
def ebpf_src_val(rs: EbpfRegs, s: I.EbpfSrc) -> M.EbpfValue:
  match s:
    case I.EbpfK{imm}:
      M.EbpfScalar{A.ebpf_imm(imm)}
    case I.EbpfX{reg}:
      EbpfRegs.get(rs, reg)

# Pointer arithmetic: ptr + scalar and scalar + ptr (ADD), ptr - scalar and
# ptr - ptr (SUB). A result that mixes a pointer with a non-scalar, or any
# other op on a pointer, is EbpfNotPointer (only an unverified program does
# this). The interpreter keeps the region and moves the offset.

type EbpfArith is Data:
  EbpfArithVal{v: M.EbpfValue}
  EbpfArithBad{}

def ebpf_ptr_add(r: M.EbpfRegion, off: W.W64, d: W.W64) -> EbpfArith:
  EbpfArithVal{M.EbpfPtr{r, W.W64.add(off, d)}}

# scalar add/sub is width-aware (a 32-bit result is zero-extended, like
# ebpf_alu); pointer offsets are always 64-bit
def ebpf_arith_add(w: I.EbpfWidth, a: M.EbpfValue, b: M.EbpfValue) -> EbpfArith:
  match a:
    case M.EbpfScalar{x}:
      match b:
        case M.EbpfScalar{y}:
          EbpfArithVal{M.EbpfScalar{A.ebpf_alu(w, I.EbpfAdd{}, x, y)}}
        case M.EbpfPtr{r, off}:
          ebpf_ptr_add(r, off, x)
        case M.EbpfUndef{}:
          EbpfArithBad{}
    case M.EbpfPtr{r, off}:
      match b:
        case M.EbpfScalar{y}:
          ebpf_ptr_add(r, off, y)
        case other:
          EbpfArithBad{}
    case M.EbpfUndef{}:
      EbpfArithBad{}

def ebpf_arith_sub(w: I.EbpfWidth, a: M.EbpfValue, b: M.EbpfValue) -> EbpfArith:
  match a:
    case M.EbpfScalar{x}:
      match b:
        case M.EbpfScalar{y}:
          EbpfArithVal{M.EbpfScalar{A.ebpf_alu(w, I.EbpfSub{}, x, y)}}
        case other:
          EbpfArithBad{}
    case M.EbpfPtr{r, off}:
      match b:
        case M.EbpfScalar{y}:
          EbpfArithVal{M.EbpfPtr{r, W.W64.sub(off, y)}}
        case M.EbpfPtr{r2, off2}:
          EbpfArithVal{M.EbpfScalar{W.W64.sub(off, off2)}}
        case M.EbpfUndef{}:
          EbpfArithBad{}
    case M.EbpfUndef{}:
      EbpfArithBad{}

def ebpf_alu_scalar(w: I.EbpfWidth, op: I.EbpfAluOp, a: M.EbpfValue, b: M.EbpfValue) -> EbpfArith:
  match a:
    case M.EbpfScalar{x}:
      match b:
        case M.EbpfScalar{y}:
          EbpfArithVal{M.EbpfScalar{A.ebpf_alu(w, op, x, y)}}
        case other:
          EbpfArithBad{}
    case other:
      EbpfArithBad{}

def ebpf_mov_val.lo(b: M.EbpfValue) -> EbpfArith:
  match b:
    case M.EbpfScalar{x}:
      EbpfArithVal{M.EbpfScalar{A.ebpf_zext32(W.W64.lo(x))}}
    case M.EbpfPtr{r, off}:
      EbpfArithVal{M.EbpfScalar{A.ebpf_zext32(W.W64.lo(off))}}
    case M.EbpfUndef{}:
      EbpfArithBad{}

# MOV copies the source: the whole value at 64 bits (a pointer or a scalar),
# or the low 32 bits zero-extended at 32 bits
def ebpf_mov_val(w: I.EbpfWidth, b: M.EbpfValue) -> EbpfArith:
  match w:
    case I.EbpfBits64{}:
      EbpfArithVal{b}
    case I.EbpfBits32{}:
      ebpf_mov_val.lo(b)

# an ALU op on two values: scalar arithmetic, or pointer +/- adjustments.
# ADD/SUB may involve pointers; MOV copies the source; every other op needs
# two scalars.
def ebpf_alu_val(w: I.EbpfWidth, op: I.EbpfAluOp, a: M.EbpfValue, b: M.EbpfValue) -> EbpfArith:
  match op:
    case I.EbpfAdd{}:
      ebpf_arith_add(w, a, b)
    case I.EbpfSub{}:
      ebpf_arith_sub(w, a, b)
    case I.EbpfMov{}:
      ebpf_mov_val(w, b)
    case other:
      ebpf_alu_scalar(w, op, a, b)

# The result of a step that only writes a register or memory, or faults
def ebpf_next(m: EbpfMachine) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      EbpfGoto{EbpfMachine{regs, 1n+pc, callers, mem, steps}}

def ebpf_set_goto(m: EbpfMachine, reg: I.EbpfReg, v: M.EbpfValue) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      EbpfGoto{EbpfMachine{EbpfRegs.set(regs, reg, v), 1n+pc, callers, mem, steps}}

def ebpf_mem_goto(m: EbpfMachine, mem: M.EbpfMem) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, old, steps}:
      EbpfGoto{EbpfMachine{regs, 1n+pc, callers, mem, steps}}

# write the result of an ALU op to dst, or fault
def ebpf_write_arith(m: EbpfMachine, +pc: Nat, +dst: I.EbpfReg, a: EbpfArith) -> EbpfStep:
  match a:
    case EbpfArithVal{v}:
      ebpf_set_goto(m, dst, v)
    case EbpfArithBad{}:
      EbpfFault{I.EbpfErrNotPointer{pc}}

# ALU and ALU64

def ebpf_exec_alu(m: EbpfMachine, +pc: Nat, w: I.EbpfWidth, op: I.EbpfAluOp, +dst: I.EbpfReg, +src: I.EbpfSrc, +regs: EbpfRegs) -> EbpfStep:
  ebpf_write_arith(m, pc, dst, ebpf_alu_val(w, op, EbpfRegs.get(regs, dst), ebpf_src_val(regs, src)))

def ebpf_neg.go(v: M.EbpfValue, +pc: Nat, m: EbpfMachine, w: I.EbpfWidth, +dst: I.EbpfReg) -> EbpfStep:
  match v:
    case M.EbpfScalar{x}:
      ebpf_set_goto(m, dst, M.EbpfScalar{A.ebpf_neg(w, x)})
    case other:
      EbpfFault{I.EbpfErrNotPointer{pc}}

def ebpf_exec_neg(m: EbpfMachine, +pc: Nat, w: I.EbpfWidth, +dst: I.EbpfReg, +regs: EbpfRegs) -> EbpfStep:
  ebpf_neg.go(EbpfRegs.get(regs, dst), pc, m, w, dst)

def ebpf_exec_movsx(m: EbpfMachine, +pc: Nat, v: M.EbpfValue, +dst: I.EbpfReg) -> EbpfStep:
  match v:
    case M.EbpfScalar{x}:
      ebpf_set_goto(m, dst, M.EbpfScalar{x})
    case other:
      EbpfFault{I.EbpfErrNotPointer{pc}}

# Loads and stores: the pointer's region and offset, plus the instruction's
# signed offset

def ebpf_mem_region(v: M.EbpfValue) -> Maybe<&2, M.EbpfRegion>:
  match v:
    case M.EbpfPtr{r, off}:
      Some{r}
    case other:
      None{}

def ebpf_eff_addr(v: M.EbpfValue, off: U32) -> W.W64:
  match v:
    case M.EbpfPtr{r, base}:
      W.W64.add(base, A.ebpf_off64(off))
    case other:
      W.W64.zero()

def ebpf_load.sext(sx: Bool, s: I.EbpfSmall, v: M.EbpfValue) -> M.EbpfValue:
  match sx:
    case False{}:
      v
    case True{}:
      match v:
        case M.EbpfScalar{x}:
          M.EbpfScalar{A.ebpf_load_sx(s, x)}
        case other:
          v

def ebpf_load.fin(r: Result<&2, &2, I.EbpfMemError, M.EbpfValue>, +pc: Nat, m: EbpfMachine, +dst: I.EbpfReg, sx: Bool, s: I.EbpfSmall) -> EbpfStep:
  match r:
    case Fail{e}:
      EbpfFault{I.EbpfErrMemory{pc, e}}
    case Done{v}:
      ebpf_set_goto(m, dst, ebpf_load.sext(sx, s, v))

def ebpf_load.go(rg: Maybe<&2, M.EbpfRegion>, +pc: Nat, m: EbpfMachine, +mem: M.EbpfMem, ptr: M.EbpfValue, +dst: I.EbpfReg, size: I.EbpfSize, off: U32, sx: Bool, small: I.EbpfSmall) -> EbpfStep:
  match rg:
    case None{}:
      EbpfFault{I.EbpfErrNotPointer{pc}}
    case Some{r}:
      ebpf_load.fin(M.EbpfMem.load(mem, r, ebpf_eff_addr(ptr, off), size), pc, m, dst, sx, small)

def ebpf_exec_ldx(m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, regs: EbpfRegs, +dst: I.EbpfReg, +src: I.EbpfReg, size: I.EbpfSize, off: U32, sx: Bool, small: I.EbpfSmall) -> EbpfStep:
  +ptr = EbpfRegs.get(regs, src)
  ebpf_load.go(ebpf_mem_region(ptr), pc, m, mem, ptr, dst, size, off, sx, small)

def ebpf_store.fin(r: Result<&2, &2, I.EbpfMemError, M.EbpfMem>, +pc: Nat, m: EbpfMachine) -> EbpfStep:
  match r:
    case Fail{e}:
      EbpfFault{I.EbpfErrMemory{pc, e}}
    case Done{mem}:
      ebpf_mem_goto(m, mem)

def ebpf_store.go(rg: Maybe<&2, M.EbpfRegion>, +pc: Nat, m: EbpfMachine, +mem: M.EbpfMem, ptr: M.EbpfValue, size: I.EbpfSize, off: U32, v: M.EbpfValue) -> EbpfStep:
  match rg:
    case None{}:
      EbpfFault{I.EbpfErrNotPointer{pc}}
    case Some{r}:
      ebpf_store.fin(M.EbpfMem.store(mem, r, ebpf_eff_addr(ptr, off), size, v), pc, m)

def ebpf_exec_st(m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, regs: EbpfRegs, +dst: I.EbpfReg, size: I.EbpfSize, off: U32, v: M.EbpfValue) -> EbpfStep:
  +ptr = EbpfRegs.get(regs, dst)
  ebpf_store.go(ebpf_mem_region(ptr), pc, m, mem, ptr, size, off, v)

# Atomics: load the old value, combine it with src, store the result; a
# fetching op first writes the old value to src (CMPXCHG compares R0).

def EbpfAtomicSize.size(s: I.EbpfAtomicSize) -> I.EbpfSize:
  match s:
    case I.EbpfAtomicW{}:
      I.EbpfSizeW{}
    case I.EbpfAtomicDW{}:
      I.EbpfSizeDW{}

def EbpfAtomicSize.width(s: I.EbpfAtomicSize) -> I.EbpfWidth:
  match s:
    case I.EbpfAtomicW{}:
      I.EbpfBits32{}
    case I.EbpfAtomicDW{}:
      I.EbpfBits64{}

def ebpf_cmpxchg.go(eq: Bool, old: W.W64, src: W.W64) -> W.W64:
  match eq:
    case True{}:
      src
    case False{}:
      old

def ebpf_cmpxchg(w: I.EbpfWidth, +old: W.W64, cmp: W.W64, src: W.W64) -> W.W64:
  ebpf_cmpxchg.go(A.ebpf_cond(w, I.EbpfJeq{}, old, cmp), old, src)

def ebpf_atomic_op(sz: I.EbpfAtomicSize, op: I.EbpfAtomicOp, old: W.W64, src: W.W64, r0: W.W64) -> W.W64:
  match op:
    case I.EbpfAtAdd{f}:
      A.ebpf_alu(EbpfAtomicSize.width(sz), I.EbpfAdd{}, old, src)
    case I.EbpfAtOr{f}:
      A.ebpf_alu(EbpfAtomicSize.width(sz), I.EbpfOr{}, old, src)
    case I.EbpfAtAnd{f}:
      A.ebpf_alu(EbpfAtomicSize.width(sz), I.EbpfAnd{}, old, src)
    case I.EbpfAtXor{f}:
      A.ebpf_alu(EbpfAtomicSize.width(sz), I.EbpfXor{}, old, src)
    case I.EbpfAtXchg{}:
      src
    case I.EbpfAtCmpxchg{}:
      ebpf_cmpxchg(EbpfAtomicSize.width(sz), old, r0, src)

# whether the op writes a result back to memory (CMPXCHG always stores old
# or src; others store the combined value)
def ebpf_atomic_fetches(op: I.EbpfAtomicOp) -> Bool:
  match op:
    case I.EbpfAtAdd{f}:
      f
    case I.EbpfAtOr{f}:
      f
    case I.EbpfAtAnd{f}:
      f
    case I.EbpfAtXor{f}:
      f
    case I.EbpfAtXchg{}:
      True{}
    case I.EbpfAtCmpxchg{}:
      False{}

# after the store, write the fetched old value: to src (plain fetch/xchg) or
# to R0 (cmpxchg)
def ebpf_atomic_wb.plain(fetch: Bool, +regs: EbpfRegs, +src: I.EbpfReg, old: W.W64) -> EbpfRegs:
  match fetch:
    case True{}:
      EbpfRegs.set(regs, src, M.EbpfScalar{old})
    case False{}:
      regs

def ebpf_atomic_wb(op: I.EbpfAtomicOp, regs: EbpfRegs, +src: I.EbpfReg, old: W.W64) -> EbpfRegs:
  match op:
    case I.EbpfAtCmpxchg{}:
      EbpfRegs.set(regs, I.EbpfR0{}, M.EbpfScalar{old})
    case other:
      ebpf_atomic_wb.plain(ebpf_atomic_fetches(op), regs, src, old)

def ebpf_atomic.store(r: Result<&2, &2, I.EbpfMemError, M.EbpfMem>, +pc: Nat, m: EbpfMachine, op: I.EbpfAtomicOp, +src: I.EbpfReg, old: W.W64) -> EbpfStep:
  match r:
    case Fail{e}:
      EbpfFault{I.EbpfErrMemory{pc, e}}
    case Done{mem}:
      match m:
        case EbpfMachine{regs, mpc, callers, oldmem, steps}:
          EbpfGoto{EbpfMachine{ebpf_atomic_wb(op, regs, src, old), 1n+mpc, callers, mem, steps}}

def ebpf_atomic.old(r: Result<&2, &2, I.EbpfMemError, M.EbpfValue>, +pc: Nat, m: EbpfMachine, +mem: M.EbpfMem, rg: M.EbpfRegion, addr: W.W64, +sz: I.EbpfAtomicSize, +op: I.EbpfAtomicOp, +srcreg: I.EbpfReg, +srcv: W.W64, +r0: W.W64) -> EbpfStep:
  match r:
    case Fail{e}:
      EbpfFault{I.EbpfErrMemory{pc, e}}
    case Done{v}:
      match v:
        case M.EbpfScalar{+old}:
          ebpf_atomic.store(M.EbpfMem.store(mem, rg, addr, EbpfAtomicSize.size(sz), M.EbpfScalar{ebpf_atomic_op(sz, op, old, srcv, r0)}), pc, m, op, srcreg, old)
        case other:
          EbpfFault{I.EbpfErrMemory{pc, I.EbpfMemPointerBytes{}}}

def ebpf_atomic.go(rg: Maybe<&2, M.EbpfRegion>, +pc: Nat, m: EbpfMachine, +mem: M.EbpfMem, +regs: EbpfRegs, +ptr: M.EbpfValue, +sz: I.EbpfAtomicSize, +op: I.EbpfAtomicOp, +dst: I.EbpfReg, +src: I.EbpfReg, +off: U32) -> EbpfStep:
  match rg:
    case None{}:
      EbpfFault{I.EbpfErrNotPointer{pc}}
    case Some{+r}:
      +addr = ebpf_eff_addr(ptr, off)
      ebpf_atomic.old(M.EbpfMem.load(mem, r, addr, EbpfAtomicSize.size(sz)), pc, m, mem, r, addr, sz, op, src, EbpfRegs.scalar(regs, src), EbpfRegs.scalar(regs, I.EbpfR0{}))

def ebpf_exec_atomic(m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, +regs: EbpfRegs, +sz: I.EbpfAtomicSize, +op: I.EbpfAtomicOp, +dst: I.EbpfReg, +src: I.EbpfReg, +off: U32) -> EbpfStep:
  +ptr = EbpfRegs.get(regs, dst)
  ebpf_atomic.go(ebpf_mem_region(ptr), pc, m, mem, regs, ptr, sz, op, dst, src, off)

# 64-bit immediate loads: EbpfLdImm64 loads imm:next; a map fd load sets a
# pointer to that map's handle (the verifier resolves the fd). Other kinds
# are unsupported here.

def ebpf_map_by_fd.pick(hit: Bool, +n: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{n}
    case False{}:
      rest

def ebpf_map_by_fd.go(maps: List<&2, M.EbpfMap>, +fd: U32, +n: Nat) -> Maybe<&2, Nat>:
  match maps:
    case Nil{}:
      None{}
    case Con{mp, t}:
      ebpf_map_by_fd.pick(U32.is_eq(M.EbpfMap.fd(mp), fd), n, ebpf_map_by_fd.go(t, fd, 1n+n))

def ebpf_map_by_fd(+mem: M.EbpfMem, fd: U32) -> Maybe<&2, Nat>:
  ebpf_map_by_fd.go(M.EbpfMem.maps(mem), fd, 0n)

# lddw takes two slots, so its pc advances by 2
def ebpf_set_goto2(m: EbpfMachine, reg: I.EbpfReg, v: M.EbpfValue) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      EbpfGoto{EbpfMachine{EbpfRegs.set(regs, reg, v), Nat.add(pc, 2n), callers, mem, steps}}

def ebpf_lddw.map(mi: Maybe<&2, Nat>, +pc: Nat, m: EbpfMachine, +dst: I.EbpfReg) -> EbpfStep:
  match mi:
    case None{}:
      EbpfFault{I.EbpfErrBadMap{pc}}
    case Some{i}:
      ebpf_set_goto2(m, dst, M.EbpfPtr{M.EbpfRgnMap{i}, W.W64.zero()})

def ebpf_exec_lddw(m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, kd: I.EbpfLddwKind, +dst: I.EbpfReg, imm: U32, next: U32) -> EbpfStep:
  match kd:
    case I.EbpfLdImm64{}:
      ebpf_set_goto2(m, dst, M.EbpfScalar{W.W64.from_parts(next, imm)})
    case I.EbpfLdMapFd{}:
      ebpf_lddw.map(ebpf_map_by_fd(mem, imm), pc, m, dst)
    case other:
      EbpfFault{I.EbpfErrUnsupported{pc}}


# Jumps

def ebpf_jump(m: EbpfMachine, off: U32) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      EbpfGoto{EbpfMachine{regs, ebpf_target(pc, A.ebpf_off64(off)), callers, mem, steps}}

def ebpf_branch(hit: Bool, m: EbpfMachine, off: U32) -> EbpfStep:
  match hit:
    case True{}:
      ebpf_jump(m, off)
    case False{}:
      ebpf_next(m)

def ebpf_cond_src(rs: EbpfRegs, s: I.EbpfSrc) -> W.W64:
  match s:
    case I.EbpfK{imm}:
      A.ebpf_imm(imm)
    case I.EbpfX{reg}:
      EbpfRegs.scalar(rs, reg)

def ebpf_exec_jmp(m: EbpfMachine, w: I.EbpfWidth, c: I.EbpfCond, +dst: I.EbpfReg, +src: I.EbpfSrc, off: U32, +regs: EbpfRegs) -> EbpfStep:
  ebpf_branch(A.ebpf_cond(w, c, EbpfRegs.scalar(regs, dst), ebpf_cond_src(regs, src)), m, off)

# Calls to helpers

def ebpf_call_args(+regs: EbpfRegs) -> List<&2, M.EbpfValue>:
  [EbpfRegs.get(regs, I.EbpfR1{}), EbpfRegs.get(regs, I.EbpfR2{}), EbpfRegs.get(regs, I.EbpfR3{}), EbpfRegs.get(regs, I.EbpfR4{}), EbpfRegs.get(regs, I.EbpfR5{})]

def ebpf_helper.fin(out: H.EbpfHelperOut, +pc: Nat, m: EbpfMachine, id: U32) -> EbpfStep:
  match out:
    case H.EbpfHelperDone{r0, mem}:
      match m:
        case EbpfMachine{regs, mpc, callers, oldmem, steps}:
          EbpfGoto{EbpfMachine{EbpfRegs.set(regs, I.EbpfR0{}, r0), 1n+mpc, callers, mem, steps}}
    case H.EbpfHelperUnknown{}:
      EbpfFault{I.EbpfErrUnknownHelper{pc, id}}
    case H.EbpfHelperFault{why}:
      EbpfFault{I.EbpfErrMemory{pc, why}}
    case H.EbpfHelperBadArg{}:
      EbpfFault{I.EbpfErrHelper{pc, id}}

def ebpf_exec_helper(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, +regs: EbpfRegs, +id: U32) -> EbpfStep:
  ebpf_helper.fin(helpers(id, ebpf_call_args(regs), mem), pc, m, id)

# Calls to program-local functions: push the current frame, give the callee
# a fresh frame whose R1 to R5 are the caller's, and a new 512-byte stack.
# The call's imm is the signed offset to the callee's first slot.

# the callee's registers: R0 undefined, R1 to R5 the caller's arguments, R6
# to R9 undefined, R10 the new frame's stack pointer
def ebpf_callee_regs(+regs: EbpfRegs, depth: Nat) -> EbpfRegs:
  EbpfRegs{[M.EbpfUndef{}, EbpfRegs.get(regs, I.EbpfR1{}), EbpfRegs.get(regs, I.EbpfR2{}), EbpfRegs.get(regs, I.EbpfR3{}), EbpfRegs.get(regs, I.EbpfR4{}), EbpfRegs.get(regs, I.EbpfR5{}), M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfUndef{}, M.EbpfPtr{M.EbpfRgnStack{depth}, W.W64.from_u32(M.ebpf_stack_size())}]}

def ebpf_local.go(ok: Bool, +regs: EbpfRegs, +pc: Nat, +callers: List<&2, EbpfFrame>, +mem: M.EbpfMem, steps: Nat, imm: U32) -> EbpfStep:
  match ok:
    case True{}:
      +depth = Nat.add(List.length(&2, EbpfFrame, callers), 1n)
      EbpfGoto{EbpfMachine{ebpf_callee_regs(regs, depth), ebpf_pc_add(pc, U32.add(imm, 1)), Con{EbpfFrame{regs, 1n+pc, I.EbpfR0{}}, callers}, M.EbpfMem.push(mem), steps}}
    case False{}:
      EbpfFault{I.EbpfErrCallDepth{pc}}

def ebpf_exec_local(m: EbpfMachine, +pc: Nat, imm: U32, limit: Nat) -> EbpfStep:
  match m:
    case EbpfMachine{regs, mpc, +callers, mem, steps}:
      ebpf_local.go(Nat.is_lt(List.length(&2, EbpfFrame, callers), limit), regs, mpc, callers, mem, steps, imm)

# EXIT: return R0 to the caller (restoring its frame, dropping this stack),
# or end the program from the outermost frame

def ebpf_exit.to(fr: EbpfFrame, rest: List<&2, EbpfFrame>, r0: M.EbpfValue, +mem: M.EbpfMem, steps: Nat) -> EbpfStep:
  match fr:
    case EbpfFrame{cregs, ret_pc, ret_reg}:
      EbpfGoto{EbpfMachine{EbpfRegs.set(cregs, ret_reg, r0), ret_pc, rest, M.EbpfMem.pop(mem), steps}}

def ebpf_exec_exit(m: EbpfMachine) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      match callers:
        case Nil{}:
          EbpfReturn{EbpfRegs.scalar(regs, I.EbpfR0{})}
        case Con{fr, rest}:
          ebpf_exit.to(fr, rest, EbpfRegs.get(regs, I.EbpfR0{}), mem, steps)

def ebpf_small_size(s: I.EbpfSmall) -> I.EbpfSize:
  match s:
    case I.EbpfSmallW{}:
      I.EbpfSizeW{}
    case I.EbpfSmallH{}:
      I.EbpfSizeH{}
    case I.EbpfSmallB{}:
      I.EbpfSizeB{}

# JMP32 unconditional jump (32-bit immediate offset)
def ebpf_jump32(m: EbpfMachine, imm: U32) -> EbpfStep:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      EbpfGoto{EbpfMachine{regs, ebpf_target(pc, A.ebpf_sext32(imm)), callers, mem, steps}}

# packet loads are network byte order regardless of host order
def ebpf_packet_be(mem: M.EbpfMem) -> M.EbpfMem:
  match mem:
    case M.EbpfMem{o, ctx, pkt, maps, stacks}:
      M.EbpfMem{C.BpfBig{}, ctx, pkt, maps, stacks}

# Legacy packet loads (LD ABS/IND): a 32/16/8-bit read from the packet at a
# fixed or indexed offset, big-endian (RFC 9669, 5.2); any fault ends the
# program. Here they read EbpfRgnPacket and fault on a bad access.
def ebpf_exec_ldabs(m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, regs: EbpfRegs, size: I.EbpfSize, imm: U32, base: W.W64) -> EbpfStep:
  ebpf_load.fin(M.EbpfMem.load(ebpf_packet_be(mem), M.EbpfRgnPacket{}, W.W64.add(base, A.ebpf_sext32(imm)), size), pc, m, I.EbpfR0{}, False{}, I.EbpfSmallW{})


def ebpf_exec_call(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, +depth_limit: Nat, m: EbpfMachine, +pc: Nat, +mem: M.EbpfMem, regs: EbpfRegs, kind: I.EbpfCallKind, imm: U32) -> EbpfStep:
  match kind:
    case I.EbpfCallHelper{}:
      ebpf_exec_helper(~helpers, m, pc, mem, regs, imm)
    case I.EbpfCallLocal{}:
      ebpf_exec_local(m, pc, imm, depth_limit)
    case I.EbpfCallBtf{}:
      EbpfFault{I.EbpfErrUnsupported{pc}}

# One instruction: dispatch on its shape, with the current machine, pc,
# memory and registers in hand
def ebpf_exec(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, ~depth_limit: Nat, +i: I.EbpfInsn, +m: EbpfMachine) -> EbpfStep:
  match i:
    case I.EbpfAlu{w, op, dst, src}:
      ebpf_exec_alu(m, EbpfMachine.pc(m), w, op, dst, src, EbpfMachine.regs(m))
    case I.EbpfNeg{w, dst}:
      ebpf_exec_neg(m, EbpfMachine.pc(m), w, dst, EbpfMachine.regs(m))
    case I.EbpfMovsx32{bits, dst, src}:
      ebpf_exec_movsx(m, EbpfMachine.pc(m), M.EbpfScalar{A.ebpf_movsx32(bits, EbpfRegs.scalar(EbpfMachine.regs(m), src))}, dst)
    case I.EbpfMovsx64{bits, dst, src}:
      ebpf_exec_movsx(m, EbpfMachine.pc(m), M.EbpfScalar{A.ebpf_movsx64(bits, EbpfRegs.scalar(EbpfMachine.regs(m), src))}, dst)
    case I.EbpfEnd{kind, bits, dst}:
      ebpf_exec_movsx(m, EbpfMachine.pc(m), M.EbpfScalar{A.ebpf_end(kind, M.EbpfMem.order(EbpfMachine.mem(m)), bits, EbpfRegs.scalar(EbpfMachine.regs(m), dst))}, dst)
    case I.EbpfLddw{kind, dst, imm, next}:
      ebpf_exec_lddw(m, EbpfMachine.pc(m), EbpfMachine.mem(m), kind, dst, imm, next)
    case I.EbpfLdx{size, dst, src, off}:
      ebpf_exec_ldx(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), dst, src, size, off, False{}, I.EbpfSmallW{})
    case I.EbpfLdxs{size, dst, src, off}:
      ebpf_exec_ldx(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), dst, src, ebpf_small_size(size), off, True{}, size)
    case I.EbpfSt{size, dst, off, imm}:
      ebpf_exec_st(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), dst, size, off, M.EbpfScalar{A.ebpf_imm(imm)})
    case I.EbpfStx{size, dst, src, off}:
      ebpf_exec_st(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), dst, size, off, EbpfRegs.get(EbpfMachine.regs(m), src))
    case I.EbpfAtomic{size, op, dst, src, off}:
      ebpf_exec_atomic(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), size, op, dst, src, off)
    case I.EbpfLdAbs{size, imm}:
      ebpf_exec_ldabs(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), ebpf_small_size(size), imm, W.W64.zero())
    case I.EbpfLdInd{size, src, imm}:
      ebpf_exec_ldabs(m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), ebpf_small_size(size), imm, EbpfRegs.scalar(EbpfMachine.regs(m), src))
    case I.EbpfJa{off}:
      ebpf_jump(m, off)
    case I.EbpfJa32{imm}:
      ebpf_jump32(m, imm)
    case I.EbpfJmp{w, cond, dst, src, off}:
      ebpf_exec_jmp(m, w, cond, dst, src, off, EbpfMachine.regs(m))
    case I.EbpfCall{kind, imm}:
      ebpf_exec_call(~helpers, depth_limit, m, EbpfMachine.pc(m), EbpfMachine.mem(m), EbpfMachine.regs(m), kind, imm)
    case I.EbpfExit{}:
      ebpf_exec_exit(m)


# The run: a program is expanded once to a slot-indexed list (each 64-bit
# immediate load's second slot becomes a None), so fetching by pc is a list
# lookup. The loop carries an EbpfProgress; a step limit (fuel) bounds it.

type EbpfOutcome is Data:
  EbpfOk{value: W.W64}
  EbpfErr{e: I.EbpfError}

type EbpfProgress is Data:
  EbpfRunning{m: EbpfMachine}
  EbpfReturned{v: W.W64}
  EbpfFaulted{e: I.EbpfError}

def ebpf_slots_list.ins(i: I.EbpfInsn, n: Nat, acc: List<&2, Maybe<&2, I.EbpfInsn>>) -> List<&2, Maybe<&2, I.EbpfInsn>>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ebpf_slots_list.ins(i, p, Con{None{}, acc})

def ebpf_slots_list.go(prog: List<&2, I.EbpfInsn>, acc: List<&2, Maybe<&2, I.EbpfInsn>>) -> List<&2, Maybe<&2, I.EbpfInsn>>:
  match prog:
    case Nil{}:
      List.reverse(&2, Maybe<&2, I.EbpfInsn>, acc)
    case Con{+i, t}:
      ebpf_slots_list.go(t, ebpf_slots_list.ins(i, Nat.sub(I.EbpfInsn.slots(i), 1n), Con{Some{i}, acc}))

# one entry per slot: Some{i} at an instruction's first slot, None at a
# 64-bit immediate load's second slot
def ebpf_slots_list(prog: List<&2, I.EbpfInsn>) -> List<&2, Maybe<&2, I.EbpfInsn>>:
  ebpf_slots_list.go(prog, Nil{})

# the instruction at slot pc, or None (past the end, or a wide second slot)
def ebpf_fetch(slots: List<&2, Maybe<&2, I.EbpfInsn>>, pc: Nat) -> Maybe<&2, I.EbpfInsn>:
  Maybe.default(&2, Maybe<&2, I.EbpfInsn>, List.get(&2, Maybe<&2, I.EbpfInsn>, slots, pc), None{})

def EbpfMachine.tick(m: EbpfMachine) -> EbpfMachine:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      EbpfMachine{regs, pc, callers, mem, 1n+steps}

def EbpfMachine.steps(m: EbpfMachine) -> Nat:
  match m:
    case EbpfMachine{regs, pc, callers, mem, steps}:
      steps

# a step's result as progress
def ebpf_progress(st: EbpfStep) -> EbpfProgress:
  match st:
    case EbpfGoto{m2}:
      EbpfRunning{m2}
    case EbpfReturn{v}:
      EbpfReturned{v}
    case EbpfFault{e}:
      EbpfFaulted{e}

# the instruction fetched, executed; the next progress
def ebpf_step1.go(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, ~depth_limit: Nat, mi: Maybe<&2, I.EbpfInsn>, +m: EbpfMachine) -> EbpfProgress:
  match mi:
    case None{}:
      EbpfFaulted{I.EbpfErrPcOut{EbpfMachine.pc(m)}}
    case Some{i}:
      ebpf_progress(ebpf_exec(~helpers, depth_limit, i, EbpfMachine.tick(m)))

def ebpf_step1(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, ~depth_limit: Nat, slots: List<&2, Maybe<&2, I.EbpfInsn>>, +m: EbpfMachine) -> EbpfProgress:
  ebpf_step1.go(~helpers, depth_limit, ebpf_fetch(slots, EbpfMachine.pc(m)), m)

# the loop: while Running and fuel remains, step; EbpfReturned/EbpfFaulted
# end it; running out of fuel is EbpfErrComplexity
def ebpf_run.go(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, ~depth_limit: Nat, fuel: Nat, prog: EbpfProgress, +slots: List<&2, Maybe<&2, I.EbpfInsn>>) -> EbpfOutcome:
  match fuel:
    case 0n:
      match prog:
        case EbpfReturned{v}:
          EbpfOk{v}
        case EbpfFaulted{e}:
          EbpfErr{e}
        case EbpfRunning{m}:
          EbpfErr{I.EbpfErrComplexity{EbpfMachine.steps(m)}}
    case 1n+f:
      match prog:
        case EbpfReturned{v}:
          EbpfOk{v}
        case EbpfFaulted{e}:
          EbpfErr{e}
        case EbpfRunning{m}:
          ebpf_run.go(~helpers, depth_limit, f, ebpf_step1(~helpers, depth_limit, slots, m), slots)

# the maximum nesting of BPF-to-BPF calls (the kernel's MAX_CALL_FRAMES)
def ebpf_max_frames() -> Nat:
  8n

# the usual step limit (the kernel's run-time instruction limit)
def ebpf_max_steps() -> Nat:
  1000000n

# the machine at entry: frame 0, pc 0, R1 the context pointer, R10 the frame
# pointer, a fresh stack
def ebpf_start(mem: M.EbpfMem) -> EbpfMachine:
  EbpfMachine{ebpf_regs.init(0n, M.EbpfPtr{M.EbpfRgnCtx{}, W.W64.zero()}), 0n, Nil{}, M.EbpfMem.push(mem), 0n}

# Run prog over mem. EbpfOk{v} is R0 at EXIT from frame 0; EbpfErr carries
# the pc. The helper table ~helpers, the call-depth limit ~depth_limit and
# the step limit fuel are parameters.
def ebpf_run_with(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, ~depth_limit: Nat, fuel: Nat, prog: List<&2, I.EbpfInsn>, mem: M.EbpfMem) -> EbpfOutcome:
  ebpf_run.go(~helpers, depth_limit, fuel, EbpfRunning{ebpf_start(mem)}, ebpf_slots_list(prog))

# the standard helper table, eight frames, a million steps
def ebpf_run(prog: List<&2, I.EbpfInsn>, mem: M.EbpfMem) -> EbpfOutcome:
  ebpf_run_with(~H.ebpf_helpers.std, ebpf_max_frames(), ebpf_max_steps(), prog, mem)
