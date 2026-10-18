# bend-osdev-ebpf: eBPF instructions, raw and decoded (RFC 9669, "BPF
# Instruction Set Architecture (ISA)", sections 3 to 5).
#
# A basic instruction is 64 bits: opcode (8), dst_reg (4), src_reg (4),
# offset (16, signed), imm (32, signed). The wide instruction (lddw,
# {IMM, DW, LD}) is 128 bits: a basic instruction, then a second one whose
# opcode, registers and offset are zero and whose imm is next_imm, the high
# half of the 64-bit immediate. EbpfRaw is one 64-bit slot, field by field,
# before byte packing; EbpfInsn is an instruction decoded into what it does,
# one constructor per instruction shape, so code that builds or inspects a
# program never handles opcode bits.
#
# The opcode is code | source | class for arithmetic and jumps, and
# mode | size | class for loads and stores (RFC 9669, 3 and 5):
#   class  LD 0, LDX 1, ST 2, STX 3, ALU 4, JMP 5, JMP32 6, ALU64 7
#   source K 0x00 (imm), X 0x08 (src_reg)
#   ALU    ADD 0x00 SUB 0x10 MUL 0x20 DIV 0x30 (offset 1: SDIV) OR 0x40
#          AND 0x50 LSH 0x60 RSH 0x70 NEG 0x80 MOD 0x90 (offset 1: SMOD)
#          XOR 0xa0 MOV 0xb0 (offset 8, 16, 32: MOVSX) ARSH 0xc0 END 0xd0
#   JMP    JA 0x00 JEQ 0x10 JGT 0x20 JGE 0x30 JSET 0x40 JNE 0x50 JSGT 0x60
#          JSGE 0x70 CALL 0x80 EXIT 0x90 JLT 0xa0 JLE 0xb0 JSLT 0xc0
#          JSLE 0xd0
#   size   W 0x00 H 0x08 B 0x10 DW 0x18
#   mode   IMM 0x00 ABS 0x20 IND 0x40 MEM 0x60 MEMSX 0x80 ATOMIC 0xc0
#   atomic (in imm) ADD 0x00 OR 0x40 AND 0x50 XOR 0xa0, FETCH 0x01,
#          XCHG 0xe1, CMPXCHG 0xf1
# Decoding is strict: a field an instruction does not use must be zero, as
# RFC 9669 requires, and a register number must be 0 to 10.
import Base
import ../bytes/bytes.bend as B
import ../bpf/insn.bend as C

# The eleven registers: R0 (return value), R1 to R5 (arguments), R6 to R9
# (callee saved), R10 (the read-only frame pointer)
type EbpfReg is Data:
  EbpfR0{}
  EbpfR1{}
  EbpfR2{}
  EbpfR3{}
  EbpfR4{}
  EbpfR5{}
  EbpfR6{}
  EbpfR7{}
  EbpfR8{}
  EbpfR9{}
  EbpfR10{}

# 32-bit (ALU, JMP32) or 64-bit (ALU64, JMP) operation
type EbpfWidth is Data:
  EbpfBits32{}
  EbpfBits64{}

# the second operand: the immediate, or a source register
type EbpfSrc is Data:
  EbpfK{imm: U32}
  EbpfX{reg: EbpfReg}

type EbpfAluOp is Data:
  EbpfAdd{}
  EbpfSub{}
  EbpfMul{}
  EbpfDiv{}
  EbpfSdiv{}
  EbpfOr{}
  EbpfAnd{}
  EbpfLsh{}
  EbpfRsh{}
  EbpfMod{}
  EbpfSmod{}
  EbpfXor{}
  EbpfMov{}
  EbpfArsh{}

type EbpfCond is Data:
  EbpfJeq{}
  EbpfJgt{}
  EbpfJge{}
  EbpfJset{}
  EbpfJne{}
  EbpfJsgt{}
  EbpfJsge{}
  EbpfJlt{}
  EbpfJle{}
  EbpfJslt{}
  EbpfJsle{}

# the size of a memory access
type EbpfSize is Data:
  EbpfSizeW{}
  EbpfSizeH{}
  EbpfSizeB{}
  EbpfSizeDW{}

# the sizes a sign-extending load (MEMSX) or the legacy packet loads use
type EbpfSmall is Data:
  EbpfSmallW{}
  EbpfSmallH{}
  EbpfSmallB{}

# the sizes MOVSX sign-extends from in a 32-bit operation: 8 or 16 bits
type EbpfHalf is Data:
  EbpfHalfB{}
  EbpfHalfH{}

# the sizes MOVSX sign-extends from in a 64-bit operation: 8, 16 or 32 bits
type EbpfSx is Data:
  EbpfSx8{}
  EbpfSx16{}
  EbpfSx32{}

# byte swaps: to little-endian or big-endian (ALU class), or unconditional
# (ALU64 class)
type EbpfEndKind is Data:
  EbpfToLe{}
  EbpfToBe{}
  EbpfBswap{}

type EbpfEndBits is Data:
  EbpfE16{}
  EbpfE32{}
  EbpfE64{}

type EbpfAtomicSize is Data:
  EbpfAtomicW{}
  EbpfAtomicDW{}

# the atomic operations; fetch: src_reg receives the old value
type EbpfAtomicOp is Data:
  EbpfAtAdd{fetch: Bool}
  EbpfAtOr{fetch: Bool}
  EbpfAtAnd{fetch: Bool}
  EbpfAtXor{fetch: Bool}
  EbpfAtXchg{}
  EbpfAtCmpxchg{}

# what a 64-bit immediate load loads, by its src_reg (RFC 9669, 5.4)
type EbpfLddwKind is Data:
  EbpfLdImm64{}
  EbpfLdMapFd{}
  EbpfLdMapValFd{}
  EbpfLdVarAddr{}
  EbpfLdCodeAddr{}
  EbpfLdMapIdx{}
  EbpfLdMapValIdx{}

# what a call calls, by its src_reg: a helper by static id, a program-local
# function (imm: its offset from the next instruction), a helper by BTF id
type EbpfCallKind is Data:
  EbpfCallHelper{}
  EbpfCallLocal{}
  EbpfCallBtf{}

# A decoded instruction. off and imm hold their fields' bits (off in its
# low 16 bits); the interpreter reads them as signed numbers.
type EbpfInsn is Data:
  EbpfAlu{w: EbpfWidth, op: EbpfAluOp, dst: EbpfReg, src: EbpfSrc}
  EbpfNeg{w: EbpfWidth, dst: EbpfReg}
  EbpfMovsx32{bits: EbpfHalf, dst: EbpfReg, src: EbpfReg}
  EbpfMovsx64{bits: EbpfSx, dst: EbpfReg, src: EbpfReg}
  EbpfEnd{kind: EbpfEndKind, bits: EbpfEndBits, dst: EbpfReg}
  EbpfLddw{kind: EbpfLddwKind, dst: EbpfReg, imm: U32, next: U32}
  EbpfLdx{size: EbpfSize, dst: EbpfReg, src: EbpfReg, off: U32}
  EbpfLdxs{size: EbpfSmall, dst: EbpfReg, src: EbpfReg, off: U32}
  EbpfSt{size: EbpfSize, dst: EbpfReg, off: U32, imm: U32}
  EbpfStx{size: EbpfSize, dst: EbpfReg, src: EbpfReg, off: U32}
  EbpfAtomic{size: EbpfAtomicSize, op: EbpfAtomicOp, dst: EbpfReg, src: EbpfReg, off: U32}
  EbpfLdAbs{size: EbpfSmall, imm: U32}
  EbpfLdInd{size: EbpfSmall, src: EbpfReg, imm: U32}
  EbpfJa{off: U32}
  EbpfJa32{imm: U32}
  EbpfJmp{w: EbpfWidth, cond: EbpfCond, dst: EbpfReg, src: EbpfSrc, off: U32}
  EbpfCall{kind: EbpfCallKind, imm: U32}
  EbpfExit{}

# One 64-bit instruction slot, before byte packing: dst and src are 4 bits,
# off 16 bits and imm 32 bits when stored
type EbpfRaw is Data:
  EbpfRaw{code: U32, dst: U32, src: U32, off: U32, imm: U32}

# Why a memory access failed (memory.bend)
type EbpfMemError is Data:
  EbpfMemOutOfBounds{size: Nat}
  EbpfMemUninit{}
  EbpfMemPointerBytes{}
  EbpfMemPointerStore{}
  EbpfMemMisaligned{}
  EbpfMemDangling{}
  EbpfMemNotMemory{}

# Why the verifier refused a program (cfg.bend, verifier.bend)
type EbpfReject is Data:
  EbpfRejEmpty{}
  EbpfRejTooLong{len: Nat}
  EbpfRejJumpOut{}
  EbpfRejJumpIntoWide{}
  EbpfRejFallsOff{}
  EbpfRejUnreachable{}
  EbpfRejBackEdge{}
  EbpfRejRecursion{}
  EbpfRejCallDepth{}
  EbpfRejCallTarget{}
  EbpfRejUnsupported{}
  EbpfRejRegUninit{}
  EbpfRejWriteFp{}
  EbpfRejPointerArith{}
  EbpfRejPointerCompare{}
  EbpfRejNotPointer{}
  EbpfRejAccess{}
  EbpfRejStackUninit{}
  EbpfRejMisaligned{}
  EbpfRejPointerLeak{}
  EbpfRejHelperUnknown{}
  EbpfRejHelperArg{}
  EbpfRejMapUnknown{}
  EbpfRejReturn{}
  EbpfRejComplexity{}

# Every failure: decoding a program, running one (runtime errors carry the
# instruction index), and verifying one
type EbpfError is Data:
  EbpfErrBadInsn{pc: Nat, code: U32}
  EbpfErrWideTruncated{pc: Nat}
  EbpfErrWideBad{pc: Nat}
  EbpfErrTruncated{len: Nat}
  EbpfErrStoredTooLong{max: Nat}
  EbpfErrPcOut{pc: Nat}
  EbpfErrIntoWide{pc: Nat}
  EbpfErrCallDepth{pc: Nat}
  EbpfErrUnknownHelper{pc: Nat, id: U32}
  EbpfErrUnsupported{pc: Nat}
  EbpfErrBadMap{pc: Nat}
  EbpfErrUninitReg{pc: Nat}
  EbpfErrPointerArith{pc: Nat}
  EbpfErrPointerCompare{pc: Nat}
  EbpfErrWriteFp{pc: Nat}
  EbpfErrNotPointer{pc: Nat}
  EbpfErrExitPointer{pc: Nat}
  EbpfErrMemory{pc: Nat, why: EbpfMemError}
  EbpfErrHelper{pc: Nat, id: U32}
  EbpfErrRejected{pc: Nat, why: EbpfReject}
  EbpfErrComplexity{steps: Nat}

# Registers as numbers

def EbpfReg.num(r: EbpfReg) -> U32:
  match r:
    case EbpfR0{}:
      0
    case EbpfR1{}:
      1
    case EbpfR2{}:
      2
    case EbpfR3{}:
      3
    case EbpfR4{}:
      4
    case EbpfR5{}:
      5
    case EbpfR6{}:
      6
    case EbpfR7{}:
      7
    case EbpfR8{}:
      8
    case EbpfR9{}:
      9
    case EbpfR10{}:
      10

def EbpfReg.pick(hit: Bool, r: EbpfReg, rest: Maybe<&2, EbpfReg>) -> Maybe<&2, EbpfReg>:
  match hit:
    case True{}:
      Some{r}
    case False{}:
      rest

# the register with this number, or None above 10
def EbpfReg.of_num(+n: U32) -> Maybe<&2, EbpfReg>:
  EbpfReg.pick(U32.is_eq(n, 0), EbpfR0{}, EbpfReg.pick(U32.is_eq(n, 1), EbpfR1{}, EbpfReg.pick(U32.is_eq(n, 2), EbpfR2{}, EbpfReg.pick(U32.is_eq(n, 3), EbpfR3{}, EbpfReg.pick(U32.is_eq(n, 4), EbpfR4{}, EbpfReg.pick(U32.is_eq(n, 5), EbpfR5{}, EbpfReg.pick(U32.is_eq(n, 6), EbpfR6{}, EbpfReg.pick(U32.is_eq(n, 7), EbpfR7{}, EbpfReg.pick(U32.is_eq(n, 8), EbpfR8{}, EbpfReg.pick(U32.is_eq(n, 9), EbpfR9{}, EbpfReg.pick(U32.is_eq(n, 10), EbpfR10{}, None{})))))))))))

def EbpfReg.is_r0(r: EbpfReg) -> Bool:
  match r:
    case EbpfR0{}:
      True{}
    case other:
      False{}

# Encoding: the fields of an instruction's first slot

def EbpfWidth.alu(w: EbpfWidth) -> U32:
  match w:
    case EbpfBits32{}:
      4
    case EbpfBits64{}:
      7

def EbpfWidth.jmp(w: EbpfWidth) -> U32:
  match w:
    case EbpfBits32{}:
      6
    case EbpfBits64{}:
      5

def EbpfSrc.bit(s: EbpfSrc) -> U32:
  match s:
    case EbpfK{imm}:
      0
    case EbpfX{r}:
      8

def EbpfSrc.reg(s: EbpfSrc) -> EbpfReg:
  match s:
    case EbpfK{imm}:
      EbpfR0{}
    case EbpfX{r}:
      r

def EbpfSrc.imm(s: EbpfSrc) -> U32:
  match s:
    case EbpfK{imm}:
      imm
    case EbpfX{r}:
      0

def EbpfAluOp.bits(op: EbpfAluOp) -> U32:
  match op:
    case EbpfAdd{}:
      0
    case EbpfSub{}:
      16
    case EbpfMul{}:
      32
    case EbpfDiv{}:
      48
    case EbpfSdiv{}:
      48
    case EbpfOr{}:
      64
    case EbpfAnd{}:
      80
    case EbpfLsh{}:
      96
    case EbpfRsh{}:
      112
    case EbpfMod{}:
      144
    case EbpfSmod{}:
      144
    case EbpfXor{}:
      160
    case EbpfMov{}:
      176
    case EbpfArsh{}:
      192

def EbpfAluOp.off(op: EbpfAluOp) -> U32:
  match op:
    case EbpfSdiv{}:
      1
    case EbpfSmod{}:
      1
    case other:
      0

def EbpfCond.bits(c: EbpfCond) -> U32:
  match c:
    case EbpfJeq{}:
      16
    case EbpfJgt{}:
      32
    case EbpfJge{}:
      48
    case EbpfJset{}:
      64
    case EbpfJne{}:
      80
    case EbpfJsgt{}:
      96
    case EbpfJsge{}:
      112
    case EbpfJlt{}:
      160
    case EbpfJle{}:
      176
    case EbpfJslt{}:
      192
    case EbpfJsle{}:
      208

def EbpfSize.bits(s: EbpfSize) -> U32:
  match s:
    case EbpfSizeW{}:
      0
    case EbpfSizeH{}:
      8
    case EbpfSizeB{}:
      16
    case EbpfSizeDW{}:
      24

def EbpfSmall.bits(s: EbpfSmall) -> U32:
  match s:
    case EbpfSmallW{}:
      0
    case EbpfSmallH{}:
      8
    case EbpfSmallB{}:
      16

def EbpfHalf.off(h: EbpfHalf) -> U32:
  match h:
    case EbpfHalfB{}:
      8
    case EbpfHalfH{}:
      16

def EbpfSx.off(s: EbpfSx) -> U32:
  match s:
    case EbpfSx8{}:
      8
    case EbpfSx16{}:
      16
    case EbpfSx32{}:
      32

def EbpfEndKind.code(k: EbpfEndKind) -> U32:
  match k:
    case EbpfToLe{}:
      212
    case EbpfToBe{}:
      220
    case EbpfBswap{}:
      215

def EbpfEndBits.imm(b: EbpfEndBits) -> U32:
  match b:
    case EbpfE16{}:
      16
    case EbpfE32{}:
      32
    case EbpfE64{}:
      64

def EbpfAtomicSize.code(s: EbpfAtomicSize) -> U32:
  match s:
    case EbpfAtomicW{}:
      195
    case EbpfAtomicDW{}:
      219

def EbpfAtomicOp.fetch_bit(f: Bool) -> U32:
  match f:
    case True{}:
      1
    case False{}:
      0

def EbpfAtomicOp.imm(op: EbpfAtomicOp) -> U32:
  match op:
    case EbpfAtAdd{f}:
      U32.or(0, EbpfAtomicOp.fetch_bit(f))
    case EbpfAtOr{f}:
      U32.or(64, EbpfAtomicOp.fetch_bit(f))
    case EbpfAtAnd{f}:
      U32.or(80, EbpfAtomicOp.fetch_bit(f))
    case EbpfAtXor{f}:
      U32.or(160, EbpfAtomicOp.fetch_bit(f))
    case EbpfAtXchg{}:
      225
    case EbpfAtCmpxchg{}:
      241

# the src_reg of a 64-bit immediate load or a call names its kind
def EbpfLddwKind.reg(k: EbpfLddwKind) -> EbpfReg:
  match k:
    case EbpfLdImm64{}:
      EbpfR0{}
    case EbpfLdMapFd{}:
      EbpfR1{}
    case EbpfLdMapValFd{}:
      EbpfR2{}
    case EbpfLdVarAddr{}:
      EbpfR3{}
    case EbpfLdCodeAddr{}:
      EbpfR4{}
    case EbpfLdMapIdx{}:
      EbpfR5{}
    case EbpfLdMapValIdx{}:
      EbpfR6{}

def EbpfLddwKind.of_reg(r: EbpfReg) -> Maybe<&2, EbpfLddwKind>:
  match r:
    case EbpfR0{}:
      Some{EbpfLdImm64{}}
    case EbpfR1{}:
      Some{EbpfLdMapFd{}}
    case EbpfR2{}:
      Some{EbpfLdMapValFd{}}
    case EbpfR3{}:
      Some{EbpfLdVarAddr{}}
    case EbpfR4{}:
      Some{EbpfLdCodeAddr{}}
    case EbpfR5{}:
      Some{EbpfLdMapIdx{}}
    case EbpfR6{}:
      Some{EbpfLdMapValIdx{}}
    case other:
      None{}

def EbpfCallKind.reg(k: EbpfCallKind) -> EbpfReg:
  match k:
    case EbpfCallHelper{}:
      EbpfR0{}
    case EbpfCallLocal{}:
      EbpfR1{}
    case EbpfCallBtf{}:
      EbpfR2{}

def EbpfCallKind.of_reg(r: EbpfReg) -> Maybe<&2, EbpfCallKind>:
  match r:
    case EbpfR0{}:
      Some{EbpfCallHelper{}}
    case EbpfR1{}:
      Some{EbpfCallLocal{}}
    case EbpfR2{}:
      Some{EbpfCallBtf{}}
    case other:
      None{}

# the opcode of an instruction
def EbpfInsn.code(i: EbpfInsn) -> U32:
  match i:
    case EbpfAlu{w, op, d, s}:
      U32.or(EbpfWidth.alu(w), U32.or(EbpfAluOp.bits(op), EbpfSrc.bit(s)))
    case EbpfNeg{w, d}:
      U32.or(EbpfWidth.alu(w), 128)
    case EbpfMovsx32{b, d, s}:
      188
    case EbpfMovsx64{b, d, s}:
      191
    case EbpfEnd{k, b, d}:
      EbpfEndKind.code(k)
    case EbpfLddw{k, d, lo, hi}:
      24
    case EbpfLdx{size, d, s, off}:
      U32.or(97, EbpfSize.bits(size))
    case EbpfLdxs{size, d, s, off}:
      U32.or(129, EbpfSmall.bits(size))
    case EbpfSt{size, d, off, imm}:
      U32.or(98, EbpfSize.bits(size))
    case EbpfStx{size, d, s, off}:
      U32.or(99, EbpfSize.bits(size))
    case EbpfAtomic{size, op, d, s, off}:
      EbpfAtomicSize.code(size)
    case EbpfLdAbs{size, imm}:
      U32.or(32, EbpfSmall.bits(size))
    case EbpfLdInd{size, s, imm}:
      U32.or(64, EbpfSmall.bits(size))
    case EbpfJa{off}:
      5
    case EbpfJa32{imm}:
      6
    case EbpfJmp{w, c, d, s, off}:
      U32.or(EbpfWidth.jmp(w), U32.or(EbpfCond.bits(c), EbpfSrc.bit(s)))
    case EbpfCall{k, imm}:
      133
    case EbpfExit{}:
      149

# dst_reg (R0 where unused)
def EbpfInsn.dst(i: EbpfInsn) -> EbpfReg:
  match i:
    case EbpfAlu{w, op, d, s}:
      d
    case EbpfNeg{w, d}:
      d
    case EbpfMovsx32{b, d, s}:
      d
    case EbpfMovsx64{b, d, s}:
      d
    case EbpfEnd{k, b, d}:
      d
    case EbpfLddw{k, d, lo, hi}:
      d
    case EbpfLdx{size, d, s, off}:
      d
    case EbpfLdxs{size, d, s, off}:
      d
    case EbpfSt{size, d, off, imm}:
      d
    case EbpfStx{size, d, s, off}:
      d
    case EbpfAtomic{size, op, d, s, off}:
      d
    case EbpfJmp{w, c, d, s, off}:
      d
    case other:
      EbpfR0{}

# src_reg (R0 where unused; the kind of a 64-bit immediate load or a call)
def EbpfInsn.src(i: EbpfInsn) -> EbpfReg:
  match i:
    case EbpfAlu{w, op, d, s}:
      EbpfSrc.reg(s)
    case EbpfMovsx32{b, d, s}:
      s
    case EbpfMovsx64{b, d, s}:
      s
    case EbpfLddw{k, d, lo, hi}:
      EbpfLddwKind.reg(k)
    case EbpfLdx{size, d, s, off}:
      s
    case EbpfLdxs{size, d, s, off}:
      s
    case EbpfStx{size, d, s, off}:
      s
    case EbpfAtomic{size, op, d, s, off}:
      s
    case EbpfLdInd{size, s, imm}:
      s
    case EbpfJmp{w, c, d, s, off}:
      EbpfSrc.reg(s)
    case EbpfCall{k, imm}:
      EbpfCallKind.reg(k)
    case other:
      EbpfR0{}

def EbpfInsn.off(i: EbpfInsn) -> U32:
  match i:
    case EbpfAlu{w, op, d, s}:
      EbpfAluOp.off(op)
    case EbpfMovsx32{b, d, s}:
      EbpfHalf.off(b)
    case EbpfMovsx64{b, d, s}:
      EbpfSx.off(b)
    case EbpfLdx{size, d, s, off}:
      off
    case EbpfLdxs{size, d, s, off}:
      off
    case EbpfSt{size, d, off, imm}:
      off
    case EbpfStx{size, d, s, off}:
      off
    case EbpfAtomic{size, op, d, s, off}:
      off
    case EbpfJa{off}:
      off
    case EbpfJmp{w, c, d, s, off}:
      off
    case other:
      0

def EbpfInsn.imm(i: EbpfInsn) -> U32:
  match i:
    case EbpfAlu{w, op, d, s}:
      EbpfSrc.imm(s)
    case EbpfEnd{k, b, d}:
      EbpfEndBits.imm(b)
    case EbpfLddw{k, d, lo, hi}:
      lo
    case EbpfSt{size, d, off, imm}:
      imm
    case EbpfAtomic{size, op, d, s, off}:
      EbpfAtomicOp.imm(op)
    case EbpfLdAbs{size, imm}:
      imm
    case EbpfLdInd{size, s, imm}:
      imm
    case EbpfJa32{imm}:
      imm
    case EbpfJmp{w, c, d, s, off}:
      EbpfSrc.imm(s)
    case EbpfCall{k, imm}:
      imm
    case other:
      0

# the slots after the first: the second half of a 64-bit immediate load
def EbpfInsn.wide(i: EbpfInsn) -> List<&2, EbpfRaw>:
  match i:
    case EbpfLddw{k, d, lo, hi}:
      [EbpfRaw{0, 0, 0, 0, hi}]
    case other:
      []

# the number of 64-bit slots an instruction takes: 2 for lddw, else 1
def EbpfInsn.slots(i: EbpfInsn) -> Nat:
  match i:
    case EbpfLddw{k, d, lo, hi}:
      2n
    case other:
      1n

def EbpfInsn.first(+i: EbpfInsn) -> EbpfRaw:
  EbpfRaw{EbpfInsn.code(i), EbpfReg.num(EbpfInsn.dst(i)), EbpfReg.num(EbpfInsn.src(i)), EbpfInsn.off(i), EbpfInsn.imm(i)}

# an instruction's slots; unused fields are zero
def EbpfInsn.encode(+i: EbpfInsn) -> List<&2, EbpfRaw>:
  Con{EbpfInsn.first(i), EbpfInsn.wide(i)}

# Decoding

# what one slot decodes to: an instruction, the first half of a 64-bit
# immediate load (which needs the next slot), or nothing RFC 9669 defines
type EbpfDec is Data:
  EbpfDecOne{insn: EbpfInsn}
  EbpfDecWide{kind: EbpfLddwKind, dst: EbpfReg, imm: U32}
  EbpfDecBad{}

def EbpfDec.pick(hit: Bool, d: EbpfDec, rest: EbpfDec) -> EbpfDec:
  match hit:
    case True{}:
      d
    case False{}:
      rest

# d, if ok
def EbpfDec.req(ok: Bool, d: EbpfDec) -> EbpfDec:
  match ok:
    case True{}:
      d
    case False{}:
      EbpfDecBad{}

def EbpfDec.lddw(k: Maybe<&2, EbpfLddwKind>, d: EbpfReg, imm: U32) -> EbpfDec:
  match k:
    case None{}:
      EbpfDecBad{}
    case Some{k}:
      EbpfDecWide{k, d, imm}

def EbpfDec.call(k: Maybe<&2, EbpfCallKind>, imm: U32) -> EbpfDec:
  match k:
    case None{}:
      EbpfDecBad{}
    case Some{k}:
      EbpfDecOne{EbpfCall{k, imm}}

def EbpfDec.both(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

# BEGIN GENERATED by gen/decode.py: decode
def EbpfDec.ld(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 24), EbpfDec.req(U32.is_zero(off), EbpfDec.lddw(EbpfLddwKind.of_reg(s), d, imm)), EbpfDec.pick(U32.is_eq(code, 32), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off))), EbpfDecOne{EbpfLdAbs{EbpfSmallW{}, imm}}), EbpfDec.pick(U32.is_eq(code, 64), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), U32.is_zero(off)), EbpfDecOne{EbpfLdInd{EbpfSmallW{}, s, imm}}), EbpfDec.pick(U32.is_eq(code, 40), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off))), EbpfDecOne{EbpfLdAbs{EbpfSmallH{}, imm}}), EbpfDec.pick(U32.is_eq(code, 72), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), U32.is_zero(off)), EbpfDecOne{EbpfLdInd{EbpfSmallH{}, s, imm}}), EbpfDec.pick(U32.is_eq(code, 48), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off))), EbpfDecOne{EbpfLdAbs{EbpfSmallB{}, imm}}), EbpfDec.pick(U32.is_eq(code, 80), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), U32.is_zero(off)), EbpfDecOne{EbpfLdInd{EbpfSmallB{}, s, imm}}), EbpfDecBad{})))))))

def EbpfDec.ldx(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 97), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdx{EbpfSizeW{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 105), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdx{EbpfSizeH{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 113), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdx{EbpfSizeB{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 121), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdx{EbpfSizeDW{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 129), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdxs{EbpfSmallW{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 137), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdxs{EbpfSmallH{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 145), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfLdxs{EbpfSmallB{}, d, s, off}}), EbpfDecBad{})))))))

def EbpfDec.st(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 98), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfSt{EbpfSizeW{}, d, off, imm}}), EbpfDec.pick(U32.is_eq(code, 106), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfSt{EbpfSizeH{}, d, off, imm}}), EbpfDec.pick(U32.is_eq(code, 114), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfSt{EbpfSizeB{}, d, off, imm}}), EbpfDec.pick(U32.is_eq(code, 122), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfSt{EbpfSizeDW{}, d, off, imm}}), EbpfDecBad{}))))

def EbpfDec.stx(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 99), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfStx{EbpfSizeW{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 107), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfStx{EbpfSizeH{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 115), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfStx{EbpfSizeB{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 123), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfStx{EbpfSizeDW{}, d, s, off}}), EbpfDec.pick(U32.is_eq(code, 195), EbpfDec.pick(U32.is_eq(imm, 0), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtAdd{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 1), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtAdd{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 64), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtOr{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 65), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtOr{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 80), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtAnd{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 81), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtAnd{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 160), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtXor{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 161), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtXor{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 225), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtXchg{}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 241), EbpfDecOne{EbpfAtomic{EbpfAtomicW{}, EbpfAtCmpxchg{}, d, s, off}}, EbpfDecBad{})))))))))), EbpfDec.pick(U32.is_eq(code, 219), EbpfDec.pick(U32.is_eq(imm, 0), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtAdd{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 1), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtAdd{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 64), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtOr{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 65), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtOr{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 80), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtAnd{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 81), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtAnd{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 160), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtXor{False{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 161), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtXor{True{}}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 225), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtXchg{}, d, s, off}}, EbpfDec.pick(U32.is_eq(imm, 241), EbpfDecOne{EbpfAtomic{EbpfAtomicDW{}, EbpfAtCmpxchg{}, d, s, off}}, EbpfDecBad{})))))))))), EbpfDecBad{}))))))

def EbpfDec.alu(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 4), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfAdd{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 12), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfAdd{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 20), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfSub{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 28), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfSub{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 36), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfMul{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 44), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfMul{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 52), EbpfDec.req(EbpfReg.is_r0(s), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfDiv{}, d, EbpfK{imm}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfSdiv{}, d, EbpfK{imm}}}))), EbpfDec.pick(U32.is_eq(code, 60), EbpfDec.req(U32.is_zero(imm), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfDiv{}, d, EbpfX{s}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfSdiv{}, d, EbpfX{s}}}))), EbpfDec.pick(U32.is_eq(code, 68), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfOr{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 76), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfOr{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 84), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfAnd{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 92), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfAnd{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 100), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfLsh{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 108), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfLsh{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 116), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfRsh{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 124), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfRsh{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 148), EbpfDec.req(EbpfReg.is_r0(s), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfMod{}, d, EbpfK{imm}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfSmod{}, d, EbpfK{imm}}}))), EbpfDec.pick(U32.is_eq(code, 156), EbpfDec.req(U32.is_zero(imm), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfMod{}, d, EbpfX{s}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfSmod{}, d, EbpfX{s}}}))), EbpfDec.pick(U32.is_eq(code, 164), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfXor{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 172), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfXor{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 180), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfMov{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 188), EbpfDec.req(U32.is_zero(imm), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfMov{}, d, EbpfX{s}}}, EbpfDec.pick(U32.is_eq(off, 8), EbpfDecOne{EbpfMovsx32{EbpfHalfB{}, d, s}}, EbpfDec.pick(U32.is_eq(off, 16), EbpfDecOne{EbpfMovsx32{EbpfHalfH{}, d, s}}, EbpfDecBad{})))), EbpfDec.pick(U32.is_eq(code, 196), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfArsh{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 204), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits32{}, EbpfArsh{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 132), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), EbpfDec.both(U32.is_zero(off), U32.is_zero(imm))), EbpfDecOne{EbpfNeg{EbpfBits32{}, d}}), EbpfDec.pick(U32.is_eq(code, 212), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDec.pick(U32.is_eq(imm, 16), EbpfDecOne{EbpfEnd{EbpfToLe{}, EbpfE16{}, d}}, EbpfDec.pick(U32.is_eq(imm, 32), EbpfDecOne{EbpfEnd{EbpfToLe{}, EbpfE32{}, d}}, EbpfDec.pick(U32.is_eq(imm, 64), EbpfDecOne{EbpfEnd{EbpfToLe{}, EbpfE64{}, d}}, EbpfDecBad{})))), EbpfDec.pick(U32.is_eq(code, 220), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDec.pick(U32.is_eq(imm, 16), EbpfDecOne{EbpfEnd{EbpfToBe{}, EbpfE16{}, d}}, EbpfDec.pick(U32.is_eq(imm, 32), EbpfDecOne{EbpfEnd{EbpfToBe{}, EbpfE32{}, d}}, EbpfDec.pick(U32.is_eq(imm, 64), EbpfDecOne{EbpfEnd{EbpfToBe{}, EbpfE64{}, d}}, EbpfDecBad{})))), EbpfDecBad{})))))))))))))))))))))))))))

def EbpfDec.jmp(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 21), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJeq{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 29), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJeq{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 37), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJgt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 45), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJgt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 53), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJge{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 61), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJge{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 69), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJset{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 77), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJset{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 85), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJne{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 93), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJne{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 101), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJsgt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 109), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJsgt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 117), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJsge{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 125), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJsge{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 165), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJlt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 173), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJlt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 181), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJle{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 189), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJle{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 197), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJslt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 205), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJslt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 213), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJsle{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 221), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits64{}, EbpfJsle{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 5), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(imm))), EbpfDecOne{EbpfJa{off}}), EbpfDec.pick(U32.is_eq(code, 133), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), U32.is_zero(off)), EbpfDec.call(EbpfCallKind.of_reg(s), imm)), EbpfDec.pick(U32.is_eq(code, 149), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), EbpfDec.both(EbpfReg.is_r0(s), EbpfDec.both(U32.is_zero(off), U32.is_zero(imm)))), EbpfDecOne{EbpfExit{}}), EbpfDecBad{})))))))))))))))))))))))))

def EbpfDec.jmp32(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 22), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJeq{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 30), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJeq{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 38), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJgt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 46), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJgt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 54), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJge{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 62), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJge{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 70), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJset{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 78), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJset{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 86), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJne{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 94), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJne{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 102), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJsgt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 110), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJsgt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 118), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJsge{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 126), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJsge{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 166), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJlt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 174), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJlt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 182), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJle{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 190), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJle{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 198), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJslt{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 206), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJslt{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 214), EbpfDec.req(EbpfReg.is_r0(s), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJsle{}, d, EbpfK{imm}, off}}), EbpfDec.pick(U32.is_eq(code, 222), EbpfDec.req(U32.is_zero(imm), EbpfDecOne{EbpfJmp{EbpfBits32{}, EbpfJsle{}, d, EbpfX{s}, off}}), EbpfDec.pick(U32.is_eq(code, 6), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(d), EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off))), EbpfDecOne{EbpfJa32{imm}}), EbpfDecBad{})))))))))))))))))))))))

def EbpfDec.alu64(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(code, 7), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfAdd{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 15), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfAdd{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 23), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfSub{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 31), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfSub{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 39), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfMul{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 47), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfMul{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 55), EbpfDec.req(EbpfReg.is_r0(s), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfDiv{}, d, EbpfK{imm}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfSdiv{}, d, EbpfK{imm}}}))), EbpfDec.pick(U32.is_eq(code, 63), EbpfDec.req(U32.is_zero(imm), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfDiv{}, d, EbpfX{s}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfSdiv{}, d, EbpfX{s}}}))), EbpfDec.pick(U32.is_eq(code, 71), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfOr{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 79), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfOr{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 87), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfAnd{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 95), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfAnd{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 103), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfLsh{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 111), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfLsh{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 119), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfRsh{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 127), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfRsh{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 151), EbpfDec.req(EbpfReg.is_r0(s), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfMod{}, d, EbpfK{imm}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfSmod{}, d, EbpfK{imm}}}))), EbpfDec.pick(U32.is_eq(code, 159), EbpfDec.req(U32.is_zero(imm), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfMod{}, d, EbpfX{s}}}, EbpfDec.req(U32.is_eq(off, 1), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfSmod{}, d, EbpfX{s}}}))), EbpfDec.pick(U32.is_eq(code, 167), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfXor{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 175), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfXor{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 183), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfMov{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 191), EbpfDec.req(U32.is_zero(imm), EbpfDec.pick(U32.is_zero(off), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfMov{}, d, EbpfX{s}}}, EbpfDec.pick(U32.is_eq(off, 8), EbpfDecOne{EbpfMovsx64{EbpfSx8{}, d, s}}, EbpfDec.pick(U32.is_eq(off, 16), EbpfDecOne{EbpfMovsx64{EbpfSx16{}, d, s}}, EbpfDec.pick(U32.is_eq(off, 32), EbpfDecOne{EbpfMovsx64{EbpfSx32{}, d, s}}, EbpfDecBad{}))))), EbpfDec.pick(U32.is_eq(code, 199), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfArsh{}, d, EbpfK{imm}}}), EbpfDec.pick(U32.is_eq(code, 207), EbpfDec.req(EbpfDec.both(U32.is_zero(imm), U32.is_zero(off)), EbpfDecOne{EbpfAlu{EbpfBits64{}, EbpfArsh{}, d, EbpfX{s}}}), EbpfDec.pick(U32.is_eq(code, 135), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), EbpfDec.both(U32.is_zero(off), U32.is_zero(imm))), EbpfDecOne{EbpfNeg{EbpfBits64{}, d}}), EbpfDec.pick(U32.is_eq(code, 215), EbpfDec.req(EbpfDec.both(EbpfReg.is_r0(s), U32.is_zero(off)), EbpfDec.pick(U32.is_eq(imm, 16), EbpfDecOne{EbpfEnd{EbpfBswap{}, EbpfE16{}, d}}, EbpfDec.pick(U32.is_eq(imm, 32), EbpfDecOne{EbpfEnd{EbpfBswap{}, EbpfE32{}, d}}, EbpfDec.pick(U32.is_eq(imm, 64), EbpfDecOne{EbpfEnd{EbpfBswap{}, EbpfE64{}, d}}, EbpfDecBad{})))), EbpfDecBad{}))))))))))))))))))))))))))

# what one slot's opcode and fields decode to, its registers decoded
def EbpfDec.op(+code: U32, +d: EbpfReg, +s: EbpfReg, +off: U32, +imm: U32) -> EbpfDec:
  EbpfDec.pick(U32.is_eq(U32.and(code, 7), 0), EbpfDec.ld(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 1), EbpfDec.ldx(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 2), EbpfDec.st(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 3), EbpfDec.stx(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 4), EbpfDec.alu(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 5), EbpfDec.jmp(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 6), EbpfDec.jmp32(code, d, s, off, imm), EbpfDec.pick(U32.is_eq(U32.and(code, 7), 7), EbpfDec.alu64(code, d, s, off, imm), EbpfDecBad{}))))))))

# END GENERATED: decode

def EbpfDec.regs(md: Maybe<&2, EbpfReg>, ms: Maybe<&2, EbpfReg>, +code: U32, +off: U32, +imm: U32) -> EbpfDec:
  match md:
    case None{}:
      EbpfDecBad{}
    case Some{d}:
      match ms:
        case None{}:
          EbpfDecBad{}
        case Some{s}:
          EbpfDec.op(code, d, s, off, imm)

# what one slot decodes to
def EbpfRaw.decode(r: EbpfRaw) -> EbpfDec:
  match r:
    case EbpfRaw{code, d, s, off, imm}:
      EbpfDec.regs(EbpfReg.of_num(d), EbpfReg.of_num(s), code, off, imm)

def EbpfRaw.code(r: EbpfRaw) -> U32:
  match r:
    case EbpfRaw{code, d, s, off, imm}:
      code

def EbpfRaw.second.go(ok: Bool, imm: U32) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{imm}
    case False{}:
      None{}

# the second slot of a 64-bit immediate load: opcode, registers and offset zero
def EbpfRaw.second(r: EbpfRaw) -> Maybe<&2, U32>:
  match r:
    case EbpfRaw{code, d, s, off, imm}:
      EbpfRaw.second.go(EbpfDec.both(U32.is_zero(code), EbpfDec.both(U32.is_zero(d), EbpfDec.both(U32.is_zero(s), U32.is_zero(off)))), imm)

# Programs. Decoding is one pass over the slots, as a tail call: the state
# is the instructions so far (last first), a 64-bit immediate load waiting
# for its second slot, or the first failure.

type EbpfDecState is Data:
  EbpfDecOk{acc: List<&2, EbpfInsn>}
  EbpfDecHalf{kind: EbpfLddwKind, dst: EbpfReg, imm: U32, acc: List<&2, EbpfInsn>}
  EbpfDecFail{e: EbpfError}

def ebpf_decode.first(d: EbpfDec, +pc: Nat, code: U32, acc: List<&2, EbpfInsn>) -> EbpfDecState:
  match d:
    case EbpfDecOne{i}:
      EbpfDecOk{Con{i, acc}}
    case EbpfDecWide{k, dst, imm}:
      EbpfDecHalf{k, dst, imm, acc}
    case EbpfDecBad{}:
      EbpfDecFail{EbpfErrBadInsn{pc, code}}

def ebpf_decode.second(m: Maybe<&2, U32>, +pc: Nat, k: EbpfLddwKind, dst: EbpfReg, imm: U32, acc: List<&2, EbpfInsn>) -> EbpfDecState:
  match m:
    case Some{hi}:
      EbpfDecOk{Con{EbpfLddw{k, dst, imm, hi}, acc}}
    case None{}:
      EbpfDecFail{EbpfErrWideBad{pc}}

def ebpf_decode.go(rs: List<&2, EbpfRaw>, +pc: Nat, st: EbpfDecState) -> Result<&2, &2, EbpfError, List<&2, EbpfInsn>>:
  match rs:
    case Nil{}:
      match st:
        case EbpfDecOk{acc}:
          Done{List.reverse(&2, EbpfInsn, acc)}
        case EbpfDecHalf{k, dst, imm, acc}:
          Fail{EbpfErrWideTruncated{Nat.sub(pc, 1n)}}
        case EbpfDecFail{e}:
          Fail{e}
    case Con{+r, t}:
      match st:
        case EbpfDecOk{acc}:
          ebpf_decode.go(t, 1n+pc, ebpf_decode.first(EbpfRaw.decode(r), pc, EbpfRaw.code(r), acc))
        case EbpfDecHalf{k, dst, imm, acc}:
          ebpf_decode.go(t, 1n+pc, ebpf_decode.second(EbpfRaw.second(r), pc, k, dst, imm, acc))
        case EbpfDecFail{e}:
          Fail{e}

# a program's instructions, from its slots: the first slot RFC 9669 does
# not define fails (EbpfErrBadInsn{pc, code}, pc its slot), as does a 64-bit
# immediate load whose second slot is missing or not zero where it must be
def ebpf_decode(rs: List<&2, EbpfRaw>) -> Result<&2, &2, EbpfError, List<&2, EbpfInsn>>:
  ebpf_decode.go(rs, 0n, EbpfDecOk{Nil{}})

# the structural form of encoding (PROOF.bend ties ebpf_encode to it)
def ebpf_encode.ref(p: List<&2, EbpfInsn>) -> List<&2, EbpfRaw>:
  match p:
    case Nil{}:
      Nil{}
    case Con{+i, t}:
      List.append(&2, EbpfRaw, EbpfInsn.encode(i), ebpf_encode.ref(t))

# the slots, last first, onto acc
def ebpf_encode.go(p: List<&2, EbpfInsn>, acc: List<&2, EbpfRaw>) -> List<&2, EbpfRaw>:
  match p:
    case Nil{}:
      acc
    case Con{+i, t}:
      ebpf_encode.go(t, List.reverse.go(&2, EbpfRaw, EbpfInsn.encode(i), acc))

# a program's slots
def ebpf_encode(p: List<&2, EbpfInsn>) -> List<&2, EbpfRaw>:
  List.reverse(&2, EbpfRaw, ebpf_encode.go(p, Nil{}))

# the number of slots a program takes
def ebpf_slots.go(p: List<&2, EbpfInsn>, n: Nat) -> Nat:
  match p:
    case Nil{}:
      n
    case Con{i, t}:
      ebpf_slots.go(t, Nat.add(EbpfInsn.slots(i), n))

def ebpf_slots(p: List<&2, EbpfInsn>) -> Nat:
  ebpf_slots.go(p, 0n)

# Stored programs: 8 bytes per slot, the fields in the host's byte order
# (RFC 9669, 3: on a little-endian host the register byte is
# src_reg << 4 | dst_reg; on a big-endian host, dst_reg << 4 | src_reg)

def EbpfRaw.to_octets(order: C.BpfOrder, r: EbpfRaw) -> B.Octets:
  match order:
    case C.BpfLittle{}:
      match r:
        case EbpfRaw{code, d, s, off, imm}:
          B.Octets.concat([B.Octets.of_list([code, U32.or(U32.shln(U32.and(s, 15), 4n), U32.and(d, 15))]), B.Octets.le16(off), B.Octets.le32(imm)])
    case C.BpfBig{}:
      match r:
        case EbpfRaw{code, d, s, off, imm}:
          B.Octets.concat([B.Octets.of_list([code, U32.or(U32.shln(U32.and(d, 15), 4n), U32.and(s, 15))]), B.Octets.be16(off), B.Octets.be32(imm)])

def ebpf_to_octets.go(rs: List<&2, EbpfRaw>, +order: C.BpfOrder, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      ebpf_to_octets.go(t, order, Con{EbpfRaw.to_octets(order, r), acc})

# a program's slots as bytes
def ebpf_to_octets(+order: C.BpfOrder, rs: List<&2, EbpfRaw>) -> B.Octets:
  B.Octets.concat(List.reverse(&2, B.Octets, ebpf_to_octets.go(rs, order, Nil{})))

def ebpf_field(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

def EbpfRaw.of_regs(order: C.BpfOrder, +b: U32, code: U32, off: U32, imm: U32) -> EbpfRaw:
  match order:
    case C.BpfLittle{}:
      EbpfRaw{code, U32.and(b, 15), U32.shrn(b, 4n), off, imm}
    case C.BpfBig{}:
      EbpfRaw{code, U32.shrn(b, 4n), U32.and(b, 15), off, imm}

def EbpfRaw.of_octets(order: C.BpfOrder, +o: B.Octets) -> EbpfRaw:
  match order:
    case C.BpfLittle{}:
      EbpfRaw.of_regs(C.BpfLittle{}, ebpf_field(B.Octets.at(o, 1n)), ebpf_field(B.Octets.at(o, 0n)), ebpf_field(B.Octets.le16_at(o, 2n)), ebpf_field(B.Octets.le32_at(o, 4n)))
    case C.BpfBig{}:
      EbpfRaw.of_regs(C.BpfBig{}, ebpf_field(B.Octets.at(o, 1n)), ebpf_field(B.Octets.at(o, 0n)), ebpf_field(B.Octets.be16_at(o, 2n)), ebpf_field(B.Octets.be32_at(o, 4n)))

def ebpf_of_octets.go(n: Nat, +order: C.BpfOrder, +o: B.Octets, acc: List<&2, EbpfRaw>) -> List<&2, EbpfRaw>:
  match n:
    case 0n:
      List.reverse(&2, EbpfRaw, acc)
    case 1n+p:
      ebpf_of_octets.go(p, order, B.Octets.drop(8n, o), Con{EbpfRaw.of_octets(order, B.Octets.take(8n, o)), acc})

def ebpf_of_octets.rem(r: Nat, q: Nat, +order: C.BpfOrder, +o: B.Octets, +len: Nat) -> Result<&2, &2, EbpfError, List<&2, EbpfRaw>>:
  match r:
    case 0n:
      Done{ebpf_of_octets.go(q, order, o, Nil{})}
    case 1n+p:
      Fail{EbpfErrTruncated{len}}

def ebpf_of_octets.fin(+order: C.BpfOrder, +o: B.Octets, +len: Nat, qr: Nat & Nat) -> Result<&2, &2, EbpfError, List<&2, EbpfRaw>>:
  (q, r) = qr
  ebpf_of_octets.rem(r, q, order, o, len)

def ebpf_of_octets.fits(over: Maybe<&2, U32>, max: Nat, +order: C.BpfOrder, +o: B.Octets) -> Result<&2, &2, EbpfError, List<&2, EbpfRaw>>:
  match over:
    case Some{b}:
      Fail{EbpfErrStoredTooLong{max}}
    case None{}:
      +len = B.Octets.len(o)
      ebpf_of_octets.fin(order, o, len, Nat.divmod(len, 8n))

# a stored program's slots: at most max bytes (checked first, by looking for
# the byte at offset max), a multiple of 8
def ebpf_of_octets_with(+max: Nat, +order: C.BpfOrder, +o: B.Octets) -> Result<&2, &2, EbpfError, List<&2, EbpfRaw>>:
  ebpf_of_octets.fits(B.Octets.at(o, max), max, order, o)

# 8 bytes for each of 1,000,000 slots (the kernel's BPF_COMPLEXITY_LIMIT_INSNS)
def ebpf_octets_max() -> Nat:
  Nat.mul(8n, 1000000n)

def ebpf_of_octets(+order: C.BpfOrder, o: B.Octets) -> Result<&2, &2, EbpfError, List<&2, EbpfRaw>>:
  ebpf_of_octets_with(ebpf_octets_max(), order, o)
