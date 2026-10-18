# bend-osdev-ebpf: the arithmetic of eBPF instructions, on values (RFC 9669,
# "BPF Instruction Set Architecture (ISA)", 4.1 to 4.3).
#
# 64-bit operations (ALU64, JMP) work on W64 (bend-osdev-word64), 32-bit ones
# (ALU, JMP32) on U32; both wrap. A 64-bit operation with an immediate sign
# extends it from 32 to 64 bits; a 32-bit operation uses the immediate's 32
# bits and zero extends its result into the register (the interpreter does
# that). Division by zero gives 0; modulo by zero leaves the dividend (for
# ALU, its low 32 bits). Signed division truncates toward zero, and signed
# modulo follows it (a % n = a - n * trunc(a / n), so -13 % 3 == -1).
# Shifts use the low 6 (64-bit) or 5 (32-bit) bits of the amount.
import Base
import ../word64/word64.bend as W
import ../bpf/insn.bend as C
import ./insn.bend as I

# Sign extension

def ebpf_fill(neg: Bool) -> U32:
  match neg:
    case True{}:
      4294967295
    case False{}:
      0

# the 32-bit word as a signed 64-bit value
def ebpf_sext32(+v: U32) -> W.W64:
  W.W64.from_parts(ebpf_fill(U32.is_ge(v, 2147483648)), v)

def ebpf_zext32(v: U32) -> W.W64:
  W.W64.from_u32(v)

def ebpf_sext_low.go(neg: Bool, low: U32, +mask: U32) -> U32:
  match neg:
    case True{}:
      U32.or(low, U32.not(mask))
    case False{}:
      low

# the low 8 or 16 bits of v, sign extended to 32 bits
def ebpf_sext8(v: U32) -> U32:
  +low = U32.and(255, v)
  ebpf_sext_low.go(U32.is_ge(low, 128), low, 255)

def ebpf_sext16(v: U32) -> U32:
  +low = U32.and(65535, v)
  ebpf_sext_low.go(U32.is_ge(low, 32768), low, 65535)

# an instruction's offset field as a signed 64-bit value
def ebpf_off64(off: U32) -> W.W64:
  ebpf_sext32(ebpf_sext16(off))

# 64-bit helpers

def ebpf_top64() -> W.W64:
  W.W64.from_parts(2147483648, 0)

def ebpf_isneg64(a: W.W64) -> Bool:
  U32.is_ge(W.W64.hi(a), 2147483648)

def ebpf_negate64(a: W.W64) -> W.W64:
  W.W64.sub(W.W64.zero(), a)

def ebpf_abs64.go(neg: Bool, a: W.W64) -> W.W64:
  match neg:
    case True{}:
      ebpf_negate64(a)
    case False{}:
      a

def ebpf_abs64(+a: W.W64) -> W.W64:
  ebpf_abs64.go(ebpf_isneg64(a), a)

def ebpf_shift64(b: W.W64) -> Nat:
  U32.to_nat(U32.and(63, W.W64.lo(b)))

def ebpf_div64(zero: Bool, +a: W.W64, +b: W.W64) -> W.W64:
  match zero:
    case True{}:
      W.W64.zero()
    case False{}:
      W.W64.div(a, b)

def ebpf_mod64(zero: Bool, +a: W.W64, +b: W.W64) -> W.W64:
  match zero:
    case True{}:
      a
    case False{}:
      W.W64.mod(a, b)

def ebpf_sdiv64(zero: Bool, +a: W.W64, +b: W.W64) -> W.W64:
  match zero:
    case True{}:
      W.W64.zero()
    case False{}:
      ebpf_abs64.go(Bool.xor(ebpf_isneg64(a), ebpf_isneg64(b)), W.W64.div(ebpf_abs64(a), ebpf_abs64(b)))

def ebpf_smod64(zero: Bool, +a: W.W64, +b: W.W64) -> W.W64:
  match zero:
    case True{}:
      a
    case False{}:
      ebpf_abs64.go(ebpf_isneg64(a), W.W64.mod(ebpf_abs64(a), ebpf_abs64(b)))

def ebpf_arsh64(neg: Bool, +a: W.W64, +n: Nat) -> W.W64:
  match neg:
    case True{}:
      W.W64.not(W.W64.shr(W.W64.not(a), n))
    case False{}:
      W.W64.shr(a, n)

# dst op src, 64 bits wide (MOV answers src)
def ebpf_alu64(op: I.EbpfAluOp, +a: W.W64, +b: W.W64) -> W.W64:
  match op:
    case I.EbpfAdd{}:
      W.W64.add(a, b)
    case I.EbpfSub{}:
      W.W64.sub(a, b)
    case I.EbpfMul{}:
      W.W64.mul(a, b)
    case I.EbpfDiv{}:
      ebpf_div64(W.W64.is_zero(b), a, b)
    case I.EbpfSdiv{}:
      ebpf_sdiv64(W.W64.is_zero(b), a, b)
    case I.EbpfOr{}:
      W.W64.or(a, b)
    case I.EbpfAnd{}:
      W.W64.and(a, b)
    case I.EbpfLsh{}:
      W.W64.shl(a, ebpf_shift64(b))
    case I.EbpfRsh{}:
      W.W64.shr(a, ebpf_shift64(b))
    case I.EbpfMod{}:
      ebpf_mod64(W.W64.is_zero(b), a, b)
    case I.EbpfSmod{}:
      ebpf_smod64(W.W64.is_zero(b), a, b)
    case I.EbpfXor{}:
      W.W64.xor(a, b)
    case I.EbpfMov{}:
      b
    case I.EbpfArsh{}:
      ebpf_arsh64(ebpf_isneg64(a), a, ebpf_shift64(b))

# 32-bit helpers

def ebpf_isneg32(a: U32) -> Bool:
  U32.is_ge(a, 2147483648)

def ebpf_abs32.go(neg: Bool, a: U32) -> U32:
  match neg:
    case True{}:
      U32.sub(0, a)
    case False{}:
      a

def ebpf_abs32(+a: U32) -> U32:
  ebpf_abs32.go(ebpf_isneg32(a), a)

def ebpf_shift32(b: U32) -> Nat:
  U32.to_nat(U32.and(31, b))

def ebpf_div32(zero: Bool, +a: U32, +b: U32) -> U32:
  match zero:
    case True{}:
      0
    case False{}:
      U32.div(a, b)

def ebpf_mod32(zero: Bool, +a: U32, +b: U32) -> U32:
  match zero:
    case True{}:
      a
    case False{}:
      U32.mod(a, b)

def ebpf_sdiv32(zero: Bool, +a: U32, +b: U32) -> U32:
  match zero:
    case True{}:
      0
    case False{}:
      ebpf_abs32.go(Bool.xor(ebpf_isneg32(a), ebpf_isneg32(b)), U32.div(ebpf_abs32(a), ebpf_abs32(b)))

def ebpf_smod32(zero: Bool, +a: U32, +b: U32) -> U32:
  match zero:
    case True{}:
      a
    case False{}:
      ebpf_abs32.go(ebpf_isneg32(a), U32.mod(ebpf_abs32(a), ebpf_abs32(b)))

def ebpf_arsh32(neg: Bool, +a: U32, +n: Nat) -> U32:
  match neg:
    case True{}:
      U32.not(U32.shrn(U32.not(a), n))
    case False{}:
      U32.shrn(a, n)

# dst op src, 32 bits wide
def ebpf_alu32(op: I.EbpfAluOp, +a: U32, +b: U32) -> U32:
  match op:
    case I.EbpfAdd{}:
      U32.add(a, b)
    case I.EbpfSub{}:
      U32.sub(a, b)
    case I.EbpfMul{}:
      U32.mul(a, b)
    case I.EbpfDiv{}:
      ebpf_div32(U32.is_zero(b), a, b)
    case I.EbpfSdiv{}:
      ebpf_sdiv32(U32.is_zero(b), a, b)
    case I.EbpfOr{}:
      U32.or(a, b)
    case I.EbpfAnd{}:
      U32.and(a, b)
    case I.EbpfLsh{}:
      U32.shln(a, ebpf_shift32(b))
    case I.EbpfRsh{}:
      U32.shrn(a, ebpf_shift32(b))
    case I.EbpfMod{}:
      ebpf_mod32(U32.is_zero(b), a, b)
    case I.EbpfSmod{}:
      ebpf_smod32(U32.is_zero(b), a, b)
    case I.EbpfXor{}:
      U32.xor(a, b)
    case I.EbpfMov{}:
      b
    case I.EbpfArsh{}:
      ebpf_arsh32(ebpf_isneg32(a), a, ebpf_shift32(b))

# A whole ALU or ALU64 instruction on register values: dst, and the source
# operand as the register holds it (for K, the immediate sign extended to
# 64 bits); the 32-bit form uses both operands' low halves and zero extends
def ebpf_alu(w: I.EbpfWidth, op: I.EbpfAluOp, a: W.W64, b: W.W64) -> W.W64:
  match w:
    case I.EbpfBits64{}:
      ebpf_alu64(op, a, b)
    case I.EbpfBits32{}:
      ebpf_zext32(ebpf_alu32(op, W.W64.lo(a), W.W64.lo(b)))

def ebpf_neg(w: I.EbpfWidth, a: W.W64) -> W.W64:
  match w:
    case I.EbpfBits64{}:
      ebpf_negate64(a)
    case I.EbpfBits32{}:
      ebpf_zext32(U32.sub(0, W.W64.lo(a)))

# MOVSX: 32-bit (8 or 16 bits, the upper half zeroed) and 64-bit
def ebpf_movsx32(b: I.EbpfHalf, a: W.W64) -> W.W64:
  match b:
    case I.EbpfHalfB{}:
      ebpf_zext32(ebpf_sext8(W.W64.lo(a)))
    case I.EbpfHalfH{}:
      ebpf_zext32(ebpf_sext16(W.W64.lo(a)))

def ebpf_movsx64(b: I.EbpfSx, a: W.W64) -> W.W64:
  match b:
    case I.EbpfSx8{}:
      ebpf_sext32(ebpf_sext8(W.W64.lo(a)))
    case I.EbpfSx16{}:
      ebpf_sext32(ebpf_sext16(W.W64.lo(a)))
    case I.EbpfSx32{}:
      ebpf_sext32(W.W64.lo(a))

# a value loaded by a sign-extending load (MEMSX) of this size
def ebpf_load_sx(s: I.EbpfSmall, a: W.W64) -> W.W64:
  match s:
    case I.EbpfSmallB{}:
      ebpf_sext32(ebpf_sext8(W.W64.lo(a)))
    case I.EbpfSmallH{}:
      ebpf_sext32(ebpf_sext16(W.W64.lo(a)))
    case I.EbpfSmallW{}:
      ebpf_sext32(W.W64.lo(a))

# Byte swaps (END). The host's byte order decides which of TO_LE and TO_BE
# swaps; the other only truncates to the width.

def ebpf_bswap16(+v: U32) -> U32:
  U32.or(U32.shln(U32.and(255, v), 8n), U32.and(255, U32.shrn(v, 8n)))

def ebpf_bswap32(+v: U32) -> U32:
  U32.or(U32.or(U32.shln(U32.and(255, v), 24n), U32.shln(U32.and(255, U32.shrn(v, 8n)), 16n)), U32.or(U32.shln(U32.and(255, U32.shrn(v, 16n)), 8n), U32.and(255, U32.shrn(v, 24n))))

def ebpf_bswap64(+a: W.W64) -> W.W64:
  W.W64.from_parts(ebpf_bswap32(W.W64.lo(a)), ebpf_bswap32(W.W64.hi(a)))

def ebpf_trunc(b: I.EbpfEndBits, +a: W.W64) -> W.W64:
  match b:
    case I.EbpfE16{}:
      ebpf_zext32(U32.and(65535, W.W64.lo(a)))
    case I.EbpfE32{}:
      ebpf_zext32(W.W64.lo(a))
    case I.EbpfE64{}:
      a

def ebpf_swap(b: I.EbpfEndBits, +a: W.W64) -> W.W64:
  match b:
    case I.EbpfE16{}:
      ebpf_zext32(ebpf_bswap16(W.W64.lo(a)))
    case I.EbpfE32{}:
      ebpf_zext32(ebpf_bswap32(W.W64.lo(a)))
    case I.EbpfE64{}:
      ebpf_bswap64(a)

def ebpf_end(k: I.EbpfEndKind, order: C.BpfOrder, b: I.EbpfEndBits, +a: W.W64) -> W.W64:
  match k:
    case I.EbpfToLe{}:
      match order:
        case C.BpfLittle{}:
          ebpf_trunc(b, a)
        case C.BpfBig{}:
          ebpf_swap(b, a)
    case I.EbpfToBe{}:
      match order:
        case C.BpfLittle{}:
          ebpf_swap(b, a)
        case C.BpfBig{}:
          ebpf_trunc(b, a)
    case I.EbpfBswap{}:
      ebpf_swap(b, a)

# Jump conditions

def ebpf_flip64(a: W.W64) -> W.W64:
  W.W64.xor(a, ebpf_top64())

def ebpf_cond64(c: I.EbpfCond, +a: W.W64, +b: W.W64) -> Bool:
  match c:
    case I.EbpfJeq{}:
      W.W64.is_eq(a, b)
    case I.EbpfJgt{}:
      W.W64.is_gt(a, b)
    case I.EbpfJge{}:
      W.W64.is_ge(a, b)
    case I.EbpfJset{}:
      Bool.not(W.W64.is_zero(W.W64.and(a, b)))
    case I.EbpfJne{}:
      Bool.not(W.W64.is_eq(a, b))
    case I.EbpfJsgt{}:
      W.W64.is_gt(ebpf_flip64(a), ebpf_flip64(b))
    case I.EbpfJsge{}:
      W.W64.is_ge(ebpf_flip64(a), ebpf_flip64(b))
    case I.EbpfJlt{}:
      W.W64.is_lt(a, b)
    case I.EbpfJle{}:
      W.W64.is_le(a, b)
    case I.EbpfJslt{}:
      W.W64.is_lt(ebpf_flip64(a), ebpf_flip64(b))
    case I.EbpfJsle{}:
      W.W64.is_le(ebpf_flip64(a), ebpf_flip64(b))

def ebpf_flip32(a: U32) -> U32:
  U32.xor(a, 2147483648)

def ebpf_cond32(c: I.EbpfCond, +a: U32, +b: U32) -> Bool:
  match c:
    case I.EbpfJeq{}:
      U32.is_eq(a, b)
    case I.EbpfJgt{}:
      U32.is_gt(a, b)
    case I.EbpfJge{}:
      U32.is_ge(a, b)
    case I.EbpfJset{}:
      Bool.not(U32.is_zero(U32.and(a, b)))
    case I.EbpfJne{}:
      Bool.not(U32.is_eq(a, b))
    case I.EbpfJsgt{}:
      U32.is_gt(ebpf_flip32(a), ebpf_flip32(b))
    case I.EbpfJsge{}:
      U32.is_ge(ebpf_flip32(a), ebpf_flip32(b))
    case I.EbpfJlt{}:
      U32.is_lt(a, b)
    case I.EbpfJle{}:
      U32.is_le(a, b)
    case I.EbpfJslt{}:
      U32.is_lt(ebpf_flip32(a), ebpf_flip32(b))
    case I.EbpfJsle{}:
      U32.is_le(ebpf_flip32(a), ebpf_flip32(b))

# a JMP or JMP32 condition on register values (the 32-bit form compares
# the low halves)
def ebpf_cond(w: I.EbpfWidth, c: I.EbpfCond, a: W.W64, b: W.W64) -> Bool:
  match w:
    case I.EbpfBits64{}:
      ebpf_cond64(c, a, b)
    case I.EbpfBits32{}:
      ebpf_cond32(c, W.W64.lo(a), W.W64.lo(b))

# the source operand of an ALU or jump instruction with an immediate, as a
# register would hold it: sign extended (the 32-bit forms use its low half,
# which is the immediate itself)
def ebpf_imm(imm: U32) -> W.W64:
  ebpf_sext32(imm)
