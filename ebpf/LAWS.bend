# DRAFT: not yet reviewed by the maintainer
#
# Laws for bend-osdev-ebpf, over its public interface.
#
# Properties, for every input:
#   * memory safety: a load or a store whose bytes fall outside the region
#     is an error, never a value (load_oob, store_oob) -- the central
#     guarantee of the memory model;
#   * a stored program longer than the byte limit is refused whatever its
#     bytes (octets_over_limit), as in bend-osdev-bpf.
# Each has a satisfiability witness, so no hypothesis is vacuous.
#
# Vectors (the specification's semantics, proved by computation):
#   * RFC 9669's arithmetic for the ALU operations (wrapping add and sub,
#     32-bit zero extension, shift-amount masking, arithmetic shift, signed
#     division, byte swap);
#   * decoding the encoding of a program that uses every instruction form
#     gives it back (round_trip);
#   * the interpreter runs (a move, a stack spill and reload, division by
#     zero) and the verifier's verdicts (accept, and rejections for an
#     uninitialised read, an out-of-bounds load, and a pointer returned).
#
# The full soundness theorem (a verified program never faults at run time)
# is not proved; what is proved is the memory model's bounds safety above,
# on which that theorem would rest, plus the control-flow checker's
# structure exercised by the vectors. See the README.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bpf/insn.bend as C
import ./insn.bend as I
import ./alu.bend as A
import ./memory.bend as M
import ./helpers.bend as H
import ./interp.bend as R
import ./cfg.bend as G
import ./verifier.bend as V
import ./ebpf.bend as E

# --- memory safety, for every input ---

law load_oob:
  for +m: M.EbpfMem
  for +r: M.EbpfRegion
  for +addr: W.W64
  for +s: I.EbpfSize
  for +l: U32
  for hlen: {M.EbpfMem.region_len(m, r) == Some{l} : Maybe<&2, U32>}
  for hob: {M.ebpf_in_bounds(l, addr, M.EbpfSize.bytes(s)) == False{} : Bool}
  {M.EbpfMem.load(m, r, addr, s) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfValue>}

law store_oob:
  for +m: M.EbpfMem
  for +r: M.EbpfRegion
  for +addr: W.W64
  for +s: I.EbpfSize
  for +v: M.EbpfValue
  for +l: U32
  for hlen: {M.EbpfMem.region_len(m, r) == Some{l} : Maybe<&2, U32>}
  for hob: {M.ebpf_in_bounds(l, addr, M.EbpfSize.bytes(s)) == False{} : Bool}
  {M.EbpfMem.store(m, r, addr, s, v) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfMem>}

# a stored program with a byte at offset max (so more than max bytes) is
# refused, whatever its bytes and byte order
law octets_over_limit:
  for +max: Nat
  for +order: C.BpfOrder
  for +o: B.Octets
  for b: U32
  for e: {B.Octets.at(o, max) == Some{b} : Maybe<&2, U32>}
  {I.ebpf_of_octets_with(max, order, o) == Fail{I.EbpfErrStoredTooLong{max}} : Result<&2, &2, I.EbpfError, List<&2, I.EbpfRaw>>}

# --- witnesses, so the hypotheses above are satisfiable ---

# a 4-byte context, read at offset 8 for 4 bytes: in range? no
law witness_load_oob:
  exs m: M.EbpfMem
  { M.EbpfMem.region_len(m, M.EbpfRgnCtx{}) == Some{4} : Maybe<&2, U32> } &
  { M.ebpf_in_bounds(4, W.W64.from_u32(8), M.EbpfSize.bytes(I.EbpfSizeW{})) == False{} : Bool }

law witness_octets_over:
  exs o: B.Octets
  { B.Octets.at(o, 8n) == Some{0} : Maybe<&2, U32> }

# --- RFC 9669 arithmetic, as vectors ---

# add wraps at 2^64: 0xFFFFFFFFFFFFFFFF + 1 == 0
law alu_add_wraps:
  {A.ebpf_alu(I.EbpfBits64{}, I.EbpfAdd{}, W.W64.max(), W.W64.one()) == W.W64.zero() : W.W64}

# sub borrows: 0 - 1 == 0xFFFFFFFFFFFFFFFF
law alu_sub_borrows:
  {A.ebpf_alu(I.EbpfBits64{}, I.EbpfSub{}, W.W64.zero(), W.W64.one()) == W.W64.max() : W.W64}

# a 32-bit op zero-extends: (0xFFFFFFFF + 1) as 32 bits == 0
law alu_add32_zext:
  {A.ebpf_alu(I.EbpfBits32{}, I.EbpfAdd{}, W.W64.from_u32(4294967295), W.W64.one()) == W.W64.zero() : W.W64}

# a 64-bit shift uses the low 6 bits of the amount: 1 << 65 == 1 << 1 == 2
law alu_lsh_masks:
  {A.ebpf_alu(I.EbpfBits64{}, I.EbpfLsh{}, W.W64.one(), W.W64.from_u32(65)) == W.W64.from_u32(2) : W.W64}

# arithmetic shift keeps the sign bit: 0x8000000000000000 >>s 1 == 0xC000000000000000
law alu_arsh_signed:
  {A.ebpf_alu(I.EbpfBits64{}, I.EbpfArsh{}, W.W64.from_parts(2147483648, 0), W.W64.one()) == W.W64.from_parts(3221225472, 0) : W.W64}

# signed division truncates toward zero: (-13) / 3 == -4
law alu_sdiv_neg:
  {A.ebpf_alu(I.EbpfBits64{}, I.EbpfSdiv{}, W.W64.from_parts(4294967295, 4294967283), W.W64.from_u32(3)) == W.W64.from_parts(4294967295, 4294967292) : W.W64}

# byte swap of 0x0000000000000001 is 0x0100000000000000
law alu_bswap64:
  {A.ebpf_bswap64(W.W64.one()) == W.W64.from_parts(16777216, 0) : W.W64}

# --- encode/decode round trip, over a program using every instruction form ---

law round_trip:
  {I.ebpf_decode(I.ebpf_encode(sample_program())) == Done{sample_program()} : Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>}

# a program with one of each instruction shape (see PROOF.bend for the def)
def sample_program() -> List<&2, I.EbpfInsn>:
  [ I.EbpfLddw{I.EbpfLdImm64{}, I.EbpfR1{}, 305419896, 2271560481}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfAdd{}, I.EbpfR1{}, I.EbpfK{7}}
  , I.EbpfAlu{I.EbpfBits32{}, I.EbpfMov{}, I.EbpfR2{}, I.EbpfX{I.EbpfR1{}}}
  , I.EbpfNeg{I.EbpfBits64{}, I.EbpfR2{}}
  , I.EbpfMovsx32{I.EbpfHalfB{}, I.EbpfR3{}, I.EbpfR2{}}
  , I.EbpfMovsx64{I.EbpfSx16{}, I.EbpfR3{}, I.EbpfR2{}}
  , I.EbpfEnd{I.EbpfToBe{}, I.EbpfE32{}, I.EbpfR3{}}
  , I.EbpfEnd{I.EbpfBswap{}, I.EbpfE64{}, I.EbpfR3{}}
  , I.EbpfStx{I.EbpfSizeDW{}, I.EbpfR10{}, I.EbpfR3{}, 65528}
  , I.EbpfSt{I.EbpfSizeW{}, I.EbpfR10{}, 65520, 42}
  , I.EbpfLdx{I.EbpfSizeDW{}, I.EbpfR4{}, I.EbpfR10{}, 65528}
  , I.EbpfLdxs{I.EbpfSmallH{}, I.EbpfR5{}, I.EbpfR10{}, 65520}
  , I.EbpfAtomic{I.EbpfAtomicDW{}, I.EbpfAtAdd{True{}}, I.EbpfR10{}, I.EbpfR4{}, 65528}
  , I.EbpfAtomic{I.EbpfAtomicW{}, I.EbpfAtCmpxchg{}, I.EbpfR10{}, I.EbpfR5{}, 65520}
  , I.EbpfJmp{I.EbpfBits64{}, I.EbpfJeq{}, I.EbpfR4{}, I.EbpfK{0}, 1}
  , I.EbpfJa{0}
  , I.EbpfJa32{0}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfK{0}}
  , I.EbpfExit{}
  ]

# --- the interpreter, as vectors ---

# mov r0, #9 ; exit  answers 9
law run_mov:
  {R.ebpf_run([I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfK{9}}, I.EbpfExit{}], empty_mem()) == R.EbpfOk{W.W64.from_u32(9)} : R.EbpfOutcome}

# a stack spill and reload round-trips the value 7
law run_stack:
  {R.ebpf_run([I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR1{}, I.EbpfK{7}}, I.EbpfStx{I.EbpfSizeDW{}, I.EbpfR10{}, I.EbpfR1{}, 65528}, I.EbpfLdx{I.EbpfSizeDW{}, I.EbpfR0{}, I.EbpfR10{}, 65528}, I.EbpfExit{}], empty_mem()) == R.EbpfOk{W.W64.from_u32(7)} : R.EbpfOutcome}

# division by zero gives 0 (RFC 9669, 4.1)
law run_divzero:
  {R.ebpf_run([I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfK{5}}, I.EbpfAlu{I.EbpfBits64{}, I.EbpfDiv{}, I.EbpfR0{}, I.EbpfK{0}}, I.EbpfExit{}], empty_mem()) == R.EbpfOk{W.W64.zero()} : R.EbpfOutcome}

def empty_mem() -> M.EbpfMem:
  M.EbpfMem.new(C.BpfLittle{}, B.Octets.empty(), B.Octets.empty(), Nil{})

# --- the verifier, as vectors ---

# a trivial program is accepted
law verify_accepts:
  {V.ebpf_verify([I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfK{0}}, I.EbpfExit{}]) == Done{Unit{}} : Result<&2, &2, I.EbpfError, Unit>}

# reading an uninitialised register (R6) is rejected
law verify_rejects_uninit:
  {V.ebpf_accepts(V.ebpf_verify([I.EbpfAlu{I.EbpfBits64{}, I.EbpfAdd{}, I.EbpfR6{}, I.EbpfK{1}}, I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfX{I.EbpfR6{}}}, I.EbpfExit{}])) == False{} : Bool}

# a load through the context pointer past its (zero) size is rejected
law verify_rejects_oob:
  {V.ebpf_accepts(V.ebpf_verify([I.EbpfLdx{I.EbpfSizeW{}, I.EbpfR0{}, I.EbpfR1{}, 0}, I.EbpfExit{}])) == False{} : Bool}

# returning a pointer (R0 = R1, the context) is rejected
law verify_rejects_leak:
  {V.ebpf_accepts(V.ebpf_verify([I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfX{I.EbpfR1{}}}, I.EbpfExit{}])) == False{} : Bool}
