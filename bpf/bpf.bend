# bend-osdev-bpf: the classic BPF interpreter.
#
# The machine of the BSD bpf(4) manual page and McCanne and Jacobson, "The
# BSD Packet Filter" (USENIX 1993): a 32-bit accumulator A, an index
# register X, a scratch memory M[0..15], and an implicit program counter.
# A, X and M start at 0. Every instruction class and addressing mode:
#   LD   A <- P[k:4], P[k:2], P[k:1] (ABS), the same at X + k (IND), k (IMM),
#        the input's length (LEN), M[k] (MEM)
#   LDX  X <- k, M[k], the length, or 4 * (P[k:1] & 0xf) (MSH)
#   ST   M[k] <- A;  STX  M[k] <- X
#   ALU  A <- A op k or A op X, for + - * / | & << >> % ^ (32-bit, wrapping;
#        a shift by 32 or more gives 0), and A <- -A (NEG)
#   JMP  pc += k (JA); pc += (A op k or A op X) ? jt : jf, for = > >= and
#        "A & operand is not zero" (JSET)
#   RET  answer k, or A
#   MISC X <- A (TAX), A <- X (TXA)
# P is the input, read in its byte order (big-endian for packets). A load
# outside the input, and a division or modulo by X = 0, end the program with
# the answer 0, as bpf(4) documents.
#
# bpf_run runs any program; on a validated one (bpf_validate) it always
# answers Done (a law). Its errors are what an unvalidated program can do:
# run past its last instruction, or use a scratch index above 15.
import Base
import ../bytes/bytes.bend as B
import ./insn.bend as I

# What a filter runs over: bytes, and the byte order its loads use
type BpfInput is Data:
  BpfInput{order: I.BpfOrder, data: B.Octets}

# a packet: loads are big-endian (network order)
def bpf_packet(o: B.Octets) -> BpfInput:
  BpfInput{I.BpfBig{}, o}

# The machine

type BpfState is Data:
  BpfState{a: U32, x: U32, mem: List<&2, U32>}

# what an instruction leads to: skip some instructions and go on, answer,
# or fail
type BpfStep is Data:
  BpfNext{skip: Nat, st: BpfState}
  BpfStop{value: U32}
  BpfFault{error: I.BpfError}

def bpf_init() -> BpfState:
  BpfState{0, 0, List.replicate(U32, 16n, 0)}

def bpf_get_a(st: BpfState) -> U32:
  match st:
    case BpfState{a, x, mem}:
      a

def bpf_set_a(st: BpfState, v: U32) -> BpfState:
  match st:
    case BpfState{a, x, mem}:
      BpfState{v, x, mem}

def bpf_set_x(st: BpfState, v: U32) -> BpfState:
  match st:
    case BpfState{a, x, mem}:
      BpfState{a, v, mem}

def bpf_set_a.m(m: Maybe<&2, U32>, st: BpfState) -> Maybe<&2, BpfState>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{bpf_set_a(st, v)}

def bpf_set_x.m(m: Maybe<&2, U32>, st: BpfState) -> Maybe<&2, BpfState>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{bpf_set_x(st, v)}

def bpf_tax(st: BpfState) -> BpfState:
  match st:
    case BpfState{+a, x, mem}:
      BpfState{a, a, mem}

def bpf_txa(st: BpfState) -> BpfState:
  match st:
    case BpfState{a, +x, mem}:
      BpfState{x, x, mem}

def bpf_neg(st: BpfState) -> BpfState:
  match st:
    case BpfState{a, x, mem}:
      BpfState{U32.sub(0, a), x, mem}

# a step that goes on to the next instruction, or ends the program with 0
def bpf_step.of(m: Maybe<&2, BpfState>) -> BpfStep:
  match m:
    case None{}:
      BpfStop{0}
    case Some{st}:
      BpfNext{0n, st}

# Loads

def bpf_load.at(order: I.BpfOrder, size: I.BpfSize, data: B.Octets, n: Nat) -> Maybe<&2, U32>:
  match order:
    case I.BpfBig{}:
      match size:
        case I.BpfW{}:
          B.Octets.be32_at(data, n)
        case I.BpfH{}:
          B.Octets.be16_at(data, n)
        case I.BpfB{}:
          B.Octets.at(data, n)
    case I.BpfLittle{}:
      match size:
        case I.BpfW{}:
          B.Octets.le32_at(data, n)
        case I.BpfH{}:
          B.Octets.le16_at(data, n)
        case I.BpfB{}:
          B.Octets.at(data, n)

def bpf_load(inp: BpfInput, size: I.BpfSize, k: U32) -> Maybe<&2, U32>:
  match inp:
    case BpfInput{order, data}:
      bpf_load.at(order, size, data, U32.to_nat(k))

# X + k does not wrap: an offset past 2^32 is outside the input
def bpf_load.ind(inp: BpfInput, size: I.BpfSize, x: U32, k: U32) -> Maybe<&2, U32>:
  match inp:
    case BpfInput{order, data}:
      bpf_load.at(order, size, data, Nat.add(U32.to_nat(x), U32.to_nat(k)))

def bpf_load.msh.fin(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Some{U32.shln(U32.and(b, 15), 2n)}

def bpf_load.msh(inp: BpfInput, k: U32) -> Maybe<&2, U32>:
  match inp:
    case BpfInput{order, data}:
      bpf_load.msh.fin(B.Octets.at(data, U32.to_nat(k)))

def bpf_len(inp: BpfInput) -> U32:
  match inp:
    case BpfInput{order, data}:
      U32.from_nat(B.Octets.len(data))

# Scratch memory

def bpf_mem.get(mem: List<&2, U32>, k: U32) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, mem, U32.to_nat(k)), 0)

def bpf_mem.set(mem: List<&2, U32>, k: U32, v: U32) -> List<&2, U32>:
  List.set(&2, U32, mem, U32.to_nat(k), v)

def bpf_mem.lda(st: BpfState, k: U32) -> BpfState:
  match st:
    case BpfState{a, x, +mem}:
      BpfState{bpf_mem.get(mem, k), x, mem}

def bpf_mem.ldx(st: BpfState, k: U32) -> BpfState:
  match st:
    case BpfState{a, x, +mem}:
      BpfState{a, bpf_mem.get(mem, k), mem}

def bpf_mem.st(st: BpfState, k: U32) -> BpfState:
  match st:
    case BpfState{+a, x, mem}:
      BpfState{a, x, bpf_mem.set(mem, k, a)}

def bpf_mem.stx(st: BpfState, k: U32) -> BpfState:
  match st:
    case BpfState{a, +x, mem}:
      BpfState{a, x, bpf_mem.set(mem, k, x)}

# a scratch access goes on only if its index is in range
def bpf_scratch(ok: Bool, k: U32, st: BpfState) -> BpfStep:
  match ok:
    case True{}:
      BpfNext{0n, st}
    case False{}:
      BpfFault{I.BpfErrBadScratch{k}}

# Arithmetic

def bpf_src(src: I.BpfSrc, x: U32) -> U32:
  match src:
    case I.BpfK{k}:
      k
    case I.BpfX{}:
      x

def bpf_shl(small: Bool, a: U32, n: U32) -> U32:
  match small:
    case True{}:
      U32.shln(a, U32.to_nat(n))
    case False{}:
      0

def bpf_shr(small: Bool, a: U32, n: U32) -> U32:
  match small:
    case True{}:
      U32.shrn(a, U32.to_nat(n))
    case False{}:
      0

def bpf_div(zero: Bool, a: U32, v: U32) -> Maybe<&2, U32>:
  match zero:
    case True{}:
      None{}
    case False{}:
      Some{U32.div(a, v)}

def bpf_mod(zero: Bool, a: U32, v: U32) -> Maybe<&2, U32>:
  match zero:
    case True{}:
      None{}
    case False{}:
      Some{U32.mod(a, v)}

# A op v, or None for a division or modulo by zero
def bpf_alu(o: I.BpfAluOp, +a: U32, +v: U32) -> Maybe<&2, U32>:
  match o:
    case I.BpfAdd{}:
      Some{U32.add(a, v)}
    case I.BpfSub{}:
      Some{U32.sub(a, v)}
    case I.BpfMul{}:
      Some{U32.mul(a, v)}
    case I.BpfDiv{}:
      bpf_div(U32.is_zero(v), a, v)
    case I.BpfOr{}:
      Some{U32.or(a, v)}
    case I.BpfAnd{}:
      Some{U32.and(a, v)}
    case I.BpfLsh{}:
      Some{bpf_shl(U32.is_lt(v, 32), a, v)}
    case I.BpfRsh{}:
      Some{bpf_shr(U32.is_lt(v, 32), a, v)}
    case I.BpfMod{}:
      bpf_mod(U32.is_zero(v), a, v)
    case I.BpfXor{}:
      Some{U32.xor(a, v)}

def bpf_test(c: I.BpfCond, +a: U32, +v: U32) -> Bool:
  match c:
    case I.BpfJeq{}:
      U32.is_eq(a, v)
    case I.BpfJgt{}:
      U32.is_gt(a, v)
    case I.BpfJge{}:
      U32.is_ge(a, v)
    case I.BpfJset{}:
      Bool.not(U32.is_zero(U32.and(a, v)))

def bpf_jsel(hit: Bool, jt: U32, jf: U32) -> Nat:
  match hit:
    case True{}:
      U32.to_nat(jt)
    case False{}:
      U32.to_nat(jf)

# One instruction

def bpf_exec(op: I.BpfOp, st: BpfState, +inp: BpfInput) -> BpfStep:
  match op:
    case I.BpfLdAbs{size, k}:
      bpf_step.of(bpf_set_a.m(bpf_load(inp, size, k), st))
    case I.BpfLdInd{size, k}:
      match st:
        case BpfState{a, +x, mem}:
          bpf_step.of(bpf_set_a.m(bpf_load.ind(inp, size, x, k), BpfState{a, x, mem}))
    case I.BpfLdImm{k}:
      BpfNext{0n, bpf_set_a(st, k)}
    case I.BpfLdLen{}:
      BpfNext{0n, bpf_set_a(st, bpf_len(inp))}
    case I.BpfLdMem{+k}:
      bpf_scratch(U32.is_lt(k, I.bpf_memwords()), k, bpf_mem.lda(st, k))
    case I.BpfLdxImm{k}:
      BpfNext{0n, bpf_set_x(st, k)}
    case I.BpfLdxMem{+k}:
      bpf_scratch(U32.is_lt(k, I.bpf_memwords()), k, bpf_mem.ldx(st, k))
    case I.BpfLdxLen{}:
      BpfNext{0n, bpf_set_x(st, bpf_len(inp))}
    case I.BpfLdxMsh{k}:
      bpf_step.of(bpf_set_x.m(bpf_load.msh(inp, k), st))
    case I.BpfSt{+k}:
      bpf_scratch(U32.is_lt(k, I.bpf_memwords()), k, bpf_mem.st(st, k))
    case I.BpfStx{+k}:
      bpf_scratch(U32.is_lt(k, I.bpf_memwords()), k, bpf_mem.stx(st, k))
    case I.BpfAlu{o, src}:
      match st:
        case BpfState{+a, +x, mem}:
          bpf_step.of(bpf_set_a.m(bpf_alu(o, a, bpf_src(src, x)), BpfState{a, x, mem}))
    case I.BpfNeg{}:
      BpfNext{0n, bpf_neg(st)}
    case I.BpfJa{k}:
      BpfNext{U32.to_nat(k), st}
    case I.BpfJmp{c, src, jt, jf}:
      match st:
        case BpfState{+a, +x, mem}:
          BpfNext{bpf_jsel(bpf_test(c, a, bpf_src(src, x)), jt, jf), BpfState{a, x, mem}}
    case I.BpfRet{v}:
      match v:
        case I.BpfRetK{k}:
          BpfStop{k}
        case I.BpfRetA{}:
          BpfStop{bpf_get_a(st)}
    case I.BpfTax{}:
      BpfNext{0n, bpf_tax(st)}
    case I.BpfTxa{}:
      BpfNext{0n, bpf_txa(st)}

# The run: one pass over the instructions, skipping the ones a jump passes
# over, so every instruction is visited at most once

def bpf_run.go(xs: List<&2, I.BpfOp>, cur: BpfStep, +inp: BpfInput) -> Result<&2, &2, I.BpfError, U32>:
  match xs:
    case Nil{}:
      match cur:
        case BpfNext{skip, st}:
          Fail{I.BpfErrFellOff{}}
        case BpfStop{v}:
          Done{v}
        case BpfFault{e}:
          Fail{e}
    case Con{op, t}:
      match cur:
        case BpfNext{skip, st}:
          match skip:
            case 0n:
              bpf_run.go(t, bpf_exec(op, st, inp), inp)
            case 1n+s:
              bpf_run.go(t, BpfNext{s, st}, inp)
        case BpfStop{v}:
          Done{v}
        case BpfFault{e}:
          Fail{e}

# the program's answer for this input
def bpf_run(+inp: BpfInput, prog: List<&2, I.BpfOp>) -> Result<&2, &2, I.BpfError, U32>:
  bpf_run.go(prog, BpfNext{0n, bpf_init()}, inp)
