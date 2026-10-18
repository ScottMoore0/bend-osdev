# bend-osdev-bpf: classic BPF instructions, raw and decoded.
#
# A classic BPF program is a list of struct sock_filter {code: u16, jt: u8,
# jf: u8, k: u32} (the BSD bpf(4) manual page; McCanne and Jacobson, "The BSD
# Packet Filter", USENIX 1993). BpfRaw is that struct, field for field. BpfOp
# is the same instruction decoded into what it does, one constructor per
# instruction and addressing mode, so code that builds or inspects a program
# never handles opcode bits.
#
# The opcode is class | size | mode for loads, class | op | source for ALU
# and jumps, class | rval for returns:
#   class  LD 0, LDX 1, ST 2, STX 3, ALU 4, JMP 5, RET 6, MISC 7
#   size   W 0x00, H 0x08, B 0x10
#   mode   IMM 0x00, ABS 0x20, IND 0x40, MEM 0x60, LEN 0x80, MSH 0xa0
#   ALU    ADD 0x00, SUB 0x10, MUL 0x20, DIV 0x30, OR 0x40, AND 0x50,
#          LSH 0x60, RSH 0x70, NEG 0x80, MOD 0x90, XOR 0xa0
#   JMP    JA 0x00, JEQ 0x10, JGT 0x20, JGE 0x30, JSET 0x40
#   source K 0x00, X 0x08;  rval K 0x00, A 0x10;  MISC TAX 0x00, TXA 0x80
import Base
import ../bytes/bytes.bend as B

# Instructions

type BpfSize is Data:
  BpfW{}
  BpfH{}
  BpfB{}

type BpfAluOp is Data:
  BpfAdd{}
  BpfSub{}
  BpfMul{}
  BpfDiv{}
  BpfOr{}
  BpfAnd{}
  BpfLsh{}
  BpfRsh{}
  BpfMod{}
  BpfXor{}

type BpfCond is Data:
  BpfJeq{}
  BpfJgt{}
  BpfJge{}
  BpfJset{}

# the second operand of an ALU or jump instruction: the constant k, or X
type BpfSrc is Data:
  BpfK{k: U32}
  BpfX{}

# what a return instruction answers: the constant k, or A
type BpfRval is Data:
  BpfRetK{k: U32}
  BpfRetA{}

# A decoded instruction. Jump offsets count the instructions skipped: a jump
# at index i by n goes to index i + 1 + n, so jumps only move forward.
type BpfOp is Data:
  BpfLdAbs{size: BpfSize, k: U32}
  BpfLdInd{size: BpfSize, k: U32}
  BpfLdImm{k: U32}
  BpfLdLen{}
  BpfLdMem{k: U32}
  BpfLdxImm{k: U32}
  BpfLdxMem{k: U32}
  BpfLdxLen{}
  BpfLdxMsh{k: U32}
  BpfSt{k: U32}
  BpfStx{k: U32}
  BpfAlu{op: BpfAluOp, src: BpfSrc}
  BpfNeg{}
  BpfJa{k: U32}
  BpfJmp{cond: BpfCond, src: BpfSrc, jt: U32, jf: U32}
  BpfRet{rval: BpfRval}
  BpfTax{}
  BpfTxa{}

# struct sock_filter; code is 16 bits and jt, jf are 8 bits when stored
type BpfRaw is Data:
  BpfRaw{code: U32, jt: U32, jf: U32, k: U32}

# the byte order of a stored program, and of a filter's loads
type BpfOrder is Data:
  BpfBig{}
  BpfLittle{}

# Every failure: decoding (BadCode, Truncated, StoredTooLong), validation
# (Empty to SeccompInsn), installing seccomp filters (PathTooLong), and
# running a program that was not validated (FellOff, BadScratch).
type BpfError is Data:
  BpfErrBadCode{pc: Nat, code: U32}
  BpfErrTruncated{len: Nat}
  BpfErrStoredTooLong{max: Nat}
  BpfErrEmpty{}
  BpfErrTooLong{len: Nat}
  BpfErrJump{pc: Nat}
  BpfErrJumpField{pc: Nat}
  BpfErrNoReturn{pc: Nat}
  BpfErrScratch{pc: Nat}
  BpfErrDivZero{pc: Nat}
  BpfErrMemInit{pc: Nat}
  BpfErrSeccompLoad{pc: Nat}
  BpfErrSeccompInsn{pc: Nat}
  BpfErrPathTooLong{total: Nat}
  BpfErrFellOff{}
  BpfErrBadScratch{k: U32}

# BPF_MEMWORDS: the scratch memory is M[0] to M[15]
def bpf_memwords() -> U32:
  16

# The C macros BPF_STMT(code, k) and BPF_JUMP(code, k, jt, jf)

def bpf_stmt(code: U32, k: U32) -> BpfRaw:
  BpfRaw{code, 0, 0, k}

def bpf_jump(code: U32, k: U32, jt: U32, jf: U32) -> BpfRaw:
  BpfRaw{code, jt, jf, k}

def BpfRaw.code(r: BpfRaw) -> U32:
  match r:
    case BpfRaw{code, jt, jf, k}:
      code

# Encoding

def BpfSize.bits(s: BpfSize) -> U32:
  match s:
    case BpfW{}:
      0
    case BpfH{}:
      8
    case BpfB{}:
      16

def BpfAluOp.bits(o: BpfAluOp) -> U32:
  match o:
    case BpfAdd{}:
      0
    case BpfSub{}:
      16
    case BpfMul{}:
      32
    case BpfDiv{}:
      48
    case BpfOr{}:
      64
    case BpfAnd{}:
      80
    case BpfLsh{}:
      96
    case BpfRsh{}:
      112
    case BpfMod{}:
      144
    case BpfXor{}:
      160

def BpfCond.bits(c: BpfCond) -> U32:
  match c:
    case BpfJeq{}:
      16
    case BpfJgt{}:
      32
    case BpfJge{}:
      48
    case BpfJset{}:
      64

def BpfSrc.bits(s: BpfSrc) -> U32:
  match s:
    case BpfK{k}:
      0
    case BpfX{}:
      8

def BpfSrc.k(s: BpfSrc) -> U32:
  match s:
    case BpfK{k}:
      k
    case BpfX{}:
      0

def BpfRval.encode(r: BpfRval) -> BpfRaw:
  match r:
    case BpfRetK{k}:
      BpfRaw{6, 0, 0, k}
    case BpfRetA{}:
      BpfRaw{22, 0, 0, 0}

# the sock_filter of an instruction; unused fields are 0
def BpfOp.encode(op: BpfOp) -> BpfRaw:
  match op:
    case BpfLdAbs{size, k}:
      BpfRaw{U32.or(32, BpfSize.bits(size)), 0, 0, k}
    case BpfLdInd{size, k}:
      BpfRaw{U32.or(64, BpfSize.bits(size)), 0, 0, k}
    case BpfLdImm{k}:
      BpfRaw{0, 0, 0, k}
    case BpfLdLen{}:
      BpfRaw{128, 0, 0, 0}
    case BpfLdMem{k}:
      BpfRaw{96, 0, 0, k}
    case BpfLdxImm{k}:
      BpfRaw{1, 0, 0, k}
    case BpfLdxMem{k}:
      BpfRaw{97, 0, 0, k}
    case BpfLdxLen{}:
      BpfRaw{129, 0, 0, 0}
    case BpfLdxMsh{k}:
      BpfRaw{177, 0, 0, k}
    case BpfSt{k}:
      BpfRaw{2, 0, 0, k}
    case BpfStx{k}:
      BpfRaw{3, 0, 0, k}
    case BpfAlu{o, +src}:
      BpfRaw{U32.or(4, U32.or(BpfAluOp.bits(o), BpfSrc.bits(src))), 0, 0, BpfSrc.k(src)}
    case BpfNeg{}:
      BpfRaw{132, 0, 0, 0}
    case BpfJa{k}:
      BpfRaw{5, 0, 0, k}
    case BpfJmp{c, +src, jt, jf}:
      BpfRaw{U32.or(5, U32.or(BpfCond.bits(c), BpfSrc.bits(src))), jt, jf, BpfSrc.k(src)}
    case BpfRet{r}:
      BpfRval.encode(r)
    case BpfTax{}:
      BpfRaw{7, 0, 0, 0}
    case BpfTxa{}:
      BpfRaw{135, 0, 0, 0}

# Decoding: every opcode classic BPF defines, and nothing else

def BpfRaw.decode.pick(hit: Bool, op: BpfOp, rest: Maybe<&2, BpfOp>) -> Maybe<&2, BpfOp>:
  match hit:
    case True{}:
      Some{op}
    case False{}:
      rest

# the instruction a sock_filter holds, or None for an opcode classic BPF does
# not define; fields the instruction does not use are ignored
def BpfRaw.decode(r: BpfRaw) -> Maybe<&2, BpfOp>:
  match r:
    case BpfRaw{+code, +jt, +jf, +k}:
      BpfRaw.decode.pick(U32.is_eq(code, 32), BpfLdAbs{BpfW{}, k},
      BpfRaw.decode.pick(U32.is_eq(code, 40), BpfLdAbs{BpfH{}, k},
      BpfRaw.decode.pick(U32.is_eq(code, 48), BpfLdAbs{BpfB{}, k},
      BpfRaw.decode.pick(U32.is_eq(code, 64), BpfLdInd{BpfW{}, k},
      BpfRaw.decode.pick(U32.is_eq(code, 72), BpfLdInd{BpfH{}, k},
      BpfRaw.decode.pick(U32.is_eq(code, 80), BpfLdInd{BpfB{}, k},
      BpfRaw.decode.pick(U32.is_eq(code, 0), BpfLdImm{k},
      BpfRaw.decode.pick(U32.is_eq(code, 128), BpfLdLen{},
      BpfRaw.decode.pick(U32.is_eq(code, 96), BpfLdMem{k},
      BpfRaw.decode.pick(U32.is_eq(code, 1), BpfLdxImm{k},
      BpfRaw.decode.pick(U32.is_eq(code, 97), BpfLdxMem{k},
      BpfRaw.decode.pick(U32.is_eq(code, 129), BpfLdxLen{},
      BpfRaw.decode.pick(U32.is_eq(code, 177), BpfLdxMsh{k},
      BpfRaw.decode.pick(U32.is_eq(code, 2), BpfSt{k},
      BpfRaw.decode.pick(U32.is_eq(code, 3), BpfStx{k},
      BpfRaw.decode.pick(U32.is_eq(code, 4), BpfAlu{BpfAdd{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 12), BpfAlu{BpfAdd{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 20), BpfAlu{BpfSub{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 28), BpfAlu{BpfSub{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 36), BpfAlu{BpfMul{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 44), BpfAlu{BpfMul{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 52), BpfAlu{BpfDiv{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 60), BpfAlu{BpfDiv{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 68), BpfAlu{BpfOr{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 76), BpfAlu{BpfOr{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 84), BpfAlu{BpfAnd{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 92), BpfAlu{BpfAnd{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 100), BpfAlu{BpfLsh{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 108), BpfAlu{BpfLsh{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 116), BpfAlu{BpfRsh{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 124), BpfAlu{BpfRsh{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 148), BpfAlu{BpfMod{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 156), BpfAlu{BpfMod{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 164), BpfAlu{BpfXor{}, BpfK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 172), BpfAlu{BpfXor{}, BpfX{}},
      BpfRaw.decode.pick(U32.is_eq(code, 132), BpfNeg{},
      BpfRaw.decode.pick(U32.is_eq(code, 5), BpfJa{k},
      BpfRaw.decode.pick(U32.is_eq(code, 21), BpfJmp{BpfJeq{}, BpfK{k}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 29), BpfJmp{BpfJeq{}, BpfX{}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 37), BpfJmp{BpfJgt{}, BpfK{k}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 45), BpfJmp{BpfJgt{}, BpfX{}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 53), BpfJmp{BpfJge{}, BpfK{k}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 61), BpfJmp{BpfJge{}, BpfX{}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 69), BpfJmp{BpfJset{}, BpfK{k}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 77), BpfJmp{BpfJset{}, BpfX{}, jt, jf},
      BpfRaw.decode.pick(U32.is_eq(code, 6), BpfRet{BpfRetK{k}},
      BpfRaw.decode.pick(U32.is_eq(code, 22), BpfRet{BpfRetA{}},
      BpfRaw.decode.pick(U32.is_eq(code, 7), BpfTax{},
      BpfRaw.decode.pick(U32.is_eq(code, 135), BpfTxa{},
      None{})))))))))))))))))))))))))))))))))))))))))))))))))
# Programs. Each program-wide loop is a tail call over an accumulator,
# reversed at the end, so a program of any length runs on both lanes. The
# structural forms (*.ref) are the references the proofs reason about;
# PROOF.bend proves each equal to its tail form for every input (F_encode,
# F_decode).

def bpf_encode.ref(ops: List<&2, BpfOp>) -> List<&2, BpfRaw>:
  match ops:
    case Nil{}:
      Nil{}
    case Con{op, t}:
      Con{BpfOp.encode(op), bpf_encode.ref(t)}

# the encoded instructions, last first, onto acc
def bpf_encode.go(ops: List<&2, BpfOp>, acc: List<&2, BpfRaw>) -> List<&2, BpfRaw>:
  match ops:
    case Nil{}:
      acc
    case Con{op, t}:
      bpf_encode.go(t, Con{BpfOp.encode(op), acc})

def bpf_encode(ops: List<&2, BpfOp>) -> List<&2, BpfRaw>:
  List.reverse(&2, BpfRaw, bpf_encode.go(ops, Nil{}))

def bpf_decode.cons(m: Maybe<&2, BpfOp>, e: BpfError, rest: Result<&2, &2, BpfError, List<&2, BpfOp>>) -> Result<&2, &2, BpfError, List<&2, BpfOp>>:
  match m:
    case None{}:
      Fail{e}
    case Some{op}:
      match rest:
        case Fail{f}:
          Fail{f}
        case Done{ops}:
          Done{Con{op, ops}}

def bpf_decode.ref.go(rs: List<&2, BpfRaw>, +pc: Nat) -> Result<&2, &2, BpfError, List<&2, BpfOp>>:
  match rs:
    case Nil{}:
      Done{Nil{}}
    case Con{+r, t}:
      bpf_decode.cons(BpfRaw.decode(r), BpfErrBadCode{pc, BpfRaw.code(r)}, bpf_decode.ref.go(t, 1n+pc))

def bpf_decode.ref(rs: List<&2, BpfRaw>) -> Result<&2, &2, BpfError, List<&2, BpfOp>>:
  bpf_decode.ref.go(rs, 0n)

# one decoded instruction pushed onto the instructions so far (last first)
def bpf_decode.push(m: Maybe<&2, BpfOp>, e: BpfError, acc: List<&2, BpfOp>) -> Result<&2, &2, BpfError, List<&2, BpfOp>>:
  match m:
    case None{}:
      Fail{e}
    case Some{op}:
      Done{Con{op, acc}}

# a: the instructions before pc, last first, or the first failure; the loop
# stops at the instruction after a failure
def bpf_decode.go(rs: List<&2, BpfRaw>, +pc: Nat, a: Result<&2, &2, BpfError, List<&2, BpfOp>>) -> Result<&2, &2, BpfError, List<&2, BpfOp>>:
  match rs:
    case Nil{}:
      match a:
        case Fail{e}:
          Fail{e}
        case Done{acc}:
          Done{List.reverse(&2, BpfOp, acc)}
    case Con{+r, t}:
      match a:
        case Fail{e}:
          Fail{e}
        case Done{acc}:
          bpf_decode.go(t, 1n+pc, bpf_decode.push(BpfRaw.decode(r), BpfErrBadCode{pc, BpfRaw.code(r)}, acc))

# every instruction decoded, or the first one that is not classic BPF
def bpf_decode(rs: List<&2, BpfRaw>) -> Result<&2, &2, BpfError, List<&2, BpfOp>>:
  bpf_decode.go(rs, 0n, Done{Nil{}})

# Stored programs: 8 bytes per instruction, in the given byte order

def BpfRaw.to_octets(order: BpfOrder, r: BpfRaw) -> B.Octets:
  match order:
    case BpfLittle{}:
      match r:
        case BpfRaw{code, jt, jf, k}:
          B.Octets.concat([B.Octets.le16(code), B.Octets.of_list([jt, jf]), B.Octets.le32(k)])
    case BpfBig{}:
      match r:
        case BpfRaw{code, jt, jf, k}:
          B.Octets.concat([B.Octets.be16(code), B.Octets.of_list([jt, jf]), B.Octets.be32(k)])

# each instruction's 8 bytes, last first, onto acc
def bpf_to_octets.go(rs: List<&2, BpfRaw>, +order: BpfOrder, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      bpf_to_octets.go(t, order, Con{BpfRaw.to_octets(order, r), acc})

def bpf_to_octets(+order: BpfOrder, rs: List<&2, BpfRaw>) -> B.Octets:
  B.Octets.concat(List.reverse(&2, B.Octets, bpf_to_octets.go(rs, order, Nil{})))

def bpf_field(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

def BpfRaw.of_octets(order: BpfOrder, +o: B.Octets) -> BpfRaw:
  match order:
    case BpfLittle{}:
      BpfRaw{bpf_field(B.Octets.le16_at(o, 0n)), bpf_field(B.Octets.at(o, 2n)), bpf_field(B.Octets.at(o, 3n)), bpf_field(B.Octets.le32_at(o, 4n))}
    case BpfBig{}:
      BpfRaw{bpf_field(B.Octets.be16_at(o, 0n)), bpf_field(B.Octets.at(o, 2n)), bpf_field(B.Octets.at(o, 3n)), bpf_field(B.Octets.be32_at(o, 4n))}

# the next n instructions, onto acc (last first), then all of them in order
def bpf_of_octets.go(n: Nat, +order: BpfOrder, +o: B.Octets, acc: List<&2, BpfRaw>) -> List<&2, BpfRaw>:
  match n:
    case 0n:
      List.reverse(&2, BpfRaw, acc)
    case 1n+p:
      bpf_of_octets.go(p, order, B.Octets.drop(8n, o), Con{BpfRaw.of_octets(order, B.Octets.take(8n, o)), acc})

def bpf_of_octets.rem(r: Nat, q: Nat, +order: BpfOrder, +o: B.Octets, +len: Nat) -> Result<&2, &2, BpfError, List<&2, BpfRaw>>:
  match r:
    case 0n:
      Done{bpf_of_octets.go(q, order, o, Nil{})}
    case 1n+p:
      Fail{BpfErrTruncated{len}}

def bpf_of_octets.fin(+order: BpfOrder, +o: B.Octets, +len: Nat, qr: Nat & Nat) -> Result<&2, &2, BpfError, List<&2, BpfRaw>>:
  (q, r) = qr
  bpf_of_octets.rem(r, q, order, o, len)

# over: the input's byte at offset max, if it has one
def bpf_of_octets.fits(over: Maybe<&2, U32>, max: Nat, +order: BpfOrder, +o: B.Octets) -> Result<&2, &2, BpfError, List<&2, BpfRaw>>:
  match over:
    case Some{b}:
      Fail{BpfErrStoredTooLong{max}}
    case None{}:
      +len = B.Octets.len(o)
      bpf_of_octets.fin(order, o, len, Nat.divmod(len, 8n))

# 8 * BPF_MAXINSNS: the bytes of the longest program validation accepts by
# default (LAWS.bend: octets_max_default ties it to bpf_maxinsns)
def bpf_octets_max() -> Nat:
  32768n

# a stored program's instructions: at most max bytes, a multiple of 8. The
# limit is checked first, by looking for the byte at offset max, so a longer
# input costs max steps whatever its length
def bpf_of_octets_with(+max: Nat, +order: BpfOrder, +o: B.Octets) -> Result<&2, &2, BpfError, List<&2, BpfRaw>>:
  bpf_of_octets.fits(B.Octets.at(o, max), max, order, o)

# the same, with the default limit, bpf_octets_max()
def bpf_of_octets(+order: BpfOrder, o: B.Octets) -> Result<&2, &2, BpfError, List<&2, BpfRaw>>:
  bpf_of_octets_with(bpf_octets_max(), order, o)

# Text

def BpfError.show(e: BpfError) -> String:
  match e:
    case BpfErrBadCode{pc, code}:
      "bad opcode " ++ U32.show(code) ++ " at " ++ Nat.show(pc)
    case BpfErrTruncated{len}:
      "truncated program of " ++ Nat.show(len) ++ " bytes"
    case BpfErrStoredTooLong{max}:
      "stored program over " ++ Nat.show(max) ++ " bytes"
    case BpfErrEmpty{}:
      "empty program"
    case BpfErrTooLong{len}:
      "program too long: " ++ Nat.show(len)
    case BpfErrJump{pc}:
      "jump out of range at " ++ Nat.show(pc)
    case BpfErrJumpField{pc}:
      "jump offset over 255 at " ++ Nat.show(pc)
    case BpfErrNoReturn{pc}:
      "no return after " ++ Nat.show(pc)
    case BpfErrScratch{pc}:
      "scratch index out of range at " ++ Nat.show(pc)
    case BpfErrDivZero{pc}:
      "division by constant zero at " ++ Nat.show(pc)
    case BpfErrMemInit{pc}:
      "scratch read before write at " ++ Nat.show(pc)
    case BpfErrSeccompLoad{pc}:
      "load not allowed in seccomp at " ++ Nat.show(pc)
    case BpfErrSeccompInsn{pc}:
      "instruction not allowed in seccomp at " ++ Nat.show(pc)
    case BpfErrPathTooLong{total}:
      "seccomp filters too long: " ++ Nat.show(total)
    case BpfErrFellOff{}:
      "ran past the end"
    case BpfErrBadScratch{k}:
      "scratch index " ++ U32.show(k)
