# bend-osdev-ebpf: the verifier (the second half), register-type tracking,
# stack initialisation and static bounds.
#
# From the Linux kernel's verifier documentation (Documentation/bpf/
# verifier.rst, a documentation page). After the control-flow checks
# (cfg.bend), the program is abstractly interpreted: each register holds an
# abstract value (a scalar with an unsigned min/max range, or a pointer to a
# region with an offset range, or uninitialised), and the effect of each
# instruction is applied. Because the control-flow check forbids back edges,
# the control-flow graph is a DAG, so one pass in slot order with the state
# at each instruction joined over its predecessors reaches a fixed point.
# The checks enforced:
#   * a register read must be initialised (no uninitialised read);
#   * R10 (the frame pointer) is read-only;
#   * pointer arithmetic adds or subtracts only scalars (and a pointer minus
#     a pointer gives a scalar); any other ALU on a pointer is rejected;
#   * a load or store through a pointer stays inside its region, using the
#     region's static size and the pointer's offset range;
#   * a stack slot is read only after it is written on every path;
#   * EXIT leaves R0 a scalar (no pointer leak to the caller).
# Region sizes come from an EbpfVerifyCtx record (the context size, the
# packet size, each map's value size). This analysis is conservative: it
# keeps a scalar's range only through moves, adds and a few operations, and
# otherwise falls back to "unknown", rejecting what it cannot prove.
import Base
import ../word64/word64.bend as W
import ./insn.bend as I
import ./memory.bend as M
import ./helpers.bend as H
import ./cfg.bend as G
import ./alu.bend as A

# an abstract pointer's region (map value regions are not resolved to an
# index here; a pointer to a map value just records that it is one)
type EbpfAbsRgn is Data:
  EbpfAbsCtx{}
  EbpfAbsStack{}
  EbpfAbsPacket{}
  EbpfAbsMapValue{}
  EbpfAbsMap{}

# an abstract register value
type EbpfAbs is Data:
  EbpfAbsUninit{}
  EbpfAbsScalar{known: Bool, c: W.W64, umin: W.W64, umax: W.W64}
  EbpfAbsPtr{rgn: EbpfAbsRgn, omin: W.W64, omax: W.W64}
  EbpfAbsUnknown{}

# a known constant scalar
def ebpf_abs_const(+v: W.W64) -> EbpfAbs:
  EbpfAbsScalar{True{}, v, v, v}

# a scalar of unknown value (the full unsigned range)
def ebpf_abs_anyscalar() -> EbpfAbs:
  EbpfAbsScalar{False{}, W.W64.zero(), W.W64.zero(), W.W64.max()}

# The region sizes the program runs against
type EbpfVerifyCtx is Data:
  EbpfVerifyCtx{ctx_size: U32, packet_size: U32, map_value_size: U32, has_packet: Bool}

def EbpfVerifyCtx.default() -> EbpfVerifyCtx:
  EbpfVerifyCtx{0, 0, 0, False{}}

# the entry state: R1 a pointer to the context at offset 0, R10 a pointer to
# the stack at offset 512 (the frame top), the rest uninitialised
def ebpf_abs_entry() -> List<&2, EbpfAbs>:
  [EbpfAbsUninit{}, EbpfAbsPtr{EbpfAbsCtx{}, W.W64.zero(), W.W64.zero()}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsUninit{}, EbpfAbsPtr{EbpfAbsStack{}, W.W64.from_u32(512), W.W64.from_u32(512)}]

def ebpf_abs_get(rs: List<&2, EbpfAbs>, r: I.EbpfReg) -> EbpfAbs:
  Maybe.default(&2, EbpfAbs, List.get(&2, EbpfAbs, rs, U32.to_nat(I.EbpfReg.num(r))), EbpfAbsUninit{})

def ebpf_abs_set(rs: List<&2, EbpfAbs>, r: I.EbpfReg, v: EbpfAbs) -> List<&2, EbpfAbs>:
  List.set(&2, EbpfAbs, rs, U32.to_nat(I.EbpfReg.num(r)), v)

def ebpf_rgn_is_ctx(b: EbpfAbsRgn) -> Bool:
  match b:
    case EbpfAbsCtx{}:
      True{}
    case other:
      False{}

def ebpf_rgn_is_stack(b: EbpfAbsRgn) -> Bool:
  match b:
    case EbpfAbsStack{}:
      True{}
    case other:
      False{}

def ebpf_rgn_is_packet(b: EbpfAbsRgn) -> Bool:
  match b:
    case EbpfAbsPacket{}:
      True{}
    case other:
      False{}

def ebpf_rgn_is_mapvalue(b: EbpfAbsRgn) -> Bool:
  match b:
    case EbpfAbsMapValue{}:
      True{}
    case other:
      False{}

def ebpf_rgn_is_map(b: EbpfAbsRgn) -> Bool:
  match b:
    case EbpfAbsMap{}:
      True{}
    case other:
      False{}

# Joining two abstract values (at a control-flow merge): equal scalars and
# equal pointers keep their value, with ranges widened; anything else that
# differs becomes unknown. Uninit joined with anything stays the narrower
# (uninit only where both are uninit, so a read after a merge is safe only
# if every path initialised it).
def ebpf_abs_join_rgn(a: EbpfAbsRgn, b: EbpfAbsRgn) -> Bool:
  match a:
    case EbpfAbsCtx{}:
      ebpf_rgn_is_ctx(b)
    case EbpfAbsStack{}:
      ebpf_rgn_is_stack(b)
    case EbpfAbsPacket{}:
      ebpf_rgn_is_packet(b)
    case EbpfAbsMapValue{}:
      ebpf_rgn_is_mapvalue(b)
    case EbpfAbsMap{}:
      ebpf_rgn_is_map(b)

def ebpf_wmin(+a: W.W64, +b: W.W64) -> W.W64:
  W.W64.sel(W.W64.is_le(a, b), a, b)

def ebpf_wmax(+a: W.W64, +b: W.W64) -> W.W64:
  W.W64.sel(W.W64.is_ge(a, b), a, b)

def ebpf_abs_join_scalar(ka: Bool, +ca: W.W64, mina: W.W64, maxa: W.W64, kb: Bool, cb: W.W64, minb: W.W64, maxb: W.W64) -> EbpfAbs:
  EbpfAbsScalar{Bool.and(Bool.and(ka, kb), W.W64.is_eq(ca, cb)), ca, ebpf_wmin(mina, minb), ebpf_wmax(maxa, maxb)}

def ebpf_abs_join_ptr(ok: Bool, ra: EbpfAbsRgn, mina: W.W64, maxa: W.W64, minb: W.W64, maxb: W.W64) -> EbpfAbs:
  match ok:
    case True{}:
      EbpfAbsPtr{ra, ebpf_wmin(mina, minb), ebpf_wmax(maxa, maxb)}
    case False{}:
      EbpfAbsUnknown{}

def ebpf_abs_join(a: EbpfAbs, b: EbpfAbs) -> EbpfAbs:
  match a:
    case EbpfAbsUninit{}:
      match b:
        case EbpfAbsUninit{}:
          EbpfAbsUninit{}
        case other:
          EbpfAbsUnknown{}
    case EbpfAbsScalar{ka, ca, mina, maxa}:
      match b:
        case EbpfAbsScalar{kb, cb, minb, maxb}:
          ebpf_abs_join_scalar(ka, ca, mina, maxa, kb, cb, minb, maxb)
        case other:
          EbpfAbsUnknown{}
    case EbpfAbsPtr{+ra, mina, maxa}:
      match b:
        case EbpfAbsPtr{rb, minb, maxb}:
          ebpf_abs_join_ptr(ebpf_abs_join_rgn(ra, rb), ra, mina, maxa, minb, maxb)
        case other:
          EbpfAbsUnknown{}
    case EbpfAbsUnknown{}:
      EbpfAbsUnknown{}

# a register state is the join, slot by slot
def ebpf_state_join.go(a: List<&2, EbpfAbs>, b: List<&2, EbpfAbs>, acc: List<&2, EbpfAbs>) -> List<&2, EbpfAbs>:
  match a:
    case Nil{}:
      List.reverse(&2, EbpfAbs, acc)
    case Con{x, ta}:
      match b:
        case Nil{}:
          List.reverse(&2, EbpfAbs, acc)
        case Con{y, tb}:
          ebpf_state_join.go(ta, tb, Con{ebpf_abs_join(x, y), acc})

def ebpf_state_join(a: List<&2, EbpfAbs>, b: List<&2, EbpfAbs>) -> List<&2, EbpfAbs>:
  ebpf_state_join.go(a, b, Nil{})

# An abstract state per slot: the registers, and the stack-initialisation
# mask (which of the 512 stack bytes are written on every path to here).
# Stored as a Maybe: None means the slot has not been reached yet (no
# predecessor state), so the first predecessor's state is taken as is.
type EbpfAbsState is Data:
  EbpfAbsState{regs: List<&2, EbpfAbs>, stack: List<&2, Bool>}

def ebpf_stack_mask_zero() -> List<&2, Bool>:
  List.replicate(Bool, 512n, False{})

def ebpf_state_entry() -> EbpfAbsState:
  EbpfAbsState{ebpf_abs_entry(), ebpf_stack_mask_zero()}

# join two stack masks: a byte is initialised only if it is on both paths
def ebpf_mask_join.go(a: List<&2, Bool>, b: List<&2, Bool>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      List.reverse(&2, Bool, acc)
    case Con{x, ta}:
      match b:
        case Nil{}:
          List.reverse(&2, Bool, acc)
        case Con{y, tb}:
          ebpf_mask_join.go(ta, tb, Con{Bool.and(x, y), acc})

def ebpf_mask_join(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  ebpf_mask_join.go(a, b, Nil{})

def ebpf_state_merge(a: EbpfAbsState, b: EbpfAbsState) -> EbpfAbsState:
  match a:
    case EbpfAbsState{ra, sa}:
      match b:
        case EbpfAbsState{rb, sb}:
          EbpfAbsState{ebpf_state_join(ra, rb), ebpf_mask_join(sa, sb)}

def ebpf_state_opt_merge(a: Maybe<&2, EbpfAbsState>, b: EbpfAbsState) -> EbpfAbsState:
  match a:
    case None{}:
      b
    case Some{s}:
      ebpf_state_merge(s, b)

# the static size of a region (stack is 512; a map handle and map value use
# the context's declared sizes)
def ebpf_region_size(vc: EbpfVerifyCtx, rgn: EbpfAbsRgn) -> Maybe<&2, U32>:
  match vc:
    case EbpfVerifyCtx{cs, ps, mvs, hp}:
      match rgn:
        case EbpfAbsCtx{}:
          Some{cs}
        case EbpfAbsStack{}:
          Some{512}
        case EbpfAbsPacket{}:
          Some{ps}
        case EbpfAbsMapValue{}:
          Some{mvs}
        case EbpfAbsMap{}:
          None{}

# size bytes at offset range [omin, omax] lie in a region of rsz bytes:
# omax + size <= rsz, all as 64-bit (no wrap)
def ebpf_fits(rsz: U32, omin: W.W64, omax: W.W64, size: U32) -> Bool:
  W.W64.is_le(W.W64.add(omax, W.W64.from_u32(size)), W.W64.from_u32(rsz))

def ebpf_fill_hi.go(neg: Bool) -> U32:
  match neg:
    case True{}:
      4294967295
    case False{}:
      0

def ebpf_fill_hi(off: U32) -> U32:
  ebpf_fill_hi.go(U32.is_ge(U32.and(65535, off), 32768))

# the effective offset range when the instruction offset off (signed 16-bit)
# is added to a pointer's [omin, omax]
def ebpf_off_range(omin: W.W64, omax: W.W64, +off: U32) -> W.W64 & W.W64:
  +d = W.W64.from_parts(ebpf_fill_hi(off), G.ebpf_signed16(off))
  (W.W64.add(omin, d), W.W64.add(omax, d))

def ebpf_fst64(p: W.W64 & W.W64) -> W.W64:
  (a, b) = p
  a

def ebpf_snd64(p: W.W64 & W.W64) -> W.W64:
  (a, b) = p
  b

# Requiring a register is initialised (not uninitialised)
def ebpf_req_init(a: EbpfAbs, +pc: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match a:
    case EbpfAbsUninit{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejRegUninit{}}}
    case other:
      Done{Unit{}}

# MOV overwrites its destination, so it need not be initialised; every other
# ALU op reads it, so it must be
def ebpf_req_dst(op: I.EbpfAluOp, a: EbpfAbs, +pc: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match op:
    case I.EbpfMov{}:
      Done{Unit{}}
    case other:
      ebpf_req_init(a, pc)

def ebpf_vchk(ok: Bool, e: I.EbpfError) -> Result<&2, &2, I.EbpfError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def ebpf_maybe_const(known: Bool, c: W.W64) -> Maybe<&2, W.W64>:
  match known:
    case True{}:
      Some{c}
    case False{}:
      None{}

def ebpf_abs_scalar_const(a: EbpfAbs) -> Maybe<&2, W.W64>:
  match a:
    case EbpfAbsScalar{known, c, mn, mx}:
      ebpf_maybe_const(known, c)
    case other:
      None{}

# shift a pointer's offset interval by a known constant delta (add or sub);
# an unknown delta widens the offset to the full range (a later access then
# cannot be proved in bounds and is rejected)
def ebpf_ptr_shift.go(add: Bool, rgn: EbpfAbsRgn, omin: W.W64, omax: W.W64, +k: W.W64) -> EbpfAbs:
  match add:
    case True{}:
      EbpfAbsPtr{rgn, W.W64.add(omin, k), W.W64.add(omax, k)}
    case False{}:
      EbpfAbsPtr{rgn, W.W64.sub(omin, k), W.W64.sub(omax, k)}

def ebpf_ptr_shift(rgn: EbpfAbsRgn, omin: W.W64, omax: W.W64, d: Maybe<&2, W.W64>, add: Bool) -> EbpfAbs:
  match d:
    case None{}:
      EbpfAbsPtr{rgn, W.W64.zero(), W.W64.max()}
    case Some{k}:
      ebpf_ptr_shift.go(add, rgn, omin, omax, k)

# a known-constant ALU result, using the interpreter's own arithmetic
def ebpf_eval_const(w: I.EbpfWidth, op: I.EbpfAluOp, a: W.W64, b: W.W64) -> W.W64:
  A.ebpf_alu(w, op, a, b)

# MOV/ADD/SUB and the rest on scalars: a known constant where both operands
# are known constants, otherwise an unknown scalar
def ebpf_scalar_binop.go(ma: Maybe<&2, W.W64>, mb: Maybe<&2, W.W64>, w: I.EbpfWidth, op: I.EbpfAluOp) -> EbpfAbs:
  match ma:
    case None{}:
      ebpf_abs_anyscalar()
    case Some{a}:
      match mb:
        case None{}:
          ebpf_abs_anyscalar()
        case Some{b}:
          ebpf_abs_const(ebpf_eval_const(w, op, a, b))

def ebpf_scalar_binop(w: I.EbpfWidth, op: I.EbpfAluOp, a: EbpfAbs, b: EbpfAbs) -> EbpfAbs:
  ebpf_scalar_binop.go(ebpf_abs_scalar_const(a), ebpf_abs_scalar_const(b), w, op)

# the result of an abstract ALU op: a new value, or a rejection
type EbpfAluRes is Data:
  EbpfAluOk{v: EbpfAbs}
  EbpfAluReject{why: I.EbpfReject}

# ADD on abstract values: scalar+scalar, pointer+scalar, scalar+pointer
def ebpf_abs_add(a: EbpfAbs, b: EbpfAbs) -> EbpfAluRes:
  match a:
    case EbpfAbsScalar{ka, ca, mina, maxa}:
      match b:
        case EbpfAbsScalar{kb, cb, minb, maxb}:
          EbpfAluOk{ebpf_scalar_binop(I.EbpfBits64{}, I.EbpfAdd{}, EbpfAbsScalar{ka, ca, mina, maxa}, EbpfAbsScalar{kb, cb, minb, maxb})}
        case EbpfAbsPtr{rb, ominb, omaxb}:
          EbpfAluOk{ebpf_ptr_shift(rb, ominb, omaxb, ebpf_maybe_const(ka, ca), True{})}
        case other:
          EbpfAluReject{I.EbpfRejPointerArith{}}
    case EbpfAbsPtr{ra, omina, omaxa}:
      match b:
        case EbpfAbsScalar{kb, cb, minb, maxb}:
          EbpfAluOk{ebpf_ptr_shift(ra, omina, omaxa, ebpf_maybe_const(kb, cb), True{})}
        case other:
          EbpfAluReject{I.EbpfRejPointerArith{}}
    case other:
      EbpfAluReject{I.EbpfRejPointerArith{}}

# SUB: scalar-scalar, pointer-scalar, pointer-pointer (same region -> scalar)
def ebpf_abs_sub(a: EbpfAbs, b: EbpfAbs) -> EbpfAluRes:
  match a:
    case EbpfAbsScalar{ka, ca, mina, maxa}:
      match b:
        case EbpfAbsScalar{kb, cb, minb, maxb}:
          EbpfAluOk{ebpf_scalar_binop(I.EbpfBits64{}, I.EbpfSub{}, EbpfAbsScalar{ka, ca, mina, maxa}, EbpfAbsScalar{kb, cb, minb, maxb})}
        case other:
          EbpfAluReject{I.EbpfRejPointerArith{}}
    case EbpfAbsPtr{ra, omina, omaxa}:
      match b:
        case EbpfAbsScalar{kb, cb, minb, maxb}:
          EbpfAluOk{ebpf_ptr_shift(ra, omina, omaxa, ebpf_maybe_const(kb, cb), False{})}
        case EbpfAbsPtr{rb, ominb, omaxb}:
          EbpfAluOk{ebpf_abs_anyscalar()}
        case other:
          EbpfAluReject{I.EbpfRejPointerArith{}}
    case other:
      EbpfAluReject{I.EbpfRejPointerArith{}}

# any other ALU op: both operands must be scalars
def ebpf_abs_other(w: I.EbpfWidth, op: I.EbpfAluOp, a: EbpfAbs, b: EbpfAbs) -> EbpfAluRes:
  match a:
    case EbpfAbsScalar{ka, ca, mina, maxa}:
      match b:
        case EbpfAbsScalar{kb, cb, minb, maxb}:
          EbpfAluOk{ebpf_scalar_binop(w, op, EbpfAbsScalar{ka, ca, mina, maxa}, EbpfAbsScalar{kb, cb, minb, maxb})}
        case other:
          EbpfAluReject{I.EbpfRejPointerArith{}}
    case other:
      EbpfAluReject{I.EbpfRejPointerArith{}}

# MOV: the source value itself (a scalar, or a pointer copied)
def ebpf_abs_alu(w: I.EbpfWidth, op: I.EbpfAluOp, a: EbpfAbs, b: EbpfAbs) -> EbpfAluRes:
  match op:
    case I.EbpfAdd{}:
      ebpf_abs_add(a, b)
    case I.EbpfSub{}:
      ebpf_abs_sub(a, b)
    case I.EbpfMov{}:
      EbpfAluOk{b}
    case other:
      ebpf_abs_other(w, op, a, b)

# Stack init mask: read whether sz bytes from offset o are all initialised,
def ebpf_at_mask(mask: List<&2, Bool>, o: Nat) -> Bool:
  Maybe.default(&2, Bool, List.get(&2, Bool, mask, o), False{})

# and set them. Offsets must be constant (omin == omax) for the stack.
def ebpf_mask_all(+mask: List<&2, Bool>, n: Nat, +o: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(ebpf_at_mask(mask, o), ebpf_mask_all(mask, p, 1n+o))

def ebpf_mask_set(n: Nat, mask: List<&2, Bool>, +o: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      mask
    case 1n+p:
      ebpf_mask_set(p, List.set(&2, Bool, mask, o, True{}), 1n+o)

# the abstract value of a register
def ebpf_reg(state: EbpfAbsState, r: I.EbpfReg) -> EbpfAbs:
  match state:
    case EbpfAbsState{regs, stack}:
      ebpf_abs_get(regs, r)

def ebpf_with_regs(state: EbpfAbsState, regs: List<&2, EbpfAbs>) -> EbpfAbsState:
  match state:
    case EbpfAbsState{old, stack}:
      EbpfAbsState{regs, stack}

def ebpf_set_reg(state: EbpfAbsState, r: I.EbpfReg, v: EbpfAbs) -> EbpfAbsState:
  match state:
    case EbpfAbsState{regs, stack}:
      EbpfAbsState{ebpf_abs_set(regs, r, v), stack}

# the source operand of an ALU/JMP as an abstract value
def ebpf_abs_src(state: EbpfAbsState, s: I.EbpfSrc) -> EbpfAbs:
  match s:
    case I.EbpfK{imm}:
      ebpf_abs_const(A.ebpf_imm(imm))
    case I.EbpfX{reg}:
      ebpf_reg(state, reg)

# Memory access checks. A load or store through a pointer must stay inside
# its region. For the stack the offset must be a known constant, and a read
# needs every byte initialised (its mask bit set); a write sets them.

def ebpf_is_stack(rgn: EbpfAbsRgn) -> Bool:
  match rgn:
    case EbpfAbsStack{}:
      True{}
    case other:
      False{}

def ebpf_const_off.go(eq: Bool, lo: W.W64) -> Maybe<&2, Nat>:
  match eq:
    case True{}:
      Some{U32.to_nat(W.W64.lo(lo))}
    case False{}:
      None{}

def ebpf_const_off(+lo: W.W64, hi: W.W64) -> Maybe<&2, Nat>:
  ebpf_const_off.go(W.W64.is_eq(lo, hi), lo)





def ebpf_stack_load.fin(ok: Bool, state: EbpfAbsState, +pc: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match ok:
    case True{}:
      Done{ebpf_set_reg(state, dst, ebpf_abs_anyscalar())}
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejStackUninit{}}}
def ebpf_stack_load.init(state: EbpfAbsState, +pc: Nat, +co: Nat, +n: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match state:
    case EbpfAbsState{regs, +stack}:
      ebpf_stack_load.fin(ebpf_mask_all(stack, n, co), state, pc, dst)
def ebpf_stack_load.go(state: EbpfAbsState, +pc: Nat, +co: Nat, inb: Bool, +n: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match inb:
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejAccess{}}}
    case True{}:
      ebpf_stack_load.init(state, pc, co, n, dst)
# a stack load of n bytes at constant offset co: initialised? in bounds?
def ebpf_stack_load(state: EbpfAbsState, +pc: Nat, mco: Maybe<&2, Nat>, +n: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match mco:
    case None{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejMisaligned{}}}
    case Some{+co}:
      ebpf_stack_load.go(state, pc, co, Nat.is_le(Nat.add(co, n), 512n), n, dst)




def ebpf_region_load.go(ok: Bool, state: EbpfAbsState, +pc: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match ok:
    case True{}:
      Done{ebpf_set_reg(state, dst, ebpf_abs_anyscalar())}
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejAccess{}}}
def ebpf_region_load.sz(msz: Maybe<&2, U32>, state: EbpfAbsState, +pc: Nat, lo: W.W64, hi: W.W64, +n: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match msz:
    case None{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejNotPointer{}}}
    case Some{rsz}:
      ebpf_region_load.go(ebpf_fits(rsz, lo, hi, U32.from_nat(n)), state, pc, dst)
# a non-stack load of n bytes over offset range [lo, hi]: in bounds?
def ebpf_region_load(state: EbpfAbsState, +pc: Nat, rgn: EbpfAbsRgn, vc: EbpfVerifyCtx, lo: W.W64, hi: W.W64, +n: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_region_load.sz(ebpf_region_size(vc, rgn), state, pc, lo, hi, n, dst)

def ebpf_load_check.ptr(stk: Bool, vc: EbpfVerifyCtx, +pc: Nat, state: EbpfAbsState, rgn: EbpfAbsRgn, +omin: W.W64, +omax: W.W64, +off: U32, +n: Nat, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match stk:
    case True{}:
      ebpf_stack_load(state, pc, ebpf_const_off(ebpf_fst64(ebpf_off_range(omin, omax, off)), ebpf_snd64(ebpf_off_range(omin, omax, off))), n, dst)
    case False{}:
      ebpf_region_load(state, pc, rgn, vc, ebpf_fst64(ebpf_off_range(omin, omax, off)), ebpf_snd64(ebpf_off_range(omin, omax, off)), n, dst)

# a load: dispatch on the base pointer's region
def ebpf_load_check(vc: EbpfVerifyCtx, +pc: Nat, state: EbpfAbsState, base: EbpfAbs, off: U32, size: I.EbpfSize, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match base:
    case EbpfAbsPtr{+rgn, omin, omax}:
      ebpf_load_check.ptr(ebpf_is_stack(rgn), vc, pc, state, rgn, omin, omax, off, U32.to_nat(M.EbpfSize.bytes(size)), dst)
    case other:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejNotPointer{}}}

def ebpf_is_scalar(v: EbpfAbs) -> Bool:
  match v:
    case EbpfAbsScalar{k, c, mn, mx}:
      True{}
    case EbpfAbsUnknown{}:
      True{}
    case other:
      False{}

def ebpf_stack_store.set(state: EbpfAbsState, +pc: Nat, +co: Nat, +n: Nat, v: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match state:
    case EbpfAbsState{regs, stack}:
      Done{EbpfAbsState{regs, ebpf_mask_set(n, stack, co)}}

def ebpf_stack_store.go(state: EbpfAbsState, +pc: Nat, +co: Nat, inb: Bool, +n: Nat, v: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match inb:
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejAccess{}}}
    case True{}:
      ebpf_stack_store.set(state, pc, co, n, v)

# A store of value v (n bytes) at a base pointer. Non-stack regions take a
# scalar (a pointer may be stored only on the stack, at an 8-aligned
# constant offset); a store sets the stack init mask.
def ebpf_stack_store(state: EbpfAbsState, +pc: Nat, mco: Maybe<&2, Nat>, +n: Nat, v: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match mco:
    case None{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejMisaligned{}}}
    case Some{+co}:
      ebpf_stack_store.go(state, pc, co, Nat.is_le(Nat.add(co, n), 512n), n, v)

def ebpf_region_store.go(ok: Bool, state: EbpfAbsState, +pc: Nat) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match ok:
    case True{}:
      Done{state}
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejAccess{}}}

def ebpf_region_store.sz(msz: Maybe<&2, U32>, state: EbpfAbsState, +pc: Nat, lo: W.W64, hi: W.W64, +n: Nat) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match msz:
    case None{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejNotPointer{}}}
    case Some{rsz}:
      ebpf_region_store.go(ebpf_fits(rsz, lo, hi, U32.from_nat(n)), state, pc)

def ebpf_region_store.val(scal: Bool, msz: Maybe<&2, U32>, state: EbpfAbsState, +pc: Nat, lo: W.W64, hi: W.W64, +n: Nat) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match scal:
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejPointerLeak{}}}
    case True{}:
      ebpf_region_store.sz(msz, state, pc, lo, hi, n)

def ebpf_region_store(state: EbpfAbsState, +pc: Nat, rgn: EbpfAbsRgn, vc: EbpfVerifyCtx, lo: W.W64, hi: W.W64, +n: Nat, v: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_region_store.val(ebpf_is_scalar(v), ebpf_region_size(vc, rgn), state, pc, lo, hi, n)

def ebpf_store_check.ptr(stk: Bool, vc: EbpfVerifyCtx, +pc: Nat, state: EbpfAbsState, rgn: EbpfAbsRgn, +omin: W.W64, +omax: W.W64, +off: U32, +n: Nat, v: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match stk:
    case True{}:
      ebpf_stack_store(state, pc, ebpf_const_off(ebpf_fst64(ebpf_off_range(omin, omax, off)), ebpf_snd64(ebpf_off_range(omin, omax, off))), n, v)
    case False{}:
      ebpf_region_store(state, pc, rgn, vc, ebpf_fst64(ebpf_off_range(omin, omax, off)), ebpf_snd64(ebpf_off_range(omin, omax, off)), n, v)

def ebpf_store_check(vc: EbpfVerifyCtx, +pc: Nat, state: EbpfAbsState, base: EbpfAbs, off: U32, size: I.EbpfSize, v: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match base:
    case EbpfAbsPtr{+rgn, omin, omax}:
      ebpf_store_check.ptr(ebpf_is_stack(rgn), vc, pc, state, rgn, omin, omax, off, U32.to_nat(M.EbpfSize.bytes(size)), v)
    case other:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejNotPointer{}}}

# requiring a register holds a scalar (reject a pointer where a number is
# needed, e.g. a jump comparison, NEG, a byte swap)
def ebpf_req_scalar(a: EbpfAbs, +pc: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match a:
    case EbpfAbsScalar{k, c, mn, mx}:
      Done{Unit{}}
    case EbpfAbsUnknown{}:
      Done{Unit{}}
    case EbpfAbsUninit{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejRegUninit{}}}
    case EbpfAbsPtr{r, lo, hi}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejPointerCompare{}}}

def ebpf_after(r: Result<&2, &2, I.EbpfError, Unit>, s: Result<&2, &2, I.EbpfError, EbpfAbsState>) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      s

def ebpf_alu_res(res: EbpfAluRes, +pc: Nat, state: EbpfAbsState, dst: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match res:
    case EbpfAluOk{v}:
      Done{ebpf_set_reg(state, dst, v)}
    case EbpfAluReject{why}:
      Fail{I.EbpfErrRejected{pc, why}}

# forbid writing R10 (the frame pointer is read-only)
def ebpf_req_writable(dst: I.EbpfReg, +pc: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match dst:
    case I.EbpfR10{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejWriteFp{}}}
    case other:
      Done{Unit{}}

# a 64-bit-immediate load's abstract result
def ebpf_lddw_abs(k: I.EbpfLddwKind, imm: U32, next: U32) -> EbpfAbs:
  match k:
    case I.EbpfLdImm64{}:
      ebpf_abs_const(W.W64.from_parts(next, imm))
    case I.EbpfLdMapFd{}:
      EbpfAbsPtr{EbpfAbsMap{}, W.W64.zero(), W.W64.zero()}
    case other:
      ebpf_abs_anyscalar()

def ebpf_is_map_ptr(a: EbpfAbs) -> Bool:
  match a:
    case EbpfAbsPtr{r, lo, hi}:
      ebpf_rgn_is_map(r)
    case other:
      False{}

def ebpf_is_mem_ptr(a: EbpfAbs) -> Bool:
  match a:
    case EbpfAbsPtr{r, lo, hi}:
      Bool.not(ebpf_rgn_is_map(r))
    case other:
      False{}

# a helper call's argument check: each sig kind against the register
def ebpf_arg_ok(kind: H.EbpfArgKind, a: EbpfAbs) -> Bool:
  match kind:
    case H.EbpfArgScalar{}:
      ebpf_is_scalar(a)
    case H.EbpfArgMap{}:
      ebpf_is_map_ptr(a)
    case H.EbpfArgKey{}:
      ebpf_is_mem_ptr(a)
    case H.EbpfArgValue{}:
      ebpf_is_mem_ptr(a)



# check each helper argument against its signature kind (R1, R2, ...)
def ebpf_argreg(n: U32) -> I.EbpfReg:
  Maybe.default(&2, I.EbpfReg, I.EbpfReg.of_num(U32.add(n, 1)), I.EbpfR0{})

def ebpf_args_pick(ok: Bool, +pc: Nat, rest: Result<&2, &2, I.EbpfError, Unit>) -> Result<&2, &2, I.EbpfError, Unit>:
  match ok:
    case True{}:
      rest
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejHelperArg{}}}

def ebpf_args_go(kinds: List<&2, H.EbpfArgKind>, +pc: Nat, +state: EbpfAbsState, +n: U32) -> Result<&2, &2, I.EbpfError, Unit>:
  match kinds:
    case Nil{}:
      Done{Unit{}}
    case Con{kind, t}:
      ebpf_args_pick(ebpf_arg_ok(kind, ebpf_reg(state, ebpf_argreg(n))), pc, ebpf_args_go(t, pc, state, U32.add(n, 1)))

# clobber R1 to R5 (caller-saved / scratch) to unknown after a call
def ebpf_clobber_args(state: EbpfAbsState) -> EbpfAbsState:
  ebpf_set_reg(ebpf_set_reg(ebpf_set_reg(ebpf_set_reg(ebpf_set_reg(state, I.EbpfR1{}, EbpfAbsUnknown{}), I.EbpfR2{}, EbpfAbsUnknown{}), I.EbpfR3{}, EbpfAbsUnknown{}), I.EbpfR4{}, EbpfAbsUnknown{}), I.EbpfR5{}, EbpfAbsUnknown{})

# R0 after a helper, by its return kind. A map-value-or-null result is kept
# as an unknown scalar: the program must null-check it before use, which
# this analysis does not model, so dereferencing it is rejected.
def ebpf_ret_abs(ret: H.EbpfRetKind) -> EbpfAbs:
  match ret:
    case H.EbpfRetScalar{}:
      ebpf_abs_anyscalar()
    case H.EbpfRetMapValueOrNull{}:
      ebpf_abs_anyscalar()

def ebpf_call_after(sig: H.EbpfHelperSig, state: EbpfAbsState) -> EbpfAbsState:
  match sig:
    case H.EbpfHelperSig{args, ret}:
      ebpf_set_reg(ebpf_clobber_args(state), I.EbpfR0{}, ebpf_ret_abs(ret))

def ebpf_call_sig(msig: Maybe<&2, H.EbpfHelperSig>, +pc: Nat, +state: EbpfAbsState, id: U32) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match msig:
    case None{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejHelperUnknown{}}}
    case Some{+sig}:
      ebpf_after(ebpf_args_go(H.EbpfHelperSig.args(sig), pc, state, 0), Done{ebpf_call_after(sig, state)})





def ebpf_small_to_size(s: I.EbpfSmall) -> I.EbpfSize:
  match s:
    case I.EbpfSmallW{}:
      I.EbpfSizeW{}
    case I.EbpfSmallH{}:
      I.EbpfSizeH{}
    case I.EbpfSmallB{}:
      I.EbpfSizeB{}

def ebpf_has_packet(vc: EbpfVerifyCtx) -> Bool:
  match vc:
    case EbpfVerifyCtx{cs, ps, mvs, hp}:
      hp

def ebpf_ldabs_check.go(ok: Bool, state: EbpfAbsState, +pc: Nat) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match ok:
    case True{}:
      Done{ebpf_set_reg(state, I.EbpfR0{}, ebpf_abs_anyscalar())}
    case False{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejUnsupported{}}}

# LD_ABS / LD_IND read the packet into R0; require a packet to exist. The
# access offset is dynamic, so this is modelled as "R0 becomes a scalar";
# the interpreter bounds-checks the actual access at run time.
def ebpf_ldabs_check(vc: EbpfVerifyCtx, +pc: Nat, state: EbpfAbsState) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_ldabs_check.go(ebpf_has_packet(vc), state, pc)

def ebpf_atomic_size(s: I.EbpfAtomicSize) -> I.EbpfSize:
  match s:
    case I.EbpfAtomicW{}:
      I.EbpfSizeW{}
    case I.EbpfAtomicDW{}:
      I.EbpfSizeDW{}

def ebpf_atomic_has_fetch(op: I.EbpfAtomicOp) -> Bool:
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

def ebpf_atomic_wb.plain(fetch: Bool, state: EbpfAbsState, src: I.EbpfReg) -> EbpfAbsState:
  match fetch:
    case True{}:
      ebpf_set_reg(state, src, ebpf_abs_anyscalar())
    case False{}:
      state

def ebpf_atomic_wb.go(op: I.EbpfAtomicOp, state: EbpfAbsState, src: I.EbpfReg) -> EbpfAbsState:
  match op:
    case I.EbpfAtCmpxchg{}:
      ebpf_set_reg(state, I.EbpfR0{}, ebpf_abs_anyscalar())
    case other:
      ebpf_atomic_wb.plain(ebpf_atomic_has_fetch(op), state, src)

def ebpf_atomic_wb(r: Result<&2, &2, I.EbpfError, EbpfAbsState>, op: I.EbpfAtomicOp, src: I.EbpfReg) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{state}:
      Done{ebpf_atomic_wb.go(op, state, src)}

# ATOMIC: a read-modify-write to memory through dst (a scalar in src). The
# access is bounds-checked like a store; a fetching op writes an unknown
# scalar back to src (or R0 for cmpxchg).
def ebpf_atomic_transfer(vc: EbpfVerifyCtx, +pc: Nat, +state: EbpfAbsState, size: I.EbpfAtomicSize, op: I.EbpfAtomicOp, +dst: I.EbpfReg, src: I.EbpfReg, off: U32) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_atomic_wb(ebpf_store_check(vc, pc, state, ebpf_reg(state, dst), off, ebpf_atomic_size(size), ebpf_abs_anyscalar()), op, src)

# a call: a helper (checked against ~sigs) or a local function (not analysed)
def ebpf_call_transfer(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, +pc: Nat, state: EbpfAbsState, kind: I.EbpfCallKind, +imm: U32) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match kind:
    case I.EbpfCallHelper{}:
      ebpf_call_sig(sigs(imm), pc, state, imm)
    case I.EbpfCallLocal{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejUnsupported{}}}
    case I.EbpfCallBtf{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejUnsupported{}}}

# writing dst (not R10) with the result of an ALU/MOV/NEG/load
def ebpf_write(dst: I.EbpfReg, +pc: Nat, res: Result<&2, &2, I.EbpfError, EbpfAbsState>) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_after(ebpf_req_writable(dst, pc), res)

# NEG / MOVSX / END: dst must be a scalar; the result is a scalar (unknown,
# conservatively)
def ebpf_scalar_op(state: EbpfAbsState, +pc: Nat, +dst: I.EbpfReg, a: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_write(dst, pc, ebpf_after(ebpf_req_scalar(a, pc), Done{ebpf_set_reg(state, dst, ebpf_abs_anyscalar())}))

# a JMP condition: both operands must be scalars (no pointer comparisons)
def ebpf_jmp_check(state: EbpfAbsState, +pc: Nat, dst: EbpfAbs, src: EbpfAbs) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_after(ebpf_req_scalar(dst, pc), ebpf_after(ebpf_req_scalar(src, pc), Done{state}))

# EXIT: R0 must be a scalar (no pointer returned to the caller)
def ebpf_exit_check.go(a: EbpfAbs, state: EbpfAbsState, +pc: Nat) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match a:
    case EbpfAbsPtr{r, lo, hi}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejReturn{}}}
    case EbpfAbsUninit{}:
      Fail{I.EbpfErrRejected{pc, I.EbpfRejRegUninit{}}}
    case other:
      Done{state}

def ebpf_exit_check(+state: EbpfAbsState, +pc: Nat) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  ebpf_exit_check.go(ebpf_reg(state, I.EbpfR0{}), state, pc)

# the abstract transfer of one instruction over a state. ~sigs gives helper
# signatures. Local (BPF-to-BPF) calls are not analysed here and are
# rejected (EbpfRejUnsupported); the README says so.
def ebpf_transfer(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, +vc: EbpfVerifyCtx, +pc: Nat, +i: I.EbpfInsn, +state: EbpfAbsState) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match i:
    case I.EbpfAlu{w, op, dst, src}:
      ebpf_write(dst, pc, ebpf_after(ebpf_req_dst(op, ebpf_reg(state, dst), pc), ebpf_after(ebpf_req_init(ebpf_abs_src(state, src), pc), ebpf_alu_res(ebpf_abs_alu(w, op, ebpf_reg(state, dst), ebpf_abs_src(state, src)), pc, state, dst))))
    case I.EbpfNeg{w, dst}:
      ebpf_scalar_op(state, pc, dst, ebpf_reg(state, dst))
    case I.EbpfMovsx32{bits, dst, src}:
      ebpf_scalar_op(state, pc, dst, ebpf_reg(state, src))
    case I.EbpfMovsx64{bits, dst, src}:
      ebpf_scalar_op(state, pc, dst, ebpf_reg(state, src))
    case I.EbpfEnd{kind, bits, dst}:
      ebpf_scalar_op(state, pc, dst, ebpf_reg(state, dst))
    case I.EbpfLddw{kind, dst, imm, next}:
      ebpf_write(dst, pc, Done{ebpf_set_reg(state, dst, ebpf_lddw_abs(kind, imm, next))})
    case I.EbpfLdx{size, dst, src, off}:
      ebpf_write(dst, pc, ebpf_after(ebpf_req_init(ebpf_reg(state, src), pc), ebpf_load_check(vc, pc, state, ebpf_reg(state, src), off, size, dst)))
    case I.EbpfLdxs{size, dst, src, off}:
      ebpf_write(dst, pc, ebpf_after(ebpf_req_init(ebpf_reg(state, src), pc), ebpf_load_check(vc, pc, state, ebpf_reg(state, src), off, ebpf_small_to_size(size), dst)))
    case I.EbpfSt{size, dst, off, imm}:
      ebpf_after(ebpf_req_init(ebpf_reg(state, dst), pc), ebpf_store_check(vc, pc, state, ebpf_reg(state, dst), off, size, ebpf_abs_const(A.ebpf_imm(imm))))
    case I.EbpfStx{size, dst, src, off}:
      ebpf_after(ebpf_req_init(ebpf_reg(state, dst), pc), ebpf_after(ebpf_req_init(ebpf_reg(state, src), pc), ebpf_store_check(vc, pc, state, ebpf_reg(state, dst), off, size, ebpf_reg(state, src))))
    case I.EbpfAtomic{size, op, dst, src, off}:
      ebpf_after(ebpf_req_init(ebpf_reg(state, dst), pc), ebpf_after(ebpf_req_scalar(ebpf_reg(state, src), pc), ebpf_atomic_transfer(vc, pc, state, size, op, dst, src, off)))
    case I.EbpfLdAbs{size, imm}:
      ebpf_ldabs_check(vc, pc, state)
    case I.EbpfLdInd{size, src, imm}:
      ebpf_after(ebpf_req_scalar(ebpf_reg(state, src), pc), ebpf_ldabs_check(vc, pc, state))
    case I.EbpfJa{off}:
      Done{state}
    case I.EbpfJa32{imm}:
      Done{state}
    case I.EbpfJmp{w, cond, dst, src, off}:
      ebpf_jmp_check(state, pc, ebpf_reg(state, dst), ebpf_abs_src(state, src))
    case I.EbpfCall{kind, imm}:
      ebpf_call_transfer(~sigs, pc, state, kind, imm)
    case I.EbpfExit{}:
      ebpf_exit_check(state, pc)

# The forward pass. states is a Maybe<EbpfAbsState> per slot (None until a
# predecessor reaches it); slot 0 starts with the entry state. Nodes are
# processed in slot order (a DAG, so all predecessors come first); each
# node's out-state is merged into its successors' slots. On any transfer
# rejection the whole program is rejected.

def ebpf_states_init(n: Nat) -> List<&2, Maybe<&2, EbpfAbsState>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Some{ebpf_state_entry()}, List.replicate(Maybe<&2, EbpfAbsState>, p, None{})}

def ebpf_states_get(states: List<&2, Maybe<&2, EbpfAbsState>>, slot: Nat) -> Maybe<&2, EbpfAbsState>:
  Maybe.default(&2, Maybe<&2, EbpfAbsState>, List.get(&2, Maybe<&2, EbpfAbsState>, states, slot), None{})

# merge out-state into the slot's stored state
def ebpf_states_merge(+states: List<&2, Maybe<&2, EbpfAbsState>>, +slot: Nat, out: EbpfAbsState) -> List<&2, Maybe<&2, EbpfAbsState>>:
  List.set(&2, Maybe<&2, EbpfAbsState>, states, slot, Some{ebpf_state_opt_merge(ebpf_states_get(states, slot), out)})

# propagate out-state to the successors of a node, per its flow
def ebpf_prop(states: List<&2, Maybe<&2, EbpfAbsState>>, +slot: Nat, +slots: Nat, fl: G.EbpfFlow, +n: Nat, +out: EbpfAbsState) -> List<&2, Maybe<&2, EbpfAbsState>>:
  match fl:
    case G.EbpfFlowNext{}:
      ebpf_states_merge(states, Nat.add(slot, slots), out)
    case G.EbpfFlowJump{off}:
      ebpf_states_merge(states, G.ebpf_target_slot(G.ebpf_branch_target(slot, off, n)), out)
    case G.EbpfFlowBranch{off}:
      ebpf_states_merge(ebpf_states_merge(states, Nat.add(slot, slots), out), G.ebpf_target_slot(G.ebpf_branch_target(slot, off, n)), out)
    case G.EbpfFlowCall{imm}:
      ebpf_states_merge(states, Nat.add(slot, slots), out)
    case G.EbpfFlowJa32{imm}:
      ebpf_states_merge(states, G.ebpf_target_slot(G.ebpf_call_target(slot, imm, n)), out)
    case G.EbpfFlowExit{}:
      states

def ebpf_verify.in(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, vc: EbpfVerifyCtx, +slot: Nat, insn: I.EbpfInsn, instate: Maybe<&2, EbpfAbsState>) -> Result<&2, &2, I.EbpfError, EbpfAbsState>:
  match instate:
    case None{}:
      Done{ebpf_state_entry()}
    case Some{st}:
      ebpf_transfer(~sigs, vc, slot, insn, st)

def EbpfInsn.flow2(i: I.EbpfInsn) -> G.EbpfFlow:
  G.EbpfInsn.flow(i)



def ebpf_step_prop.go(res: Result<&2, &2, I.EbpfError, EbpfAbsState>, +slot: Nat, +slots: Nat, fl: G.EbpfFlow, +n: Nat, states: List<&2, Maybe<&2, EbpfAbsState>>) -> Result<&2, &2, I.EbpfError, List<&2, Maybe<&2, EbpfAbsState>>>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{out}:
      Done{ebpf_prop(states, slot, slots, fl, n, out)}

# transfer one node and propagate its out-state to successors, or Fail
def ebpf_step_prop(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, vc: EbpfVerifyCtx, +n: Nat, nd: G.EbpfNode, +states: List<&2, Maybe<&2, EbpfAbsState>>) -> Result<&2, &2, I.EbpfError, List<&2, Maybe<&2, EbpfAbsState>>>:
  match nd:
    case G.EbpfNode{+slot, +slots, +insn}:
      ebpf_step_prop.go(ebpf_verify.in(~sigs, vc, slot, insn, ebpf_states_get(states, slot)), slot, slots, EbpfInsn.flow2(insn), n, states)

def ebpf_verify.done(cur: Result<&2, &2, I.EbpfError, List<&2, Maybe<&2, EbpfAbsState>>>) -> Result<&2, &2, I.EbpfError, Unit>:
  match cur:
    case Fail{e}:
      Fail{e}
    case Done{states}:
      Done{Unit{}}

# the forward pass: cur threads the per-slot states (or the first failure)
def ebpf_verify.go(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, +vc: EbpfVerifyCtx, +n: Nat, nodes: List<&2, G.EbpfNode>, cur: Result<&2, &2, I.EbpfError, List<&2, Maybe<&2, EbpfAbsState>>>) -> Result<&2, &2, I.EbpfError, Unit>:
  match nodes:
    case Nil{}:
      ebpf_verify.done(cur)
    case Con{nd, t}:
      match cur:
        case Fail{e}:
          Fail{e}
        case Done{states}:
          ebpf_verify.go(~sigs, vc, n, t, ebpf_step_prop(~sigs, vc, n, nd, states))


# The verifier's options: the control-flow options and the region sizes
type EbpfVerifyOptions is Data:
  EbpfVerifyOptions{cfg: G.EbpfCfgOptions, ctx: EbpfVerifyCtx}

def EbpfVerifyOptions.default() -> EbpfVerifyOptions:
  EbpfVerifyOptions{G.EbpfCfgOptions.default(), EbpfVerifyCtx.default()}

# the context-size and packet options for an XDP program (a 24-byte xdp_md
# context with data/data_end), packets up to packet_size bytes
def EbpfVerifyOptions.xdp(packet_size: U32) -> EbpfVerifyOptions:
  EbpfVerifyOptions{G.EbpfCfgOptions.default(), EbpfVerifyCtx{24, packet_size, 0, True{}}}

def ebpf_verify.pass(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, vc: EbpfVerifyCtx, prog: List<&2, I.EbpfInsn>, cfgok: Result<&2, &2, I.EbpfError, Unit>) -> Result<&2, &2, I.EbpfError, Unit>:
  match cfgok:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      +nodes = G.ebpf_nodes(prog)
      ebpf_verify.go(~sigs, vc, G.ebpf_count_slots(nodes), nodes, Done{ebpf_states_init(G.ebpf_count_slots(nodes))})

# verify prog with helper signatures ~sigs and these options: the
# control-flow check (cfg.bend) then the abstract pass. Done{Unit{}} means
# accepted; a rejection carries the pc and reason.
def ebpf_verify_with(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, opts: EbpfVerifyOptions, +prog: List<&2, I.EbpfInsn>) -> Result<&2, &2, I.EbpfError, Unit>:
  match opts:
    case EbpfVerifyOptions{cfg, vc}:
      ebpf_verify.pass(~sigs, vc, prog, G.ebpf_cfg_check_with(cfg, prog))

# the standard helper signatures, default options
def ebpf_verify(prog: List<&2, I.EbpfInsn>) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_verify_with(~H.ebpf_helper_sigs.std, EbpfVerifyOptions.default(), prog)

# accepted?
def ebpf_accepts(r: Result<&2, &2, I.EbpfError, Unit>) -> Bool:
  Result.is_done(&2, &2, I.EbpfError, Unit, r)
