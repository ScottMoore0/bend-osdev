# bend-osdev-ebpf: control-flow checks (the first half of the verifier).
#
# From the Linux kernel's verifier documentation (Documentation/bpf/
# verifier.rst, a documentation page, not kernel source): before a program
# runs, its control flow is checked:
#   * the program is not empty and within the instruction limit;
#   * every jump and call-local target is a slot inside the program, and
#     lands on an instruction's first slot (not a wide instruction's second
#     slot, and not past the end);
#   * execution never falls off the end: the last instruction is EXIT or an
#     unconditional jump, and no reachable instruction's only successor is
#     past the end;
#   * every instruction is reachable from the start;
#   * there are no back edges (a jump or fall-through to an already-visited
#     instruction) unless the bounded-loop option allows them, which keeps
#     the program a DAG so it terminates.
# Targets are slot indices: an instruction at slot pc with offset off goes
# to slot pc + 1 + off (off is signed); a local call's imm is the signed
# offset to the callee's first slot. These checks work on the slot-indexed
# program (each instruction tagged with its slot), so indices are exact.
import Base
import ../word64/word64.bend as W
import ./insn.bend as I

type EbpfCfgOptions is Data:
  EbpfCfgOptions{max_insns: Nat, allow_loops: Bool}

# the kernel's default: up to 1,000,000 instructions, no back edges
def EbpfCfgOptions.default() -> EbpfCfgOptions:
  EbpfCfgOptions{1000000n, False{}}

def EbpfCfgOptions.loops(max: Nat) -> EbpfCfgOptions:
  EbpfCfgOptions{max, True{}}

# a slot's signed target pc + 1 + off, as a Nat index and whether it is in
# range (0 <= target < n). off is a 16-bit signed field.
type EbpfTarget is Data:
  EbpfTarget{to: Nat, ok: Bool}

def ebpf_signed16.go(neg: Bool, low: U32) -> U32:
  match neg:
    case True{}:
      U32.or(low, 4294901760)
    case False{}:
      low

def ebpf_signed16(off: U32) -> U32:
  +low = U32.and(65535, off)
  ebpf_signed16.go(U32.is_ge(low, 32768), low)

# the slot a branch at pc with offset off (relative to pc + 1) targets: the
# signed 32-bit sum pc + 1 + off, in range iff below n. pc and n are below
# 2^32 and off is a 16-bit signed field, so an in-range target never wraps;
# a backward or far target lands outside [0, n) and is rejected.
def ebpf_branch_target(pc: Nat, off: U32, n: Nat) -> EbpfTarget:
  +to = U32.add(U32.add(U32.from_nat(pc), ebpf_signed16(off)), 1)
  EbpfTarget{U32.to_nat(to), U32.is_lt(to, U32.from_nat(n))}

# a local call's target: pc + 1 + imm (imm a 32-bit signed offset)
def ebpf_call_target(pc: Nat, imm: U32, n: Nat) -> EbpfTarget:
  +to = U32.add(U32.add(U32.from_nat(pc), imm), 1)
  EbpfTarget{U32.to_nat(to), U32.is_lt(to, U32.from_nat(n))}

# An instruction's successors (slot indices) and whether it ends a path
# (EXIT) or always jumps (so the slot after it need not exist).

type EbpfFlow is Data:
  EbpfFlowNext{}
  EbpfFlowJump{off: U32}
  EbpfFlowBranch{off: U32}
  EbpfFlowCall{imm: U32}
  EbpfFlowExit{}
  EbpfFlowJa32{imm: U32}

def EbpfInsn.flow.call(k: I.EbpfCallKind, imm: U32) -> EbpfFlow:
  match k:
    case I.EbpfCallLocal{}:
      EbpfFlowCall{imm}
    case other:
      EbpfFlowNext{}

# how control leaves an instruction
def EbpfInsn.flow(i: I.EbpfInsn) -> EbpfFlow:
  match i:
    case I.EbpfJa{off}:
      EbpfFlowJump{off}
    case I.EbpfJa32{imm}:
      EbpfFlowJa32{imm}
    case I.EbpfJmp{w, cond, dst, src, off}:
      EbpfFlowBranch{off}
    case I.EbpfCall{kind, imm}:
      EbpfInsn.flow.call(kind, imm)
    case I.EbpfExit{}:
      EbpfFlowExit{}
    case other:
      EbpfFlowNext{}

# A node: an instruction, its first-slot index, and its slot count
type EbpfNode is Data:
  EbpfNode{slot: Nat, slots: Nat, insn: I.EbpfInsn}

def ebpf_nodes.go(prog: List<&2, I.EbpfInsn>, +slot: Nat, acc: List<&2, EbpfNode>) -> List<&2, EbpfNode>:
  match prog:
    case Nil{}:
      List.reverse(&2, EbpfNode, acc)
    case Con{+i, t}:
      +s = I.EbpfInsn.slots(i)
      ebpf_nodes.go(t, Nat.add(slot, s), Con{EbpfNode{slot, s, i}, acc})

# the instructions with their slot indices
def ebpf_nodes(prog: List<&2, I.EbpfInsn>) -> List<&2, EbpfNode>:
  ebpf_nodes.go(prog, 0n, Nil{})

# a Bool per slot: True at an instruction's first slot, False at a wide
# second slot (so is_start also rejects a target that lands mid-instruction)
def ebpf_starts.ins(n: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ebpf_starts.ins(p, Con{False{}, acc})

def ebpf_starts.go(nodes: List<&2, EbpfNode>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match nodes:
    case Nil{}:
      List.reverse(&2, Bool, acc)
    case Con{nd, t}:
      match nd:
        case EbpfNode{slot, slots, insn}:
          ebpf_starts.go(t, ebpf_starts.ins(Nat.sub(slots, 1n), Con{True{}, acc}))

def ebpf_starts(nodes: List<&2, EbpfNode>) -> List<&2, Bool>:
  ebpf_starts.go(nodes, Nil{})

def ebpf_is_start(starts: List<&2, Bool>, s: Nat) -> Bool:
  Maybe.default(&2, Bool, List.get(&2, Bool, starts, s), False{})

def ebpf_chk(ok: Bool, e: I.EbpfError) -> Result<&2, &2, I.EbpfError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def ebpf_both(r: Result<&2, &2, I.EbpfError, Unit>, s: Result<&2, &2, I.EbpfError, Unit>) -> Result<&2, &2, I.EbpfError, Unit>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      s

def ebpf_edge_back(+allow_loops: Bool, from: Nat, to: Nat, +pc: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match allow_loops:
    case True{}:
      Done{Unit{}}
    case False{}:
      ebpf_chk(Nat.is_lt(from, to), I.EbpfErrRejected{pc, I.EbpfRejBackEdge{}})

# a target slot must be an instruction start; when loops are off it must be
# strictly ahead of the branching slot (no back edges keep the CFG a DAG)
def ebpf_edge_ok(+allow_loops: Bool, starts: List<&2, Bool>, from: Nat, +to: Nat, +pc: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_both(ebpf_chk(ebpf_is_start(starts, to), I.EbpfErrRejected{pc, I.EbpfRejJumpOut{}}), ebpf_edge_back(allow_loops, from, to, pc))

# the target of a branch is in range (checked with ebpf_branch_target)
def ebpf_target_slot(t: EbpfTarget) -> Nat:
  match t:
    case EbpfTarget{to, ok}:
      to

def ebpf_target_ok(t: EbpfTarget) -> Bool:
  match t:
    case EbpfTarget{to, ok}:
      ok

# the slot after this instruction exists and is a start (never falls off)
def ebpf_fall_edge(starts: List<&2, Bool>, +fall: Nat, +slot: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_chk(ebpf_is_start(starts, fall), I.EbpfErrRejected{slot, I.EbpfRejFallsOff{}})

def ebpf_edge_checked(inrange: Bool, allow_loops: Bool, starts: List<&2, Bool>, +slot: Nat, to: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match inrange:
    case True{}:
      ebpf_edge_ok(allow_loops, starts, slot, to, slot)
    case False{}:
      Fail{I.EbpfErrRejected{slot, I.EbpfRejJumpOut{}}}

# a local call may target any instruction start in range (loops/recursion
# across functions are handled by the frame limit at run time)
def ebpf_call_checked(inrange: Bool, starts: List<&2, Bool>, +slot: Nat, to: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match inrange:
    case True{}:
      ebpf_chk(ebpf_is_start(starts, to), I.EbpfErrRejected{slot, I.EbpfRejCallTarget{}})
    case False{}:
      Fail{I.EbpfErrRejected{slot, I.EbpfRejCallTarget{}}}

def ebpf_jump_edge(+allow_loops: Bool, starts: List<&2, Bool>, n: Nat, +slot: Nat, off: U32) -> Result<&2, &2, I.EbpfError, Unit>:
  +tg = ebpf_branch_target(slot, off, n)
  ebpf_edge_checked(ebpf_target_ok(tg), allow_loops, starts, slot, ebpf_target_slot(tg))

def ebpf_ja32_edge(+allow_loops: Bool, starts: List<&2, Bool>, n: Nat, +slot: Nat, imm: U32) -> Result<&2, &2, I.EbpfError, Unit>:
  +tg = ebpf_call_target(slot, imm, n)
  ebpf_edge_checked(ebpf_target_ok(tg), allow_loops, starts, slot, ebpf_target_slot(tg))

def ebpf_call_edge(+allow_loops: Bool, starts: List<&2, Bool>, n: Nat, +slot: Nat, imm: U32) -> Result<&2, &2, I.EbpfError, Unit>:
  +tg = ebpf_call_target(slot, imm, n)
  ebpf_call_checked(ebpf_target_ok(tg), starts, slot, ebpf_target_slot(tg))

# a fall-through edge (to the next slot) and/or a jump edge, per the flow
def ebpf_flow_edges(+allow_loops: Bool, +starts: List<&2, Bool>, +n: Nat, +slot: Nat, +fall: Nat, fl: EbpfFlow) -> Result<&2, &2, I.EbpfError, Unit>:
  match fl:
    case EbpfFlowNext{}:
      ebpf_fall_edge(starts, fall, slot)
    case EbpfFlowJump{off}:
      ebpf_jump_edge(allow_loops, starts, n, slot, off)
    case EbpfFlowBranch{off}:
      ebpf_both(ebpf_fall_edge(starts, fall, slot), ebpf_jump_edge(allow_loops, starts, n, slot, off))
    case EbpfFlowCall{imm}:
      ebpf_both(ebpf_fall_edge(starts, fall, slot), ebpf_call_edge(allow_loops, starts, n, slot, imm))
    case EbpfFlowJa32{imm}:
      ebpf_ja32_edge(allow_loops, starts, n, slot, imm)
    case EbpfFlowExit{}:
      Done{Unit{}}

# the checks for one node's edges (n is the slot count)
def ebpf_node_edges(+allow_loops: Bool, starts: List<&2, Bool>, n: Nat, +nd: EbpfNode) -> Result<&2, &2, I.EbpfError, Unit>:
  match nd:
    case EbpfNode{+slot, slots, insn}:
      ebpf_flow_edges(allow_loops, starts, n, slot, Nat.add(slot, slots), EbpfInsn.flow(insn))

def ebpf_edges.go(+allow_loops: Bool, +starts: List<&2, Bool>, +n: Nat, nodes: List<&2, EbpfNode>, acc: Result<&2, &2, I.EbpfError, Unit>) -> Result<&2, &2, I.EbpfError, Unit>:
  match nodes:
    case Nil{}:
      acc
    case Con{nd, t}:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{u}:
          ebpf_edges.go(allow_loops, starts, n, t, ebpf_node_edges(allow_loops, starts, n, nd))

# every edge of every instruction is in range and a valid target
def ebpf_edges(+allow_loops: Bool, starts: List<&2, Bool>, n: Nat, nodes: List<&2, EbpfNode>) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_edges.go(allow_loops, starts, n, nodes, Done{Unit{}})

# Reachability. With no back edges every edge points forward, so one
# left-to-right sweep suffices: slot 0 is reached, and processing a reached
# instruction marks its successors (all ahead) reached. reached is a Bool
# per slot, indexed by absolute slot. (With loops allowed this
# under-approximates, so reachability is only checked when loops are off;
# the README says so.)

def ebpf_at(xs: List<&2, Bool>, i: Nat) -> Bool:
  Maybe.default(&2, Bool, List.get(&2, Bool, xs, i), False{})

def ebpf_reach.set.go(xs: List<&2, Bool>, to: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      List.reverse(&2, Bool, acc)
    case Con{h, t}:
      match to:
        case 0n:
          List.reverse.go(&2, Bool, acc, Con{True{}, t})
        case 1n+p:
          ebpf_reach.set.go(t, p, Con{h, acc})

# reached with the entry at index to set True
def ebpf_reach.set(xs: List<&2, Bool>, to: Nat) -> List<&2, Bool>:
  ebpf_reach.set.go(xs, to, Nil{})

# mark the successors of the node at slot (whose flow is fl); n slots total
def ebpf_reach.mark(reached: List<&2, Bool>, +slot: Nat, +slots: Nat, fl: EbpfFlow, +n: Nat) -> List<&2, Bool>:
  match fl:
    case EbpfFlowNext{}:
      ebpf_reach.set(reached, Nat.add(slot, slots))
    case EbpfFlowJump{off}:
      ebpf_reach.set(reached, ebpf_target_slot(ebpf_branch_target(slot, off, n)))
    case EbpfFlowBranch{off}:
      ebpf_reach.set(ebpf_reach.set(reached, Nat.add(slot, slots)), ebpf_target_slot(ebpf_branch_target(slot, off, n)))
    case EbpfFlowCall{imm}:
      ebpf_reach.set(ebpf_reach.set(reached, Nat.add(slot, slots)), ebpf_target_slot(ebpf_call_target(slot, imm, n)))
    case EbpfFlowJa32{imm}:
      ebpf_reach.set(reached, ebpf_target_slot(ebpf_call_target(slot, imm, n)))
    case EbpfFlowExit{}:
      reached

# whether the next node (head of t) is reached in the given reached list
def ebpf_reach.ahead(reached: List<&2, Bool>, t: List<&2, EbpfNode>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{nd, r}:
      match nd:
        case EbpfNode{slot, slots, insn}:
          ebpf_at(reached, slot)

def ebpf_reach.next_slot(t: List<&2, EbpfNode>) -> Nat:
  match t:
    case Nil{}:
      0n
    case Con{nd, r}:
      match nd:
        case EbpfNode{slot, slots, insn}:
          slot

def ebpf_reach.go(nodes: List<&2, EbpfNode>, ok: Bool, +slot: Nat, reached: List<&2, Bool>, +n: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match nodes:
    case Nil{}:
      Done{Unit{}}
    case Con{nd, +t}:
      match nd:
        case EbpfNode{+slot2, +slots, insn}:
          match ok:
            case False{}:
              Fail{I.EbpfErrRejected{slot, I.EbpfRejUnreachable{}}}
            case True{}:
              +marked = ebpf_reach.mark(reached, slot2, slots, EbpfInsn.flow(insn), n)
              ebpf_reach.go(t, ebpf_reach.ahead(marked, t), ebpf_reach.next_slot(t), marked, n)

def ebpf_reach.init(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{True{}, List.replicate(Bool, p, False{})}

# every instruction start is reached from slot 0
def ebpf_reach_check(nodes: List<&2, EbpfNode>, +n: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_reach.go(nodes, True{}, 0n, ebpf_reach.init(n), n)

# The whole control-flow check: length, then every edge in range and landing
# on an instruction start (no fall-off, no jump out, no jump into a wide
# second slot, no back edges unless allowed), then, when loops are off,
# reachability of every instruction. n is the slot count.

def ebpf_cfg.len(+n: Nat, +count: Nat, max: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_both(ebpf_chk(Nat.is_lt(0n, count), I.EbpfErrRejected{0n, I.EbpfRejEmpty{}}), ebpf_chk(Nat.is_le(n, max), I.EbpfErrRejected{0n, I.EbpfRejTooLong{n}}))

def ebpf_cfg.reach(allow_loops: Bool, nodes: List<&2, EbpfNode>, n: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match allow_loops:
    case True{}:
      Done{Unit{}}
    case False{}:
      ebpf_reach_check(nodes, n)

def ebpf_cfg.after_edges(v: Result<&2, &2, I.EbpfError, Unit>, +allow_loops: Bool, +nodes: List<&2, EbpfNode>, +n: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      ebpf_cfg.reach(allow_loops, nodes, n)

def ebpf_cfg.after_len(v: Result<&2, &2, I.EbpfError, Unit>, +allow_loops: Bool, starts: List<&2, Bool>, +nodes: List<&2, EbpfNode>, +n: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      ebpf_cfg.after_edges(ebpf_edges(allow_loops, starts, n, nodes), allow_loops, nodes, n)

def ebpf_cfg_check_go(opts: EbpfCfgOptions, +nodes: List<&2, EbpfNode>, +n: Nat, +count: Nat) -> Result<&2, &2, I.EbpfError, Unit>:
  match opts:
    case EbpfCfgOptions{max, allow_loops}:
      ebpf_cfg.after_len(ebpf_cfg.len(n, count, max), allow_loops, ebpf_starts(nodes), nodes, n)

# the slot count of a node list
def ebpf_count_slots.go(nodes: List<&2, EbpfNode>, n: Nat) -> Nat:
  match nodes:
    case Nil{}:
      n
    case Con{nd, t}:
      match nd:
        case EbpfNode{slot, slots, insn}:
          ebpf_count_slots.go(t, Nat.add(n, slots))

def ebpf_count_slots(nodes: List<&2, EbpfNode>) -> Nat:
  ebpf_count_slots.go(nodes, 0n)

# the control-flow check for a decoded program, with these options
def ebpf_cfg_check_with(opts: EbpfCfgOptions, prog: List<&2, I.EbpfInsn>) -> Result<&2, &2, I.EbpfError, Unit>:
  +nodes = ebpf_nodes(prog)
  ebpf_cfg_check_go(opts, nodes, ebpf_count_slots(nodes), List.length(&2, EbpfNode, nodes))

# the default options (no loops, the instruction limit)
def ebpf_cfg_check(prog: List<&2, I.EbpfInsn>) -> Result<&2, &2, I.EbpfError, Unit>:
  ebpf_cfg_check_with(EbpfCfgOptions.default(), prog)
