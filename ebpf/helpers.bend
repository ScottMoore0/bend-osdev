# bend-osdev-ebpf: helper functions, the interface and a standard table.
#
# RFC 9669 (4.3.1) leaves helpers to the platform: a call {CALL, K, JMP}
# with src_reg 0 calls helper imm, with arguments in R1 to R5 and its result
# in R0. Here a helper table is a template argument of the interpreter
#   ~helpers: U32 -> List<&2, EbpfValue> -> EbpfMem -> EbpfHelperOut
# (the id, R1 to R5, the memory), and the verifier takes the matching
#   ~sigs: U32 -> Maybe<&2, EbpfHelperSig>
# which says what each argument must be and what R0 holds after the call.
# A table and its signatures go together; a helper must behave as its
# signature says (the verifier trusts it).
#
# The standard table has the three array-map helpers whose ids Linux
# assigns (bpf_map_lookup_elem 1, bpf_map_update_elem 2, bpf_map_delete_elem
# 3), for maps whose keys are 32-bit indices.
import Base
import ../word64/word64.bend as W
import ./insn.bend as I
import ./memory.bend as M

type EbpfHelperOut is Data:
  EbpfHelperDone{r0: M.EbpfValue, mem: M.EbpfMem}
  EbpfHelperUnknown{}
  EbpfHelperFault{why: I.EbpfMemError}
  EbpfHelperBadArg{}

# what an argument register must hold
type EbpfArgKind is Data:
  EbpfArgScalar{}
  EbpfArgMap{}
  EbpfArgKey{}
  EbpfArgValue{}

# what R0 holds after the call: a number, or a pointer to a value of the map
# passed as the first map argument, or 0
type EbpfRetKind is Data:
  EbpfRetScalar{}
  EbpfRetMapValueOrNull{}

type EbpfHelperSig is Data:
  EbpfHelperSig{args: List<&2, EbpfArgKind>, ret: EbpfRetKind}

def EbpfHelperSig.args(s: EbpfHelperSig) -> List<&2, EbpfArgKind>:
  match s:
    case EbpfHelperSig{args, ret}:
      args

def EbpfHelperSig.ret(s: EbpfHelperSig) -> EbpfRetKind:
  match s:
    case EbpfHelperSig{args, ret}:
      ret

# A table with no helpers
def ebpf_helpers.none(id: U32, args: List<&2, M.EbpfValue>, mem: M.EbpfMem) -> EbpfHelperOut:
  EbpfHelperUnknown{}

def ebpf_helper_sigs.none(id: U32) -> Maybe<&2, EbpfHelperSig>:
  None{}

# The standard table

def ebpf_arg(args: List<&2, M.EbpfValue>, n: Nat) -> M.EbpfValue:
  Maybe.default(&2, M.EbpfValue, List.get(&2, M.EbpfValue, args, n), M.EbpfUndef{})

# -errno as a 64-bit value
def ebpf_errno(e: U32) -> W.W64:
  W.W64.sub(W.W64.zero(), W.W64.from_u32(e))

def ebpf_map_of(v: M.EbpfValue) -> Maybe<&2, Nat>:
  match v:
    case M.EbpfPtr{r, off}:
      match r:
        case M.EbpfRgnMap{mi}:
          Some{mi}
        case other:
          None{}
    case other:
      None{}

def ebpf_map_get(mem: M.EbpfMem, mi: Nat) -> Maybe<&2, M.EbpfMap>:
  List.get(&2, M.EbpfMap, M.EbpfMem.maps(mem), mi)

# the 32-bit key a pointer argument points to
def ebpf_key.got(r: Result<&2, &2, I.EbpfMemError, M.EbpfValue>) -> Result<&2, &2, I.EbpfMemError, U32>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{k}:
      match k:
        case M.EbpfScalar{x}:
          Done{W.W64.lo(x)}
        case other:
          Fail{I.EbpfMemPointerBytes{}}

def ebpf_key(+mem: M.EbpfMem, v: M.EbpfValue) -> Result<&2, &2, I.EbpfMemError, U32>:
  match v:
    case M.EbpfPtr{r, off}:
      ebpf_key.got(M.EbpfMem.load(mem, r, off, I.EbpfSizeW{}))
    case other:
      Fail{I.EbpfMemNotMemory{}}

def ebpf_lookup.fin(ok: Bool, +mi: Nat, +idx: U32, mem: M.EbpfMem) -> EbpfHelperOut:
  match ok:
    case True{}:
      EbpfHelperDone{M.EbpfPtr{M.EbpfRgnMapValue{mi, U32.to_nat(idx)}, W.W64.zero()}, mem}
    case False{}:
      EbpfHelperDone{M.EbpfScalar{W.W64.zero()}, mem}

def ebpf_lookup.go(m: Maybe<&2, M.EbpfMap>, +mi: Nat, k: Result<&2, &2, I.EbpfMemError, U32>, mem: M.EbpfMem) -> EbpfHelperOut:
  match m:
    case None{}:
      EbpfHelperBadArg{}
    case Some{mp}:
      match k:
        case Fail{e}:
          EbpfHelperFault{e}
        case Done{+idx}:
          ebpf_lookup.fin(Nat.is_lt(U32.to_nat(idx), M.EbpfMap.entries(mp)), mi, idx, mem)

# bpf_map_lookup_elem(map, key): a pointer to the value, or 0 past the end
def ebpf_map_lookup.go(m: Maybe<&2, Nat>, +args: List<&2, M.EbpfValue>, +mem: M.EbpfMem) -> EbpfHelperOut:
  match m:
    case None{}:
      EbpfHelperBadArg{}
    case Some{+mi}:
      ebpf_lookup.go(ebpf_map_get(mem, mi), mi, ebpf_key(mem, ebpf_arg(args, 1n)), mem)

def ebpf_map_lookup(+args: List<&2, M.EbpfValue>, +mem: M.EbpfMem) -> EbpfHelperOut:
  ebpf_map_lookup.go(ebpf_map_of(ebpf_arg(args, 0n)), args, mem)

def ebpf_update.write(r: Result<&2, &2, I.EbpfMemError, M.EbpfMem>) -> EbpfHelperOut:
  match r:
    case Fail{e}:
      EbpfHelperFault{e}
    case Done{m2}:
      EbpfHelperDone{M.EbpfScalar{W.W64.zero()}, m2}

def ebpf_update.bytes(r: Result<&2, &2, I.EbpfMemError, List<&2, U32>>, +mi: Nat, +idx: U32, mem: M.EbpfMem) -> EbpfHelperOut:
  match r:
    case Fail{e}:
      EbpfHelperFault{e}
    case Done{bs}:
      ebpf_update.write(M.EbpfMem.write_bytes(bs, mem, M.EbpfRgnMapValue{mi, U32.to_nat(idx)}, W.W64.zero()))

def ebpf_update.fin(ok: Bool, +mi: Nat, +idx: U32, +size: U32, val: M.EbpfValue, +mem: M.EbpfMem) -> EbpfHelperOut:
  match ok:
    case True{}:
      match val:
        case M.EbpfPtr{r, off}:
          ebpf_update.bytes(M.EbpfMem.read_bytes(U32.to_nat(size), mem, r, off), mi, idx, mem)
        case other:
          EbpfHelperBadArg{}
    case False{}:
      EbpfHelperDone{M.EbpfScalar{ebpf_errno(7)}, mem}

def ebpf_update.go(m: Maybe<&2, M.EbpfMap>, +mi: Nat, k: Result<&2, &2, I.EbpfMemError, U32>, val: M.EbpfValue, +mem: M.EbpfMem) -> EbpfHelperOut:
  match m:
    case None{}:
      EbpfHelperBadArg{}
    case Some{+mp}:
      match k:
        case Fail{e}:
          EbpfHelperFault{e}
        case Done{+idx}:
          ebpf_update.fin(Nat.is_lt(U32.to_nat(idx), M.EbpfMap.entries(mp)), mi, idx, M.EbpfMap.value_size(mp), val, mem)

# bpf_map_update_elem(map, key, value, flags): the value copied in, 0; or
# -E2BIG (7) past the end
def ebpf_map_update.go(m: Maybe<&2, Nat>, +args: List<&2, M.EbpfValue>, +mem: M.EbpfMem) -> EbpfHelperOut:
  match m:
    case None{}:
      EbpfHelperBadArg{}
    case Some{+mi}:
      ebpf_update.go(ebpf_map_get(mem, mi), mi, ebpf_key(mem, ebpf_arg(args, 1n)), ebpf_arg(args, 2n), mem)

def ebpf_map_update(+args: List<&2, M.EbpfValue>, +mem: M.EbpfMem) -> EbpfHelperOut:
  ebpf_map_update.go(ebpf_map_of(ebpf_arg(args, 0n)), args, mem)

# bpf_map_delete_elem(map, key): array maps cannot delete: -EINVAL (22)
def ebpf_map_delete(args: List<&2, M.EbpfValue>, mem: M.EbpfMem) -> EbpfHelperOut:
  EbpfHelperDone{M.EbpfScalar{ebpf_errno(22)}, mem}

def ebpf_helpers.std.go(is1: Bool, is2: Bool, is3: Bool, args: List<&2, M.EbpfValue>, mem: M.EbpfMem) -> EbpfHelperOut:
  match is1:
    case True{}:
      ebpf_map_lookup(args, mem)
    case False{}:
      match is2:
        case True{}:
          ebpf_map_update(args, mem)
        case False{}:
          match is3:
            case True{}:
              ebpf_map_delete(args, mem)
            case False{}:
              EbpfHelperUnknown{}

# bpf_map_lookup_elem (1), bpf_map_update_elem (2), bpf_map_delete_elem (3)
def ebpf_helpers.std(id: U32, args: List<&2, M.EbpfValue>, mem: M.EbpfMem) -> EbpfHelperOut:
  +i = id
  ebpf_helpers.std.go(U32.is_eq(i, 1), U32.is_eq(i, 2), U32.is_eq(i, 3), args, mem)

def ebpf_helper_sigs.std.go(is1: Bool, is2: Bool, is3: Bool) -> Maybe<&2, EbpfHelperSig>:
  match is1:
    case True{}:
      Some{EbpfHelperSig{[EbpfArgMap{}, EbpfArgKey{}], EbpfRetMapValueOrNull{}}}
    case False{}:
      match is2:
        case True{}:
          Some{EbpfHelperSig{[EbpfArgMap{}, EbpfArgKey{}, EbpfArgValue{}, EbpfArgScalar{}], EbpfRetScalar{}}}
        case False{}:
          match is3:
            case True{}:
              Some{EbpfHelperSig{[EbpfArgMap{}, EbpfArgKey{}], EbpfRetScalar{}}}
            case False{}:
              None{}

def ebpf_helper_sigs.std(id: U32) -> Maybe<&2, EbpfHelperSig>:
  +i = id
  ebpf_helper_sigs.std.go(U32.is_eq(i, 1), U32.is_eq(i, 2), U32.is_eq(i, 3))
