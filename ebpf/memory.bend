# bend-osdev-ebpf: the memory model.
#
# Every pointer is a region and an offset into it (EbpfPtr{rgn, off}): the
# context, a frame's 512-byte stack, the packet, one value of a map, or a
# map itself (a handle, which helpers take and which cannot be read). Every
# load and store checks its bytes lie inside its region (an access outside
# fails with EbpfMemOutOfBounds, never answering a value: a law), so no
# program can reach outside the memory it was given, whatever it computes.
#
# The context, the packet and map values are plain bytes. A stack is 512
# cells, each uninitialised, a byte, or one of the eight parts of a pointer
# stored there: a stack read fails if it meets an uninitialised byte
# (EbpfMemUninit), an 8-byte aligned load of a stored pointer gives the
# pointer back, and any other access to a stored pointer fails
# (EbpfMemPointerBytes). Pointers can be stored only on the stack, 8-byte
# aligned. Stack accesses must be aligned to their size (as the Linux
# verifier requires); other regions take any alignment. Multi-byte values
# are stored in the host's byte order (RFC 9669, 3), a parameter here.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bpf/insn.bend as C
import ./insn.bend as I

type EbpfRegion is Data:
  EbpfRgnCtx{}
  EbpfRgnStack{depth: Nat}
  EbpfRgnPacket{}
  EbpfRgnMapValue{map: Nat, idx: Nat}
  EbpfRgnMap{map: Nat}

# what a register holds: a number, a pointer, or nothing yet
type EbpfValue is Data:
  EbpfScalar{v: W.W64}
  EbpfPtr{rgn: EbpfRegion, off: W.W64}
  EbpfUndef{}

type EbpfCell is Data:
  EbpfCellUninit{}
  EbpfCellByte{b: U32}
  EbpfCellPtr{v: EbpfValue, part: Nat}

# an array map: fd names it in 64-bit immediate loads (RFC 9669, 5.4); each
# value is value_size bytes
type EbpfMap is Data:
  EbpfMap{fd: U32, value_size: U32, values: List<&2, List<&2, U32>>}

type EbpfMem is Data:
  EbpfMem{order: C.BpfOrder, ctx: List<&2, U32>, packet: List<&2, U32>, maps: List<&2, EbpfMap>, stacks: List<&2, List<&2, EbpfCell>>}

# Where the context holds the packet's bounds: a 32-bit load from offset
# data (data_end) gives a pointer to the packet's first byte (just past its
# last), as the kernel rewrites such loads. pkt False: no packet fields.
type EbpfCtxLayout is Data:
  EbpfCtxLayout{size: U32, pkt: Bool, data: U32, data_end: U32}

# a context of size bytes with no packet fields
def EbpfCtxLayout.plain(size: U32) -> EbpfCtxLayout:
  EbpfCtxLayout{size, False{}, 0, 0}

# struct xdp_md: data at 0, data_end at 4, then data_meta, ingress_ifindex,
# rx_queue_index, egress_ifindex (24 bytes)
def EbpfCtxLayout.xdp() -> EbpfCtxLayout:
  EbpfCtxLayout{24, True{}, 0, 4}

# The stack of one frame

def ebpf_stack_size() -> U32:
  512

def ebpf_stack.fresh() -> List<&2, EbpfCell>:
  List.replicate(EbpfCell, 512n, EbpfCellUninit{})

# Building memory

def ebpf_mask.go(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{h, t}:
      ebpf_mask.go(t, Con{U32.and(255, h), acc})

def EbpfMap.of_values.go(vs: List<&2, B.Octets>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match vs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, acc)
    case Con{v, t}:
      EbpfMap.of_values.go(t, Con{B.Octets.to_list(v), acc})

# an array map with these values (each should be value_size bytes)
def EbpfMap.of_values(fd: U32, value_size: U32, vs: List<&2, B.Octets>) -> EbpfMap:
  EbpfMap{fd, value_size, EbpfMap.of_values.go(vs, Nil{})}

# an array map of entries zero values
def EbpfMap.array(fd: U32, +value_size: U32, entries: Nat) -> EbpfMap:
  EbpfMap{fd, value_size, List.replicate(List<&2, U32>, entries, B.zeros.fast(U32.to_nat(value_size)))}

def EbpfMap.value_size(m: EbpfMap) -> U32:
  match m:
    case EbpfMap{fd, vs, values}:
      vs

def EbpfMap.entries(m: EbpfMap) -> Nat:
  match m:
    case EbpfMap{fd, vs, values}:
      List.length(&2, List<&2, U32>, values)

def EbpfMap.fd(m: EbpfMap) -> U32:
  match m:
    case EbpfMap{fd, vs, values}:
      fd

# memory for a run: the context, the packet and the maps, with no stacks
# yet (the interpreter adds one per frame)
def EbpfMem.new(order: C.BpfOrder, ctx: B.Octets, packet: B.Octets, maps: List<&2, EbpfMap>) -> EbpfMem:
  EbpfMem{order, B.Octets.to_list(ctx), B.Octets.to_list(packet), maps, Nil{}}

def EbpfMem.order(m: EbpfMem) -> C.BpfOrder:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      o

def EbpfMem.ctx(m: EbpfMem) -> B.Octets:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      B.Octets.of_list(ctx)

def EbpfMem.packet(m: EbpfMem) -> B.Octets:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      B.Octets.of_list(pkt)

def EbpfMem.packet_len(m: EbpfMem) -> U32:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      U32.from_nat(B.len.fast(pkt))

def EbpfMem.maps(m: EbpfMem) -> List<&2, EbpfMap>:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      maps

def EbpfMem.map_value.of(v: Maybe<&2, List<&2, U32>>) -> Maybe<&2, B.Octets>:
  match v:
    case None{}:
      None{}
    case Some{bs}:
      Some{B.Octets.of_list(bs)}

def EbpfMem.map_value.go(m: Maybe<&2, EbpfMap>, idx: Nat) -> Maybe<&2, B.Octets>:
  match m:
    case None{}:
      None{}
    case Some{mp}:
      match mp:
        case EbpfMap{fd, vs, values}:
          EbpfMem.map_value.of(List.get(&2, List<&2, U32>, values, idx))

# the value at idx of the map at index map
def EbpfMem.map_value(m: EbpfMem, map: Nat, idx: Nat) -> Maybe<&2, B.Octets>:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      EbpfMem.map_value.go(List.get(&2, EbpfMap, maps, map), idx)

# the number of frames' stacks
def EbpfMem.depth(m: EbpfMem) -> Nat:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      List.length(&2, List<&2, EbpfCell>, stacks)

# a new frame's stack, at depth EbpfMem.depth(m)
def EbpfMem.push(m: EbpfMem) -> EbpfMem:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      EbpfMem{o, ctx, pkt, maps, List.append(&2, List<&2, EbpfCell>, stacks, [ebpf_stack.fresh()])}

# the deepest frame's stack removed
def EbpfMem.pop(m: EbpfMem) -> EbpfMem:
  match m:
    case EbpfMem{o, ctx, pkt, maps, +stacks}:
      EbpfMem{o, ctx, pkt, maps, List.take(&2, List<&2, EbpfCell>, stacks, Nat.sub(List.length(&2, List<&2, EbpfCell>, stacks), 1n))}

# Lists, as tail calls: elements i to i + n - 1 replaced by ys

def ebpf_splice.go(-A: Data, i: Nat, xs: List<&2, A>, ys: List<&2, A>, n: Nat, acc: List<&2, A>) -> List<&2, A>:
  match i:
    case 0n:
      List.reverse.go(&2, A, acc, List.append(&2, A, ys, List.drop(&2, A, xs, n)))
    case 1n+p:
      match xs:
        case Nil{}:
          List.reverse(&2, A, acc)
        case Con{h, t}:
          ebpf_splice.go(A, p, t, ys, n, Con{h, acc})

def ebpf_splice(-A: Data, xs: List<&2, A>, i: Nat, n: Nat, ys: List<&2, A>) -> List<&2, A>:
  ebpf_splice.go(A, i, xs, ys, n, Nil{})

def ebpf_slice(-A: Data, xs: List<&2, A>, i: Nat, n: Nat) -> List<&2, A>:
  List.take(&2, A, List.drop(&2, A, xs, i), n)

# Regions as areas: the bytes or cells a region names, or why it names none

type EbpfArea is Data:
  EbpfAreaBytes{bytes: List<&2, U32>}
  EbpfAreaCells{cells: List<&2, EbpfCell>}
  EbpfAreaNone{why: I.EbpfMemError}

def EbpfMem.area.val(v: Maybe<&2, List<&2, U32>>) -> EbpfArea:
  match v:
    case None{}:
      EbpfAreaNone{I.EbpfMemDangling{}}
    case Some{bs}:
      EbpfAreaBytes{bs}

def EbpfMem.area.map(m: Maybe<&2, EbpfMap>, idx: Nat) -> EbpfArea:
  match m:
    case None{}:
      EbpfAreaNone{I.EbpfMemDangling{}}
    case Some{mp}:
      match mp:
        case EbpfMap{fd, vs, values}:
          EbpfMem.area.val(List.get(&2, List<&2, U32>, values, idx))

def EbpfMem.area.stack(s: Maybe<&2, List<&2, EbpfCell>>) -> EbpfArea:
  match s:
    case None{}:
      EbpfAreaNone{I.EbpfMemDangling{}}
    case Some{cs}:
      EbpfAreaCells{cs}

def EbpfMem.area(m: EbpfMem, r: EbpfRegion) -> EbpfArea:
  match m:
    case EbpfMem{o, ctx, pkt, maps, stacks}:
      match r:
        case EbpfRgnCtx{}:
          EbpfAreaBytes{ctx}
        case EbpfRgnStack{d}:
          EbpfMem.area.stack(List.get(&2, List<&2, EbpfCell>, stacks, d))
        case EbpfRgnPacket{}:
          EbpfAreaBytes{pkt}
        case EbpfRgnMapValue{mi, idx}:
          EbpfMem.area.map(List.get(&2, EbpfMap, maps, mi), idx)
        case EbpfRgnMap{mi}:
          EbpfAreaNone{I.EbpfMemNotMemory{}}

def EbpfArea.len(a: EbpfArea) -> Maybe<&2, U32>:
  match a:
    case EbpfAreaBytes{bs}:
      Some{U32.from_nat(B.len.fast(bs))}
    case EbpfAreaCells{cs}:
      Some{U32.from_nat(List.length(&2, EbpfCell, cs))}
    case EbpfAreaNone{why}:
      None{}

# the size in bytes of the memory a region names, or None (a map handle, or
# a region that does not exist: a frame that has returned, a missing map)
def EbpfMem.region_len(+m: EbpfMem, r: EbpfRegion) -> Maybe<&2, U32>:
  EbpfArea.len(EbpfMem.area(m, r))

def EbpfSize.bytes(s: I.EbpfSize) -> U32:
  match s:
    case I.EbpfSizeB{}:
      1
    case I.EbpfSizeH{}:
      2
    case I.EbpfSizeW{}:
      4
    case I.EbpfSizeDW{}:
      8

# size bytes at addr lie inside a region of len bytes: addr <= len and
# size <= len - addr, compared as 64-bit numbers (so no wrapping)
def ebpf_in_bounds(+len: U32, +addr: W.W64, +size: U32) -> Bool:
  I.EbpfDec.both(W.W64.is_le(addr, W.W64.from_u32(len)), W.W64.is_le(W.W64.from_u32(size), W.W64.sub(W.W64.from_u32(len), addr)))

def ebpf_aligned(addr: W.W64, +size: U32) -> Bool:
  U32.is_zero(U32.and(W.W64.lo(addr), U32.sub(size, 1)))

# Bytes and values

def ebpf_bytes.value(order: C.BpfOrder, s: I.EbpfSize, +bs: List<&2, U32>) -> W.W64:
  match order:
    case C.BpfLittle{}:
      match s:
        case I.EbpfSizeB{}:
          W.W64.from_u32(Maybe.default(&2, U32, B.at(bs, 0n), 0))
        case I.EbpfSizeH{}:
          W.W64.from_u32(Maybe.default(&2, U32, B.le16_at(bs, 0n), 0))
        case I.EbpfSizeW{}:
          W.W64.from_u32(Maybe.default(&2, U32, B.le32_at(bs, 0n), 0))
        case I.EbpfSizeDW{}:
          Maybe.default(&2, W.W64, B.le64_at(bs, 0n), W.W64.zero())
    case C.BpfBig{}:
      match s:
        case I.EbpfSizeB{}:
          W.W64.from_u32(Maybe.default(&2, U32, B.at(bs, 0n), 0))
        case I.EbpfSizeH{}:
          W.W64.from_u32(Maybe.default(&2, U32, B.be16_at(bs, 0n), 0))
        case I.EbpfSizeW{}:
          W.W64.from_u32(Maybe.default(&2, U32, B.be32_at(bs, 0n), 0))
        case I.EbpfSizeDW{}:
          Maybe.default(&2, W.W64, B.be64_at(bs, 0n), W.W64.zero())

# the low size bytes of v, in storage order
def ebpf_value.bytes(order: C.BpfOrder, s: I.EbpfSize, +v: W.W64) -> List<&2, U32>:
  match order:
    case C.BpfLittle{}:
      match s:
        case I.EbpfSizeB{}:
          [U32.and(255, W.W64.lo(v))]
        case I.EbpfSizeH{}:
          B.le16(W.W64.lo(v))
        case I.EbpfSizeW{}:
          B.le32(W.W64.lo(v))
        case I.EbpfSizeDW{}:
          B.le64(v)
    case C.BpfBig{}:
      match s:
        case I.EbpfSizeB{}:
          [U32.and(255, W.W64.lo(v))]
        case I.EbpfSizeH{}:
          B.be16(W.W64.lo(v))
        case I.EbpfSizeW{}:
          B.be32(W.W64.lo(v))
        case I.EbpfSizeDW{}:
          B.be64(v)

# Reading stack cells: all bytes; or the eight parts of one pointer, in
# order; else uninitialised, or part of a pointer

def ebpf_cells.bytes(cs: List<&2, EbpfCell>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case Con{c, t}:
      match c:
        case EbpfCellByte{b}:
          ebpf_cells.bytes(t, Con{b, acc})
        case other:
          None{}

def ebpf_cells.uninit(cs: List<&2, EbpfCell>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      match c:
        case EbpfCellUninit{}:
          True{}
        case other:
          ebpf_cells.uninit(t)

def ebpf_cells.parts(cs: List<&2, EbpfCell>, +k: Nat) -> Bool:
  match cs:
    case Nil{}:
      Nat.is_eq(k, 8n)
    case Con{c, t}:
      match c:
        case EbpfCellPtr{v, part}:
          Bool.and(Nat.is_eq(part, k), ebpf_cells.parts(t, 1n+k))
        case other:
          False{}

def ebpf_cells.first_ptr(cs: List<&2, EbpfCell>) -> Maybe<&2, EbpfValue>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case EbpfCellPtr{v, part}:
          Some{v}
        case other:
          None{}

def ebpf_cells.got(m: Maybe<&2, EbpfValue>) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{I.EbpfMemPointerBytes{}}

def ebpf_cells.why(uninit: Bool) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match uninit:
    case True{}:
      Fail{I.EbpfMemUninit{}}
    case False{}:
      Fail{I.EbpfMemPointerBytes{}}

def ebpf_cells.ptr(ok: Bool, +cs: List<&2, EbpfCell>) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match ok:
    case True{}:
      ebpf_cells.got(ebpf_cells.first_ptr(cs))
    case False{}:
      ebpf_cells.why(ebpf_cells.uninit(cs))

def ebpf_cells.read(m: Maybe<&2, List<&2, U32>>, order: C.BpfOrder, +s: I.EbpfSize, +cs: List<&2, EbpfCell>) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match m:
    case Some{bs}:
      Done{EbpfScalar{ebpf_bytes.value(order, s, bs)}}
    case None{}:
      ebpf_cells.ptr(I.EbpfDec.both(U32.is_eq(EbpfSize.bytes(s), 8), ebpf_cells.parts(cs, 0n)), cs)

def ebpf_cells.of_bytes(bs: List<&2, U32>, acc: List<&2, EbpfCell>) -> List<&2, EbpfCell>:
  match bs:
    case Nil{}:
      List.reverse(&2, EbpfCell, acc)
    case Con{b, t}:
      ebpf_cells.of_bytes(t, Con{EbpfCellByte{b}, acc})

def ebpf_cells.of_ptr(n: Nat, +v: EbpfValue, +k: Nat, acc: List<&2, EbpfCell>) -> List<&2, EbpfCell>:
  match n:
    case 0n:
      List.reverse(&2, EbpfCell, acc)
    case 1n+p:
      ebpf_cells.of_ptr(p, v, 1n+k, Con{EbpfCellPtr{v, k}, acc})

# Loads

def EbpfMem.load.cells(ok: Bool, cs: List<&2, EbpfCell>, +order: C.BpfOrder, +addr: W.W64, +s: I.EbpfSize) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match ok:
    case True{}:
      +got = ebpf_slice(EbpfCell, cs, U32.to_nat(W.W64.lo(addr)), U32.to_nat(EbpfSize.bytes(s)))
      ebpf_cells.read(ebpf_cells.bytes(got, Nil{}), order, s, got)
    case False{}:
      Fail{I.EbpfMemMisaligned{}}

def EbpfMem.load.area(a: EbpfArea, +order: C.BpfOrder, +addr: W.W64, +s: I.EbpfSize) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match a:
    case EbpfAreaBytes{bs}:
      Done{EbpfScalar{ebpf_bytes.value(order, s, ebpf_slice(U32, bs, U32.to_nat(W.W64.lo(addr)), U32.to_nat(EbpfSize.bytes(s))))}}
    case EbpfAreaCells{cs}:
      EbpfMem.load.cells(ebpf_aligned(addr, EbpfSize.bytes(s)), cs, order, addr, s)
    case EbpfAreaNone{why}:
      Fail{why}

def EbpfMem.load.chk(ok: Bool, a: EbpfArea, +order: C.BpfOrder, +addr: W.W64, +s: I.EbpfSize) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match ok:
    case True{}:
      EbpfMem.load.area(a, order, addr, s)
    case False{}:
      Fail{I.EbpfMemOutOfBounds{U32.to_nat(EbpfSize.bytes(s))}}

def EbpfMem.load.len(len: Maybe<&2, U32>, a: EbpfArea, +order: C.BpfOrder, +addr: W.W64, +s: I.EbpfSize) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  match len:
    case Some{l}:
      EbpfMem.load.chk(ebpf_in_bounds(l, addr, EbpfSize.bytes(s)), a, order, addr, s)
    case None{}:
      match a:
        case EbpfAreaNone{why}:
          Fail{why}
        case other:
          Fail{I.EbpfMemDangling{}}

# the value of size bytes at addr in region r: a number, or a pointer stored
# on the stack; or why not
def EbpfMem.load(+m: EbpfMem, +r: EbpfRegion, +addr: W.W64, +s: I.EbpfSize) -> Result<&2, &2, I.EbpfMemError, EbpfValue>:
  EbpfMem.load.len(EbpfMem.region_len(m, r), EbpfMem.area(m, r), EbpfMem.order(m), addr, s)

# Stores

def EbpfMem.put.map.go(g: Maybe<&2, EbpfMap>, maps: List<&2, EbpfMap>, +mi: Nat, +idx: Nat, +bs: List<&2, U32>) -> List<&2, EbpfMap>:
  match g:
    case None{}:
      maps
    case Some{mp}:
      match mp:
        case EbpfMap{fd, vs, values}:
          List.set(&2, EbpfMap, maps, mi, EbpfMap{fd, vs, List.set(&2, List<&2, U32>, values, idx, bs)})

def EbpfMem.put.map(+maps: List<&2, EbpfMap>, +mi: Nat, +idx: Nat, +bs: List<&2, U32>) -> List<&2, EbpfMap>:
  EbpfMem.put.map.go(List.get(&2, EbpfMap, maps, mi), maps, mi, idx, bs)

# memory with region r's area replaced
def EbpfMem.put(m: EbpfMem, r: EbpfRegion, a: EbpfArea) -> EbpfMem:
  match m:
    case EbpfMem{o, ctx, pkt, +maps, +stacks}:
      match r:
        case EbpfRgnCtx{}:
          match a:
            case EbpfAreaBytes{bs}:
              EbpfMem{o, bs, pkt, maps, stacks}
            case other:
              EbpfMem{o, ctx, pkt, maps, stacks}
        case EbpfRgnStack{+d}:
          match a:
            case EbpfAreaCells{cs}:
              EbpfMem{o, ctx, pkt, maps, List.set(&2, List<&2, EbpfCell>, stacks, d, cs)}
            case other:
              EbpfMem{o, ctx, pkt, maps, stacks}
        case EbpfRgnPacket{}:
          match a:
            case EbpfAreaBytes{bs}:
              EbpfMem{o, ctx, bs, maps, stacks}
            case other:
              EbpfMem{o, ctx, pkt, maps, stacks}
        case EbpfRgnMapValue{mi, idx}:
          match a:
            case EbpfAreaBytes{bs}:
              EbpfMem{o, ctx, pkt, EbpfMem.put.map(maps, mi, idx, bs), stacks}
            case other:
              EbpfMem{o, ctx, pkt, maps, stacks}
        case EbpfRgnMap{mi}:
          EbpfMem{o, ctx, pkt, maps, stacks}

def ebpf_store.ptr(ok: Bool, +cs: List<&2, EbpfCell>, +i: Nat, +v: EbpfValue) -> Result<&2, &2, I.EbpfMemError, EbpfArea>:
  match ok:
    case True{}:
      Done{EbpfAreaCells{ebpf_splice(EbpfCell, cs, i, 8n, ebpf_cells.of_ptr(8n, v, 0n, Nil{}))}}
    case False{}:
      Fail{I.EbpfMemPointerStore{}}

def EbpfMem.store.cells(ok: Bool, +cs: List<&2, EbpfCell>, +order: C.BpfOrder, +addr: W.W64, +s: I.EbpfSize, v: EbpfValue) -> Result<&2, &2, I.EbpfMemError, EbpfArea>:
  match ok:
    case True{}:
      match v:
        case EbpfScalar{x}:
          Done{EbpfAreaCells{ebpf_splice(EbpfCell, cs, U32.to_nat(W.W64.lo(addr)), U32.to_nat(EbpfSize.bytes(s)), ebpf_cells.of_bytes(ebpf_value.bytes(order, s, x), Nil{}))}}
        case EbpfPtr{pr, po}:
          ebpf_store.ptr(U32.is_eq(EbpfSize.bytes(s), 8), cs, U32.to_nat(W.W64.lo(addr)), EbpfPtr{pr, po})
        case EbpfUndef{}:
          Fail{I.EbpfMemUninit{}}
    case False{}:
      Fail{I.EbpfMemMisaligned{}}

# the area with v's size bytes written at addr
def EbpfMem.store.area(a: EbpfArea, +order: C.BpfOrder, +addr: W.W64, +s: I.EbpfSize, v: EbpfValue) -> Result<&2, &2, I.EbpfMemError, EbpfArea>:
  match a:
    case EbpfAreaBytes{bs}:
      match v:
        case EbpfScalar{x}:
          Done{EbpfAreaBytes{ebpf_splice(U32, bs, U32.to_nat(W.W64.lo(addr)), U32.to_nat(EbpfSize.bytes(s)), ebpf_value.bytes(order, s, x))}}
        case EbpfPtr{pr, po}:
          Fail{I.EbpfMemPointerStore{}}
        case EbpfUndef{}:
          Fail{I.EbpfMemUninit{}}
    case EbpfAreaCells{cs}:
      EbpfMem.store.cells(ebpf_aligned(addr, EbpfSize.bytes(s)), cs, order, addr, s, v)
    case EbpfAreaNone{why}:
      Fail{why}

def EbpfMem.store.fin(+m: EbpfMem, +r: EbpfRegion, res: Result<&2, &2, I.EbpfMemError, EbpfArea>) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{EbpfMem.put(m, r, a)}

def EbpfMem.store.chk(ok: Bool, +m: EbpfMem, +r: EbpfRegion, a: EbpfArea, +addr: W.W64, +s: I.EbpfSize, v: EbpfValue) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  match ok:
    case True{}:
      EbpfMem.store.fin(m, r, EbpfMem.store.area(a, EbpfMem.order(m), addr, s, v))
    case False{}:
      Fail{I.EbpfMemOutOfBounds{U32.to_nat(EbpfSize.bytes(s))}}

def EbpfMem.store.len(len: Maybe<&2, U32>, +m: EbpfMem, +r: EbpfRegion, a: EbpfArea, +addr: W.W64, +s: I.EbpfSize, v: EbpfValue) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  match len:
    case Some{l}:
      EbpfMem.store.chk(ebpf_in_bounds(l, addr, EbpfSize.bytes(s)), m, r, a, addr, s, v)
    case None{}:
      match a:
        case EbpfAreaNone{why}:
          Fail{why}
        case other:
          Fail{I.EbpfMemDangling{}}

# memory with v's low size bytes (or, on the stack, an 8-byte pointer)
# written at addr in region r; or why not
def EbpfMem.store(+m: EbpfMem, +r: EbpfRegion, +addr: W.W64, +s: I.EbpfSize, v: EbpfValue) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  EbpfMem.store.len(EbpfMem.region_len(m, r), m, r, EbpfMem.area(m, r), addr, s, v)

def EbpfMem.read_bytes.step(acc: Result<&2, &2, I.EbpfMemError, List<&2, U32>>, r: Result<&2, &2, I.EbpfMemError, EbpfValue>) -> Result<&2, &2, I.EbpfMemError, List<&2, U32>>:
  match acc:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{v}:
          match v:
            case EbpfScalar{x}:
              Done{Con{W.W64.lo(x), xs}}
            case other:
              Fail{I.EbpfMemPointerBytes{}}

def EbpfMem.read_bytes.go(n: Nat, +m: EbpfMem, +r: EbpfRegion, +addr: W.W64, acc: Result<&2, &2, I.EbpfMemError, List<&2, U32>>) -> Result<&2, &2, I.EbpfMemError, List<&2, U32>>:
  match n:
    case 0n:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{xs}:
          Done{List.reverse(&2, U32, xs)}
    case 1n+p:
      EbpfMem.read_bytes.go(p, m, r, W.W64.add(addr, W.W64.one()), EbpfMem.read_bytes.step(acc, EbpfMem.load(m, r, addr, I.EbpfSizeB{})))

# n bytes from addr in region r, one load each (helpers read keys and
# values this way)
def EbpfMem.read_bytes(n: Nat, +m: EbpfMem, +r: EbpfRegion, +addr: W.W64) -> Result<&2, &2, I.EbpfMemError, List<&2, U32>>:
  EbpfMem.read_bytes.go(n, m, r, addr, Done{Nil{}})

def EbpfMem.write_bytes.step(st: Result<&2, &2, I.EbpfMemError, EbpfMem>, +r: EbpfRegion, +addr: W.W64, b: U32) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  match st:
    case Fail{e}:
      Fail{e}
    case Done{m}:
      EbpfMem.store(m, r, addr, I.EbpfSizeB{}, EbpfScalar{W.W64.from_u32(b)})

def EbpfMem.write_bytes.go(bs: List<&2, U32>, st: Result<&2, &2, I.EbpfMemError, EbpfMem>, +r: EbpfRegion, +addr: W.W64) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  match bs:
    case Nil{}:
      st
    case Con{b, t}:
      EbpfMem.write_bytes.go(t, EbpfMem.write_bytes.step(st, r, addr, b), r, W.W64.add(addr, W.W64.one()))

# the bytes bs written from addr in region r, one store each
def EbpfMem.write_bytes(bs: List<&2, U32>, m: EbpfMem, +r: EbpfRegion, +addr: W.W64) -> Result<&2, &2, I.EbpfMemError, EbpfMem>:
  EbpfMem.write_bytes.go(bs, Done{m}, r, addr)
