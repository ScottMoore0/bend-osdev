import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./container.bend as C
import ./lzma.bend as L
import ./lzma2.bend as L2
import ./xz.bend as X
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# The bound: xz_decode ends with a guard that answers XzOutputTooLarge for any
# output longer than the maximum. e says which way the guard went.
def xz_bound_pick(+max: U32, +o: B.Octets, b: Bool, +e: {b == Nat.is_le(B.Octets.len(o), U32.to_nat(max)) : Bool}) -> {Laws.xz_within(max, X.Xz.bound.pick(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)) == True{} : Bool}:
  match b:
    case True{}:
      %e : {Laws.xz_within(max, X.Xz.bound.pick(_, o)) == True{} : Bool}
      %e : {_ == True{} : Bool}
      {==}
    case False{}:
      %e : {Laws.xz_within(max, X.Xz.bound.pick(_, o)) == True{} : Bool}
      {==}

def xz_bound_ok(+max: U32, r: Result<&2, &2, E.XzError, B.Octets>) -> {Laws.xz_within(max, X.Xz.bound(max, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+o}:
      xz_bound_pick(max, o, Nat.is_le(B.Octets.len(o), U32.to_nat(max)), {==})

def Laws.output_bounded(p, i):
  xz_bound_ok(X.XzParams.max_out(p), X.xz_decode.fin(X.XzDecoder.feed(X.XzDecoder.start(p), i)))

def Laws.empty_input(p):
  {==}

# A first chunk that does not reset the dictionary: the input is read through
# bytes' law octets_to_of (as in bad_magic below), the loop's bound through
# len_fast (the feed counts its buffer with B.len.fast), then the rest
# computes.
def Laws.lzma2_needs_reset(d, m, xs):
  +k = L2.XzLzma2.start.depth(d, m)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{2, xs})), B.mask(Con{2, xs}), BL.octets_to_of(Con{2, xs})) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(L2.XzLzma2.loop(1n+B.len.fast(B.append.fast(Nil{}, _)), L2.XzL2Go{L2.XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), L2.XzL2Ctl{True{}, True{}, False{}, m, 0n, Nat.min(k, 12n), k}, B.append.fast(Nil{}, _)}, Nil{}}))) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  %BL.len_fast(B.mask(Con{2, xs})) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(L2.XzLzma2.loop(1n+_, L2.XzL2Go{L2.XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), L2.XzL2Ctl{True{}, True{}, False{}, m, 0n, Nat.min(k, 12n), k}, B.mask(Con{2, xs})}, Nil{}}))) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

def Laws.lzma2_end_only(d, m):
  {==}

def Laws.empty_file():
  {==}

def Laws.one_byte():
  {==}

def Laws.one_byte_bad_check():
  {==}

def Laws.bad_header_crc():
  {==}

def Laws.lzma2_uncompressed():
  {==}

def Laws.lzma2_too_large():
  {==}

def Laws.lzma2_dict_sizes():
  {==}

# Bad magic: the first comparison of the magic bytes fails, so the header
# parser fails, so the decoder's first step stops, whatever follows.

def xz_magic_first(+h: U32, +t: List<&2, U32>, +e: {False{} == U32.is_eq(h, 253) : Bool}) -> {Fail{E.XzBadMagic{}} == C.XzC.magic.go([55, 122, 88, 90, 0], U32.is_eq(h, 253), t, E.XzBadMagic{}) : Result<&2, &2, E.XzError, List<&2, U32>>}:
  %e : {Fail{E.XzBadMagic{}} == C.XzC.magic.go([55, 122, 88, 90, 0], _, t, E.XzBadMagic{}) : Result<&2, &2, E.XzError, List<&2, U32>>}
  {==}

def xz_header_bad(+h: U32, +t: List<&2, U32>, +e: {False{} == U32.is_eq(h, 253) : Bool}) -> {Fail{E.XzBadMagic{}} == C.XzC.header(Con{h, t}) : Result<&2, &2, E.XzError, C.XzGot<U32>>}:
  %xz_magic_first(h, t, e) : {Fail{E.XzBadMagic{}} == C.XzC.header.after(_) : Result<&2, &2, E.XzError, C.XzGot<U32>>}
  {==}

def xz_loop_bad(n: Nat, +run: X.XzRun, +h: U32, +t: List<&2, U32>, +acc: List<&2, B.Octets>, +e: {False{} == U32.is_eq(h, 253) : Bool}) -> {X.XzStop{E.XzBadMagic{}} == X.XzDecoder.loop(1n+n, X.XzGo{X.XzDecoder{X.XzPhHeader{}, run, Con{h, t}}, acc}) : X.XzStep}:
  match n:
    case 0n:
      %xz_header_bad(h, t, e) : {X.XzStop{E.XzBadMagic{}} == X.XzDecoder.loop(0n, X.Xz.header(_, run, Con{h, t}, acc)) : X.XzStep}
      {==}
    case 1n+p:
      %xz_header_bad(h, t, e) : {X.XzStop{E.XzBadMagic{}} == X.XzDecoder.loop(1n+p, X.Xz.header(_, run, Con{h, t}, acc)) : X.XzStep}
      {==}

# The decoder reads its input through bytes' law octets_to_of (a list made
# into Octets and back is the list masked), so the first byte it sees is
# B.byte(b), whatever Octets stores.
def Laws.bad_magic(p, b, xs, e):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{b, xs})), B.mask(Con{b, xs}), BL.octets_to_of(Con{b, xs})) : {X.Xz.bound(X.XzParams.max_out(p), X.xz_decode.fin(X.XzDecoder.feed.fin(X.XzDecoder.loop(1n+Nat.add(Nat.mul(2n, B.len.fast(B.append.fast(Nil{}, _))), 3n), X.XzGo{X.XzDecoder{X.XzPhHeader{}, X.XzRun{0, Nil{}, X.XzParams.max_out(p)}, B.append.fast(Nil{}, _)}, Nil{}})))) == Fail{E.XzBadMagic{}} : Result<&2, &2, E.XzError, B.Octets>}
  %xz_loop_bad(Nat.add(Nat.mul(2n, B.len.fast(Con{B.byte(b), B.mask(xs)})), 3n), X.XzRun{0, Nil{}, X.XzParams.max_out(p)}, B.byte(b), B.mask(xs), Nil{}, Equal.sym(Bool, U32.is_eq(B.byte(b), 253), False{}, e)) : {X.Xz.bound(X.XzParams.max_out(p), X.xz_decode.fin(X.XzDecoder.feed.fin(_))) == Fail{E.XzBadMagic{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

# Reserved control bytes: the control byte is at least 3, so not a stream end
# or an uncompressed chunk, and below 128, so not an LZMA chunk.

def xz_control_bad(+c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, -probs: Array<U32>, -dict: Array<U32>, +regs: L.XzLzRegs, +ctl: L2.XzL2Ctl, +acc: List<&2, U32>, +e1: {False{} == U32.is_lt(c, 3) : Bool}, +e2: {True{} == U32.is_lt(c, 128) : Bool}) -> {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.control(U32.is_lt(c, 3), c, rest, buf, probs, dict, regs, ctl, acc) : L2.XzL2Step}:
  %e1 : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.control(_, c, rest, buf, probs, dict, regs, ctl, acc) : L2.XzL2Step}
  %e2 : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.control.high(_, c, rest, buf, probs, dict, regs, ctl, acc) : L2.XzL2Step}
  {==}

def xz_loop_control_bad(n: Nat, -probs: Array<U32>, -dict: Array<U32>, +regs: L.XzLzRegs, +nr: Bool, +np: Bool, +room: U32, +cons: Nat, +dd: Nat, +md: Nat, +c: U32, +rest: List<&2, U32>, +acc: List<&2, U32>, +e1: {False{} == U32.is_lt(c, 3) : Bool}, +e2: {True{} == U32.is_lt(c, 128) : Bool}) -> {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.loop(1n+n, L2.XzL2Go{L2.XzLzma2{probs, dict, regs, L2.XzL2Ctl{nr, np, False{}, room, cons, dd, md}, Con{c, rest}}, acc}) : L2.XzL2Step}:
  match n:
    case 0n:
      %xz_control_bad(c, rest, Con{c, rest}, probs, dict, regs, L2.XzL2Ctl{nr, np, False{}, room, cons, dd, md}, acc, e1, e2) : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.loop(0n, _) : L2.XzL2Step}
      {==}
    case 1n+p:
      %xz_control_bad(c, rest, Con{c, rest}, probs, dict, regs, L2.XzL2Ctl{nr, np, False{}, room, cons, dd, md}, acc, e1, e2) : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.loop(1n+p, _) : L2.XzL2Step}
      {==}

def Laws.lzma2_reserved_control(d, m, c, xs, e1, e2):
  +k = L2.XzLzma2.start.depth(d, m)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{c, xs})), B.mask(Con{c, xs}), BL.octets_to_of(Con{c, xs})) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(L2.XzLzma2.loop(1n+B.len.fast(B.append.fast(Nil{}, _)), L2.XzL2Go{L2.XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), L2.XzL2Ctl{True{}, True{}, False{}, m, 0n, Nat.min(k, 12n), k}, B.append.fast(Nil{}, _)}, Nil{}}))) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  %xz_loop_control_bad(B.len.fast(Con{B.byte(c), B.mask(xs)}), Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), True{}, True{}, m, 0n, Nat.min(k, 12n), k, B.byte(c), B.mask(xs), Nil{}, Equal.sym(Bool, U32.is_lt(B.byte(c), 3), False{}, e1), Equal.sym(Bool, U32.is_lt(B.byte(c), 128), True{}, e2)) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(_)) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}