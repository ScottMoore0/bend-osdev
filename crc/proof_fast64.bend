# Proofs for bend-osdev-crc: the 64-bit table-driven fast path (table.bend)
# equals the bitwise reference (crc.bend) for every parameter set and input.
#
# The method is the 32-bit one (proof_fast.bend): array's laws turn each
# table fill into Arrays.of_list(8, l, 0) for a Data list l of the engine's
# eight steps on each byte, and every table read in the loop is of_list_get.
# A W64 is used through bend-osdev-word64's public defs and its parts_of
# law: a register is taken apart into its halves, word64's shifts become the
# clean shifts of proof_engine64.bend (proof_cases64.bend), and one byte
# step is the 32-bit argument again: the register XOR the input byte splits
# into the part the table looks up and the rest, eight steps commute with
# XOR, and on the rest they only shift. Lemmas are prefixed cf6.
import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ../bytes/bytes.bend as B
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ./crc.bend as C
import ./table.bend as T
import ./proof_word.bend as PW
import ./proof_engine.bend as PE
import ./proof_cases.bend as PC
import ./proof_engine64.bend as P6
import ./proof_cases64.bend as C6
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# word64's one-place shifts are the clean shifts

def cf6.shr1(+c: W.W64) -> {W.W64.shr(c, 1n) == P6.c6.shr1(c) : W.W64}:
  %WL.parts_of(c) : {W.W64.shr(_, 1n) == P6.c6.shr1(_) : W.W64}
  C6.c6t.shr1_eq(W.W64.hi(c), W.W64.lo(c))

def cf6.shl1(+c: W.W64) -> {W.W64.shl(c, 1n) == P6.c6.shl1(c) : W.W64}:
  %WL.parts_of(c) : {W.W64.shl(_, 1n) == P6.c6.shl1(_) : W.W64}
  C6.c6t.shl1_eq(W.W64.hi(c), W.W64.lo(c))

# The engines are their clean forms

def cf6.pick_r(b: Bool, +p: W.W64, +c: W.W64) -> {C.r64.pick(b, p, c) == P6.c6.rpick(b, p, c) : W.W64}:
  match b:
    case True{}:
      %Equal.sym(W.W64, W.W64.shr(c, 1n), P6.c6.shr1(c), cf6.shr1(c)) : {W.W64.xor(_, p) == W.W64.xor(P6.c6.shr1(c), p) : W.W64}
      {==}
    case False{}:
      cf6.shr1(c)

def cf6.r_rb(n: Nat, +p: W.W64, +c: W.W64) -> {C.r64.bits(n, p, c) == P6.c6.rb(n, p, c) : W.W64}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Bool, U32.is_eq(U32.and(W.W64.lo(c), 1), 1), PW.cw.odd(W.W64.lo(c)), PW.cw.odd_test(W.W64.lo(c))) : {C.r64.bits(k, p, C.r64.pick(_, p, c)) == P6.c6.rb(k, p, P6.c6.rpick(PW.cw.odd(W.W64.lo(c)), p, c)) : W.W64}
      %Equal.sym(W.W64, C.r64.pick(PW.cw.odd(W.W64.lo(c)), p, c), P6.c6.rpick(PW.cw.odd(W.W64.lo(c)), p, c), cf6.pick_r(PW.cw.odd(W.W64.lo(c)), p, c)) : {C.r64.bits(k, p, _) == P6.c6.rb(k, p, P6.c6.rpick(PW.cw.odd(W.W64.lo(c)), p, c)) : W.W64}
      cf6.r_rb(k, p, P6.c6.rpick(PW.cw.odd(W.W64.lo(c)), p, c))

def cf6.pick_n(b: Bool, +p: W.W64, +c: W.W64) -> {C.n64.pick(b, p, c) == P6.c6.npick(b, p, c) : W.W64}:
  match b:
    case True{}:
      %Equal.sym(W.W64, W.W64.shl(c, 1n), P6.c6.shl1(c), cf6.shl1(c)) : {W.W64.xor(_, p) == W.W64.xor(P6.c6.shl1(c), p) : W.W64}
      {==}
    case False{}:
      cf6.shl1(c)

# the most-significant-first test of bit 63 (bit 31 of the high half)
def cf6.ntest(+x: U32) -> {Bool.not(U32.is_eq(U32.and(x, 2147483648), 0)) == PW.cw.bitk(31n, x) : Bool}:
  PC.ct.test(31n, x)

def cf6.n_nb(n: Nat, +p: W.W64, +c: W.W64) -> {C.n64.bits(n, p, c) == P6.c6.nb(n, p, c) : W.W64}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Bool, Bool.not(U32.is_eq(U32.and(W.W64.hi(c), 2147483648), 0)), PW.cw.bitk(31n, W.W64.hi(c)), cf6.ntest(W.W64.hi(c))) : {C.n64.bits(k, p, C.n64.pick(_, p, c)) == P6.c6.nb(k, p, P6.c6.npick(PW.cw.bitk(31n, W.W64.hi(c)), p, c)) : W.W64}
      %Equal.sym(W.W64, C.n64.pick(PW.cw.bitk(31n, W.W64.hi(c)), p, c), P6.c6.npick(PW.cw.bitk(31n, W.W64.hi(c)), p, c), cf6.pick_n(PW.cw.bitk(31n, W.W64.hi(c)), p, c)) : {C.n64.bits(k, p, _) == P6.c6.nb(k, p, P6.c6.npick(PW.cw.bitk(31n, W.W64.hi(c)), p, c)) : W.W64}
      cf6.n_nb(k, p, P6.c6.npick(PW.cw.bitk(31n, W.W64.hi(c)), p, c))

# The fills, write by write

def cf6.hd8() -> {Nat.is_lt(8n, 32n) == True{} : Bool}:
  {==}

def cf6.hl_tab(+e: P6.CrcPfEng64) -> {List.length(&2, W.W64, C6.c6t.tab(e)) == A.Arrays.slots(8n) : Nat}:
  {==}

def cf6.hl_rep() -> {List.length(&2, W.W64, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero())) == A.Arrays.slots(8n) : Nat}:
  {==}

def cf6.hl_set(+xs: List<&2, W.W64>, +k: Nat, +v: W.W64, +hl: {List.length(&2, W.W64, xs) == A.Arrays.slots(8n) : Nat}) -> {List.length(&2, W.W64, List.set(&2, W.W64, xs, k, v)) == A.Arrays.slots(8n) : Nat}:
  Equal.trans(Nat, List.length(&2, W.W64, List.set(&2, W.W64, xs, k, v)), List.length(&2, W.W64, xs), A.Arrays.slots(8n), AL.set_length(W.W64, xs, k, v), hl)

def cf6.fz() -> {U32.from_nat(0n) == 0 : U32}:
  {==}

def cf6.fill_r(n: Nat, +xs: List<&2, W.W64>, +p: W.W64, +k: Nat, +hl: {List.length(&2, W.W64, xs) == A.Arrays.slots(8n) : Nat}) -> {T.t64.fill.r(n, A.Arrays.of_list(W.W64, 8n, xs, W.W64.zero()), p, U32.from_nat(k)) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(n, xs, P6.CrcPfR64{p}, k), W.W64.zero()) : Array<W.W64>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.add(U32.from_nat(k), 1), U32.inc(U32.from_nat(k)), PW.cw.add_one(U32.from_nat(k))) : {T.t64.fill.r(j, Array.set(W.W64, A.Arrays.of_list(W.W64, 8n, xs, W.W64.zero()), U32.from_nat(k), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k)))), p, _) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k)))), P6.CrcPfR64{p}, 1n+k), W.W64.zero()) : Array<W.W64>}
      %Equal.sym(Array<W.W64>, Array.set(W.W64, A.Arrays.of_list(W.W64, 8n, xs, W.W64.zero()), U32.from_nat(k), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k)))), A.Arrays.of_list(W.W64, 8n, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k)))), W.W64.zero()), AL.of_list_set(W.W64, 8n, xs, W.W64.zero(), hl, cf6.hd8(), U32.from_nat(k), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k))))) : {T.t64.fill.r(j, _, p, U32.from_nat(1n+k)) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k)))), P6.CrcPfR64{p}, 1n+k), W.W64.zero()) : Array<W.W64>}
      cf6.fill_r(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k)))), p, 1n+k, cf6.hl_set(xs, A.Arrays.index(8n, U32.from_nat(k)), C.r64.bits(8n, p, W.W64.from_u32(U32.from_nat(k))), hl))

def cf6.fill_n(n: Nat, +xs: List<&2, W.W64>, +p: W.W64, +k: Nat, +hl: {List.length(&2, W.W64, xs) == A.Arrays.slots(8n) : Nat}) -> {T.t64.fill.n(n, A.Arrays.of_list(W.W64, 8n, xs, W.W64.zero()), p, U32.from_nat(k)) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(n, xs, P6.CrcPfN64{p}, k), W.W64.zero()) : Array<W.W64>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.add(U32.from_nat(k), 1), U32.inc(U32.from_nat(k)), PW.cw.add_one(U32.from_nat(k))) : {T.t64.fill.n(j, Array.set(W.W64, A.Arrays.of_list(W.W64, 8n, xs, W.W64.zero()), U32.from_nat(k), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0))), p, _) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0))), P6.CrcPfN64{p}, 1n+k), W.W64.zero()) : Array<W.W64>}
      %Equal.sym(Array<W.W64>, Array.set(W.W64, A.Arrays.of_list(W.W64, 8n, xs, W.W64.zero()), U32.from_nat(k), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0))), A.Arrays.of_list(W.W64, 8n, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0))), W.W64.zero()), AL.of_list_set(W.W64, 8n, xs, W.W64.zero(), hl, cf6.hd8(), U32.from_nat(k), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0)))) : {T.t64.fill.n(j, _, p, U32.from_nat(1n+k)) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0))), P6.CrcPfN64{p}, 1n+k), W.W64.zero()) : Array<W.W64>}
      cf6.fill_n(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0))), p, 1n+k, cf6.hl_set(xs, A.Arrays.index(8n, U32.from_nat(k)), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.from_nat(k), 24n), 0)), hl))

# The tables, built from Array.new, are the lists C6.c6t.tab

def cf6.table_r(+p: W.W64) -> {T.t64.fill.r(256n, Array.new(W.W64, 8n, W.W64.zero()), p, 0) == A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()) : Array<W.W64>}:
  %Equal.sym(Array<W.W64>, Array.new(W.W64, 8n, W.W64.zero()), A.Arrays.of_list(W.W64, 8n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), W.W64.zero()), AL.of_list_new(W.W64, 8n, W.W64.zero())) : {T.t64.fill.r(256n, _, p, 0) == A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()) : Array<W.W64>}
  %C6.c6t.tab_model(P6.CrcPfR64{p}) : {T.t64.fill.r(256n, A.Arrays.of_list(W.W64, 8n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), W.W64.zero()), p, 0) == A.Arrays.of_list(W.W64, 8n, _, W.W64.zero()) : Array<W.W64>}
  %cf6.fz() : {T.t64.fill.r(256n, A.Arrays.of_list(W.W64, 8n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), W.W64.zero()), p, _) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(256n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), P6.CrcPfR64{p}, 0n), W.W64.zero()) : Array<W.W64>}
  cf6.fill_r(256n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), p, 0n, cf6.hl_rep())

def cf6.table_n(+p: W.W64) -> {T.t64.fill.n(256n, Array.new(W.W64, 8n, W.W64.zero()), p, 0) == A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()) : Array<W.W64>}:
  %Equal.sym(Array<W.W64>, Array.new(W.W64, 8n, W.W64.zero()), A.Arrays.of_list(W.W64, 8n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), W.W64.zero()), AL.of_list_new(W.W64, 8n, W.W64.zero())) : {T.t64.fill.n(256n, _, p, 0) == A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()) : Array<W.W64>}
  %C6.c6t.tab_model(P6.CrcPfN64{p}) : {T.t64.fill.n(256n, A.Arrays.of_list(W.W64, 8n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), W.W64.zero()), p, 0) == A.Arrays.of_list(W.W64, 8n, _, W.W64.zero()) : Array<W.W64>}
  %cf6.fz() : {T.t64.fill.n(256n, A.Arrays.of_list(W.W64, 8n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), W.W64.zero()), p, _) == A.Arrays.of_list(W.W64, 8n, P6.c6.fill_model(256n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), P6.CrcPfN64{p}, 0n), W.W64.zero()) : Array<W.W64>}
  cf6.fill_n(256n, List.replicate(W.W64, A.Arrays.slots(8n), W.W64.zero()), p, 0n, cf6.hl_rep())

# A table read at any index is the engine on the index's low byte

def cf6.look_low(+e: P6.CrcPfEng64, j: U32) -> {A.Arrays.nth(W.W64, C6.c6t.tab(e), U32.to_nat(PE.ce.lowbyte(j)), W.W64.zero()) == P6.c6.ev(e, PE.ce.lowbyte(j)) : W.W64}:
  match j:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      C6.c6t.look(e, b0, b1, b2, b3, b4, b5, b6, b7)

def cf6.look_any(+e: P6.CrcPfEng64, +j: U32) -> {A.Arrays.nth(W.W64, C6.c6t.tab(e), A.Arrays.index(8n, j), W.W64.zero()) == P6.c6.ev(e, PE.ce.lowbyte(j)) : W.W64}:
  %UL.u32_and_comm(255, j) : {A.Arrays.nth(W.W64, C6.c6t.tab(e), U32.to_nat(_), W.W64.zero()) == P6.c6.ev(e, PE.ce.lowbyte(j)) : W.W64}
  %Equal.sym(U32, U32.and(255, j), PE.ce.lowbyte(j), PE.ce.mask_low(j)) : {A.Arrays.nth(W.W64, C6.c6t.tab(e), U32.to_nat(_), W.W64.zero()) == P6.c6.ev(e, PE.ce.lowbyte(j)) : W.W64}
  cf6.look_low(e, j)

# The register XOR the input byte, split into the part the table looks up
# and the rest

def cf6.dec_r(+ch: U32, +cl: U32, +h: U32) -> {W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255))) == W.W64.xor(W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h)))) : W.W64}:
  P6.c6.fp_cong(U32.xor(ch, 0), U32.xor(ch, 0), U32.xor(cl, U32.and(h, 255)), U32.xor(U32.and(4294967040, cl), U32.and(255, U32.xor(cl, h))), {==}, Equal.trans(U32, U32.xor(cl, U32.and(h, 255)), U32.xor(cl, U32.and(255, h)), U32.xor(U32.and(4294967040, cl), U32.and(255, U32.xor(cl, h))), Equal.cong(U32, U32, z => U32.xor(cl, z), U32.and(h, 255), U32.and(255, h), UL.u32_and_comm(h, 255)), PC.ct.r_split(cl, h)))

def cf6.dec_n(+ch: U32, +cl: U32, +h: U32) -> {W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0)) == W.W64.xor(W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0)) : W.W64}:
  P6.c6.fp_cong(U32.xor(ch, U32.shln(U32.and(h, 255), 24n)), U32.xor(U32.and(U32.not(4278190080), ch), U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n)), U32.xor(cl, 0), U32.xor(cl, 0), Equal.trans(U32, U32.xor(ch, U32.shln(U32.and(h, 255), 24n)), U32.xor(ch, U32.shln(U32.and(255, h), 24n)), U32.xor(U32.and(U32.not(4278190080), ch), U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n)), Equal.cong(U32, U32, z => U32.xor(ch, U32.shln(z, 24n)), U32.and(h, 255), U32.and(255, h), UL.u32_and_comm(h, 255)), Equal.sym(U32, U32.xor(U32.and(U32.not(4278190080), ch), U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n)), U32.xor(ch, U32.shln(U32.and(255, h), 24n)), PE.ce.core_split(24n, 4278190080, ch, h, PC.ct.win32(ch)))), {==})

# Reflected: one byte step through the table is eight bitwise steps

def cf6.step_rp(+ch: U32, +cl: U32, +h: U32, +p: W.W64) -> {W.W64.xor(W.W64.shr(W.W64.from_parts(ch, cl), 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfR64{p}), A.Arrays.index(8n, U32.and(U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h), 255)), W.W64.zero())) == C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255)))) : W.W64}:
  %Equal.sym(W.W64, A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfR64{p}), A.Arrays.index(8n, U32.and(U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h), 255)), W.W64.zero()), P6.c6.ev(P6.CrcPfR64{p}, PE.ce.lowbyte(U32.and(U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h), 255))), cf6.look_any(P6.CrcPfR64{p}, U32.and(U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h), 255))) : {W.W64.xor(W.W64.shr(W.W64.from_parts(ch, cl), 8n), _) == C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255)))) : W.W64}
  %Equal.sym(U32, PE.ce.lowbyte(U32.and(U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h), 255)), U32.and(255, U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h)), PE.ce.low_and(U32.xor(W.W64.lo(W.W64.from_parts(ch, cl)), h))) : {W.W64.xor(W.W64.shr(W.W64.from_parts(ch, cl), 8n), C.r64.bits(8n, p, W.W64.from_u32(_))) == C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255)))) : W.W64}
  %Equal.sym(U32, W.W64.lo(W.W64.from_parts(ch, cl)), cl, WL.lo_from_parts(ch, cl)) : {W.W64.xor(W.W64.shr(W.W64.from_parts(ch, cl), 8n), C.r64.bits(8n, p, W.W64.from_u32(U32.and(255, U32.xor(_, h))))) == C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255)))) : W.W64}
  %Equal.sym(W.W64, C.r64.bits(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h)))), P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h)))), cf6.r_rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) : {W.W64.xor(W.W64.shr(W.W64.from_parts(ch, cl), 8n), _) == C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255)))) : W.W64}
  %Equal.sym(W.W64, W.W64.shr(W.W64.from_parts(ch, cl), 8n), P6.c6.shr8(W.W64.from_parts(ch, cl)), C6.c6t.shr8_eq(ch, cl)) : {W.W64.xor(_, P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) == C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255)))) : W.W64}
  %Equal.sym(W.W64, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_u32(U32.and(h, 255))), W.W64.xor(W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h)))), cf6.dec_r(ch, cl, h)) : {W.W64.xor(P6.c6.shr8(W.W64.from_parts(ch, cl)), P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) == C.r64.bits(8n, p, _) : W.W64}
  %Equal.sym(W.W64, C.r64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h))))), P6.c6.rb(8n, p, W.W64.xor(W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h))))), cf6.r_rb(8n, p, W.W64.xor(W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h)))))) : {W.W64.xor(P6.c6.shr8(W.W64.from_parts(ch, cl)), P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) == _ : W.W64}
  %Equal.sym(W.W64, P6.c6.rb(8n, p, W.W64.xor(W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h))))), W.W64.xor(P6.c6.rb(8n, p, W.W64.from_parts(ch, U32.and(4294967040, cl))), P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))), P6.c6.r_lin(8n, p, W.W64.from_parts(ch, U32.and(4294967040, cl)), W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) : {W.W64.xor(P6.c6.shr8(W.W64.from_parts(ch, cl)), P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) == _ : W.W64}
  %Equal.sym(W.W64, P6.c6.rb(8n, p, W.W64.from_parts(ch, U32.and(4294967040, cl))), P6.c6.shr8(W.W64.from_parts(ch, cl)), C6.c6t.r_high(p, ch, cl)) : {W.W64.xor(P6.c6.shr8(W.W64.from_parts(ch, cl)), P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) == W.W64.xor(_, P6.c6.rb(8n, p, W.W64.from_u32(U32.and(255, U32.xor(cl, h))))) : W.W64}
  {==}

def cf6.step_r(+c: W.W64, +h: U32, +p: W.W64) -> {W.W64.xor(W.W64.shr(c, 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfR64{p}), A.Arrays.index(8n, U32.and(U32.xor(W.W64.lo(c), h), 255)), W.W64.zero())) == C.r64.bits(8n, p, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))) : W.W64}:
  %WL.parts_of(c) : {W.W64.xor(W.W64.shr(_, 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfR64{p}), A.Arrays.index(8n, U32.and(U32.xor(W.W64.lo(_), h), 255)), W.W64.zero())) == C.r64.bits(8n, p, W.W64.xor(_, W.W64.from_u32(U32.and(h, 255)))) : W.W64}
  cf6.step_rp(W.W64.hi(c), W.W64.lo(c), h, p)

def cf6.loop_r(xs: List<&2, U32>, +p: W.W64, +c: W.W64) -> {T.t64.r.raw(xs, (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), c)) == (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), C.r64.raw(xs, p, c)) : Array<W.W64> & W.W64}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Array<W.W64> & W.W64, Array.get(W.W64, A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), U32.and(U32.xor(W.W64.lo(c), h), 255)), (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfR64{p}), A.Arrays.index(8n, U32.and(U32.xor(W.W64.lo(c), h), 255)), W.W64.zero())), AL.of_list_get(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero(), cf6.hl_tab(P6.CrcPfR64{p}), cf6.hd8(), U32.and(U32.xor(W.W64.lo(c), h), 255))) : {T.t64.r.raw(t, T.t64.r.fin(_, c)) == (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), C.r64.raw(t, p, C.r64.bits(8n, p, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))))) : Array<W.W64> & W.W64}
      %Equal.sym(W.W64, W.W64.xor(W.W64.shr(c, 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfR64{p}), A.Arrays.index(8n, U32.and(U32.xor(W.W64.lo(c), h), 255)), W.W64.zero())), C.r64.bits(8n, p, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))), cf6.step_r(c, h, p)) : {T.t64.r.raw(t, (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), _)) == (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), C.r64.raw(t, p, C.r64.bits(8n, p, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))))) : Array<W.W64> & W.W64}
      cf6.loop_r(t, p, C.r64.bits(8n, p, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))))

def cf6.upd_r(+p: W.W64, +c: W.W64, +xs: List<&2, U32>) -> {T.t64.snd(T.t64.r.raw(xs, (T.t64.fill.r(256n, Array.new(W.W64, 8n, W.W64.zero()), p, 0), c))) == C.r64.raw(xs, p, c) : W.W64}:
  %Equal.sym(Array<W.W64>, T.t64.fill.r(256n, Array.new(W.W64, 8n, W.W64.zero()), p, 0), A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), cf6.table_r(p)) : {T.t64.snd(T.t64.r.raw(xs, (_, c))) == C.r64.raw(xs, p, c) : W.W64}
  %Equal.sym(Array<W.W64> & W.W64, T.t64.r.raw(xs, (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), c)), (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfR64{p}), W.W64.zero()), C.r64.raw(xs, p, c)), cf6.loop_r(xs, p, c)) : {T.t64.snd(_) == C.r64.raw(xs, p, c) : W.W64}
  {==}

# Most significant bit first: one byte step through the table is eight
# bitwise steps

def cf6.step_np(+ch: U32, +cl: U32, +h: U32, +p: W.W64) -> {W.W64.xor(W.W64.shl(W.W64.from_parts(ch, cl), 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfN64{p}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h), 255)), W.W64.zero())) == C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}:
  %Equal.sym(W.W64, A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfN64{p}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h), 255)), W.W64.zero()), P6.c6.ev(P6.CrcPfN64{p}, PE.ce.lowbyte(U32.and(U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h), 255))), cf6.look_any(P6.CrcPfN64{p}, U32.and(U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h), 255))) : {W.W64.xor(W.W64.shl(W.W64.from_parts(ch, cl), 8n), _) == C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}
  %Equal.sym(U32, PE.ce.lowbyte(U32.and(U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h), 255)), U32.and(255, U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h)), PE.ce.low_and(U32.xor(U32.shrn(W.W64.hi(W.W64.from_parts(ch, cl)), 24n), h))) : {W.W64.xor(W.W64.shl(W.W64.from_parts(ch, cl), 8n), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(_, 24n), 0))) == C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}
  %Equal.sym(U32, W.W64.hi(W.W64.from_parts(ch, cl)), ch, WL.hi_from_parts(ch, cl)) : {W.W64.xor(W.W64.shl(W.W64.from_parts(ch, cl), 8n), C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(_, 24n), h)), 24n), 0))) == C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}
  %Equal.sym(W.W64, C.n64.bits(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0)), P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0)), cf6.n_nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) : {W.W64.xor(W.W64.shl(W.W64.from_parts(ch, cl), 8n), _) == C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}
  %Equal.sym(W.W64, W.W64.shl(W.W64.from_parts(ch, cl), 8n), P6.c6.shl8(W.W64.from_parts(ch, cl)), C6.c6t.shl8_eq(ch, cl)) : {W.W64.xor(_, P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) == C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}
  %Equal.sym(W.W64, W.W64.xor(W.W64.from_parts(ch, cl), W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0)), W.W64.xor(W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0)), cf6.dec_n(ch, cl, h)) : {W.W64.xor(P6.c6.shl8(W.W64.from_parts(ch, cl)), P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) == C.n64.bits(8n, p, _) : W.W64}
  %Equal.sym(W.W64, C.n64.bits(8n, p, W.W64.xor(W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))), P6.c6.nb(8n, p, W.W64.xor(W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))), cf6.n_nb(8n, p, W.W64.xor(W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0)))) : {W.W64.xor(P6.c6.shl8(W.W64.from_parts(ch, cl)), P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) == _ : W.W64}
  %Equal.sym(W.W64, P6.c6.nb(8n, p, W.W64.xor(W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))), W.W64.xor(P6.c6.nb(8n, p, W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl)), P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))), P6.c6.n_lin(8n, p, W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl), W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) : {W.W64.xor(P6.c6.shl8(W.W64.from_parts(ch, cl)), P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) == _ : W.W64}
  %Equal.sym(W.W64, P6.c6.nb(8n, p, W.W64.from_parts(U32.and(U32.not(4278190080), ch), cl)), P6.c6.shl8(W.W64.from_parts(ch, cl)), C6.c6t.n_high(p, ch, cl)) : {W.W64.xor(P6.c6.shl8(W.W64.from_parts(ch, cl)), P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) == W.W64.xor(_, P6.c6.nb(8n, p, W.W64.from_parts(U32.shln(U32.and(255, U32.xor(U32.shrn(ch, 24n), h)), 24n), 0))) : W.W64}
  {==}

def cf6.step_n(+c: W.W64, +h: U32, +p: W.W64) -> {W.W64.xor(W.W64.shl(c, 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfN64{p}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(W.W64.hi(c), 24n), h), 255)), W.W64.zero())) == C.n64.bits(8n, p, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}:
  %WL.parts_of(c) : {W.W64.xor(W.W64.shl(_, 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfN64{p}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(W.W64.hi(_), 24n), h), 255)), W.W64.zero())) == C.n64.bits(8n, p, W.W64.xor(_, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))) : W.W64}
  cf6.step_np(W.W64.hi(c), W.W64.lo(c), h, p)

def cf6.loop_n(xs: List<&2, U32>, +p: W.W64, +c: W.W64) -> {T.t64.n.raw(xs, (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), c)) == (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), C.n64.raw(xs, p, c)) : Array<W.W64> & W.W64}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Array<W.W64> & W.W64, Array.get(W.W64, A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), U32.and(U32.xor(U32.shrn(W.W64.hi(c), 24n), h), 255)), (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfN64{p}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(W.W64.hi(c), 24n), h), 255)), W.W64.zero())), AL.of_list_get(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero(), cf6.hl_tab(P6.CrcPfN64{p}), cf6.hd8(), U32.and(U32.xor(U32.shrn(W.W64.hi(c), 24n), h), 255))) : {T.t64.n.raw(t, T.t64.n.fin(_, c)) == (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), C.n64.raw(t, p, C.n64.bits(8n, p, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))))) : Array<W.W64> & W.W64}
      %Equal.sym(W.W64, W.W64.xor(W.W64.shl(c, 8n), A.Arrays.nth(W.W64, C6.c6t.tab(P6.CrcPfN64{p}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(W.W64.hi(c), 24n), h), 255)), W.W64.zero())), C.n64.bits(8n, p, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))), cf6.step_n(c, h, p)) : {T.t64.n.raw(t, (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), _)) == (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), C.n64.raw(t, p, C.n64.bits(8n, p, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))))) : Array<W.W64> & W.W64}
      cf6.loop_n(t, p, C.n64.bits(8n, p, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))))

def cf6.upd_n(+p: W.W64, +c: W.W64, +xs: List<&2, U32>) -> {T.t64.snd(T.t64.n.raw(xs, (T.t64.fill.n(256n, Array.new(W.W64, 8n, W.W64.zero()), p, 0), c))) == C.n64.raw(xs, p, c) : W.W64}:
  %Equal.sym(Array<W.W64>, T.t64.fill.n(256n, Array.new(W.W64, 8n, W.W64.zero()), p, 0), A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), cf6.table_n(p)) : {T.t64.snd(T.t64.n.raw(xs, (_, c))) == C.n64.raw(xs, p, c) : W.W64}
  %Equal.sym(Array<W.W64> & W.W64, T.t64.n.raw(xs, (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), c)), (A.Arrays.of_list(W.W64, 8n, C6.c6t.tab(P6.CrcPfN64{p}), W.W64.zero()), C.n64.raw(xs, p, c)), cf6.loop_n(xs, p, c)) : {T.t64.snd(_) == C.n64.raw(xs, p, c) : W.W64}
  {==}

# The fast path is the reference, for every parameter set, register and input
def cf6.update64(spec: C.Crc64Spec, +c: W.W64, +o: B.Octets) -> {T.Crc64Spec.update_fast(spec, c, o) == C.Crc64Spec.update(spec, c, o) : W.W64}:
  match spec:
    case C.Crc64Spec{+poly, init, reflected, xorout}:
      match reflected:
        case True{}:
          cf6.upd_r(C.reflect64(poly), c, B.Octets.to_list(o))
        case False{}:
          cf6.upd_n(poly, c, B.Octets.to_list(o))
