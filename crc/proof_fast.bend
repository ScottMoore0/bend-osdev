# Proofs for bend-osdev-crc: the table-driven fast path (table.bend) equals
# the bitwise reference (crc.bend) for every parameter set and input.
#
# The method (as bend-osdev-blockdev's ImgDev and bend-osdev-ringbuf follow
# their arrays): array's laws turn the table fill, write by write, into
# Arrays.of_list(8, l, 0) for a Data list l whose entry i is the engine's
# eight steps on the byte i (of_list_new, of_list_set, index_of_nat by way
# of the counter i as U32.from_nat(i)); every table read in the loop is then
# of_list_get, a literal pair of the same table and that entry. A table read
# at a byte b is the engine on b (proof_cases.bend, by cases on b's bits).
# What is left is one byte step: the register XOR the input byte splits into
# the part the table looks up and the rest, eight engine steps commute with
# XOR (proof_engine.bend), and on the rest they only shift. Lemmas are
# prefixed cf.
import Base
import ../bytes/bytes.bend as B
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ./crc.bend as C
import ./table.bend as T
import ./proof_word.bend as PW
import ./proof_engine.bend as PE
import ./proof_cases.bend as PC

def cf.hd8() -> {Nat.is_lt(8n, 32n) == True{} : Bool}:
  {==}

def cf.hl_tab(+e: PE.CrcPfEng) -> {List.length(&2, U32, PC.ct.tab(e)) == A.Arrays.slots(8n) : Nat}:
  {==}

def cf.hl_rep() -> {List.length(&2, U32, List.replicate(U32, A.Arrays.slots(8n), 0)) == A.Arrays.slots(8n) : Nat}:
  {==}

def cf.hl_set(+xs: List<&2, U32>, +k: Nat, +v: U32, +hl: {List.length(&2, U32, xs) == A.Arrays.slots(8n) : Nat}) -> {List.length(&2, U32, List.set(&2, U32, xs, k, v)) == A.Arrays.slots(8n) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, List.set(&2, U32, xs, k, v)), List.length(&2, U32, xs), A.Arrays.slots(8n), AL.set_length(U32, xs, k, v), hl)

# a table: the array of the list PC.ct.tab(e)
def cf.otab(+e: PE.CrcPfEng) -> Array<U32>:
  A.Arrays.of_list(U32, 8n, PC.ct.tab(e), 0)

# The fills, write by write

def cf.fill_r(n: Nat, +xs: List<&2, U32>, +p: U32, +k: Nat, +hl: {List.length(&2, U32, xs) == A.Arrays.slots(8n) : Nat}) -> {T.t32.fill.r(n, A.Arrays.of_list(U32, 8n, xs, 0), p, U32.from_nat(k)) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(n, xs, PE.CrcPfR{p}, k), 0) : Array<U32>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.add(U32.from_nat(k), 1), U32.inc(U32.from_nat(k)), PW.cw.add_one(U32.from_nat(k))) : {T.t32.fill.r(j, Array.set(U32, A.Arrays.of_list(U32, 8n, xs, 0), U32.from_nat(k), C.r32.bits(8n, p, U32.from_nat(k))), p, _) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r32.bits(8n, p, U32.from_nat(k))), PE.CrcPfR{p}, 1n+k), 0) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, A.Arrays.of_list(U32, 8n, xs, 0), U32.from_nat(k), C.r32.bits(8n, p, U32.from_nat(k))), A.Arrays.of_list(U32, 8n, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r32.bits(8n, p, U32.from_nat(k))), 0), AL.of_list_set(U32, 8n, xs, 0, hl, cf.hd8(), U32.from_nat(k), C.r32.bits(8n, p, U32.from_nat(k)))) : {T.t32.fill.r(j, _, p, U32.from_nat(1n+k)) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r32.bits(8n, p, U32.from_nat(k))), PE.CrcPfR{p}, 1n+k), 0) : Array<U32>}
      cf.fill_r(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.r32.bits(8n, p, U32.from_nat(k))), p, 1n+k, cf.hl_set(xs, A.Arrays.index(8n, U32.from_nat(k)), C.r32.bits(8n, p, U32.from_nat(k)), hl))

def cf.fill_n(n: Nat, +xs: List<&2, U32>, +p: U32, +s: Nat, +tb: U32, +m: U32, +k: Nat, +hl: {List.length(&2, U32, xs) == A.Arrays.slots(8n) : Nat}) -> {T.t32.fill.n(n, A.Arrays.of_list(U32, 8n, xs, 0), p, s, tb, m, U32.from_nat(k)) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(n, xs, PE.CrcPfN{p, s, tb, m}, k), 0) : Array<U32>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.add(U32.from_nat(k), 1), U32.inc(U32.from_nat(k)), PW.cw.add_one(U32.from_nat(k))) : {T.t32.fill.n(j, Array.set(U32, A.Arrays.of_list(U32, 8n, xs, 0), U32.from_nat(k), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s))), p, s, tb, m, _) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s))), PE.CrcPfN{p, s, tb, m}, 1n+k), 0) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, A.Arrays.of_list(U32, 8n, xs, 0), U32.from_nat(k), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s))), A.Arrays.of_list(U32, 8n, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s))), 0), AL.of_list_set(U32, 8n, xs, 0, hl, cf.hd8(), U32.from_nat(k), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s)))) : {T.t32.fill.n(j, _, p, s, tb, m, U32.from_nat(1n+k)) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s))), PE.CrcPfN{p, s, tb, m}, 1n+k), 0) : Array<U32>}
      cf.fill_n(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s))), p, s, tb, m, 1n+k, cf.hl_set(xs, A.Arrays.index(8n, U32.from_nat(k)), C.n32.bits(8n, p, tb, m, U32.shln(U32.from_nat(k), s)), hl))

# The tables, built from Array.new, are the lists PC.ct.tab (the counter
# 0 is rewritten to U32.from_nat(0n), so that the kernel compares the fill
# terms as written instead of running the fills)

def cf.fz() -> {U32.from_nat(0n) == 0 : U32}:
  {==}

def cf.table_r(+p: U32) -> {T.t32.fill.r(256n, Array.new(U32, 8n, 0), p, 0) == cf.otab(PE.CrcPfR{p}) : Array<U32>}:
  %Equal.sym(Array<U32>, Array.new(U32, 8n, 0), A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), AL.of_list_new(U32, 8n, 0)) : {T.t32.fill.r(256n, _, p, 0) == cf.otab(PE.CrcPfR{p}) : Array<U32>}
  %PC.ct.tab_model(PE.CrcPfR{p}) : {T.t32.fill.r(256n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), p, 0) == A.Arrays.of_list(U32, 8n, _, 0) : Array<U32>}
  %cf.fz() : {T.t32.fill.r(256n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), p, _) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(256n, List.replicate(U32, A.Arrays.slots(8n), 0), PE.CrcPfR{p}, 0n), 0) : Array<U32>}
  cf.fill_r(256n, List.replicate(U32, A.Arrays.slots(8n), 0), p, 0n, cf.hl_rep())

def cf.table_n(+p: U32, +s: Nat, +tb: U32, +m: U32) -> {T.t32.fill.n(256n, Array.new(U32, 8n, 0), p, s, tb, m, 0) == cf.otab(PE.CrcPfN{p, s, tb, m}) : Array<U32>}:
  %Equal.sym(Array<U32>, Array.new(U32, 8n, 0), A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), AL.of_list_new(U32, 8n, 0)) : {T.t32.fill.n(256n, _, p, s, tb, m, 0) == cf.otab(PE.CrcPfN{p, s, tb, m}) : Array<U32>}
  %PC.ct.tab_model(PE.CrcPfN{p, s, tb, m}) : {T.t32.fill.n(256n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), p, s, tb, m, 0) == A.Arrays.of_list(U32, 8n, _, 0) : Array<U32>}
  %cf.fz() : {T.t32.fill.n(256n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), p, s, tb, m, _) == A.Arrays.of_list(U32, 8n, PE.ce.fill_model(256n, List.replicate(U32, A.Arrays.slots(8n), 0), PE.CrcPfN{p, s, tb, m}, 0n), 0) : Array<U32>}
  cf.fill_n(256n, List.replicate(U32, A.Arrays.slots(8n), 0), p, s, tb, m, 0n, cf.hl_rep())

# A table read at any index is the engine on the index's low byte

def cf.look_low(+e: PE.CrcPfEng, j: U32) -> {A.Arrays.nth(U32, PC.ct.tab(e), U32.to_nat(PE.ce.lowbyte(j)), 0) == PE.ce.ev(e, PE.ce.lowbyte(j)) : U32}:
  match j:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      PC.ct.look(e, b0, b1, b2, b3, b4, b5, b6, b7)

def cf.look_any(+e: PE.CrcPfEng, +j: U32) -> {A.Arrays.nth(U32, PC.ct.tab(e), A.Arrays.index(8n, j), 0) == PE.ce.ev(e, PE.ce.lowbyte(j)) : U32}:
  %PW.cw.ua_comm(255, j) : {A.Arrays.nth(U32, PC.ct.tab(e), U32.to_nat(_), 0) == PE.ce.ev(e, PE.ce.lowbyte(j)) : U32}
  %Equal.sym(U32, U32.and(255, j), PE.ce.lowbyte(j), PE.ce.mask_low(j)) : {A.Arrays.nth(U32, PC.ct.tab(e), U32.to_nat(_), 0) == PE.ce.ev(e, PE.ce.lowbyte(j)) : U32}
  cf.look_low(e, j)

# Reflected: one byte step through the table is eight bitwise steps

def cf.step_r(+c: U32, +h: U32, +p: U32) -> {U32.xor(U32.shrn(c, 8n), A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfR{p}), A.Arrays.index(8n, U32.and(U32.xor(c, h), 255)), 0)) == C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))) : U32}:
  %Equal.sym(U32, A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfR{p}), A.Arrays.index(8n, U32.and(U32.xor(c, h), 255)), 0), PE.ce.ev(PE.CrcPfR{p}, PE.ce.lowbyte(U32.and(U32.xor(c, h), 255))), cf.look_any(PE.CrcPfR{p}, U32.and(U32.xor(c, h), 255))) : {U32.xor(U32.shrn(c, 8n), _) == C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))) : U32}
  %Equal.sym(U32, PE.ce.lowbyte(U32.and(U32.xor(c, h), 255)), U32.and(255, U32.xor(c, h)), PE.ce.low_and(U32.xor(c, h))) : {U32.xor(U32.shrn(c, 8n), C.r32.bits(8n, p, _)) == C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))) : U32}
  %PW.cw.ua_comm(255, h) : {U32.xor(U32.shrn(c, 8n), C.r32.bits(8n, p, U32.and(255, U32.xor(c, h)))) == C.r32.bits(8n, p, U32.xor(c, _)) : U32}
  %Equal.sym(U32, U32.xor(c, U32.and(255, h)), U32.xor(U32.and(4294967040, c), U32.and(255, U32.xor(c, h))), PC.ct.r_split(c, h)) : {U32.xor(U32.shrn(c, 8n), C.r32.bits(8n, p, U32.and(255, U32.xor(c, h)))) == C.r32.bits(8n, p, _) : U32}
  %Equal.sym(U32, C.r32.bits(8n, p, U32.xor(U32.and(4294967040, c), U32.and(255, U32.xor(c, h)))), PE.ce.rb(8n, p, U32.xor(U32.and(4294967040, c), U32.and(255, U32.xor(c, h)))), PE.ce.r_rb(8n, p, U32.xor(U32.and(4294967040, c), U32.and(255, U32.xor(c, h))))) : {U32.xor(U32.shrn(c, 8n), C.r32.bits(8n, p, U32.and(255, U32.xor(c, h)))) == _ : U32}
  %Equal.sym(U32, PE.ce.rb(8n, p, U32.xor(U32.and(4294967040, c), U32.and(255, U32.xor(c, h)))), U32.xor(PE.ce.rb(8n, p, U32.and(4294967040, c)), PE.ce.rb(8n, p, U32.and(255, U32.xor(c, h)))), PE.ce.r_lin(8n, p, U32.and(4294967040, c), U32.and(255, U32.xor(c, h)))) : {U32.xor(U32.shrn(c, 8n), C.r32.bits(8n, p, U32.and(255, U32.xor(c, h)))) == _ : U32}
  %Equal.sym(U32, PE.ce.rb(8n, p, U32.and(4294967040, c)), U32.shrn(c, 8n), PC.ct.r_high(p, c)) : {U32.xor(U32.shrn(c, 8n), C.r32.bits(8n, p, U32.and(255, U32.xor(c, h)))) == U32.xor(_, PE.ce.rb(8n, p, U32.and(255, U32.xor(c, h)))) : U32}
  %Equal.sym(U32, C.r32.bits(8n, p, U32.and(255, U32.xor(c, h))), PE.ce.rb(8n, p, U32.and(255, U32.xor(c, h))), PE.ce.r_rb(8n, p, U32.and(255, U32.xor(c, h)))) : {U32.xor(U32.shrn(c, 8n), _) == U32.xor(U32.shrn(c, 8n), PE.ce.rb(8n, p, U32.and(255, U32.xor(c, h)))) : U32}
  {==}

def cf.loop_r(xs: List<&2, U32>, +p: U32, +c: U32) -> {T.t32.r.raw(xs, (cf.otab(PE.CrcPfR{p}), c)) == (cf.otab(PE.CrcPfR{p}), C.r32.raw(xs, p, c)) : Array<U32> & U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, cf.otab(PE.CrcPfR{p}), U32.and(U32.xor(c, h), 255)), (cf.otab(PE.CrcPfR{p}), A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfR{p}), A.Arrays.index(8n, U32.and(U32.xor(c, h), 255)), 0)), AL.of_list_get(U32, 8n, PC.ct.tab(PE.CrcPfR{p}), 0, cf.hl_tab(PE.CrcPfR{p}), cf.hd8(), U32.and(U32.xor(c, h), 255))) : {T.t32.r.raw(t, T.t32.r.fin(_, c)) == (cf.otab(PE.CrcPfR{p}), C.r32.raw(t, p, C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))))) : Array<U32> & U32}
      %Equal.sym(U32, U32.xor(U32.shrn(c, 8n), A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfR{p}), A.Arrays.index(8n, U32.and(U32.xor(c, h), 255)), 0)), C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))), cf.step_r(c, h, p)) : {T.t32.r.raw(t, (cf.otab(PE.CrcPfR{p}), _)) == (cf.otab(PE.CrcPfR{p}), C.r32.raw(t, p, C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))))) : Array<U32> & U32}
      cf.loop_r(t, p, C.r32.bits(8n, p, U32.xor(c, U32.and(h, 255))))

def cf.upd_r(+rp: U32, +c: U32, +xs: List<&2, U32>) -> {T.t32.snd(T.t32.r.raw(xs, (T.t32.fill.r(256n, Array.new(U32, 8n, 0), rp, 0), c))) == C.r32.raw(xs, rp, c) : U32}:
  %Equal.sym(Array<U32>, T.t32.fill.r(256n, Array.new(U32, 8n, 0), rp, 0), cf.otab(PE.CrcPfR{rp}), cf.table_r(rp)) : {T.t32.snd(T.t32.r.raw(xs, (_, c))) == C.r32.raw(xs, rp, c) : U32}
  %Equal.sym(Array<U32> & U32, T.t32.r.raw(xs, (cf.otab(PE.CrcPfR{rp}), c)), (cf.otab(PE.CrcPfR{rp}), C.r32.raw(xs, rp, c)), cf.loop_r(xs, rp, c)) : {T.t32.snd(_) == C.r32.raw(xs, rp, c) : U32}
  {==}

# Most significant bit first, width 8 and up: one byte step through the
# table is eight bitwise steps

def cf.n_nb(n: Nat, +p: U32, +k: Nat, +m: U32, +c: U32) -> {C.n32.bits(n, p, U32.shln(1, k), m, c) == PE.ce.nb(n, p, k, m, c) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Bool, Bool.not(U32.is_eq(U32.and(c, U32.shln(1, k)), 0)), PW.cw.bitk(k, c), PC.ct.test(k, c)) : {C.n32.bits(j, p, U32.shln(1, k), m, C.n32.pick(_, p, m, c)) == PE.ce.nb(j, p, k, m, PE.ce.npick(PW.cw.bitk(k, c), p, m, c)) : U32}
      %Equal.sym(U32, C.n32.pick(PW.cw.bitk(k, c), p, m, c), PE.ce.npick(PW.cw.bitk(k, c), p, m, c), PE.ce.pick_np(PW.cw.bitk(k, c), p, m, c)) : {C.n32.bits(j, p, U32.shln(1, k), m, _) == PE.ce.nb(j, p, k, m, PE.ce.npick(PW.cw.bitk(k, c), p, m, c)) : U32}
      cf.n_nb(j, p, k, m, PE.ce.npick(PW.cw.bitk(k, c), p, m, c))

def cf.step_n(+width: Nat, +hw: {Nat.is_lt(width, 8n) == False{} : Bool}, +c: U32, +h: U32, +p: U32) -> {U32.and(U32.xor(U32.shln(c, 8n), A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255)), 0)), U32.sub(U32.shln(1, width), 1)) == C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))) : U32}:
  %Equal.sym(U32, A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255)), 0), PE.ce.ev(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}, PE.ce.lowbyte(U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255))), cf.look_any(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}, U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255))) : {U32.and(U32.xor(U32.shln(c, 8n), _), U32.sub(U32.shln(1, width), 1)) == C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))) : U32}
  %Equal.sym(U32, PE.ce.lowbyte(U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255)), U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), PE.ce.low_and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h))) : {U32.and(U32.xor(U32.shln(c, 8n), C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.shln(_, Nat.sub(width, 8n)))), U32.sub(U32.shln(1, width), 1)) == C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))) : U32}
  %Equal.sym(U32, C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), Nat.sub(width, 8n))), PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), Nat.sub(width, 8n))), cf.n_nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), Nat.sub(width, 8n)))) : {U32.and(U32.xor(U32.shln(c, 8n), _), U32.sub(U32.shln(1, width), 1)) == C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))) : U32}
  %Equal.sym(U32, C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))), PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))), cf.n_nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n))))) : {U32.and(U32.xor(U32.shln(c, 8n), PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), Nat.sub(width, 8n)))), U32.sub(U32.shln(1, width), 1)) == _ : U32}
  %PW.cw.ua_comm(U32.sub(U32.shln(1, width), 1), U32.xor(U32.shln(c, 8n), PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), Nat.sub(width, 8n))))) : {_ == PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))) : U32}
  %PW.cw.ua_comm(255, h) : {U32.and(U32.sub(U32.shln(1, width), 1), U32.xor(U32.shln(c, 8n), PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h)), Nat.sub(width, 8n))))) == PE.ce.nb(8n, p, Nat.sub(width, 1n), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(_, Nat.sub(width, 8n)))) : U32}
  PC.ct.core(width, hw, c, h, p)

def cf.loop_n(xs: List<&2, U32>, +width: Nat, +hw: {Nat.is_lt(width, 8n) == False{} : Bool}, +p: U32, +c: U32) -> {T.t32.n.raw(xs, Nat.sub(width, 8n), U32.sub(U32.shln(1, width), 1), (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), c)) == (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), C.n32.raw(xs, p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c)) : Array<U32> & U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255)), (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255)), 0)), AL.of_list_get(U32, 8n, PC.ct.tab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), 0, cf.hl_tab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), cf.hd8(), U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255))) : {T.t32.n.raw(t, Nat.sub(width, 8n), U32.sub(U32.shln(1, width), 1), T.t32.n.fin(_, c, U32.sub(U32.shln(1, width), 1))) == (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), C.n32.raw(t, p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))))) : Array<U32> & U32}
      %Equal.sym(U32, U32.and(U32.xor(U32.shln(c, 8n), A.Arrays.nth(U32, PC.ct.tab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), A.Arrays.index(8n, U32.and(U32.xor(U32.shrn(c, Nat.sub(width, 8n)), h), 255)), 0)), U32.sub(U32.shln(1, width), 1)), C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))), cf.step_n(width, hw, c, h, p)) : {T.t32.n.raw(t, Nat.sub(width, 8n), U32.sub(U32.shln(1, width), 1), (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), _)) == (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), C.n32.raw(t, p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))))) : Array<U32> & U32}
      cf.loop_n(t, width, hw, p, C.n32.bits(8n, p, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), U32.xor(c, U32.shln(U32.and(h, 255), Nat.sub(width, 8n)))))

def cf.upd_n(+width: Nat, +hw: {Nat.is_lt(width, 8n) == False{} : Bool}, +p: U32, +c: U32, +xs: List<&2, U32>) -> {T.t32.update.msb(False{}, width, p, c, xs) == C.Crc32Spec.update.msb(False{}, width, p, c, xs) : U32}:
  %Equal.sym(Array<U32>, T.t32.fill.n(256n, Array.new(U32, 8n, 0), p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), 0), cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), cf.table_n(p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1))) : {T.t32.snd(T.t32.n.raw(xs, Nat.sub(width, 8n), U32.sub(U32.shln(1, width), 1), (_, c))) == C.n32.raw(xs, p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c) : U32}
  %Equal.sym(Array<U32> & U32, T.t32.n.raw(xs, Nat.sub(width, 8n), U32.sub(U32.shln(1, width), 1), (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), c)), (cf.otab(PE.CrcPfN{p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1)}), C.n32.raw(xs, p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c)), cf.loop_n(xs, width, hw, p, c)) : {T.t32.snd(_) == C.n32.raw(xs, p, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c) : U32}
  {==}

# below width 8 both are the bitwise engine
def cf.upd_msb(small: Bool, +width: Nat, +eh: {Nat.is_lt(width, 8n) == small : Bool}, +p: U32, +c: U32, +xs: List<&2, U32>) -> {T.t32.update.msb(small, width, p, c, xs) == C.Crc32Spec.update.msb(small, width, p, c, xs) : U32}:
  match small:
    case True{}:
      {==}
    case False{}:
      cf.upd_n(width, eh, p, c, xs)

# The fast path is the reference, for every parameter set, register and input
def cf.update32(spec: C.Crc32Spec, +c: U32, +o: B.Octets) -> {T.Crc32Spec.update_fast(spec, c, o) == C.Crc32Spec.update(spec, c, o) : U32}:
  match spec:
    case C.Crc32Spec{+width, +poly, init, reflected, xorout}:
      match reflected:
        case True{}:
          cf.upd_r(C.reflect32(poly, width), c, B.Octets.to_list(o))
        case False{}:
          cf.upd_msb(Nat.is_lt(width, 8n), width, {==}, poly, c, B.Octets.to_list(o))
