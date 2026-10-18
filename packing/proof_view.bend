# Proof helpers for bend-osdev-packing: the view of a buffer as bits
# (view.bend). Bytes to bits and back, 8 at a time; the reorderings of
# proof_list.bend; and bytes' mask, which keeps a byte's low 8 bits (the
# bits the view reads).
import Base
import ../bytes/bytes.bend as B
import ./view.bend as V
import ./proof_list.bend as PL

def pv.ge8(n: Nat) -> Bool:
  match n:
    case 8n+k:
      True{}
    case _:
      False{}

def pv.p8(n: Nat) -> Nat:
  match n:
    case 8n+k:
      k
    case _:
      0n

def pv.nz(-k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  PL.pl.ft(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+k, 0n, Equal.sym(Nat, 0n, 1n+k, e)))

# a list shorter than 8 has no length 8 + m
def pv.short(-j: Nat, -m: Nat, e: {j == Nat.add(8n, m) : Nat}, f: {pv.ge8(j) == False{} : Bool}) -> Empty:
  PL.pl.ft(Equal.trans(Bool, False{}, pv.ge8(j), True{}, Equal.sym(Bool, pv.ge8(j), False{}, f), Equal.cong(Nat, Bool, z => pv.ge8(z), j, Nat.add(8n, m), e)))

# bytes' mask keeps the bits the view reads
def pv.bb_mask(+m: Bool, +y: U32, -r: List<&2, Bool>) -> {V.packing.byte_bits(m, B.byte(y), r) == V.packing.byte_bits(m, y, r) : List<&2, Bool>}:
  match m y:
    case False{} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      {==}
    case True{} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      {==}

def pv.bits_mask(+m: Bool, ys: List<&2, U32>) -> {V.packing.bits_of(m, B.mask(ys)) == V.packing.bits_of(m, ys) : List<&2, Bool>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %pv.bits_mask(m, t) : {V.packing.byte_bits(m, B.byte(y), V.packing.bits_of(m, B.mask(t))) == V.packing.byte_bits(m, y, _) : List<&2, Bool>}
      pv.bb_mask(m, y, V.packing.bits_of(m, B.mask(t)))

# bytes made from 8n bits give the bits back
def pv.bits_bytes(n: Nat, bs: List<&2, Bool>, +m: Bool, +h: {List.length(&2, Bool, bs) == Nat.mul(n, 8n) : Nat}) -> {V.packing.bits_of(m, V.packing.bytes_of(m, bs)) == bs : List<&2, Bool>}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{b, t}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{b, t})) == Con{b, t} : List<&2, Bool>}, pv.nz(List.length(&2, Bool, t), Equal.sym(Nat, 1n+List.length(&2, Bool, t), 0n, h)))
    case 1n+k Con{+c0, Con{+c1, Con{+c2, Con{+c3, Con{+c4, Con{+c5, Con{+c6, Con{+c7, +t}}}}}}}}:
      match m:
        case False{}:
          %pv.bits_bytes(k, t, False{}, Equal.cong(Nat, Nat, z => pv.p8(z), 8n+List.length(&2, Bool, t), 8n+Nat.mul(k, 8n), h)) : {Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, V.packing.bits_of(False{}, V.packing.bytes_of(False{}, t))}}}}}}}} == Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, _}}}}}}}} : List<&2, Bool>}
          {==}
        case True{}:
          %pv.bits_bytes(k, t, True{}, Equal.cong(Nat, Nat, z => pv.p8(z), 8n+List.length(&2, Bool, t), 8n+Nat.mul(k, 8n), h)) : {Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, V.packing.bits_of(True{}, V.packing.bytes_of(True{}, t))}}}}}}}} == Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, _}}}}}}}} : List<&2, Bool>}
          {==}
    case 1n+k Nil{}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Nil{})) == Nil{} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Nil{}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Nil{}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Nil{}})) == Con{c0, Nil{}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Nil{}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Nil{}}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Con{c1, Nil{}}})) == Con{c0, Con{c1, Nil{}}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Nil{}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Nil{}}}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Nil{}}}})) == Con{c0, Con{c1, Con{c2, Nil{}}}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Nil{}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}})) == Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}})) == Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}})) == Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}}:
      Empty.absurd({V.packing.bits_of(m, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}})) == Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}} : List<&2, Bool>}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}}), Nat.mul(k, 8n), h, {==}))

def pv.len_bytes(n: Nat, bs: List<&2, Bool>, +m: Bool, +h: {List.length(&2, Bool, bs) == Nat.mul(n, 8n) : Nat}) -> {List.length(&2, U32, V.packing.bytes_of(m, bs)) == n : Nat}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{b, t}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{b, t})) == 0n : Nat}, pv.nz(List.length(&2, Bool, t), Equal.sym(Nat, 1n+List.length(&2, Bool, t), 0n, h)))
    case 1n+ +k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, +t}}}}}}}}:
      %pv.len_bytes(k, t, m, Equal.cong(Nat, Nat, z => pv.p8(z), 8n+List.length(&2, Bool, t), 8n+Nat.mul(k, 8n), h)) : {1n+List.length(&2, U32, V.packing.bytes_of(m, t)) == 1n+_ : Nat}
      {==}
    case 1n+k Nil{}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Nil{})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Nil{}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Nil{}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Nil{}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Nil{}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Nil{}}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Con{c1, Nil{}}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Nil{}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Nil{}}}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Nil{}}}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Nil{}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Nil{}}}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Nil{}}}}}}}), Nat.mul(k, 8n), h, {==}))
    case 1n+k Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}}:
      Empty.absurd({List.length(&2, U32, V.packing.bytes_of(m, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}})) == 1n+k : Nat}, pv.short(List.length(&2, Bool, Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Nil{}}}}}}}}), Nat.mul(k, 8n), h, {==}))

def pv.len_bits(+m: Bool, ys: List<&2, U32>) -> {List.length(&2, Bool, V.packing.bits_of(m, ys)) == Nat.mul(List.length(&2, U32, ys), 8n) : Nat}:
  match m ys:
    case _ Nil{}:
      {==}
    case False{} Con{U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}, +t}:
      %pv.len_bits(False{}, t) : {8n+List.length(&2, Bool, V.packing.bits_of(False{}, t)) == 8n+_ : Nat}
      {==}
    case True{} Con{U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}, +t}:
      %pv.len_bits(True{}, t) : {8n+List.length(&2, Bool, V.packing.bits_of(True{}, t)) == 8n+_ : Nat}
      {==}

