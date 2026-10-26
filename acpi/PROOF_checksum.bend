# The proof of LAWS_checksum.bend.
#
# AcpiChecksum.sum adds the bytes' low 8 bits in a U32 and keeps the low 8
# bits of the total. Its value is low(8, ckp.ns(bytes)), ckp.ns being the
# Nat sum of the bytes' low 8 bits (ckp.sumv): the low 8 bits of a U32 sum
# do not see the 2^32 a wrap takes away (u32's u32_add_wrap, and low_add_dbl
# with 2^32 = 2^8 2^24), nor the high bits of an addend (ckp.l1). fix(i, o)
# is take(i, o) ++ [b] ++ drop(1 + i, o), and o itself is take(i, o) ++
# [o_i] ++ drop(1 + i, o) (ckp.split, through bytes' take, drop and at
# laws). With S the sum of o and T the sum of the bytes other than o_i,
# byte_for computes w = S - o_i and b = 256 - w, each modulo 256 (U32
# subtraction plus the subtrahend is the minuend plus 2^32 on a borrow,
# u32_sub_wrap); so w = T and b + T = 0 modulo 256 (ckp.zero, by cancelling
# o_i: ckp.cancel).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP
import ./checksum.bend as C
import ./LAWS_checksum.bend as Laws

def ckp.bool(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ckp.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %e : ckp.bool(_)
  Unit{}

def ckp.isz(+n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def ckp.nz0(+e: {0n == 1n : Nat}) -> Empty:
  %e : ckp.isz(_)
  Unit{}

def ckp.is1(+n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      match p:
        case 0n:
          Empty
        case 1n+q:
          Unit

def ckp.nz1(-k: Nat, +e: {1n+1n+k == 1n : Nat}) -> Empty:
  %e : ckp.is1(_)
  Unit{}

# a byte's low 8 bits, through bytes' byte, are its low 8 bits

def ckp.bb2(+z: U32) -> {B.byte(U32.and(255, z)) == U32.and(255, z) : U32}:
  match z:
    case U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, WCon{z8, WCon{z9, WCon{z10, WCon{z11, WCon{z12, WCon{z13, WCon{z14, WCon{z15, WCon{z16, WCon{z17, WCon{z18, WCon{z19, WCon{z20, WCon{z21, WCon{z22, WCon{z23, WCon{z24, WCon{z25, WCon{z26, WCon{z27, WCon{z28, WCon{z29, WCon{z30, WCon{z31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def ckp.bb3(+z: U32) -> {U32.and(255, B.byte(z)) == U32.and(255, z) : U32}:
  match z:
    case U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, WCon{z8, WCon{z9, WCon{z10, WCon{z11, WCon{z12, WCon{z13, WCon{z14, WCon{z15, WCon{z16, WCon{z17, WCon{z18, WCon{z19, WCon{z20, WCon{z21, WCon{z22, WCon{z23, WCon{z24, WCon{z25, WCon{z26, WCon{z27, WCon{z28, WCon{z29, WCon{z30, WCon{z31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def ckp.bb(+z: U32) -> {U32.and(255, B.byte(U32.and(255, z))) == U32.and(255, z) : U32}:
  match z:
    case U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, WCon{z8, WCon{z9, WCon{z10, WCon{z11, WCon{z12, WCon{z13, WCon{z14, WCon{z15, WCon{z16, WCon{z17, WCon{z18, WCon{z19, WCon{z20, WCon{z21, WCon{z22, WCon{z23, WCon{z24, WCon{z25, WCon{z26, WCon{z27, WCon{z28, WCon{z29, WCon{z30, WCon{z31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# Nat arithmetic modulo 256

def ckp.am(+z: U32) -> {U32.to_nat(U32.and(255, z)) == U.U32Nat.low(8n, U32.to_nat(z)) : Nat}:
  %UL.u32_and_comm(z, 255) : {U32.to_nat(_) == U.U32Nat.low(8n, U32.to_nat(z)) : Nat}
  UL.u32_and_mask(z, 255, 8n, {==})

def ckp.l1(+x: Nat, +y: Nat) -> {U.U32Nat.low(8n, Nat.add(x, y)) == U.U32Nat.low(8n, Nat.add(U.U32Nat.low(8n, x), y)) : Nat}:
  %UL.low_high(8n, x) : {U.U32Nat.low(8n, Nat.add(_, y)) == U.U32Nat.low(8n, Nat.add(U.U32Nat.low(8n, x), y)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U.U32Nat.low(8n, x), U.U32Nat.dbl(8n, U.U32Nat.high(8n, x))), y), Nat.add(U.U32Nat.low(8n, x), Nat.add(U.U32Nat.dbl(8n, U.U32Nat.high(8n, x)), y)), UL.nat_add_assoc(U.U32Nat.low(8n, x), U.U32Nat.dbl(8n, U.U32Nat.high(8n, x)), y)) : {U.U32Nat.low(8n, _) == U.U32Nat.low(8n, Nat.add(U.U32Nat.low(8n, x), y)) : Nat}
  %UL.nat_add_comm(y, U.U32Nat.dbl(8n, U.U32Nat.high(8n, x))) : {U.U32Nat.low(8n, Nat.add(U.U32Nat.low(8n, x), _)) == U.U32Nat.low(8n, Nat.add(U.U32Nat.low(8n, x), y)) : Nat}
  %UL.nat_add_assoc(U.U32Nat.low(8n, x), y, U.U32Nat.dbl(8n, U.U32Nat.high(8n, x))) : {U.U32Nat.low(8n, _) == U.U32Nat.low(8n, Nat.add(U.U32Nat.low(8n, x), y)) : Nat}
  UL.low_add_dbl(8n, Nat.add(U.U32Nat.low(8n, x), y), U.U32Nat.high(8n, x))

def ckp.l1r(+a: Nat, +b: Nat) -> {U.U32Nat.low(8n, Nat.add(a, b)) == U.U32Nat.low(8n, Nat.add(a, U.U32Nat.low(8n, b))) : Nat}:
  %UL.nat_add_comm(b, a) : {U.U32Nat.low(8n, _) == U.U32Nat.low(8n, Nat.add(a, U.U32Nat.low(8n, b))) : Nat}
  %UL.nat_add_comm(U.U32Nat.low(8n, b), a) : {U.U32Nat.low(8n, Nat.add(b, a)) == U.U32Nat.low(8n, _) : Nat}
  ckp.l1(b, a)

def ckp.l2(+z: Nat, +k: Nat) -> {U.U32Nat.low(8n, Nat.add(z, U.U32Nat.dbl(32n, k))) == U.U32Nat.low(8n, z) : Nat}:
  %UL.dbl_dbl(8n, 24n, k) : {U.U32Nat.low(8n, Nat.add(z, _)) == U.U32Nat.low(8n, z) : Nat}
  UL.low_add_dbl(8n, z, U.U32Nat.dbl(24n, k))

def ckp.ll(+z: Nat) -> {U.U32Nat.low(8n, U.U32Nat.low(8n, z)) == U.U32Nat.low(8n, z) : Nat}:
  UL.low_small(8n, U.U32Nat.low(8n, z), UL.low_lt(8n, z))

# x + a and x + b agree modulo 256: so do a and b

def ckp.cr(+x: Nat, +a: Nat, +b: Nat, +e: {U.U32Nat.low(8n, Nat.add(x, a)) == U.U32Nat.low(8n, Nat.add(x, b)) : Nat}) -> {Nat.add(x, Nat.add(a, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))) == Nat.add(x, Nat.add(b, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))))) : Nat}:
  %UL.nat_add_assoc(x, a, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))) : {_ == Nat.add(x, Nat.add(b, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))))) : Nat}
  %UL.low_high(8n, Nat.add(x, a)) : {Nat.add(_, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))) == Nat.add(x, Nat.add(b, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))))) : Nat}
  %UL.nat_add_assoc(x, b, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))) : {Nat.add(Nat.add(U.U32Nat.low(8n, Nat.add(x, a)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))) == _ : Nat}
  %UL.low_high(8n, Nat.add(x, b)) : {Nat.add(Nat.add(U.U32Nat.low(8n, Nat.add(x, a)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))) == Nat.add(_, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))) : Nat}
  %Equal.sym(Nat, U.U32Nat.low(8n, Nat.add(x, a)), U.U32Nat.low(8n, Nat.add(x, b)), e) : {Nat.add(Nat.add(_, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))) == Nat.add(Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))), Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), Nat.add(U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))), UL.nat_add_assoc(U.U32Nat.low(8n, Nat.add(x, b)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))) : {_ == Nat.add(Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))), Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), Nat.add(U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))))), UL.nat_add_assoc(U.U32Nat.low(8n, Nat.add(x, b)), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))))) : {Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), Nat.add(U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))) == _ : Nat}
  %UL.nat_add_comm(U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))) : {Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), Nat.add(U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a))), U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))) == Nat.add(U.U32Nat.low(8n, Nat.add(x, b)), _) : Nat}
  {==}

def ckp.cancel(+x: Nat, +a: Nat, +b: Nat, +e: {U.U32Nat.low(8n, Nat.add(x, a)) == U.U32Nat.low(8n, Nat.add(x, b)) : Nat}) -> {U.U32Nat.low(8n, a) == U.U32Nat.low(8n, b) : Nat}:
  %UL.low_add_dbl(8n, a, U.U32Nat.high(8n, Nat.add(x, b))) : {_ == U.U32Nat.low(8n, b) : Nat}
  %UL.low_add_dbl(8n, b, U.U32Nat.high(8n, Nat.add(x, a))) : {U.U32Nat.low(8n, Nat.add(a, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))) == _ : Nat}
  %UL.nat_add_cancel(x, Nat.add(a, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b)))), Nat.add(b, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, a)))), ckp.cr(x, a, b, e)) : {U.U32Nat.low(8n, Nat.add(a, U.U32Nat.dbl(8n, U.U32Nat.high(8n, Nat.add(x, b))))) == U.U32Nat.low(8n, _) : Nat}
  {==}

# w + x = A + (x + D) and c + w = 0 modulo 256: A + (c + D) = 0

def ckp.e1x(+nA: Nat, +nD: Nat, +x: Nat, +w: Nat, +e1: {U.U32Nat.low(8n, Nat.add(w, x)) == U.U32Nat.low(8n, Nat.add(nA, Nat.add(x, nD))) : Nat}) -> {U.U32Nat.low(8n, Nat.add(x, w)) == U.U32Nat.low(8n, Nat.add(x, Nat.add(nA, nD))) : Nat}:
  %UL.nat_add_comm(w, x) : {U.U32Nat.low(8n, _) == U.U32Nat.low(8n, Nat.add(x, Nat.add(nA, nD))) : Nat}
  %UL.nat_add_left_comm(nA, x, nD) : {U.U32Nat.low(8n, Nat.add(w, x)) == U.U32Nat.low(8n, _) : Nat}
  e1

def ckp.zero(+nA: Nat, +nD: Nat, +x: Nat, +c: Nat, +w: Nat, +e1: {U.U32Nat.low(8n, Nat.add(w, x)) == U.U32Nat.low(8n, Nat.add(nA, Nat.add(x, nD))) : Nat}, +e2: {U.U32Nat.low(8n, Nat.add(c, w)) == 0n : Nat}) -> {U.U32Nat.low(8n, Nat.add(nA, Nat.add(c, nD))) == 0n : Nat}:
  %UL.nat_add_left_comm(c, nA, nD) : {U.U32Nat.low(8n, _) == 0n : Nat}
  %Equal.sym(Nat, U.U32Nat.low(8n, Nat.add(c, Nat.add(nA, nD))), U.U32Nat.low(8n, Nat.add(c, U.U32Nat.low(8n, Nat.add(nA, nD)))), ckp.l1r(c, Nat.add(nA, nD))) : {_ == 0n : Nat}
  %ckp.cancel(x, w, Nat.add(nA, nD), ckp.e1x(nA, nD, x, w, e1)) : {U.U32Nat.low(8n, Nat.add(c, _)) == 0n : Nat}
  %ckp.l1r(c, w) : {_ == 0n : Nat}
  e2

# The sum's value: low(8, ns(bytes))

def ckp.ns(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(U32.to_nat(U32.and(255, h)), ckp.ns(t))

def ckp.go(+xs: List<&2, U32>, +acc: U32) -> {U.U32Nat.low(8n, U32.to_nat(C.ck.sum.go(xs, acc))) == U.U32Nat.low(8n, Nat.add(U32.to_nat(acc), ckp.ns(xs))) : Nat}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(acc), 0n), U32.to_nat(acc), UL.nat_add_zero(U32.to_nat(acc))) : {U.U32Nat.low(8n, U32.to_nat(acc)) == U.U32Nat.low(8n, _) : Nat}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, U.U32Nat.low(8n, U32.to_nat(C.ck.sum.go(t, U32.add(acc, U32.and(255, h))))), U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))), ckp.go(t, U32.add(acc, U32.and(255, h)))) : {_ == U.U32Nat.low(8n, Nat.add(U32.to_nat(acc), Nat.add(U32.to_nat(U32.and(255, h)), ckp.ns(t)))) : Nat}
      %UL.nat_add_assoc(U32.to_nat(acc), U32.to_nat(U32.and(255, h)), ckp.ns(t)) : {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))) == U.U32Nat.low(8n, _) : Nat}
      %UL.u32_add_wrap(acc, U32.and(255, h)) : {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))) == U.U32Nat.low(8n, Nat.add(_, ckp.ns(t))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc)))), ckp.ns(t)), Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), Nat.add(U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc))), ckp.ns(t))), UL.nat_add_assoc(U32.to_nat(U32.add(acc, U32.and(255, h))), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc))), ckp.ns(t))) : {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))) == U.U32Nat.low(8n, _) : Nat}
      %UL.nat_add_comm(ckp.ns(t), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc)))) : {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))) == U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), _)) : Nat}
      %UL.nat_add_assoc(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc)))) : {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))) == U.U32Nat.low(8n, _) : Nat}
      Equal.sym(Nat, U.U32Nat.low(8n, Nat.add(Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t)), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc))))), U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t))), ckp.l2(Nat.add(U32.to_nat(U32.add(acc, U32.and(255, h))), ckp.ns(t)), U.U32Nat.bit(U32.is_lt(U32.add(acc, U32.and(255, h)), acc))))

def ckp.sumv(+o: B.Octets) -> {U32.to_nat(C.AcpiChecksum.sum(o)) == U.U32Nat.low(8n, ckp.ns(B.Octets.to_list(o))) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.and(255, C.ck.sum.go(B.Octets.to_list(o), 0))), U.U32Nat.low(8n, U32.to_nat(C.ck.sum.go(B.Octets.to_list(o), 0))), ckp.am(C.ck.sum.go(B.Octets.to_list(o), 0))) : {_ == U.U32Nat.low(8n, ckp.ns(B.Octets.to_list(o))) : Nat}
  ckp.go(B.Octets.to_list(o), 0)

def ckp.nsapp(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {ckp.ns(B.append(xs, ys)) == Nat.add(ckp.ns(xs), ckp.ns(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, ckp.ns(B.append(t, ys)), Nat.add(ckp.ns(t), ckp.ns(ys)), ckp.nsapp(t, ys)) : {Nat.add(U32.to_nat(U32.and(255, h)), _) == Nat.add(ckp.ns(Con{h, t}), ckp.ns(ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(U32.and(255, h)), ckp.ns(t)), ckp.ns(ys)), Nat.add(U32.to_nat(U32.and(255, h)), Nat.add(ckp.ns(t), ckp.ns(ys))), UL.nat_add_assoc(U32.to_nat(U32.and(255, h)), ckp.ns(t), ckp.ns(ys)))

# A byte string with a byte at offset i: the bytes before it, it, and the
# bytes after it

def ckp.one(+l: List<&2, U32>, +hl: {B.len(l) == 1n : Nat}) -> {ckp.ns(l) == U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.at(l, 0n), 0))) : Nat}:
  match l:
    case Nil{}:
      Empty.absurd({ckp.ns(Nil{}) == U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.at(Nil{}, 0n), 0))) : Nat}, ckp.nz0(hl))
    case Con{+h, +t}:
      match t:
        case Nil{}:
          %Equal.sym(U32, U32.and(255, B.byte(h)), U32.and(255, h), ckp.bb3(h)) : {Nat.add(U32.to_nat(U32.and(255, h)), 0n) == U32.to_nat(_) : Nat}
          UL.nat_add_zero(U32.to_nat(U32.and(255, h)))
        case Con{h2, t2}:
          Empty.absurd({ckp.ns(Con{h, Con{h2, t2}}) == U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.at(Con{h, Con{h2, t2}}, 0n), 0))) : Nat}, ckp.nz1(B.len(t2), hl))

def ckp.head(+d: B.Octets, +hd: {Nat.is_le(1n, B.Octets.len(d)) == True{} : Bool}) -> {ckp.ns(B.Octets.to_list(d)) == Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(d, 0n), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}:
  %BL.octets_take_drop(1n, d) : {ckp.ns(B.Octets.to_list(_)) == Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(d, 0n), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.take(1n, d), B.Octets.drop(1n, d))), B.append(B.Octets.to_list(B.Octets.take(1n, d)), B.Octets.to_list(B.Octets.drop(1n, d))), BL.octets_append_list(B.Octets.take(1n, d), B.Octets.drop(1n, d))) : {ckp.ns(_) == Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(d, 0n), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}
  %Equal.sym(Nat, ckp.ns(B.append(B.Octets.to_list(B.Octets.take(1n, d)), B.Octets.to_list(B.Octets.drop(1n, d)))), Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(1n, d))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))), ckp.nsapp(B.Octets.to_list(B.Octets.take(1n, d)), B.Octets.to_list(B.Octets.drop(1n, d)))) : {_ == Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(d, 0n), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}
  %BL.octets_at_take(1n, d, 0n, {==}) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(1n, d))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) == Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, _, 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.take(1n, d), 0n), B.at(B.Octets.to_list(B.Octets.take(1n, d)), 0n), BL.octets_at_list(B.Octets.take(1n, d), 0n)) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(1n, d))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) == Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, _, 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}
  %ckp.one(B.Octets.to_list(B.Octets.take(1n, d)), Equal.trans(Nat, B.len(B.Octets.to_list(B.Octets.take(1n, d))), B.Octets.len(B.Octets.take(1n, d)), 1n, Equal.sym(Nat, B.Octets.len(B.Octets.take(1n, d)), B.len(B.Octets.to_list(B.Octets.take(1n, d))), BL.octets_len_list(B.Octets.take(1n, d))), BL.octets_len_take_le(1n, d, hd))) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(1n, d))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) == Nat.add(_, ckp.ns(B.Octets.to_list(B.Octets.drop(1n, d)))) : Nat}
  {==}

def ckp.lt_sub(+i: Nat, +n: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_le(1n, Nat.sub(n, i)) == True{} : Bool}:
  match i:
    case 0n:
      match n:
        case 0n:
          Empty.absurd({Nat.is_le(1n, Nat.sub(0n, 0n)) == True{} : Bool}, ckp.ft(h))
        case 1n+p:
          UO.nat_le_add_r(1n, p)
    case 1n+ip:
      match n:
        case 0n:
          Empty.absurd({Nat.is_le(1n, Nat.sub(0n, 1n+ip)) == True{} : Bool}, ckp.ft(h))
        case 1n+p:
          ckp.lt_sub(ip, p, h)

def ckp.hdd(+i: Nat, +o: B.Octets, +h: {Nat.is_lt(i, B.Octets.len(o)) == True{} : Bool}) -> {Nat.is_le(1n, B.Octets.len(B.Octets.drop(i, o))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.drop(i, o)), Nat.sub(B.Octets.len(o), i), BL.octets_len_drop(i, o)) : {Nat.is_le(1n, _) == True{} : Bool}
  ckp.lt_sub(i, B.Octets.len(o), h)

def ckp.split(+i: Nat, +o: B.Octets, +h: {Nat.is_lt(i, B.Octets.len(o)) == True{} : Bool}) -> {ckp.ns(B.Octets.to_list(o)) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}:
  %BL.octets_take_drop(i, o) : {ckp.ns(B.Octets.to_list(_)) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.take(i, o), B.Octets.drop(i, o))), B.append(B.Octets.to_list(B.Octets.take(i, o)), B.Octets.to_list(B.Octets.drop(i, o))), BL.octets_append_list(B.Octets.take(i, o), B.Octets.drop(i, o))) : {ckp.ns(_) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(Nat, ckp.ns(B.append(B.Octets.to_list(B.Octets.take(i, o)), B.Octets.to_list(B.Octets.drop(i, o)))), Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), ckp.ns(B.Octets.to_list(B.Octets.drop(i, o)))), ckp.nsapp(B.Octets.to_list(B.Octets.take(i, o)), B.Octets.to_list(B.Octets.drop(i, o)))) : {_ == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(Nat, ckp.ns(B.Octets.to_list(B.Octets.drop(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(B.Octets.drop(i, o), 0n), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, B.Octets.drop(i, o))))), ckp.head(B.Octets.drop(i, o), ckp.hdd(i, o, h))) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), _) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.drop(i, o), 0n), B.Octets.at(o, Nat.add(i, 0n)), BL.octets_at_drop(i, o, 0n)) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, _, 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, B.Octets.drop(i, o)))))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(Nat, Nat.add(i, 0n), i, UL.nat_add_zero(i)) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, _), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n, B.Octets.drop(i, o)))))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(B.Octets, B.Octets.drop(1n, B.Octets.drop(i, o)), B.Octets.drop(Nat.add(i, 1n), o), BL.octets_drop_drop(i, 1n, o)) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(_)))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %UL.nat_add_comm(1n, i) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(_, o))))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  {==}

# The fixed bytes: the bytes before i, the checksum byte, the bytes after

def ckp.fixsum(+i: Nat, +o: B.Octets, +h: {Nat.is_lt(i, B.Octets.len(o)) == True{} : Bool}) -> {ckp.ns(B.Octets.to_list(C.AcpiChecksum.fix(i, o))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}:
  %Equal.sym(Bool, Nat.is_lt(i, B.Octets.len(o)), True{}, h) : {ckp.ns(B.Octets.to_list(C.ck.fix.pick(_, i, o))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(B.Octets, B.Octets.concat(Con{B.Octets.take(i, o), [B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)]}), B.Octets.append(B.Octets.take(i, o), B.Octets.concat([B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)])), BL.octets_concat_cons(B.Octets.take(i, o), [B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)])) : {ckp.ns(B.Octets.to_list(_)) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(B.Octets, B.Octets.concat(Con{B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), [B.Octets.drop(1n+i, o)]}), B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.concat([B.Octets.drop(1n+i, o)])), BL.octets_concat_cons(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), [B.Octets.drop(1n+i, o)])) : {ckp.ns(B.Octets.to_list(B.Octets.append(B.Octets.take(i, o), _))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(B.Octets, B.Octets.concat(Con{B.Octets.drop(1n+i, o), Nil{}}), B.Octets.append(B.Octets.drop(1n+i, o), B.Octets.concat(Nil{})), BL.octets_concat_cons(B.Octets.drop(1n+i, o), Nil{})) : {ckp.ns(B.Octets.to_list(B.Octets.append(B.Octets.take(i, o), B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), _)))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(B.Octets, B.Octets.concat(Nil{}), B.Octets.empty(), BL.octets_concat_nil()) : {ckp.ns(B.Octets.to_list(B.Octets.append(B.Octets.take(i, o), B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.append(B.Octets.drop(1n+i, o), _))))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.drop(1n+i, o), B.Octets.empty()), B.Octets.drop(1n+i, o), BL.octets_append_empty_r(B.Octets.drop(1n+i, o))) : {ckp.ns(B.Octets.to_list(B.Octets.append(B.Octets.take(i, o), B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), _)))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.take(i, o), B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)))), B.append(B.Octets.to_list(B.Octets.take(i, o)), B.Octets.to_list(B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)))), BL.octets_append_list(B.Octets.take(i, o), B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o)))) : {ckp.ns(_) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o))), B.append(B.Octets.to_list(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)])), B.Octets.to_list(B.Octets.drop(1n+i, o))), BL.octets_append_list(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)]), B.Octets.drop(1n+i, o))) : {ckp.ns(B.append(B.Octets.to_list(B.Octets.take(i, o)), _)) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([C.AcpiChecksum.byte_for(i, o)])), B.mask([C.AcpiChecksum.byte_for(i, o)]), BL.octets_to_of([C.AcpiChecksum.byte_for(i, o)])) : {ckp.ns(B.append(B.Octets.to_list(B.Octets.take(i, o)), B.append(_, B.Octets.to_list(B.Octets.drop(1n+i, o))))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(Nat, ckp.ns(B.append(B.Octets.to_list(B.Octets.take(i, o)), B.append(B.mask([C.AcpiChecksum.byte_for(i, o)]), B.Octets.to_list(B.Octets.drop(1n+i, o))))), Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), ckp.ns(B.append(B.mask([C.AcpiChecksum.byte_for(i, o)]), B.Octets.to_list(B.Octets.drop(1n+i, o))))), ckp.nsapp(B.Octets.to_list(B.Octets.take(i, o)), B.append(B.mask([C.AcpiChecksum.byte_for(i, o)]), B.Octets.to_list(B.Octets.drop(1n+i, o))))) : {_ == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  %Equal.sym(U32, U32.and(255, B.byte(U32.and(255, U32.sub(256, U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0)))))))), U32.and(255, U32.sub(256, U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0)))))), ckp.bb(U32.sub(256, U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))))) : {Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(_), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) == Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))) : Nat}
  {==}

# w = S - o_i and b = 256 - w, modulo 256

def ckp.e1g(+so: U32, +b: U32, +n: Nat, +ev: {U32.to_nat(so) == U.U32Nat.low(8n, n) : Nat}) -> {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.and(255, U32.sub(so, b))), U32.to_nat(b))) == U.U32Nat.low(8n, n) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.and(255, U32.sub(so, b))), U.U32Nat.low(8n, U32.to_nat(U32.sub(so, b))), ckp.am(U32.sub(so, b))) : {U.U32Nat.low(8n, Nat.add(_, U32.to_nat(b))) == U.U32Nat.low(8n, n) : Nat}
  %ckp.l1(U32.to_nat(U32.sub(so, b)), U32.to_nat(b)) : {_ == U.U32Nat.low(8n, n) : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(U32.sub(so, b)), U32.to_nat(b)), Nat.add(U32.to_nat(so), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(so, b)))), UL.u32_sub_wrap(so, b)) : {U.U32Nat.low(8n, _) == U.U32Nat.low(8n, n) : Nat}
  %Equal.sym(Nat, U.U32Nat.low(8n, Nat.add(U32.to_nat(so), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(so, b))))), U.U32Nat.low(8n, U32.to_nat(so)), ckp.l2(U32.to_nat(so), U.U32Nat.bit(U32.is_lt(so, b)))) : {_ == U.U32Nat.low(8n, n) : Nat}
  %Equal.sym(Nat, U32.to_nat(so), U.U32Nat.low(8n, n), ev) : {U.U32Nat.low(8n, _) == U.U32Nat.low(8n, n) : Nat}
  ckp.ll(n)

def ckp.e2g(+wu: U32) -> {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.and(255, U32.sub(256, wu))), U32.to_nat(wu))) == 0n : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.and(255, U32.sub(256, wu))), U.U32Nat.low(8n, U32.to_nat(U32.sub(256, wu))), ckp.am(U32.sub(256, wu))) : {U.U32Nat.low(8n, Nat.add(_, U32.to_nat(wu))) == 0n : Nat}
  %ckp.l1(U32.to_nat(U32.sub(256, wu)), U32.to_nat(wu)) : {_ == 0n : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(U32.sub(256, wu)), U32.to_nat(wu)), Nat.add(U32.to_nat(256), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(256, wu)))), UL.u32_sub_wrap(256, wu)) : {U.U32Nat.low(8n, _) == 0n : Nat}
  ckp.l2(U32.to_nat(256), U.U32Nat.bit(U32.is_lt(256, wu)))

def ckp.e1(+i: Nat, +o: B.Octets, +h: {Nat.is_lt(i, B.Octets.len(o)) == True{} : Bool}) -> {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))), U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))) == U.U32Nat.low(8n, Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o)))))) : Nat}:
  %ckp.split(i, o, h) : {U.U32Nat.low(8n, Nat.add(U32.to_nat(U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))), U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))) == U.U32Nat.low(8n, _) : Nat}
  ckp.e1g(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0)), ckp.ns(B.Octets.to_list(o)), ckp.sumv(o))

def ckp.fixzero(+i: Nat, +o: B.Octets, +h: {Nat.is_lt(i, B.Octets.len(o)) == True{} : Bool}) -> {U32.to_nat(C.AcpiChecksum.sum(C.AcpiChecksum.fix(i, o))) == 0n : Nat}:
  %Equal.sym(Nat, U32.to_nat(C.AcpiChecksum.sum(C.AcpiChecksum.fix(i, o))), U.U32Nat.low(8n, ckp.ns(B.Octets.to_list(C.AcpiChecksum.fix(i, o)))), ckp.sumv(C.AcpiChecksum.fix(i, o))) : {_ == 0n : Nat}
  %Equal.sym(Nat, ckp.ns(B.Octets.to_list(C.AcpiChecksum.fix(i, o))), Nat.add(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), Nat.add(U32.to_nat(C.AcpiChecksum.byte_for(i, o)), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))))), ckp.fixsum(i, o, h)) : {U.U32Nat.low(8n, _) == 0n : Nat}
  ckp.zero(ckp.ns(B.Octets.to_list(B.Octets.take(i, o))), ckp.ns(B.Octets.to_list(B.Octets.drop(1n+i, o))), U32.to_nat(U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))), U32.to_nat(C.AcpiChecksum.byte_for(i, o)), U32.to_nat(U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))), ckp.e1(i, o, h), ckp.e2g(U32.and(255, U32.sub(C.AcpiChecksum.sum(o), U32.and(255, Maybe.default(&2, U32, B.Octets.at(o, i), 0))))))

# The laws

def Laws.fix_ok(i, o, h):
  %Equal.sym(Bool, U32.is_eq(C.AcpiChecksum.sum(C.AcpiChecksum.fix(i, o)), 0), Nat.is_eq(U32.to_nat(C.AcpiChecksum.sum(C.AcpiChecksum.fix(i, o))), U32.to_nat(0)), UL.u32_eq_value(C.AcpiChecksum.sum(C.AcpiChecksum.fix(i, o)), 0)) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(C.AcpiChecksum.sum(C.AcpiChecksum.fix(i, o))), 0n, ckp.fixzero(i, o, h)) : {Nat.is_eq(_, U32.to_nat(0)) == True{} : Bool}
  {==}

def Laws.fix_example():
  {==}
