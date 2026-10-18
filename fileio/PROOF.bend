import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./off.bend as O
import ./LAWS.bend as Laws

# halves and join are a tuple and its match, so after they unfold only
# word64's interface laws are needed (never the inside of W64)

def Laws.off_join_halves(v):
  WL.parts_of(v)

def Laws.off_halves_join(h, l):
  %WL.hi_from_parts(h, l) : {O.FileIO.off.halves(O.FileIO.off.join((h, l))) == (_, l) : U32 & U32}
  %WL.lo_from_parts(h, l) : {O.FileIO.off.halves(O.FileIO.off.join((h, l))) == (W.W64.hi(W.W64.from_parts(h, l)), _) : U32 & U32}
  {==}

def Laws.off_of_u32(o):
  Laws.off_halves_join(0, o)

def Laws.off_fits32_of_u32(o):
  %Equal.sym(U32, W.W64.hi(W.W64.from_parts(0, o)), 0, WL.hi_from_parts(0, o)) : {U32.is_eq(_, 0) == True{} : Bool}
  {==}

def Laws.off_halves_carry():
  {==}

def Laws.off_halves_max():
  {==}

def Laws.off_fits32_past():
  {==}
