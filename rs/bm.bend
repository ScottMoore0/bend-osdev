# bend-osdev-rs, the Berlekamp-Massey algorithm: the shortest linear
# feedback shift register that generates a finite sequence, from J. L.
# Massey, "Shift-Register Synthesis and BCH Decoding", IEEE Transactions on
# Information Theory, vol. IT-15, no. 1, January 1969, pp. 122-127,
# section III, the LFSR synthesis algorithm (steps 1 to 6):
#
#   1) C(D) = 1, B(D) = 1, x = 1, L = 0, b = 1, N = 0
#   2) if N = n stop; else d = s_N + sum (i = 1 .. L) c_i s_(N-i)
#   3) if d = 0: x = x + 1
#   4) if d != 0 and 2L > N: C(D) = C(D) - d b^-1 D^x B(D); x = x + 1
#   5) if d != 0 and 2L <= N: T(D) = C(D); C(D) = C(D) - d b^-1 D^x B(D);
#      L = N + 1 - L; B(D) = T(D); b = d; x = 1
#   6) N = N + 1, back to 2
#
# over GF(2^m), where subtraction is addition. For BCH and Reed-Solomon
# decoding (Massey, section V) the sequence is the syndromes S_m0,
# S_(m0+1), ...; when the error weight is at most t, C(D) is the error
# locator polynomial prod (1 - X_i D), whose roots are the inverses of the
# error locators (equation 27, Theorem 5 and its corollary).
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./arith.bend as A

# The register: C(D) lowest coefficient first, and its length L
type RsLfsr is Data:
  RsLfsr{conn: List<&2, U32>, len: Nat}

def RsLfsr.conn(r: RsLfsr) -> List<&2, U32>:
  match r:
    case RsLfsr{c, l}:
      c

def RsLfsr.len(r: RsLfsr) -> Nat:
  match r:
    case RsLfsr{c, l}:
      l

# The algorithm's state: C, B, L, x, b, N, and the digits so far, newest
# first (s_(N-1), s_(N-2), ...)
type RsBmState is Data:
  RsBmState{c: List<&2, U32>, b: List<&2, U32>, l: Nat, x: Nat, bd: U32, n: Nat, hist: List<&2, U32>}

def rsbm.tail(p: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      t

# sum c_i s_(N-i), with cs = c_1, c_2, ... and hist = s_(N-1), s_(N-2), ...
def rsbm.dot(+f: M.GfmField, cs: List<&2, U32>, hist: List<&2, U32>) -> U32:
  match cs hist:
    case Con{c, ct} Con{h, ht}:
      M.Gfm.add(f, M.Gfm.mul(f, c, h), rsbm.dot(f, ct, ht))
    case _ _:
      0

# C(D) - d b^-1 D^x B(D)
def rsbm.upd(+f: M.GfmField, c: List<&2, U32>, +b: List<&2, U32>, +x: Nat, +d: U32, +bd: U32) -> List<&2, U32>:
  P.RsPoly.add(f, c, P.RsPoly.scale(f, A.RsGf.div(f, d, bd), P.RsPoly.shift(x, b)))

# steps 4 and 5 (d != 0)
def rsbm.nonzero(grow: Bool, +f: M.GfmField, st: RsBmState, +d: U32, +s: U32) -> RsBmState:
  match grow:
    case True{}:
      match st:
        case RsBmState{+c, +b, +l, +x, +bd, +n, hist}:
          RsBmState{rsbm.upd(f, c, b, x, d, bd), c, Nat.sub(1n+n, l), 1n, d, 1n+n, Con{s, hist}}
    case False{}:
      match st:
        case RsBmState{+c, +b, +l, +x, +bd, +n, hist}:
          RsBmState{rsbm.upd(f, c, b, x, d, bd), b, l, 1n+x, bd, 1n+n, Con{s, hist}}

# step 3 (d = 0), or on to steps 4 and 5
def rsbm.after(zero: Bool, +f: M.GfmField, st: RsBmState, +d: U32, +s: U32) -> RsBmState:
  match zero:
    case True{}:
      match st:
        case RsBmState{c, b, l, x, bd, n, hist}:
          RsBmState{c, b, l, 1n+x, bd, 1n+n, Con{s, hist}}
    case False{}:
      match st:
        case RsBmState{c, b, +l, x, bd, +n, hist}:
          rsbm.nonzero(Nat.is_le(Nat.add(l, l), n), f, RsBmState{c, b, l, x, bd, n, hist}, d, s)

# one digit s_N: step 2's discrepancy, then 3, 4 or 5, and 6
def rsbm.step(+f: M.GfmField, st: RsBmState, +s: U32) -> RsBmState:
  match st:
    case RsBmState{+c, b, l, x, bd, n, +hist}:
      +d = M.Gfm.add(f, s, rsbm.dot(f, rsbm.tail(c), hist))
      rsbm.after(U32.is_eq(d, 0), f, RsBmState{c, b, l, x, bd, n, hist}, d, s)

def rsbm.run(seq: List<&2, U32>, +f: M.GfmField, st: RsBmState) -> RsBmState:
  match seq:
    case Nil{}:
      st
    case Con{s, t}:
      rsbm.run(t, f, rsbm.step(f, st, s))

def rsbm.fin(+f: M.GfmField, st: RsBmState) -> RsLfsr:
  match st:
    case RsBmState{c, b, l, x, bd, n, hist}:
      RsLfsr{P.RsPoly.norm(f, c), l}

# step 1, then the digits of seq in order: the shortest LFSR generating
# seq (C(D) with trailing zero coefficients removed)
def RsBm.lfsr(+f: M.GfmField, seq: List<&2, U32>) -> RsLfsr:
  rsbm.fin(f, rsbm.run(seq, f, RsBmState{[1], [1], 0n, 1n, 1, 0n, Nil{}}))
