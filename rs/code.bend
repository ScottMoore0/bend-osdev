# bend-osdev-rs, the parameters of a Reed-Solomon code over GF(2^m), and its
# generator polynomial.
#
# A code is fixed by (W. A. Geisel, "Tutorial on Reed-Solomon Error
# Correction Coding", NASA TM-102162, 1990, section 3.3, table 3.3-1 and
# section 3.3.1):
#   * the field GF(2^m) and its field generator polynomial F(X), with the
#     primitive element alpha = X (bend-osdev-gf's GfmField; F must be
#     primitive);
#   * the code word generator's primitive element alpha^G (here alpha^prim,
#     the root spacing);
#   * the first consecutive root FCR;
#   * the number of parity-check symbols n - k = 2t (nroots).
# The generator is g(X) = (X + (alpha^G)^FCR) ... (X + (alpha^G)^(FCR+2t-1))
# (section 3.3.1). The block length is n = 2^m - 1; a codeword may be
# shortened (fewer message symbols, the leading ones taken as zero).
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./arith.bend as A

type RsCode is Data:
  RsCode{field: M.GfmField, fcr: U32, prim: U32, nroots: U32}

def Rs.code(f: M.GfmField, fcr: U32, prim: U32, nroots: U32) -> RsCode:
  RsCode{f, fcr, prim, nroots}

def Rs.field(c: RsCode) -> M.GfmField:
  match c:
    case RsCode{f, fcr, prim, nroots}:
      f

def Rs.fcr(c: RsCode) -> U32:
  match c:
    case RsCode{f, fcr, prim, nroots}:
      fcr

def Rs.prim(c: RsCode) -> U32:
  match c:
    case RsCode{f, fcr, prim, nroots}:
      prim

def Rs.nroots(c: RsCode) -> U32:
  match c:
    case RsCode{f, fcr, prim, nroots}:
      nroots

# the block length n = 2^m - 1
def Rs.n(c: RsCode) -> U32:
  M.Gfm.mask(Rs.field(c))

# the most message symbols, k = n - 2t
def Rs.k(+c: RsCode) -> U32:
  U32.sub(Rs.n(c), Rs.nroots(c))

# alpha^G = alpha^prim (alpha = x, so 2^prim), and its inverse
def Rs.beta(+c: RsCode) -> U32:
  A.RsGf.pow_nat(Rs.field(c), 2, U32.to_nat(Rs.prim(c)))

def Rs.beta_inv(+c: RsCode) -> U32:
  A.RsGf.inv(Rs.field(c), Rs.beta(c))

# the roots (alpha^G)^FCR .. (alpha^G)^(FCR + 2t - 1), each the one before
# times alpha^G
def rs.roots.go(n: Nat, +f: M.GfmField, +beta: U32, +r: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{r, rs.roots.go(k, f, beta, M.Gfm.mul(f, r, beta))}

def Rs.roots(+c: RsCode) -> List<&2, U32>:
  +f = Rs.field(c)
  +beta = Rs.beta(c)
  rs.roots.go(U32.to_nat(Rs.nroots(c)), f, beta, A.RsGf.pow_nat(f, beta, U32.to_nat(Rs.fcr(c))))

# g(X), lowest coefficient first (its leading coefficient is 1)
def Rs.generator(+c: RsCode) -> List<&2, U32>:
  P.RsPoly.from_roots(Rs.field(c), Rs.roots(c))

# Named codes

# x^8 + x^4 + x^3 + x^2 + 1 (0x11D)
def Rs.gf256() -> M.GfmField:
  M.GfmField{8n, 285}

# x^8 + x^7 + x^2 + x + 1 (0x187), CCSDS 131.0-B-5 section 4.3.3
def Rs.gf256_ccsds() -> M.GfmField:
  M.GfmField{8n, 391}

# RS(255,223): 32 parity symbols over 0x11D, FCR = 1, alpha^G = alpha
# (Geisel's choices, section 3.3.1)
def Rs.rs255_223() -> RsCode:
  RsCode{Rs.gf256(), 1, 1, 32}

# an 8-bit code with 16 parity symbols over 0x11D, FCR = 0, alpha^G = alpha
def Rs.rs8_p16() -> RsCode:
  RsCode{Rs.gf256(), 0, 1, 16}

# CCSDS 131.0-B-5 section 4.3: E = 16 (RS(255,223)), roots alpha^(11 j) for
# j = 128 - E .. 127 + E, in the conventional (not the dual-basis)
# representation
def Rs.ccsds() -> RsCode:
  RsCode{Rs.gf256_ccsds(), 112, 11, 32}

# CCSDS with E = 8 (RS(255,239))
def Rs.ccsds_e8() -> RsCode:
  RsCode{Rs.gf256_ccsds(), 120, 11, 16}

# Geisel's (15,9) example: GF(16) with X^4 + X + 1, FCR = 1, alpha^G = alpha
def Rs.geisel15_9() -> RsCode:
  RsCode{M.Gfm.gf16(), 1, 1, 6}

# Small codes, for exhaustive checks and proofs

# x^2 + x + 1 and x^3 + x + 1 (both primitive)
def Rs.gf4() -> M.GfmField:
  M.GfmField{2n, 7}

def Rs.gf8() -> M.GfmField:
  M.GfmField{3n, 11}

# GF(4), n = 3, 2 parity symbols (t = 1): Geisel's table 3.2-1, the
# smallest RS code
def Rs.small4() -> RsCode:
  RsCode{Rs.gf4(), 1, 1, 2}

# GF(8), n = 7, 4 parity symbols (t = 2)
def Rs.small8() -> RsCode:
  RsCode{Rs.gf8(), 1, 1, 4}
