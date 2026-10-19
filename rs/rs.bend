# bend-osdev-rs, decoding with errors and erasures, after Geisel (NASA
# TM-102162), chapter 4 (five stages) and chapter 5 (symbol erasure):
#
#   1. the syndromes S_i of the received word (syndrome.bend);
#   2. with e erasures at known positions, the erasure locator
#      Gamma(X) = prod (1 + X_j X), and the modified syndromes, the
#      coefficients e .. 2t - 1 of S(X) Gamma(X) (Geisel, section 5.3.3:
#      S''_i = sum_j sigma''_j S_(i-j));
#   3. the error locator Lambda(X) from the modified syndromes by the
#      Berlekamp-Massey algorithm (bm.bend), refused unless 2L + e <= 2t;
#   4. the locations: the roots of Psi(X) = Lambda(X) Gamma(X) among the
#      word's positions, by the Chien search (chien.bend), refused unless
#      Psi has as many as its degree;
#   5. the values, by Forney's formula with Omega(X) = S(X) Psi(X) mod X^2t
#      (forney.bend), and the corrected word C(X)' = R(X) + E(X)'
#      (section 4.6).
#
# Words are lists of symbols, highest power first, as transmitted; a word
# may be shortened (its length npos is at most n, and more than 2t). The
# last symbol is position 0, the first position npos - 1. Erasures are
# given as indexes into the word (0 the first symbol). Symbols are read
# modulo 2^m. The corrections depend only on the syndromes and the
# erasures (Rs.plan), so the corrected word is the received word plus a
# function of its syndromes.
#
# A policy (RsOpts): whether to check that the corrected word's syndromes
# are zero before answering (the default; Geisel's optional sixth stage,
# chapter 4).
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./arith.bend as A
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as Sy
import ./bm.bend as Bm
import ./chien.bend as Ch
import ./forney.bend as Fo

# A correction: add value to the symbol at position pos (a power of X)
type RsFix is Data:
  RsFix{pos: U32, value: U32}

# A corrected word and how many symbols were corrected
type RsFixed is Data:
  RsFixed{word: List<&2, U32>, count: Nat}

type RsOpts is Data:
  RsOpts{verify: Bool}

# the default policy: check the corrected word's syndromes
def Rs.opts() -> RsOpts:
  RsOpts{True{}}

# Stage 2 to 5: the corrections for the syndromes synd, the erasures at
# positions eras (powers of X) and a word of npos symbols

def rs.dec.locs(+f: M.GfmField, +beta: U32, ps: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{A.RsGf.pow_nat(f, beta, U32.to_nat(p)), rs.dec.locs(f, beta, t)}

def rs.dec.vcons(+p: U32, v: Maybe<&2, U32>, rest: Maybe<&2, List<&2, RsFix>>) -> Maybe<&2, List<&2, RsFix>>:
  match v rest:
    case Some{y} Some{r}:
      Some{Con{RsFix{p, y}, r}}
    case _ _:
      None{}

def rs.dec.values(ps: List<&2, U32>, +f: M.GfmField, +omega: List<&2, U32>, +dpsi: List<&2, U32>, +fcr: U32, +beta: U32, +binv: U32) -> Maybe<&2, List<&2, RsFix>>:
  match ps:
    case Nil{}:
      Some{Nil{}}
    case Con{+p, t}:
      rs.dec.vcons(p, Fo.RsForney.value(f, omega, dpsi, fcr, beta, binv, p), rs.dec.values(t, f, omega, dpsi, fcr, beta, binv))

def rs.dec.found(ok: Bool, vals: Maybe<&2, List<&2, RsFix>>) -> Result<&2, &2, E.RsError, List<&2, RsFix>>:
  match ok:
    case False{}:
      Fail{E.RsUncorrectable{}}
    case True{}:
      match vals:
        case None{}:
          Fail{E.RsUncorrectable{}}
        case Some{v}:
          Done{v}

# stages 4 and 5, once Lambda is accepted
def rs.dec.locate(+c: C.RsCode, +synd: List<&2, U32>, +psi: List<&2, U32>, +npos: U32) -> Result<&2, &2, E.RsError, List<&2, RsFix>>:
  +f = C.Rs.field(c)
  +ps = Ch.RsChien.roots(f, psi, C.Rs.beta_inv(c), npos)
  rs.dec.found(Nat.is_eq(List.length(&2, U32, ps), P.RsPoly.deg(psi)), rs.dec.values(ps, f, P.RsPoly.trunc(U32.to_nat(C.Rs.nroots(c)), P.RsPoly.mul(f, synd, psi)), P.RsPoly.deriv(psi), C.Rs.fcr(c), C.Rs.beta(c), C.Rs.beta_inv(c)))

def rs.dec.lam(ok: Bool, +c: C.RsCode, +synd: List<&2, U32>, +gamma: List<&2, U32>, +lam: List<&2, U32>, +npos: U32) -> Result<&2, &2, E.RsError, List<&2, RsFix>>:
  match ok:
    case False{}:
      Fail{E.RsUncorrectable{}}
    case True{}:
      rs.dec.locate(c, synd, P.RsPoly.norm(C.Rs.field(c), P.RsPoly.mul(C.Rs.field(c), lam, gamma)), npos)

def rs.dec.bm(+c: C.RsCode, +synd: List<&2, U32>, +gamma: List<&2, U32>, +ne: Nat, +npos: U32, lf: Bm.RsLfsr) -> Result<&2, &2, E.RsError, List<&2, RsFix>>:
  match lf:
    case Bm.RsLfsr{lam, +l}:
      rs.dec.lam(Nat.is_le(Nat.add(Nat.add(l, l), ne), U32.to_nat(C.Rs.nroots(c))), c, synd, gamma, lam, npos)

def rs.dec.plan(zero: Bool, +c: C.RsCode, +synd: List<&2, U32>, +eras: List<&2, U32>, +npos: U32) -> Result<&2, &2, E.RsError, List<&2, RsFix>>:
  match zero:
    case True{}:
      Done{Nil{}}
    case False{}:
      +f = C.Rs.field(c)
      +ne = List.length(&2, U32, eras)
      +gamma = P.RsPoly.locator(f, rs.dec.locs(f, C.Rs.beta(c), eras))
      rs.dec.bm(c, synd, gamma, ne, npos, Bm.RsBm.lfsr(f, List.drop(&2, U32, P.RsPoly.trunc(U32.to_nat(C.Rs.nroots(c)), P.RsPoly.mul(f, synd, gamma)), ne)))

# the corrections for these syndromes and erasures (positions, powers of X)
# in a word of npos symbols; none if the syndromes are all zero
def Rs.plan(+c: C.RsCode, +synd: List<&2, U32>, +eras: List<&2, U32>, +npos: U32) -> Result<&2, &2, E.RsError, List<&2, RsFix>>:
  rs.dec.plan(P.RsPoly.is_zero(C.Rs.field(c), synd), c, synd, eras, npos)

# Applying corrections

def rs.fix.one(w: List<&2, U32>, i: Nat, +f: M.GfmField, +v: U32) -> List<&2, U32>:
  match w:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      match i:
        case 0n:
          Con{M.Gfm.add(f, s, v), t}
        case 1n+k:
          Con{s, rs.fix.one(t, k, f, v)}

def rs.fix.all(fs: List<&2, RsFix>, +f: M.GfmField, +npos: Nat, w: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      w
    case Con{x, t}:
      match x:
        case RsFix{p, v}:
          rs.fix.all(t, f, npos, rs.fix.one(w, Nat.sub(Nat.sub(npos, 1n), U32.to_nat(p)), f, v))

# the word with the corrections added
def Rs.apply(+c: C.RsCode, fs: List<&2, RsFix>, +w: List<&2, U32>) -> List<&2, U32>:
  rs.fix.all(fs, C.Rs.field(c), List.length(&2, U32, w), w)

# Checking the word and the erasures

def rs.memb(+i: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(Nat.is_eq(i, x), rs.memb(i, t))

def rs.eras.one(bad: Bool, +i: Nat, rest: Maybe<&2, E.RsError>) -> Maybe<&2, E.RsError>:
  match bad:
    case True{}:
      Some{E.RsBadErasure{i}}
    case False{}:
      rest

# each erasure inside the word, and none twice
def rs.eras.go(es: List<&2, Nat>, +npos: Nat, +seen: List<&2, Nat>) -> Maybe<&2, E.RsError>:
  match es:
    case Nil{}:
      None{}
    case Con{+i, t}:
      rs.eras.one(Bool.or(Bool.not(Nat.is_lt(i, npos)), rs.memb(i, seen)), i, rs.eras.go(t, npos, Con{i, seen}))

def rs.eras.count(over: Bool, +ne: Nat, rest: Maybe<&2, E.RsError>) -> Maybe<&2, E.RsError>:
  match over:
    case True{}:
      Some{E.RsTooManyErasures{ne}}
    case False{}:
      rest

def rs.len.ok(ok: Bool, +len: Nat, rest: Maybe<&2, E.RsError>) -> Maybe<&2, E.RsError>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{E.RsBadLength{len}}

# None if a word of len symbols with these erasures can be decoded, else why
def Rs.check(+c: C.RsCode, +len: Nat, +eras: List<&2, Nat>) -> Maybe<&2, E.RsError>:
  +nr = U32.to_nat(C.Rs.nroots(c))
  rs.len.ok(Bool.and(Nat.is_lt(nr, len), Nat.is_le(len, U32.to_nat(C.Rs.n(c)))), len, rs.eras.count(Nat.is_lt(nr, List.length(&2, Nat, eras)), List.length(&2, Nat, eras), rs.eras.go(eras, len, Nil{})))

# erasure indexes as positions (powers of X) in a word of npos symbols
def rs.eras.pos(es: List<&2, Nat>, +npos: Nat) -> List<&2, U32>:
  match es:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Con{U32.from_nat(Nat.sub(Nat.sub(npos, 1n), i)), rs.eras.pos(t, npos)}

# Correcting and decoding

def rs.cor.verify(ok: Bool, +w: List<&2, U32>, +count: Nat) -> Result<&2, &2, E.RsError, RsFixed>:
  match ok:
    case True{}:
      Done{RsFixed{w, count}}
    case False{}:
      Fail{E.RsUncorrectable{}}

def rs.cor.check(verify: Bool, +c: C.RsCode, +w: List<&2, U32>) -> Bool:
  match verify:
    case True{}:
      P.RsPoly.is_zero(C.Rs.field(c), Sy.Rs.syndromes(c, w))
    case False{}:
      True{}

def rs.cor.fin(r: Result<&2, &2, E.RsError, List<&2, RsFix>>, opts: RsOpts, +c: C.RsCode, +w: List<&2, U32>) -> Result<&2, &2, E.RsError, RsFixed>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+fs}:
      match opts:
        case RsOpts{verify}:
          +w2 = Rs.apply(c, fs, w)
          rs.cor.verify(rs.cor.check(verify, c, w2), w2, List.length(&2, RsFix, fs))

def rs.cor.go(err: Maybe<&2, E.RsError>, +opts: RsOpts, +c: C.RsCode, +w: List<&2, U32>, +eras: List<&2, Nat>) -> Result<&2, &2, E.RsError, RsFixed>:
  match err:
    case Some{e}:
      Fail{e}
    case None{}:
      rs.cor.fin(Rs.plan(c, Sy.Rs.syndromes(c, w), rs.eras.pos(eras, List.length(&2, U32, w)), U32.from_nat(List.length(&2, U32, w))), opts, c, w)

# the received word corrected, under a policy
def Rs.correct_with(+opts: RsOpts, +c: C.RsCode, +word: List<&2, U32>, +eras: List<&2, Nat>) -> Result<&2, &2, E.RsError, RsFixed>:
  rs.cor.go(Rs.check(c, List.length(&2, U32, word), eras), opts, c, E.Rs.mask(c, word), eras)

# the received word corrected (word: highest power first; eras: indexes of
# the symbols known to be unreliable)
def Rs.correct(+c: C.RsCode, +word: List<&2, U32>, +eras: List<&2, Nat>) -> Result<&2, &2, E.RsError, RsFixed>:
  Rs.correct_with(Rs.opts(), c, word, eras)

def rs.dec.msg(+c: C.RsCode, r: Result<&2, &2, E.RsError, RsFixed>) -> Result<&2, &2, E.RsError, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match x:
        case RsFixed{+w, count}:
          Done{List.take(&2, U32, w, Nat.sub(List.length(&2, U32, w), U32.to_nat(C.Rs.nroots(c))))}

# the message of a received word: the corrected word without its parity
def Rs.decode(+c: C.RsCode, +word: List<&2, U32>, +eras: List<&2, Nat>) -> Result<&2, &2, E.RsError, List<&2, U32>>:
  rs.dec.msg(c, Rs.correct(c, word, eras))

# a test helper: v added to the symbol at index i (0 the first symbol)
def Rs.inject(w: List<&2, U32>, i: Nat, +v: U32) -> List<&2, U32>:
  match w:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      match i:
        case 0n:
          Con{U32.xor(s, v), t}
        case 1n+k:
          Con{s, Rs.inject(t, k, v)}
