# bend-osdev-rs, systematic encoding: the parity-check symbols are
# CK(X) = X^(n-k) M(X) mod g(X), and the codeword is the message followed by
# them, C(X) = X^(n-k) M(X) + CK(X) (Geisel, NASA TM-102162, section 3.1,
# table 3.1-1, and the shift-register divider of appendix A).
#
# Words are lists of symbols, highest power first, as transmitted: the
# message M_(k-1) .. M_0, then CK_(n-k-1) .. CK_0. A message shorter than k
# symbols gives a shortened codeword (the missing leading symbols are
# zero and not sent).
#
# The remainder is kept in a register of 2t symbols, highest first. For
# each message symbol m, from the first: the feedback is m + r_(2t-1); the
# register shifts up one place and adds the feedback times the generator's
# coefficients g_(2t-1) .. g_0.
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./code.bend as C

type RsError is Data:
  RsBadLength{len: Nat}
  RsTooManyErasures{count: Nat}
  RsBadErasure{index: Nat}
  RsUncorrectable{}

# every symbol read modulo 2^m
def Rs.mask(+c: C.RsCode, w: List<&2, U32>) -> List<&2, U32>:
  match w:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{M.Gfm.elt(C.Rs.field(c), s), Rs.mask(c, t)}

# the generator's coefficients below the leading 1, highest first
def Rs.gen_desc(+c: C.RsCode) -> List<&2, U32>:
  List.reverse(&2, U32, List.take(&2, U32, C.Rs.generator(c), U32.to_nat(C.Rs.nroots(c))))

def rs.enc.top(reg: List<&2, U32>) -> U32:
  match reg:
    case Nil{}:
      0
    case Con{r, t}:
      r

# the register shifted up one place, a zero coming in at the bottom
def rs.enc.up(reg: List<&2, U32>) -> List<&2, U32>:
  match reg:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      List.append(&2, U32, t, [0])

def rs.enc.step(+f: M.GfmField, +gd: List<&2, U32>, +reg: List<&2, U32>, m: U32) -> List<&2, U32>:
  P.RsPoly.add(f, rs.enc.up(reg), P.RsPoly.scale(f, M.Gfm.add(f, m, rs.enc.top(reg)), gd))

def rs.enc.run(msg: List<&2, U32>, +f: M.GfmField, +gd: List<&2, U32>, reg: List<&2, U32>) -> List<&2, U32>:
  match msg:
    case Nil{}:
      reg
    case Con{m, t}:
      rs.enc.run(t, f, gd, rs.enc.step(f, gd, reg, m))

def rs.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{0, rs.zeros(k)}

# the 2t parity-check symbols of a message, highest first
def Rs.parity(+c: C.RsCode, msg: List<&2, U32>) -> List<&2, U32>:
  rs.enc.run(msg, C.Rs.field(c), Rs.gen_desc(c), rs.zeros(U32.to_nat(C.Rs.nroots(c))))

# the message (each symbol read modulo 2^m) followed by its parity
def Rs.codeword(+c: C.RsCode, +msg: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Rs.mask(c, msg), Rs.parity(c, msg))

def rs.enc.pick(ok: Bool, +c: C.RsCode, +msg: List<&2, U32>) -> Result<&2, &2, RsError, List<&2, U32>>:
  match ok:
    case True{}:
      Done{Rs.codeword(c, msg)}
    case False{}:
      Fail{RsBadLength{List.length(&2, U32, msg)}}

# the codeword of a message of at most k symbols (else RsBadLength)
def Rs.encode(+c: C.RsCode, +msg: List<&2, U32>) -> Result<&2, &2, RsError, List<&2, U32>>:
  rs.enc.pick(Nat.is_le(List.length(&2, U32, msg), U32.to_nat(C.Rs.k(c))), c, msg)
