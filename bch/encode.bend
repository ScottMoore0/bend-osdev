# bend-osdev-bch, systematic encoding as polynomial division over GF(2):
# the parity bits are the remainder of D(X) X^deg(g) by g(X), and the
# codeword is the data bits followed by the parity bits (the same
# construction as Reed-Solomon's, Geisel, NASA TM-102162, section 3.1,
# here with coefficients in GF(2)).
#
# Bits are in order, highest power first. The remainder is a register of
# deg(g) bits, highest first: for each data bit, the feedback is the bit
# plus the register's top bit; the register shifts up one place and, if the
# feedback is 1, adds g's coefficients below its leading 1.
import Base
import ./code.bend as C

type BchError is Data:
  BchBadLength{len: Nat}
  BchUncorrectable{}

def bch.top(reg: List<&2, Bool>) -> Bool:
  match reg:
    case Nil{}:
      False{}
    case Con{r, t}:
      r

def bch.up(reg: List<&2, Bool>) -> List<&2, Bool>:
  match reg:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      List.append(&2, Bool, t, [False{}])

# a + (fb ? g : 0), bitwise
def bch.addif(+fb: Bool, a: List<&2, Bool>, g: List<&2, Bool>) -> List<&2, Bool>:
  match a g:
    case Con{x, s} Con{y, t}:
      Con{Bool.xor(x, Bool.and(fb, y)), bch.addif(fb, s, t)}
    case _ _:
      a

def bch.enc.step(+gd: List<&2, Bool>, +reg: List<&2, Bool>, b: Bool) -> List<&2, Bool>:
  bch.addif(Bool.xor(b, bch.top(reg)), bch.up(reg), gd)

def bch.enc.run(bits: List<&2, Bool>, +gd: List<&2, Bool>, reg: List<&2, Bool>) -> List<&2, Bool>:
  match bits:
    case Nil{}:
      reg
    case Con{b, t}:
      bch.enc.run(t, gd, bch.enc.step(gd, reg, b))

def bch.falses(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{False{}, bch.falses(k)}

# g's coefficients below the leading 1, highest first
def Bch.gen_desc(+c: C.BchCode) -> List<&2, Bool>:
  List.reverse(&2, Bool, List.take(&2, Bool, C.Bch.generator(c), C.Bch.parity_bits(c)))

# the parity bits of the data bits
def Bch.parity(+c: C.BchCode, bits: List<&2, Bool>) -> List<&2, Bool>:
  bch.enc.run(bits, Bch.gen_desc(c), bch.falses(C.Bch.parity_bits(c)))

# the data bits followed by their parity bits
def Bch.codeword(+c: C.BchCode, +bits: List<&2, Bool>) -> List<&2, Bool>:
  List.append(&2, Bool, bits, Bch.parity(c, bits))

def bch.enc.pick(ok: Bool, +c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, BchError, List<&2, Bool>>:
  match ok:
    case True{}:
      Done{Bch.codeword(c, bits)}
    case False{}:
      Fail{BchBadLength{List.length(&2, Bool, bits)}}

# the codeword of at most n - deg(g) data bits (else BchBadLength)
def Bch.encode_bits(+c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, BchError, List<&2, Bool>>:
  bch.enc.pick(Nat.is_le(Nat.add(List.length(&2, Bool, bits), C.Bch.parity_bits(c)), U32.to_nat(C.Bch.n(c))), c, bits)
