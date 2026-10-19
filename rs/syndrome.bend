# bend-osdev-rs, syndromes: S_i = R((alpha^G)^i) for i = FCR .. FCR + 2t - 1
# (Geisel, NASA TM-102162, section 4.2.1), each by Horner's rule over the
# received word, highest power first. A codeword's syndromes are all zero.
import Base
import ../gf/gfm.bend as M
import ./code.bend as C

# R(x), for the word w highest power first
def rs.syn.one(w: List<&2, U32>, +f: M.GfmField, +x: U32, acc: U32) -> U32:
  match w:
    case Nil{}:
      acc
    case Con{s, t}:
      rs.syn.one(t, f, x, M.Gfm.add(f, M.Gfm.mul(f, acc, x), s))

# the word, read as a polynomial highest power first, at x
def Rs.eval_word(+f: M.GfmField, w: List<&2, U32>, +x: U32) -> U32:
  rs.syn.one(w, f, x, 0)

def rs.syn.all(rts: List<&2, U32>, +f: M.GfmField, +w: List<&2, U32>) -> List<&2, U32>:
  match rts:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{Rs.eval_word(f, w, r), rs.syn.all(t, f, w)}

# S_FCR .. S_(FCR+2t-1)
def Rs.syndromes(+c: C.RsCode, +w: List<&2, U32>) -> List<&2, U32>:
  rs.syn.all(C.Rs.roots(c), C.Rs.field(c), w)
