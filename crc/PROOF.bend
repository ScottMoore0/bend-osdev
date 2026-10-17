import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./crc.bend as C
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# Each engine folds the bytes one at a time, so running it over a ++ b is
# running it over a, then over b from where it stopped: induction on a.

def r32_split(xs: List<&2, U32>, +poly: U32, c: U32, ys: List<&2, U32>) -> {C.r32.raw(B.append(xs, ys), poly, c) == C.r32.raw(ys, poly, C.r32.raw(xs, poly, c)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      r32_split(t, poly, C.r32.bits(8n, poly, U32.xor(c, U32.and(h, 255))), ys)

def n32_split(xs: List<&2, U32>, +poly: U32, +shift: Nat, +topbit: U32, +mask: U32, c: U32, ys: List<&2, U32>) -> {C.n32.raw(B.append(xs, ys), poly, shift, topbit, mask, c) == C.n32.raw(ys, poly, shift, topbit, mask, C.n32.raw(xs, poly, shift, topbit, mask, c)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      n32_split(t, poly, shift, topbit, mask, C.n32.bits(8n, poly, topbit, mask, U32.xor(c, U32.shln(U32.and(h, 255), shift))), ys)

def r64_split(xs: List<&2, U32>, +poly: W.W64, c: W.W64, ys: List<&2, U32>) -> {C.r64.raw(B.append(xs, ys), poly, c) == C.r64.raw(ys, poly, C.r64.raw(xs, poly, c)) : W.W64}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      r64_split(t, poly, C.r64.bits(8n, poly, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))), ys)

def n64_split(xs: List<&2, U32>, +poly: W.W64, c: W.W64, ys: List<&2, U32>) -> {C.n64.raw(B.append(xs, ys), poly, c) == C.n64.raw(ys, poly, C.n64.raw(xs, poly, c)) : W.W64}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      n64_split(t, poly, C.n64.bits(8n, poly, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))), ys)

# The law over Octets follows from the engines' list lemmas through bytes'
# interface law octets_append_list, never through how Octets stores bytes.
def Laws.streaming32(spec, c, a, b):
  match spec:
    case C.Crc32Spec{+width, +poly, init, reflected, xorout}:
      match reflected:
        case True{}:
          %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {C.r32.raw(_, C.reflect32(poly, width), c) == C.r32.raw(B.Octets.to_list(b), C.reflect32(poly, width), C.r32.raw(B.Octets.to_list(a), C.reflect32(poly, width), c)) : U32}
          r32_split(B.Octets.to_list(a), C.reflect32(poly, width), c, B.Octets.to_list(b))
        case False{}:
          %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {C.n32.raw(_, poly, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c) == C.n32.raw(B.Octets.to_list(b), poly, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), C.n32.raw(B.Octets.to_list(a), poly, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c)) : U32}
          n32_split(B.Octets.to_list(a), poly, Nat.sub(width, 8n), U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c, B.Octets.to_list(b))

def Laws.streaming64(spec, c, a, b):
  match spec:
    case C.Crc64Spec{+poly, init, reflected, xorout}:
      match reflected:
        case True{}:
          %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {C.r64.raw(_, C.reflect64(poly), c) == C.r64.raw(B.Octets.to_list(b), C.reflect64(poly), C.r64.raw(B.Octets.to_list(a), C.reflect64(poly), c)) : W.W64}
          r64_split(B.Octets.to_list(a), C.reflect64(poly), c, B.Octets.to_list(b))
        case False{}:
          %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {C.n64.raw(_, poly, c) == C.n64.raw(B.Octets.to_list(b), poly, C.n64.raw(B.Octets.to_list(a), poly, c)) : W.W64}
          n64_split(B.Octets.to_list(a), poly, c, B.Octets.to_list(b))

def Laws.check_crc32c():
  {==}

def Laws.check_crc32():
  {==}

def Laws.check_crc16():
  {==}

def Laws.check_crc_t10dif():
  {==}

def Laws.check_crc64_ecma():
  {==}

def Laws.check_crc64_xz():
  {==}

def Laws.check_crc64_nvme():
  {==}

def Laws.empty_crc32c():
  {==}

def Laws.empty_crc_t10dif():
  {==}
