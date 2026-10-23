# bend-osdev-siphash: proofs of LAWS.bend.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./siphash.bend as S
import ./halfsiphash.bend as H
import ./LAWS.bend as Laws

# The byte loop over a joined list is the loop over the first part, then the
# second

def sip_go_append(xs: List<&2, U32>, +ys: List<&2, U32>, s: S.SipState) -> {S.sip.go(B.append(xs, ys), s) == S.sip.go(ys, S.sip.go(xs, s)) : S.SipState}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      sip_go_append(t, ys, S.sip.step(s, h))

def hsip_go_append(xs: List<&2, U32>, +ys: List<&2, U32>, s: H.HsipState) -> {H.hsip.go(B.append(xs, ys), s) == H.hsip.go(ys, H.hsip.go(xs, s)) : H.HsipState}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      hsip_go_append(t, ys, H.hsip.step(s, h))

# Output lengths: the bytes of two words, and of four

def le32_len(a: U32) -> {B.Octets.len(B.Octets.le32(a)) == 4n : Nat}:
  match a:
    case U32{w}:
      {==}

def le32x2_len(a: U32, b: U32) -> {B.Octets.len(B.Octets.append(B.Octets.le32(a), B.Octets.le32(b))) == 8n : Nat}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          {==}

def le64_halves_len(a: U32, b: U32) -> {B.Octets.len(B.Octets.of_list(B.append(B.le32(a), B.le32(b)))) == 8n : Nat}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          {==}

def le64_len(+v: W.W64) -> {B.Octets.len(B.Octets.le64(v)) == 8n : Nat}:
  le64_halves_len(W.W64.lo(v), W.W64.hi(v))

def le64x2_halves_len(a: U32, b: U32, c: U32, d: U32) -> {B.Octets.len(B.Octets.append(B.Octets.of_list(B.append(B.le32(a), B.le32(b))), B.Octets.of_list(B.append(B.le32(c), B.le32(d))))) == 16n : Nat}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          match c:
            case U32{z}:
              match d:
                case U32{u}:
                  {==}

def le64x2_len(+v: W.W64, +w: W.W64) -> {B.Octets.len(B.Octets.append(B.Octets.le64(v), B.Octets.le64(w))) == 16n : Nat}:
  le64x2_halves_len(W.W64.lo(v), W.W64.hi(v), W.W64.lo(w), W.W64.hi(w))

def sip_fin_len(c: Nat, wide: Bool, +d: Nat, s: S.SipV) -> {B.Octets.len(S.sip.fin(wide, d, s)) == S.SipParams.out_len(S.SipParams{c, d, wide}) : Nat}:
  match wide:
    case False{}:
      le64_len(S.sip.out(S.sip.rounds(d, S.sip.xor2(255, s))))
    case True{}:
      +t = S.sip.rounds(d, S.sip.xor2(238, s))
      le64x2_len(S.sip.out(t), S.sip.out(S.sip.rounds(d, S.sip.xor1(221, t))))

def hsip_fin_len(c: Nat, wide: Bool, +d: Nat, s: H.HsipV) -> {B.Octets.len(H.hsip.fin(wide, d, s)) == H.HalfSipParams.out_len(S.SipParams{c, d, wide}) : Nat}:
  match wide:
    case False{}:
      le32_len(H.hsip.out(H.hsip.rounds(d, H.hsip.xor2(255, s))))
    case True{}:
      +t = H.hsip.rounds(d, H.hsip.xor2(238, s))
      le32x2_len(H.hsip.out(t), H.hsip.out(H.hsip.rounds(d, H.hsip.xor1(221, t))))

# SipHash

def Laws.siphash_streaming(s, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {S.sip.go(_, s) == S.SipHash.update(S.SipHash.update(s, a), b) : S.SipState}
  sip_go_append(B.Octets.to_list(a), B.Octets.to_list(b), s)

def Laws.siphash_update_empty(s):
  {==}

def Laws.siphash_split(prm, k, a, b):
  %Laws.siphash_streaming(S.SipHash.start(prm, k), a, b) : {S.SipHash.finish(_) == S.SipHash.hash(prm, k, B.Octets.append(a, b)) : B.Octets}
  {==}

def Laws.siphash_length(s):
  match s:
    case S.SipState{prm, v, lo, hi, k, n}:
      match prm:
        case S.SipParams{c, d, wide}:
          sip_fin_len(c, wide, d, S.sip.compress(c, v, W.W64.from_parts(U32.or(hi, U32.shln(U32.and(255, n), 24n)), lo)))

# HalfSipHash

def Laws.halfsiphash_streaming(s, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {H.hsip.go(_, s) == H.HalfSipHash.update(H.HalfSipHash.update(s, a), b) : H.HsipState}
  hsip_go_append(B.Octets.to_list(a), B.Octets.to_list(b), s)

def Laws.halfsiphash_update_empty(s):
  {==}

def Laws.halfsiphash_split(prm, k, a, b):
  %Laws.halfsiphash_streaming(H.HalfSipHash.start(prm, k), a, b) : {H.HalfSipHash.finish(_) == H.HalfSipHash.hash(prm, k, B.Octets.append(a, b)) : B.Octets}
  {==}

def Laws.halfsiphash_length(s):
  match s:
    case H.HsipState{prm, v, m, k, n}:
      match prm:
        case S.SipParams{c, d, wide}:
          hsip_fin_len(c, wide, d, H.hsip.compress(c, v, U32.or(m, U32.shln(U32.and(255, n), 24n))))

# Vectors

def Laws.siphash_key_paper():
  {==}

def Laws.siphash24_paper():
  {==}

def Laws.siphash24_vector_0():
  {==}

def Laws.siphash24_vector_8():
  {==}

def Laws.siphash24_wide_vector_15():
  {==}

def Laws.siphash13_openssl():
  {==}

def Laws.halfsiphash24_vector_0():
  {==}

def Laws.halfsiphash24_vector_7():
  {==}

def Laws.halfsiphash24_wide_vector_15():
  {==}

def Laws.siphash_key_15():
  {==}

def Laws.halfsiphash_key_16():
  {==}
