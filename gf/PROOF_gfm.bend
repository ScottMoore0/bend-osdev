# Proofs of LAWS_gfm.bend: Gfm.elt masks with the field's mask, and masking
# twice is masking once (bit by bit)
import Base
import ./gfm.bend as M
import ./LAWS_gfm.bend as Laws

def gfm_bool_and_idem(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(a, Bool.and(a, b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def gfm_word_and_idem(n: Nat, k: Word(n), a: Word(n)) -> {Word.and(n, k, a) == Word.and(n, k, Word.and(n, k, a)) : Word(n)}:
  match n:
    case 0n:
      match k a:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match k a:
        case WCon{kh, kt} WCon{ah, at}:
          %gfm_bool_and_idem(kh, ah) : {WCon{Bool.and(kh, ah), Word.and(p, kt, at)} == WCon{_, Word.and(p, kt, Word.and(p, kt, at))} : Word(1n+p)}
          %gfm_word_and_idem(p, kt, at) : {WCon{Bool.and(kh, ah), Word.and(p, kt, at)} == WCon{Bool.and(kh, ah), _} : Word(1n+p)}
          {==}

def gfm_u32_and_idem(k: U32, a: U32) -> {U32.and(k, a) == U32.and(k, U32.and(k, a)) : U32}:
  match k a:
    case U32{x} U32{y}:
      %gfm_word_and_idem(32n, x, y) : {U32{Word.and(32n, x, y)} == U32{_} : U32}
      {==}

def Laws.gfm_mul_elt(f, a, b):
  %gfm_u32_and_idem(M.Gfm.mask(f), a) : {M.gfm.mul.raw(f, _, M.Gfm.elt(f, b)) == M.Gfm.mul(f, a, b) : U32}
  {==}
