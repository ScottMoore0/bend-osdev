# Proofs of LAWS_bm.bend: Boyer-Moore finds exactly what the reference
# finds, whole and in chunks.
#
# Ignoring case is the exact search of the folded pattern in the folded
# text (bp.conv). In the exact search, each window's report is the
# reference's test at that offset (bp.hit_ok: the window's trailing match
# count, bp.cmr, is the whole pattern exactly when the pattern is there),
# and no offset the step skips holds the pattern (bp.safe):
#
# * Horspool's shift h: the window's last byte b does not occur in the
#   pattern at positions m - h to m - 2 (bp.hs_go), and a skipped offset
#   i puts pattern position m - 1 - i under b (bp.hsafe);
# * the good-suffix shift g after a mismatch at j: every s below g fails
#   its definition (bp.least_nok), and an occurrence at offset s would
#   make it hold, since the pattern there agrees with the matched suffix
#   and puts the window's byte j, which is not pattern byte j, under j
#   (bp.okw, bp.gsafe_mis);
# * after a match, every s below the shift is not a period (bp.per_nok),
#   and an occurrence at s would make it one (bp.gsafe_full);
# * the default rule's shift is the larger of the two, so each offset
#   below it is below one of them.
#
# So the scan reports what the reference reports (bp.main). Between
# chunks the search keeps the last m - 1 bytes: the reference over a
# chunk's bytes, then the rest of the text, is its matches in them, then
# those starting in the kept bytes or later (bp.ns), so the chunked
# search reports what the reference reports in the whole text (bp.rg).
import Base
import ./textsearch.bend as T
import ./bm.bend as M
import ./naive.bend as V
import ./proof_lib.bend as L
import ./LAWS_bm.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# Lists of bytes

def bp.app_assoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %bp.app_assoc(t, ys, zs) : {Con{h, List.append(&2, U32, List.append(&2, U32, t, ys), zs)} == Con{h, _} : List<&2, U32>}
      {==}

def bp.rev_go(xs: List<&2, U32>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, xs, acc) == List.append(&2, U32, List.reverse.go(&2, U32, xs, Nil{}), acc) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +A = List.reverse.go(&2, U32, t, Nil{})
      %Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, t, Con{x, acc}), List.append(&2, U32, A, Con{x, acc}), bp.rev_go(t, Con{x, acc})) : {_ == List.append(&2, U32, List.reverse.go(&2, U32, t, [x]), acc) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, t, [x]), List.append(&2, U32, A, [x]), bp.rev_go(t, [x])) : {List.append(&2, U32, A, Con{x, acc}) == List.append(&2, U32, _, acc) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, A, [x]), acc), List.append(&2, U32, A, Con{x, acc}), bp.app_assoc(A, [x], acc)) : {List.append(&2, U32, A, Con{x, acc}) == _ : List<&2, U32>}
      {==}

# the reverse of x then xs: the reverse of xs, then x
def bp.rev_con(+x: U32, xs: List<&2, U32>) -> {List.reverse(&2, U32, Con{x, xs}) == List.append(&2, U32, List.reverse(&2, U32, xs), [x]) : List<&2, U32>}:
  bp.rev_go(xs, [x])

def bp.len_app1(xs: List<&2, U32>, +x: U32) -> {List.length(&2, U32, List.append(&2, U32, xs, [x])) == 1n+List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %bp.len_app1(t, x) : {1n+List.length(&2, U32, List.append(&2, U32, t, [x])) == 1n+_ : Nat}
      {==}

def bp.len_rev(xs: List<&2, U32>) -> {List.length(&2, U32, List.reverse(&2, U32, xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, U32>, List.reverse(&2, U32, Con{x, t}), List.append(&2, U32, List.reverse(&2, U32, t), [x]), bp.rev_con(x, t)) : {List.length(&2, U32, _) == 1n+List.length(&2, U32, t) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, List.reverse(&2, U32, t), [x])), 1n+List.length(&2, U32, List.reverse(&2, U32, t)), bp.len_app1(List.reverse(&2, U32, t), x)) : {_ == 1n+List.length(&2, U32, t) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, t)), List.length(&2, U32, t), bp.len_rev(t)) : {1n+_ == 1n+List.length(&2, U32, t) : Nat}
      {==}

# The window's trailing match count

# k matches below a length-L tail: then L + 1 with a matching first byte,
# else L; fewer than L: k
def bp.ck(e1: Bool, e2: Bool, +l: Nat, k: Nat) -> Nat:
  match e1:
    case True{}:
      M.ts.bm.pick(e2, 1n+l, l)
    case False{}:
      k

# how many of the last bytes of p and w agree (for lists of one length),
# counted from the front
def bp.cmr(p: List<&2, U32>, w: List<&2, U32>) -> Nat:
  match p w:
    case Con{+a, +pt} Con{+b, +wt}:
      +k = bp.cmr(pt, wt)
      bp.ck(Nat.is_eq(k, List.length(&2, U32, pt)), U32.is_eq(a, b), List.length(&2, U32, pt), k)
    case _ _:
      0n

def bp.pk1(e: Bool) -> {M.ts.bm.pick(e, 1n, 0n) == bp.ck(True{}, e, 0n, 0n) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def bp.ck_succ(e1: Bool, e2: Bool, +l: Nat, +k: Nat) -> {1n+bp.ck(e1, e2, l, k) == bp.ck(e1, e2, 1n+l, 1n+k) : Nat}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def bp.snoc_x(e: Bool, +c1: Nat, +l: Nat, +e2: Bool) -> {M.ts.bm.pick(e, 1n+bp.ck(Nat.is_eq(c1, l), e2, l, c1), 0n) == bp.ck(Nat.is_eq(M.ts.bm.pick(e, 1n+c1, 0n), 1n+l), e2, 1n+l, M.ts.bm.pick(e, 1n+c1, 0n)) : Nat}:
  match e:
    case True{}:
      bp.ck_succ(Nat.is_eq(c1, l), e2, l, c1)
    case False{}:
      {==}

# the count on xs then a, ys then b: the count on xs, ys, one more if it
# was all of them and a is b
def bp.common_snoc(xs: List<&2, U32>, ys: List<&2, U32>, +a: U32, +b: U32, +h: {Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, ys)) == True{} : Bool}) -> {M.ts.bm.common(False{}, List.append(&2, U32, xs, [a]), List.append(&2, U32, ys, [b])) == bp.ck(Nat.is_eq(M.ts.bm.common(False{}, xs, ys), List.length(&2, U32, xs)), U32.is_eq(a, b), List.length(&2, U32, xs), M.ts.bm.common(False{}, xs, ys)) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      bp.pk1(U32.is_eq(a, b))
    case Nil{} Con{+y, +yt}:
      L.tsl.absurd(Nat, M.ts.bm.common(False{}, [a], Con{y, List.append(&2, U32, yt, [b])}), M.ts.bm.pick(U32.is_eq(a, b), 1n, 0n), h)
    case Con{+x, +xt} Nil{}:
      L.tsl.absurd(Nat, M.ts.bm.common(False{}, Con{x, List.append(&2, U32, xt, [a])}, [b]), 0n, h)
    case Con{+x, +xt} Con{+y, +yt}:
      +c1 = M.ts.bm.common(False{}, xt, yt)
      +l = List.length(&2, U32, xt)
      %Equal.sym(Nat, M.ts.bm.common(False{}, List.append(&2, U32, xt, [a]), List.append(&2, U32, yt, [b])), bp.ck(Nat.is_eq(c1, l), U32.is_eq(a, b), l, c1), bp.common_snoc(xt, yt, a, b, h)) : {M.ts.bm.pick(U32.is_eq(x, y), 1n+_, 0n) == bp.ck(Nat.is_eq(M.ts.bm.pick(U32.is_eq(x, y), 1n+c1, 0n), 1n+l), U32.is_eq(a, b), 1n+l, M.ts.bm.pick(U32.is_eq(x, y), 1n+c1, 0n)) : Nat}
      bp.snoc_x(U32.is_eq(x, y), c1, l, U32.is_eq(a, b))

def bp.hl(pt: List<&2, U32>, wt: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, pt), List.length(&2, U32, wt)) == True{} : Bool}) -> {Nat.is_eq(List.length(&2, U32, List.reverse(&2, U32, pt)), List.length(&2, U32, List.reverse(&2, U32, wt))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, pt)), List.length(&2, U32, pt), bp.len_rev(pt)) : {Nat.is_eq(_, List.length(&2, U32, List.reverse(&2, U32, wt))) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, wt)), List.length(&2, U32, wt), bp.len_rev(wt)) : {Nat.is_eq(List.length(&2, U32, pt), _) == True{} : Bool}
  h

# the code's count (from the ends, over the reversed lists) is bp.cmr
def bp.cr(p: List<&2, U32>, w: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, p), List.length(&2, U32, w)) == True{} : Bool}) -> {M.ts.bm.common(False{}, List.reverse(&2, U32, p), List.reverse(&2, U32, w)) == bp.cmr(p, w) : Nat}:
  match p w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +wt}:
      {==}
    case Con{+a, +pt} Nil{}:
      L.tsl.absurd(Nat, M.ts.bm.common(False{}, List.reverse(&2, U32, Con{a, pt}), Nil{}), 0n, h)
    case Con{+a, +pt} Con{+b, +wt}:
      +k = bp.cmr(pt, wt)
      +l = List.length(&2, U32, pt)
      +rp = List.reverse(&2, U32, pt)
      +rw = List.reverse(&2, U32, wt)
      %Equal.sym(List<&2, U32>, List.reverse(&2, U32, Con{a, pt}), List.append(&2, U32, rp, [a]), bp.rev_con(a, pt)) : {M.ts.bm.common(False{}, _, List.reverse(&2, U32, Con{b, wt})) == bp.ck(Nat.is_eq(k, l), U32.is_eq(a, b), l, k) : Nat}
      %Equal.sym(List<&2, U32>, List.reverse(&2, U32, Con{b, wt}), List.append(&2, U32, rw, [b]), bp.rev_con(b, wt)) : {M.ts.bm.common(False{}, List.append(&2, U32, rp, [a]), _) == bp.ck(Nat.is_eq(k, l), U32.is_eq(a, b), l, k) : Nat}
      %bp.cr(pt, wt, h) : {M.ts.bm.common(False{}, List.append(&2, U32, rp, [a]), List.append(&2, U32, rw, [b])) == bp.ck(Nat.is_eq(_, l), U32.is_eq(a, b), l, _) : Nat}
      %bp.len_rev(pt) : {M.ts.bm.common(False{}, List.append(&2, U32, rp, [a]), List.append(&2, U32, rw, [b])) == bp.ck(Nat.is_eq(M.ts.bm.common(False{}, rp, rw), _), U32.is_eq(a, b), _, M.ts.bm.common(False{}, rp, rw)) : Nat}
      bp.common_snoc(rp, rw, a, b, bp.hl(pt, wt, h))

def bp.ck_le(e1: Bool, e2: Bool, +l: Nat, +k: Nat, +ih: {Nat.is_lt(k, 1n+l) == True{} : Bool}) -> {Nat.is_lt(bp.ck(e1, e2, l, k), 2n+l) == True{} : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          L.tsl.lt_succ(l)
        case False{}:
          L.tsl.lt_weak(l, 1n+l, L.tsl.lt_succ(l))
    case False{}:
      L.tsl.lt_weak(k, 1n+l, ih)

def bp.cmr_le(p: List<&2, U32>, w: List<&2, U32>) -> {Nat.is_lt(bp.cmr(p, w), 1n+List.length(&2, U32, p)) == True{} : Bool}:
  match p w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +wt}:
      {==}
    case Con{+a, +pt} Nil{}:
      {==}
    case Con{+a, +pt} Con{+b, +wt}:
      bp.ck_le(Nat.is_eq(bp.cmr(pt, wt), List.length(&2, U32, pt)), U32.is_eq(a, b), List.length(&2, U32, pt), bp.cmr(pt, wt), bp.cmr_le(pt, wt))

def bp.cm_h(e1: Bool, e2: Bool, +l: Nat, +k: Nat, +h_le: {Nat.is_lt(k, 1n+l) == True{} : Bool}) -> {Nat.is_eq(bp.ck(e1, e2, l, k), 1n+l) == Bool.and(e2, e1) : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          L.tsl.nat_refl(l)
        case False{}:
          L.tsl.lt_ne(l, 1n+l, L.tsl.lt_succ(l))
    case False{}:
      match e2:
        case True{}:
          L.tsl.lt_ne(k, 1n+l, h_le)
        case False{}:
          L.tsl.lt_ne(k, 1n+l, h_le)

# the count is the whole pattern exactly when the pattern is there
def bp.cm(p: List<&2, U32>, w: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, p), List.length(&2, U32, w)) == True{} : Bool}) -> {Nat.is_eq(bp.cmr(p, w), List.length(&2, U32, p)) == V.ts.naive.at(False{}, p, w) : Bool}:
  match p w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +wt}:
      {==}
    case Con{+a, +pt} Nil{}:
      L.tsl.absurd(Bool, Nat.is_eq(0n, 1n+List.length(&2, U32, pt)), False{}, h)
    case Con{+a, +pt} Con{+b, +wt}:
      +k = bp.cmr(pt, wt)
      +l = List.length(&2, U32, pt)
      %bp.cm(pt, wt, h) : {Nat.is_eq(bp.ck(Nat.is_eq(k, l), U32.is_eq(a, b), l, k), 1n+l) == Bool.and(U32.is_eq(a, b), _) : Bool}
      bp.cm_h(Nat.is_eq(k, l), U32.is_eq(a, b), l, k, bp.cmr_le(pt, wt))

# whether p and w agree from position lo on (p no longer than w)
def bp.suf(p: List<&2, U32>, +w: List<&2, U32>, +lo: Nat) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{+a, +pt}:
      match w:
        case Nil{}:
          False{}
        case Con{+b, +wt}:
          match lo:
            case 0n:
              Bool.and(U32.is_eq(a, b), bp.suf(pt, wt, 0n))
            case 1n+l:
              bp.suf(pt, wt, l)

# ... so they agree at each position u >= lo
def bp.suf_at(p: List<&2, U32>, w: List<&2, U32>, lo: Nat, u: Nat, +h: {bp.suf(p, w, lo) == True{} : Bool}, +h1: {Nat.is_lt(u, lo) == False{} : Bool}, +h2: {Nat.is_lt(u, List.length(&2, U32, p)) == True{} : Bool}) -> {U32.is_eq(M.ts.bm.at(p, u), M.ts.bm.at(w, u)) == True{} : Bool}:
  match p:
    case Nil{}:
      L.tsl.lt_zero_abs(Bool, U32.is_eq(0, M.ts.bm.at(w, u)), True{}, u, h2)
    case Con{+a, +pt}:
      match w:
        case Nil{}:
          L.tsl.absurd(Bool, U32.is_eq(M.ts.bm.at(Con{a, pt}, u), 0), True{}, h)
        case Con{+b, +wt}:
          match lo:
            case 0n:
              match u:
                case 0n:
                  L.tsl.and_l(U32.is_eq(a, b), bp.suf(pt, wt, 0n), h)
                case 1n+ +v:
                  bp.suf_at(pt, wt, 0n, v, L.tsl.and_r(U32.is_eq(a, b), bp.suf(pt, wt, 0n), h), L.tsl.lt_zero(v), h2)
            case 1n+ +l:
              match u:
                case 0n:
                  L.tsl.absurd_tf(Bool, U32.is_eq(a, b), True{}, h1)
                case 1n+ +v:
                  bp.suf_at(pt, wt, l, v, h, h1, h2)

def bp.cf_ih0(+k: Nat, +l: Nat, +pt: List<&2, U32>, +wt: List<&2, U32>, +h_e1: {Nat.is_eq(k, l) == True{} : Bool}, +ih: {bp.suf(pt, wt, Nat.sub(l, k)) == True{} : Bool}) -> {bp.suf(pt, wt, 0n) == True{} : Bool}:
  +e0 = Equal.trans(Nat, Nat.sub(l, k), Nat.sub(l, l), 0n, Equal.cong(Nat, Nat, n => Nat.sub(l, n), k, l, L.tsl.nat_eq(k, l, h_e1)), L.tsl.sub_self(l))
  %e0 : {bp.suf(pt, wt, _) == True{} : Bool}
  ih

def bp.cf_h(e1: Bool, e2: Bool, +a: U32, +b: U32, +pt: List<&2, U32>, +wt: List<&2, U32>, +l: Nat, +k: Nat, +h_e1: {Nat.is_eq(k, l) == e1 : Bool}, +h_e2: {U32.is_eq(a, b) == e2 : Bool}, +h_le: {Nat.is_lt(k, 1n+l) == True{} : Bool}, +ih: {bp.suf(pt, wt, Nat.sub(l, k)) == True{} : Bool}) -> {bp.suf(Con{a, pt}, Con{b, wt}, Nat.sub(1n+l, bp.ck(e1, e2, l, k))) == True{} : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          %Equal.sym(Nat, Nat.sub(l, l), 0n, L.tsl.sub_self(l)) : {bp.suf(Con{a, pt}, Con{b, wt}, _) == True{} : Bool}
          %Equal.sym(Bool, U32.is_eq(a, b), True{}, h_e2) : {Bool.and(_, bp.suf(pt, wt, 0n)) == True{} : Bool}
          bp.cf_ih0(k, l, pt, wt, h_e1, ih)
        case False{}:
          %Equal.sym(Nat, Nat.sub(1n+l, l), 1n+Nat.sub(l, l), L.tsl.sub_succ_le(l, l, L.tsl.lt_succ(l))) : {bp.suf(Con{a, pt}, Con{b, wt}, _) == True{} : Bool}
          %Equal.sym(Nat, Nat.sub(l, l), 0n, L.tsl.sub_self(l)) : {bp.suf(Con{a, pt}, Con{b, wt}, 1n+_) == True{} : Bool}
          bp.cf_ih0(k, l, pt, wt, h_e1, ih)
    case False{}:
      %Equal.sym(Nat, Nat.sub(1n+l, k), 1n+Nat.sub(l, k), L.tsl.sub_succ_le(l, k, h_le)) : {bp.suf(Con{a, pt}, Con{b, wt}, _) == True{} : Bool}
      ih

# the window agrees with the pattern from length minus count on
def bp.cf_suf(p: List<&2, U32>, w: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, p), List.length(&2, U32, w)) == True{} : Bool}) -> {bp.suf(p, w, Nat.sub(List.length(&2, U32, p), bp.cmr(p, w))) == True{} : Bool}:
  match p w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +wt}:
      {==}
    case Con{+a, +pt} Nil{}:
      L.tsl.absurd(Bool, False{}, True{}, h)
    case Con{+a, +pt} Con{+b, +wt}:
      bp.cf_h(Nat.is_eq(bp.cmr(pt, wt), List.length(&2, U32, pt)), U32.is_eq(a, b), a, b, pt, wt, List.length(&2, U32, pt), bp.cmr(pt, wt), {==}, {==}, bp.cmr_le(pt, wt), bp.cf_suf(pt, wt, h))

def bp.mis_h(e1: Bool, e2: Bool, +a: U32, +b: U32, pt: List<&2, U32>, +wt: List<&2, U32>, +k: Nat, +h_e1: {Nat.is_eq(k, List.length(&2, U32, pt)) == e1 : Bool}, +h_e2: {U32.is_eq(a, b) == e2 : Bool}, +h_le: {Nat.is_lt(k, 1n+List.length(&2, U32, pt)) == True{} : Bool}, +hk: {k == bp.cmr(pt, wt) : Nat}, +hn: {Nat.is_eq(bp.ck(e1, e2, List.length(&2, U32, pt), k), 1n+List.length(&2, U32, pt)) == False{} : Bool}, rec: {Nat.is_eq(k, List.length(&2, U32, pt)) == False{} : Bool} -> {U32.is_eq(M.ts.bm.at(pt, Nat.sub(Nat.sub(List.length(&2, U32, pt), 1n), k)), M.ts.bm.at(wt, Nat.sub(Nat.sub(List.length(&2, U32, pt), 1n), k))) == False{} : Bool}) -> {U32.is_eq(M.ts.bm.at(Con{a, pt}, Nat.sub(List.length(&2, U32, pt), bp.ck(e1, e2, List.length(&2, U32, pt), k))), M.ts.bm.at(Con{b, wt}, Nat.sub(List.length(&2, U32, pt), bp.ck(e1, e2, List.length(&2, U32, pt), k)))) == False{} : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          L.tsl.absurd(Bool, U32.is_eq(M.ts.bm.at(Con{a, pt}, Nat.sub(List.length(&2, U32, pt), 1n+List.length(&2, U32, pt))), M.ts.bm.at(Con{b, wt}, Nat.sub(List.length(&2, U32, pt), 1n+List.length(&2, U32, pt)))), False{}, Equal.trans(Bool, False{}, Nat.is_eq(List.length(&2, U32, pt), List.length(&2, U32, pt)), True{}, Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, pt), List.length(&2, U32, pt)), False{}, hn), L.tsl.nat_refl(List.length(&2, U32, pt))))
        case False{}:
          %Equal.sym(Nat, Nat.sub(List.length(&2, U32, pt), List.length(&2, U32, pt)), 0n, L.tsl.sub_self(List.length(&2, U32, pt))) : {U32.is_eq(M.ts.bm.at(Con{a, pt}, _), M.ts.bm.at(Con{b, wt}, _)) == False{} : Bool}
          h_e2
    case False{}:
      match pt:
        case Nil{}:
          L.tsl.absurd_tf(Bool, U32.is_eq(M.ts.bm.at(Con{a, Nil{}}, Nat.sub(0n, k)), M.ts.bm.at(Con{b, wt}, Nat.sub(0n, k))), False{}, Equal.trans(Bool, True{}, Nat.is_eq(0n, 0n), False{}, {==}, Equal.trans(Bool, Nat.is_eq(0n, 0n), Nat.is_eq(k, 0n), False{}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 0n), 0n, k, Equal.trans(Nat, 0n, bp.cmr(Nil{}, wt), k, {==}, Equal.sym(Nat, k, bp.cmr(Nil{}, wt), hk))), h_e1)))
        case Con{+a2, +pt2}:
          +l2 = List.length(&2, U32, pt2)
          +h_lt = L.tsl.lt_succ_ne(k, 1n+l2, h_le, h_e1)
          %Equal.sym(Nat, Nat.sub(1n+l2, k), 1n+Nat.sub(l2, k), L.tsl.sub_succ_le(l2, k, h_lt)) : {U32.is_eq(M.ts.bm.at(Con{a, Con{a2, pt2}}, _), M.ts.bm.at(Con{b, wt}, _)) == False{} : Bool}
          %L.tsl.sub_zero(l2) : {U32.is_eq(M.ts.bm.at(Con{a2, pt2}, Nat.sub(_, k)), M.ts.bm.at(wt, Nat.sub(_, k))) == False{} : Bool}
          rec(h_e1)

# when the count is not the whole pattern, the byte before the agreeing
# end differs
def bp.cf_mis(p: List<&2, U32>, w: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, p), List.length(&2, U32, w)) == True{} : Bool}, +hn: {Nat.is_eq(bp.cmr(p, w), List.length(&2, U32, p)) == False{} : Bool}) -> {U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, w))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, w)))) == False{} : Bool}:
  match p w:
    case Nil{} Nil{}:
      L.tsl.absurd_tf(Bool, U32.is_eq(0, 0), False{}, hn)
    case Nil{} Con{+b, +wt}:
      L.tsl.absurd_tf(Bool, U32.is_eq(0, M.ts.bm.at(Con{b, wt}, 0n)), False{}, hn)
    case Con{+a, +pt} Nil{}:
      L.tsl.absurd(Bool, U32.is_eq(M.ts.bm.at(Con{a, pt}, Nat.sub(Nat.sub(1n+List.length(&2, U32, pt), 1n), 0n)), 0), False{}, h)
    case Con{+a, +pt} Con{+b, +wt}:
      +k = bp.cmr(pt, wt)
      %Equal.sym(Nat, Nat.sub(List.length(&2, U32, pt), 0n), List.length(&2, U32, pt), L.tsl.sub_zero(List.length(&2, U32, pt))) : {U32.is_eq(M.ts.bm.at(Con{a, pt}, Nat.sub(_, bp.ck(Nat.is_eq(k, List.length(&2, U32, pt)), U32.is_eq(a, b), List.length(&2, U32, pt), k))), M.ts.bm.at(Con{b, wt}, Nat.sub(_, bp.ck(Nat.is_eq(k, List.length(&2, U32, pt)), U32.is_eq(a, b), List.length(&2, U32, pt), k)))) == False{} : Bool}
      bp.mis_h(Nat.is_eq(k, List.length(&2, U32, pt)), U32.is_eq(a, b), a, b, pt, wt, k, {==}, {==}, bp.cmr_le(pt, wt), {==}, hn, hk => bp.cf_mis(pt, wt, h, hk))

# Positions in lists of bytes

def bp.drop0(xs: List<&2, U32>) -> {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}

def bp.at_drop(w: List<&2, U32>, i: Nat, +t: Nat) -> {M.ts.bm.at(List.drop(&2, U32, w, i), t) == M.ts.bm.at(w, Nat.add(i, t)) : U32}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match i:
        case 0n:
          {==}
        case 1n+ +j:
          bp.at_drop(r, j, t)

def bp.at_take(w: List<&2, U32>, n: Nat, u: Nat, +h: {Nat.is_lt(u, n) == True{} : Bool}) -> {M.ts.bm.at(List.take(&2, U32, w, n), u) == M.ts.bm.at(w, u) : U32}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match n:
        case 0n:
          L.tsl.lt_zero_abs(U32, M.ts.bm.at(Nil{}, u), M.ts.bm.at(Con{x, r}, u), u, h)
        case 1n+ +k:
          match u:
            case 0n:
              {==}
            case 1n+ +v:
              bp.at_take(r, k, v, h)

def bp.len_take(w: List<&2, U32>, n: Nat, +h: {Nat.is_lt(n, 1n+List.length(&2, U32, w)) == True{} : Bool}) -> {List.length(&2, U32, List.take(&2, U32, w, n)) == n : Nat}:
  match w:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+ +k:
          L.tsl.lt_zero_abs(Nat, 0n, 1n+k, k, h)
    case Con{+x, +r}:
      match n:
        case 0n:
          {==}
        case 1n+ +k:
          %bp.len_take(r, k, h) : {1n+List.length(&2, U32, List.take(&2, U32, r, k)) == 1n+_ : Nat}
          {==}

def bp.len_take_short(w: List<&2, U32>, n: Nat, +h: {Nat.is_lt(List.length(&2, U32, w), n) == True{} : Bool}) -> {List.length(&2, U32, List.take(&2, U32, w, n)) == List.length(&2, U32, w) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match n:
        case 0n:
          L.tsl.absurd(Nat, 0n, 1n+List.length(&2, U32, r), h)
        case 1n+ +k:
          %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, r, k)), List.length(&2, U32, r), bp.len_take_short(r, k, h)) : {1n+_ == 1n+List.length(&2, U32, r) : Nat}
          {==}

def bp.len_drop(w: List<&2, U32>, i: Nat) -> {List.length(&2, U32, List.drop(&2, U32, w, i)) == Nat.sub(List.length(&2, U32, w), i) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match i:
        case 0n:
          {==}
        case 1n+ +j:
          bp.len_drop(r, j)

def bp.drop_tail(t: List<&2, U32>, i: Nat) -> {List.tail(&2, U32, List.drop(&2, U32, t, i)) == List.drop(&2, U32, t, 1n+i) : List<&2, U32>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match i:
        case 0n:
          Equal.sym(List<&2, U32>, List.drop(&2, U32, r, 0n), r, bp.drop0(r))
        case 1n+ +j:
          bp.drop_tail(r, j)

def bp.nil_con(-b: U32, -t: List<&2, U32>, +e: {Nil{} == Con{b, t} : List<&2, U32>}) -> {False{} == True{} : Bool}:
  Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, U32>, Bool, xs => List.is_empty(&2, U32, xs), Nil{}, Con{b, t}, e))

def bp.con_hd(-x: U32, -xs: List<&2, U32>, -b: U32, -t: List<&2, U32>, +e: {Con{x, xs} == Con{b, t} : List<&2, U32>}) -> {x == b : U32}:
  Equal.cong(List<&2, U32>, U32, ys => M.ts.bm.at(ys, 0n), Con{x, xs}, Con{b, t}, e)

def bp.con_tl(-x: U32, -xs: List<&2, U32>, -b: U32, -t: List<&2, U32>, +e: {Con{x, xs} == Con{b, t} : List<&2, U32>}) -> {xs == t : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.tail(&2, U32, ys), Con{x, xs}, Con{b, t}, e)

# the rest from n is b then t: byte n is b, the rest from n + 1 is t, and
# n is below the length
def bp.drop_at(p: List<&2, U32>, n: Nat, -b: U32, -t: List<&2, U32>, +e: {List.drop(&2, U32, p, n) == Con{b, t} : List<&2, U32>}) -> {M.ts.bm.at(p, n) == b : U32}:
  match p:
    case Nil{}:
      L.tsl.absurd(U32, 0, b, bp.nil_con(b, t, e))
    case Con{+x, +q}:
      match n:
        case 0n:
          bp.con_hd(x, q, b, t, e)
        case 1n+ +i:
          bp.drop_at(q, i, b, t, e)

def bp.drop_tl(p: List<&2, U32>, n: Nat, -b: U32, -t: List<&2, U32>, +e: {List.drop(&2, U32, p, n) == Con{b, t} : List<&2, U32>}) -> {List.drop(&2, U32, p, 1n+n) == t : List<&2, U32>}:
  match p:
    case Nil{}:
      L.tsl.absurd(List<&2, U32>, Nil{}, t, bp.nil_con(b, t, e))
    case Con{+x, +q}:
      match n:
        case 0n:
          Equal.trans(List<&2, U32>, List.drop(&2, U32, q, 0n), q, t, bp.drop0(q), bp.con_tl(x, q, b, t, e))
        case 1n+ +i:
          bp.drop_tl(q, i, b, t, e)

def bp.drop_lt(p: List<&2, U32>, n: Nat, -b: U32, -t: List<&2, U32>, +e: {List.drop(&2, U32, p, n) == Con{b, t} : List<&2, U32>}) -> {Nat.is_lt(n, List.length(&2, U32, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      L.tsl.absurd(Bool, Nat.is_lt(n, 0n), True{}, bp.nil_con(b, t, e))
    case Con{+x, +q}:
      match n:
        case 0n:
          {==}
        case 1n+ +i:
          bp.drop_lt(q, i, b, t, e)

def bp.drop_nil(p: List<&2, U32>, n: Nat, +e: {List.drop(&2, U32, p, n) == Nil{} : List<&2, U32>}) -> {Nat.is_lt(n, List.length(&2, U32, p)) == False{} : Bool}:
  match p:
    case Nil{}:
      L.tsl.lt_zero(n)
    case Con{+x, +q}:
      match n:
        case 0n:
          L.tsl.absurd(Bool, True{}, False{}, Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, U32>, Bool, xs => List.is_empty(&2, U32, xs), Nil{}, Con{x, q}, Equal.sym(List<&2, U32>, Con{x, q}, Nil{}, e))))
        case 1n+ +i:
          bp.drop_nil(q, i, e)

# The reference's test at a position

def bp.not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      L.tsl.absurd(Bool, True{}, False{}, h)
    case False{}:
      {==}

def bp.or_true_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the pattern at u: each pattern byte is the byte at the same position
def bp.nat_pos(p: List<&2, U32>, u: List<&2, U32>, t: Nat, +h: {V.ts.naive.at(False{}, p, u) == True{} : Bool}, +ht: {Nat.is_lt(t, List.length(&2, U32, p)) == True{} : Bool}) -> {U32.is_eq(M.ts.bm.at(p, t), M.ts.bm.at(u, t)) == True{} : Bool}:
  match p:
    case Nil{}:
      L.tsl.lt_zero_abs(Bool, U32.is_eq(0, M.ts.bm.at(u, t)), True{}, t, ht)
    case Con{+a, +q}:
      match u:
        case Nil{}:
          L.tsl.absurd(Bool, U32.is_eq(M.ts.bm.at(Con{a, q}, t), 0), True{}, h)
        case Con{+b, +r}:
          match t:
            case 0n:
              L.tsl.and_l(U32.is_eq(a, b), V.ts.naive.at(False{}, q, r), h)
            case 1n+ +s:
              bp.nat_pos(q, r, s, L.tsl.and_r(U32.is_eq(a, b), V.ts.naive.at(False{}, q, r), h), ht)

# shorter than the pattern: no match
def bp.at_short(+icase: Bool, p: List<&2, U32>, u: List<&2, U32>, +h: {Nat.is_lt(List.length(&2, U32, u), List.length(&2, U32, p)) == True{} : Bool}) -> {V.ts.naive.at(icase, p, u) == False{} : Bool}:
  match p:
    case Nil{}:
      L.tsl.lt_zero_abs(Bool, True{}, False{}, List.length(&2, U32, u), h)
    case Con{+a, +q}:
      match u:
        case Nil{}:
          {==}
        case Con{+b, +r}:
          %Equal.sym(Bool, V.ts.naive.at(icase, q, r), False{}, bp.at_short(icase, q, r, h)) : {Bool.and(T.ts.same(icase, a, b), _) == False{} : Bool}
          L.tsl.and_false_r(T.ts.same(icase, a, b))

# the test reads only the first m bytes
def bp.at_take_p(p: List<&2, U32>, w: List<&2, U32>) -> {V.ts.naive.at(False{}, p, List.take(&2, U32, w, List.length(&2, U32, p))) == V.ts.naive.at(False{}, p, w) : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +q}:
      match w:
        case Nil{}:
          {==}
        case Con{+b, +r}:
          %bp.at_take_p(q, r) : {Bool.and(U32.is_eq(a, b), V.ts.naive.at(False{}, q, List.take(&2, U32, r, List.length(&2, U32, q)))) == Bool.and(U32.is_eq(a, b), _) : Bool}
          {==}

# ... so bytes after them do not matter
def bp.at_app(+icase: Bool, p: List<&2, U32>, b: List<&2, U32>, +r: List<&2, U32>, +h: {Nat.is_lt(List.length(&2, U32, b), List.length(&2, U32, p)) == False{} : Bool}) -> {V.ts.naive.at(icase, p, List.append(&2, U32, b, r)) == V.ts.naive.at(icase, p, b) : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +q}:
      match b:
        case Nil{}:
          L.tsl.absurd_tf(Bool, V.ts.naive.at(icase, Con{a, q}, r), False{}, h)
        case Con{+c, +bt}:
          %bp.at_app(icase, q, bt, r, h) : {Bool.and(T.ts.same(icase, a, c), V.ts.naive.at(icase, q, List.append(&2, U32, bt, r))) == Bool.and(T.ts.same(icase, a, c), _) : Bool}
          {==}

# The bad-character shift

# no pattern position from lo below hi holds b
def bp.nob(+p: List<&2, U32>, +b: U32, +lo: Nat, hi: Nat) -> Bool:
  match hi:
    case 0n:
      True{}
    case 1n+ +k:
      Bool.and(bp.nob(p, b, lo, k), Bool.or(Nat.is_lt(k, lo), Bool.not(U32.is_eq(M.ts.bm.at(p, k), b))))

def bp.nob_ext_h(e: Bool, +k: Nat, +p: List<&2, U32>, +b: U32, +lo: Nat, +v: Nat, +h: {bp.nob(p, b, lo, 1n+k) == True{} : Bool}, +hv1: {Nat.is_lt(v, 1n+k) == True{} : Bool}, +hv2: {Nat.is_lt(v, lo) == False{} : Bool}, +ev: {Nat.is_eq(v, k) == e : Bool}, rec: {Nat.is_lt(v, k) == True{} : Bool} -> {U32.is_eq(M.ts.bm.at(p, v), b) == False{} : Bool}) -> {U32.is_eq(M.ts.bm.at(p, v), b) == False{} : Bool}:
  match e:
    case True{}:
      +h2 = L.tsl.and_r(bp.nob(p, b, lo, k), Bool.or(Nat.is_lt(k, lo), Bool.not(U32.is_eq(M.ts.bm.at(p, k), b))), h)
      +ekv = Equal.sym(Nat, v, k, L.tsl.nat_eq(v, k, ev))
      +hk = Equal.trans(Bool, Nat.is_lt(k, lo), Nat.is_lt(v, lo), False{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, lo), k, v, ekv), hv2)
      +h3 = Equal.trans(Bool, Bool.not(U32.is_eq(M.ts.bm.at(p, k), b)), Bool.or(Nat.is_lt(k, lo), Bool.not(U32.is_eq(M.ts.bm.at(p, k), b))), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Bool.not(U32.is_eq(M.ts.bm.at(p, k), b))), False{}, Nat.is_lt(k, lo), Equal.sym(Bool, Nat.is_lt(k, lo), False{}, hk)), h2)
      %ekv : {U32.is_eq(M.ts.bm.at(p, _), b) == False{} : Bool}
      bp.not_true(U32.is_eq(M.ts.bm.at(p, k), b), h3)
    case False{}:
      rec(L.tsl.lt_succ_ne(v, k, hv1, ev))

def bp.nob_ext(hi: Nat, +p: List<&2, U32>, +b: U32, +lo: Nat, +v: Nat, +h: {bp.nob(p, b, lo, hi) == True{} : Bool}, +hv1: {Nat.is_lt(v, hi) == True{} : Bool}, +hv2: {Nat.is_lt(v, lo) == False{} : Bool}) -> {U32.is_eq(M.ts.bm.at(p, v), b) == False{} : Bool}:
  match hi:
    case 0n:
      L.tsl.lt_zero_abs(Bool, U32.is_eq(M.ts.bm.at(p, v), b), False{}, v, hv1)
    case 1n+ +k:
      bp.nob_ext_h(Nat.is_eq(v, k), k, p, b, lo, v, h, hv1, hv2, {==}, hl => bp.nob_ext(k, p, b, lo, v, L.tsl.and_l(bp.nob(p, b, lo, k), Bool.or(Nat.is_lt(k, lo), Bool.not(U32.is_eq(M.ts.bm.at(p, k), b))), h), hl, hv2))

def bp.nob_empty(hi: Nat, +p: List<&2, U32>, +b: U32, +lo: Nat, +h: {Nat.is_lt(hi, 1n+lo) == True{} : Bool}) -> {bp.nob(p, b, lo, hi) == True{} : Bool}:
  match hi:
    case 0n:
      {==}
    case 1n+ +k:
      %Equal.sym(Bool, Nat.is_lt(k, lo), True{}, h) : {Bool.and(bp.nob(p, b, lo, k), Bool.or(_, Bool.not(U32.is_eq(M.ts.bm.at(p, k), b)))) == True{} : Bool}
      %Equal.sym(Bool, bp.nob(p, b, lo, k), True{}, bp.nob_empty(k, p, b, lo, L.tsl.lt_weak(k, lo, h))) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

# j < m - 1: m - ((m - 1) - j) is j + 1
def bp.sub_cj(+m: Nat, +j: Nat, +h: {Nat.is_lt(j, Nat.sub(m, 1n)) == True{} : Bool}) -> {Nat.sub(m, Nat.sub(Nat.sub(m, 1n), j)) == 1n+j : Nat}:
  match m:
    case 0n:
      L.tsl.lt_zero_abs(Nat, 0n, 1n+j, j, h)
    case 1n+ +k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, L.tsl.sub_zero(k)) : {Nat.sub(1n+k, Nat.sub(_, j)) == 1n+j : Nat}
      +hk = Equal.trans(Bool, Nat.is_lt(j, k), Nat.is_lt(j, Nat.sub(k, 0n)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(j, n), k, Nat.sub(k, 0n), Equal.sym(Nat, Nat.sub(k, 0n), k, L.tsl.sub_zero(k))), h)
      %Equal.sym(Nat, Nat.sub(1n+k, Nat.sub(k, j)), 1n+Nat.sub(k, Nat.sub(k, j)), L.tsl.sub_succ_le(k, Nat.sub(k, j), L.tsl.sub_le(k, j))) : {_ == 1n+j : Nat}
      %Equal.sym(Nat, Nat.sub(k, Nat.sub(k, j)), j, L.tsl.sub_sub(k, j, L.tsl.lt_weak(j, k, hk))) : {1n+_ == 1n+j : Nat}
      {==}

def bp.hs_nob(e: Bool, +x: U32, +j: Nat, +r: Nat, +p: List<&2, U32>, +b: U32, +m: Nat, +ex: {U32.is_eq(x, b) == e : Bool}, +h_pj: {M.ts.bm.at(p, j) == x : U32}, +h_jc: {Nat.is_lt(j, Nat.sub(m, 1n)) == True{} : Bool}, +h_nob: {bp.nob(p, b, Nat.sub(m, r), j) == True{} : Bool}) -> {bp.nob(p, b, Nat.sub(m, M.ts.bm.pick(e, Nat.sub(Nat.sub(m, 1n), j), r)), 1n+j) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, Nat.sub(m, Nat.sub(Nat.sub(m, 1n), j)), 1n+j, bp.sub_cj(m, j, h_jc)) : {bp.nob(p, b, _, 1n+j) == True{} : Bool}
      bp.nob_empty(1n+j, p, b, 1n+j, L.tsl.lt_succ(1n+j))
    case False{}:
      %Equal.sym(Bool, bp.nob(p, b, Nat.sub(m, r), j), True{}, h_nob) : {Bool.and(_, Bool.or(Nat.is_lt(j, Nat.sub(m, r)), Bool.not(U32.is_eq(M.ts.bm.at(p, j), b)))) == True{} : Bool}
      %Equal.sym(U32, M.ts.bm.at(p, j), x, h_pj) : {Bool.and(True{}, Bool.or(Nat.is_lt(j, Nat.sub(m, r)), Bool.not(U32.is_eq(_, b)))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(x, b), False{}, ex) : {Bool.and(True{}, Bool.or(Nat.is_lt(j, Nat.sub(m, r)), Bool.not(_))) == True{} : Bool}
      bp.or_true_r(Nat.is_lt(j, Nat.sub(m, r)))

# Horspool's scan over the pattern before its last byte: no position from
# m minus the shift found to m - 2 holds b
def bp.hs_go(xs: List<&2, U32>, +j: Nat, +r: Nat, +v: Nat, +p: List<&2, U32>, +b: U32, +m: Nat, +h_c: {Nat.is_lt(Nat.sub(m, 1n), 1n+List.length(&2, U32, p)) == True{} : Bool}, +h_xs: {List.drop(&2, U32, List.take(&2, U32, p, Nat.sub(m, 1n)), j) == xs : List<&2, U32>}, +h_nob: {bp.nob(p, b, Nat.sub(m, r), j) == True{} : Bool}, +hv1: {Nat.is_lt(v, Nat.sub(m, 1n)) == True{} : Bool}, +hv2: {Nat.is_lt(v, Nat.sub(m, M.ts.bm.hs.go(xs, b, m, j, r))) == False{} : Bool}) -> {U32.is_eq(M.ts.bm.at(p, v), b) == False{} : Bool}:
  match xs:
    case Nil{}:
      +c = Nat.sub(m, 1n)
      +X = List.take(&2, U32, p, c)
      +e_len = bp.len_take(p, c, h_c)
      +h_jc = Equal.trans(Bool, Nat.is_lt(j, c), Nat.is_lt(j, List.length(&2, U32, X)), False{}, Equal.cong(Nat, Bool, n => Nat.is_lt(j, n), c, List.length(&2, U32, X), Equal.sym(Nat, List.length(&2, U32, X), c, e_len)), bp.drop_nil(X, j, h_xs))
      bp.nob_ext(j, p, b, Nat.sub(m, r), v, h_nob, L.tsl.lt_le_trans(v, c, j, hv1, L.tsl.nlt_le(j, c, h_jc)), hv2)
    case Con{+x, +t}:
      +c = Nat.sub(m, 1n)
      +X = List.take(&2, U32, p, c)
      +e_len = bp.len_take(p, c, h_c)
      +h_jX = bp.drop_lt(X, j, x, t, h_xs)
      +h_jc = Equal.trans(Bool, Nat.is_lt(j, c), Nat.is_lt(j, List.length(&2, U32, X)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(j, n), c, List.length(&2, U32, X), Equal.sym(Nat, List.length(&2, U32, X), c, e_len)), h_jX)
      +h_pj = Equal.trans(U32, M.ts.bm.at(p, j), M.ts.bm.at(X, j), x, Equal.sym(U32, M.ts.bm.at(X, j), M.ts.bm.at(p, j), bp.at_take(p, c, j, h_jc)), bp.drop_at(X, j, x, t, h_xs))
      bp.hs_go(t, 1n+j, M.ts.bm.pick(U32.is_eq(x, b), Nat.sub(c, j), r), v, p, b, m, h_c, bp.drop_tl(X, j, x, t, h_xs), bp.hs_nob(U32.is_eq(x, b), x, j, r, p, b, m, {==}, h_pj, h_jc, h_nob), hv1, hv2)

def bp.hs_le_h(e: Bool, +j: Nat, +r: Nat, +m: Nat, +h_r: {Nat.is_lt(r, 1n+m) == True{} : Bool}) -> {Nat.is_lt(M.ts.bm.pick(e, Nat.sub(Nat.sub(m, 1n), j), r), 1n+m) == True{} : Bool}:
  match e:
    case True{}:
      L.tsl.lt_le_trans(Nat.sub(Nat.sub(m, 1n), j), 1n+Nat.sub(m, 1n), 1n+m, L.tsl.sub_le(Nat.sub(m, 1n), j), L.tsl.sub_le(m, 1n))
    case False{}:
      h_r

def bp.hs_le(xs: List<&2, U32>, +j: Nat, +r: Nat, +b: U32, +m: Nat, +h_r: {Nat.is_lt(r, 1n+m) == True{} : Bool}) -> {Nat.is_lt(M.ts.bm.hs.go(xs, b, m, j, r), 1n+m) == True{} : Bool}:
  match xs:
    case Nil{}:
      h_r
    case Con{+x, +t}:
      bp.hs_le(t, 1n+j, M.ts.bm.pick(U32.is_eq(x, b), Nat.sub(Nat.sub(m, 1n), j), r), b, m, bp.hs_le_h(U32.is_eq(x, b), j, r, m, h_r))

# The good-suffix searches: every shift below the one found fails

def bp.ln2(e: Bool, +s: Nat, +i: Nat, +p: List<&2, U32>, +m: Nat, +j: Nat, +h1: {Nat.is_lt(i, s) == False{} : Bool}, +e0: {M.ts.bm.gs.ok(p, m, j, s) == False{} : Bool}, +ei: {Nat.is_eq(i, s) == e : Bool}, rec: {Nat.is_lt(i, 1n+s) == False{} : Bool} -> {M.ts.bm.gs.ok(p, m, j, i) == False{} : Bool}) -> {M.ts.bm.gs.ok(p, m, j, i) == False{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, i, s, L.tsl.nat_eq(i, s, ei)) : {M.ts.bm.gs.ok(p, m, j, _) == False{} : Bool}
      e0
    case False{}:
      rec(L.tsl.lt_nle(s, i, L.tsl.nlt_ne(i, s, h1, ei)))

def bp.ln1(e: Bool, +f: Nat, +s: Nat, +i: Nat, +p: List<&2, U32>, +m: Nat, +j: Nat, +h1: {Nat.is_lt(i, s) == False{} : Bool}, +e0: {M.ts.bm.gs.ok(p, m, j, s) == e : Bool}, +h2: {Nat.is_lt(i, M.ts.bm.pick(e, s, M.ts.bm.gs.least(f, p, m, j, 1n+s))) == True{} : Bool}, rec: {Nat.is_lt(i, 1n+s) == False{} : Bool} -> {Nat.is_lt(i, M.ts.bm.gs.least(f, p, m, j, 1n+s)) == True{} : Bool} -> {M.ts.bm.gs.ok(p, m, j, i) == False{} : Bool}) -> {M.ts.bm.gs.ok(p, m, j, i) == False{} : Bool}:
  match e:
    case True{}:
      L.tsl.absurd(Bool, M.ts.bm.gs.ok(p, m, j, i), False{}, Equal.trans(Bool, False{}, Nat.is_lt(i, s), True{}, Equal.sym(Bool, Nat.is_lt(i, s), False{}, h1), h2))
    case False{}:
      bp.ln2(Nat.is_eq(i, s), s, i, p, m, j, h1, e0, {==}, h1b => rec(h1b, h2))

def bp.least_nok(fuel: Nat, +s: Nat, +i: Nat, +p: List<&2, U32>, +m: Nat, +j: Nat, +h_inv: {Nat.is_lt(m, Nat.add(s, fuel)) == True{} : Bool}, +h1: {Nat.is_lt(i, s) == False{} : Bool}, +h2: {Nat.is_lt(i, M.ts.bm.gs.least(fuel, p, m, j, s)) == True{} : Bool}) -> {M.ts.bm.gs.ok(p, m, j, i) == False{} : Bool}:
  match fuel:
    case 0n:
      +h_ms = Equal.trans(Bool, Nat.is_lt(m, s), Nat.is_lt(m, Nat.add(s, 0n)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(m, n), s, Nat.add(s, 0n), Equal.sym(Nat, Nat.add(s, 0n), s, UL.nat_add_zero(s))), h_inv)
      L.tsl.absurd(Bool, M.ts.bm.gs.ok(p, m, j, i), False{}, Equal.trans(Bool, False{}, Nat.is_lt(i, s), True{}, Equal.sym(Bool, Nat.is_lt(i, s), False{}, h1), UO.nat_lt_trans(i, m, s, h2, h_ms)))
    case 1n+ +f:
      +h_inv2 = Equal.trans(Bool, Nat.is_lt(m, Nat.add(1n+s, f)), Nat.is_lt(m, Nat.add(s, 1n+f)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(m, n), 1n+Nat.add(s, f), Nat.add(s, 1n+f), Equal.sym(Nat, Nat.add(s, 1n+f), 1n+Nat.add(s, f), UL.nat_add_succ(s, f))), h_inv)
      bp.ln1(M.ts.bm.gs.ok(p, m, j, s), f, s, i, p, m, j, h1, {==}, h2, h1b => h2b => bp.least_nok(f, 1n+s, i, p, m, j, h_inv2, h1b, h2b))

def bp.pn2(e: Bool, +s: Nat, +i: Nat, +p: List<&2, U32>, +m: Nat, +h1: {Nat.is_lt(i, s) == False{} : Bool}, +e0: {M.ts.bm.agree(p, m, s, 0n) == False{} : Bool}, +ei: {Nat.is_eq(i, s) == e : Bool}, rec: {Nat.is_lt(i, 1n+s) == False{} : Bool} -> {M.ts.bm.agree(p, m, i, 0n) == False{} : Bool}) -> {M.ts.bm.agree(p, m, i, 0n) == False{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, i, s, L.tsl.nat_eq(i, s, ei)) : {M.ts.bm.agree(p, m, _, 0n) == False{} : Bool}
      e0
    case False{}:
      rec(L.tsl.lt_nle(s, i, L.tsl.nlt_ne(i, s, h1, ei)))

def bp.pn1(e: Bool, +f: Nat, +s: Nat, +i: Nat, +p: List<&2, U32>, +m: Nat, +h1: {Nat.is_lt(i, s) == False{} : Bool}, +e0: {M.ts.bm.agree(p, m, s, 0n) == e : Bool}, +h2: {Nat.is_lt(i, M.ts.bm.pick(e, s, M.ts.bm.gs.period(f, p, m, 1n+s))) == True{} : Bool}, rec: {Nat.is_lt(i, 1n+s) == False{} : Bool} -> {Nat.is_lt(i, M.ts.bm.gs.period(f, p, m, 1n+s)) == True{} : Bool} -> {M.ts.bm.agree(p, m, i, 0n) == False{} : Bool}) -> {M.ts.bm.agree(p, m, i, 0n) == False{} : Bool}:
  match e:
    case True{}:
      L.tsl.absurd(Bool, M.ts.bm.agree(p, m, i, 0n), False{}, Equal.trans(Bool, False{}, Nat.is_lt(i, s), True{}, Equal.sym(Bool, Nat.is_lt(i, s), False{}, h1), h2))
    case False{}:
      bp.pn2(Nat.is_eq(i, s), s, i, p, m, h1, e0, {==}, h1b => rec(h1b, h2))

def bp.per_nok(fuel: Nat, +s: Nat, +i: Nat, +p: List<&2, U32>, +m: Nat, +h_inv: {Nat.is_lt(m, Nat.add(s, fuel)) == True{} : Bool}, +h1: {Nat.is_lt(i, s) == False{} : Bool}, +h2: {Nat.is_lt(i, M.ts.bm.gs.period(fuel, p, m, s)) == True{} : Bool}) -> {M.ts.bm.agree(p, m, i, 0n) == False{} : Bool}:
  match fuel:
    case 0n:
      +h_ms = Equal.trans(Bool, Nat.is_lt(m, s), Nat.is_lt(m, Nat.add(s, 0n)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(m, n), s, Nat.add(s, 0n), Equal.sym(Nat, Nat.add(s, 0n), s, UL.nat_add_zero(s))), h_inv)
      L.tsl.absurd(Bool, M.ts.bm.agree(p, m, i, 0n), False{}, Equal.trans(Bool, False{}, Nat.is_lt(i, s), True{}, Equal.sym(Bool, Nat.is_lt(i, s), False{}, h1), UO.nat_lt_trans(i, m, s, h2, h_ms)))
    case 1n+ +f:
      +h_inv2 = Equal.trans(Bool, Nat.is_lt(m, Nat.add(1n+s, f)), Nat.is_lt(m, Nat.add(s, 1n+f)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(m, n), 1n+Nat.add(s, f), Nat.add(s, 1n+f), Equal.sym(Nat, Nat.add(s, 1n+f), 1n+Nat.add(s, f), UL.nat_add_succ(s, f))), h_inv)
      bp.pn1(M.ts.bm.agree(p, m, s, 0n), f, s, i, p, m, h1, {==}, h2, h1b => h2b => bp.per_nok(f, 1n+s, i, p, m, h_inv2, h1b, h2b))

# entry u of the good-suffix table is the search at position u
def bp.tab(n: Nat, +p: List<&2, U32>, +m: Nat, +j0: Nat, u: Nat, +h: {Nat.is_lt(u, n) == True{} : Bool}) -> {M.ts.bm.nat_at(M.ts.bm.gs.table(n, p, m, j0), u) == M.ts.bm.gs.least(m, p, m, Nat.add(j0, u), 1n) : Nat}:
  match n:
    case 0n:
      L.tsl.lt_zero_abs(Nat, 0n, M.ts.bm.gs.least(m, p, m, Nat.add(j0, u), 1n), u, h)
    case 1n+ +k:
      match u:
        case 0n:
          %Equal.sym(Nat, Nat.add(j0, 0n), j0, UL.nat_add_zero(j0)) : {M.ts.bm.gs.least(m, p, m, j0, 1n) == M.ts.bm.gs.least(m, p, m, _, 1n) : Nat}
          {==}
        case 1n+ +v:
          %Equal.sym(Nat, Nat.add(j0, 1n+v), 1n+Nat.add(j0, v), UL.nat_add_succ(j0, v)) : {M.ts.bm.nat_at(M.ts.bm.gs.table(k, p, m, 1n+j0), v) == M.ts.bm.gs.least(m, p, m, _, 1n) : Nat}
          bp.tab(k, p, m, 1n+j0, v, h)

# Shifts and steps

def bp.max1_pos(+x: Nat) -> {Nat.is_lt(0n, Nat.max(x, 1n)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      {==}

def bp.max1_lt(+x: Nat, +i: Nat, +h1: {Nat.is_lt(0n, i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.max(x, 1n)) == True{} : Bool}) -> {Nat.is_lt(i, x) == True{} : Bool}:
  match x:
    case 0n:
      match i:
        case 0n:
          L.tsl.absurd(Bool, False{}, True{}, h1)
        case 1n+ +k:
          L.tsl.lt_zero_abs(Bool, Nat.is_lt(1n+k, 0n), True{}, k, h2)
    case 1n+ +y:
      Equal.trans(Bool, Nat.is_lt(i, 1n+y), Nat.is_lt(i, 1n+Nat.max(y, 0n)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(i, 1n+n), y, Nat.max(y, 0n), Equal.sym(Nat, Nat.max(y, 0n), y, L.tsl.max_zero(y))), h2)

def bp.max_lt(+a: Nat, +b: Nat, +i: Nat, +h1: {Nat.is_lt(i, Nat.max(a, b)) == True{} : Bool}, +h2: {Nat.is_lt(i, a) == False{} : Bool}) -> {Nat.is_lt(i, b) == True{} : Bool}:
  match a:
    case 0n:
      h1
    case 1n+ +a1:
      match b:
        case 0n:
          L.tsl.absurd(Bool, Nat.is_lt(i, 0n), True{}, Equal.trans(Bool, False{}, Nat.is_lt(i, 1n+a1), True{}, Equal.sym(Bool, Nat.is_lt(i, 1n+a1), False{}, h2), h1))
        case 1n+ +b1:
          match i:
            case 0n:
              {==}
            case 1n+ +k:
              bp.max_lt(a1, b1, k, h1, h2)

# One window: w is the text from the window's start, p the pattern

def bp.win_len(+w: List<&2, U32>, +p: List<&2, U32>, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}) -> {List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))) == List.length(&2, U32, p) : Nat}:
  bp.len_take(w, List.length(&2, U32, p), L.tsl.nlt_le(List.length(&2, U32, w), List.length(&2, U32, p), h_long))

def bp.win_eq(+w: List<&2, U32>, +p: List<&2, U32>, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}) -> {Nat.is_eq(List.length(&2, U32, p), List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p)))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p), bp.win_len(w, p, h_long)) : {Nat.is_eq(List.length(&2, U32, p), _) == True{} : Bool}
  L.tsl.nat_refl(List.length(&2, U32, p))

def bp.at_win(+w: List<&2, U32>, +p: List<&2, U32>, +u: Nat, +h: {Nat.is_lt(u, List.length(&2, U32, p)) == True{} : Bool}) -> {M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), u) == M.ts.bm.at(w, u) : U32}:
  bp.at_take(w, List.length(&2, U32, p), u, h)

def bp.pos_nlt1(+i: Nat, +h: {Nat.is_lt(0n, i) == True{} : Bool}) -> {Nat.is_lt(i, 1n) == False{} : Bool}:
  match i:
    case 0n:
      L.tsl.absurd(Bool, True{}, False{}, h)
    case 1n+ +k:
      L.tsl.lt_zero(k)

def bp.c_lt_m(+p: List<&2, U32>, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p)) == True{} : Bool}:
  %L.tsl.succ_pred(List.length(&2, U32, p), h_pos) : {Nat.is_lt(Nat.sub(List.length(&2, U32, p), 1n), _) == True{} : Bool}
  L.tsl.lt_succ(Nat.sub(List.length(&2, U32, p), 1n))

# Horspool: an offset i below the shift h puts pattern position m - 1 - i
# under the window's last byte, which no pattern position from m - h to
# m - 2 holds
def bp.hsafe_h(b0: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_ih: {Nat.is_lt(i, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))) == True{} : Bool}, +e0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == b0 : Bool}) -> {b0 == False{} : Bool}:
  match b0:
    case True{}:
      +h_hm = bp.hs_le(List.take(&2, U32, p, Nat.sub(List.length(&2, U32, p), 1n)), 0n, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), List.length(&2, U32, p), L.tsl.lt_succ(List.length(&2, U32, p)))
      +h_im = L.tsl.lt_le_trans(i, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), List.length(&2, U32, p), h_ih, h_hm)
      +e_m = L.tsl.succ_pred(List.length(&2, U32, p), h_pos)
      +h_ic = Equal.trans(Bool, Nat.is_lt(i, 1n+Nat.sub(List.length(&2, U32, p), 1n)), Nat.is_lt(i, List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(i, n), 1n+Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p), e_m), h_im)
      +v = Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), i)
      +hv1 = L.tsl.sub_lt(Nat.sub(List.length(&2, U32, p), 1n), i, h_i1, h_ic)
      +hmono = Equal.trans(Bool, Nat.is_lt(Nat.sub(List.length(&2, U32, p), M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))), 1n+Nat.sub(1n+Nat.sub(List.length(&2, U32, p), 1n), 1n+i)), Nat.is_lt(Nat.sub(List.length(&2, U32, p), M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))), 1n+Nat.sub(List.length(&2, U32, p), 1n+i)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(Nat.sub(List.length(&2, U32, p), M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))), 1n+Nat.sub(n, 1n+i)), 1n+Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p), e_m), L.tsl.sub_mono(1n+i, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), List.length(&2, U32, p), h_ih))
      +hv2 = L.tsl.le_nlt(Nat.sub(List.length(&2, U32, p), M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))), v, hmono)
      +h_nb = bp.hs_go(List.take(&2, U32, p, Nat.sub(List.length(&2, U32, p), 1n)), 0n, List.length(&2, U32, p), v, p, M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), List.length(&2, U32, p), L.tsl.sub_le(List.length(&2, U32, p), 1n), bp.drop0(List.take(&2, U32, p, Nat.sub(List.length(&2, U32, p), 1n))), {==}, hv1, hv2)
      +h_cm = bp.c_lt_m(p, h_pos)
      +h_vm = UO.nat_lt_trans(v, Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p), hv1, h_cm)
      +h_eq1 = bp.nat_pos(p, List.drop(&2, U32, w, i), v, e0, h_vm)
      +e_b = Equal.trans(U32, M.ts.bm.at(List.drop(&2, U32, w, i), v), M.ts.bm.at(w, Nat.add(i, v)), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), bp.at_drop(w, i, v), Equal.trans(U32, M.ts.bm.at(w, Nat.add(i, v)), M.ts.bm.at(w, Nat.sub(List.length(&2, U32, p), 1n)), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), Equal.cong(Nat, U32, n => M.ts.bm.at(w, n), Nat.add(i, v), Nat.sub(List.length(&2, U32, p), 1n), L.tsl.add_sub(i, Nat.sub(List.length(&2, U32, p), 1n), h_ic)), Equal.sym(U32, M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), M.ts.bm.at(w, Nat.sub(List.length(&2, U32, p), 1n)), bp.at_win(w, p, Nat.sub(List.length(&2, U32, p), 1n), h_cm))))
      +h_eq2 = Equal.trans(Bool, U32.is_eq(M.ts.bm.at(p, v), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), U32.is_eq(M.ts.bm.at(p, v), M.ts.bm.at(List.drop(&2, U32, w, i), v)), True{}, Equal.cong(U32, Bool, y => U32.is_eq(M.ts.bm.at(p, v), y), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), M.ts.bm.at(List.drop(&2, U32, w, i), v), Equal.sym(U32, M.ts.bm.at(List.drop(&2, U32, w, i), v), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)), e_b)), h_eq1)
      L.tsl.absurd(Bool, True{}, False{}, Equal.trans(Bool, False{}, U32.is_eq(M.ts.bm.at(p, v), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), True{}, Equal.sym(Bool, U32.is_eq(M.ts.bm.at(p, v), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), False{}, h_nb), h_eq2))
    case False{}:
      {==}

def bp.hsafe(+w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_ih: {Nat.is_lt(i, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  bp.hsafe_h(V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)), w, p, i, h_pos, h_long, h_i1, h_ih, {==})

# The pattern at offset s agrees with itself shifted by s wherever the
# window agrees with the pattern

def bp.agw_h(b1: Bool, +lo: Nat, +w: List<&2, U32>, +p: List<&2, U32>, +s: Nat, +lo0: Nat, +hb0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, s)) == True{} : Bool}, +h_suf: {bp.suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), lo0) == True{} : Bool}, +h_lo: {Nat.is_lt(lo, lo0) == False{} : Bool}, +h_lm: {Nat.is_lt(lo, List.length(&2, U32, p)) == True{} : Bool}, +e1: {Nat.is_lt(lo, s) == b1 : Bool}) -> {Bool.or(b1, U32.is_eq(M.ts.bm.at(p, Nat.sub(lo, s)), M.ts.bm.at(p, lo))) == True{} : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      +t = Nat.sub(lo, s)
      +h_sl = L.tsl.nlt_le(lo, s, e1)
      +h_tm = L.tsl.lt_le_trans(t, 1n+lo, List.length(&2, U32, p), L.tsl.sub_le(lo, s), h_lm)
      +eA = bp.nat_pos(p, List.drop(&2, U32, w, s), t, hb0, h_tm)
      +eX = Equal.trans(U32, M.ts.bm.at(List.drop(&2, U32, w, s), t), M.ts.bm.at(w, Nat.add(s, t)), M.ts.bm.at(w, lo), bp.at_drop(w, s, t), Equal.cong(Nat, U32, n => M.ts.bm.at(w, n), Nat.add(s, t), lo, L.tsl.add_sub(s, lo, h_sl)))
      +eA2 = L.tsl.u32_eq(M.ts.bm.at(p, t), M.ts.bm.at(List.drop(&2, U32, w, s), t), eA)
      +eP = bp.suf_at(p, List.take(&2, U32, w, List.length(&2, U32, p)), lo0, lo, h_suf, h_lo, h_lm)
      +eP2 = L.tsl.u32_eq(M.ts.bm.at(p, lo), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), lo), eP)
      +eW = bp.at_win(w, p, lo, h_lm)
      +eA3 = Equal.trans(U32, M.ts.bm.at(p, t), M.ts.bm.at(List.drop(&2, U32, w, s), t), M.ts.bm.at(w, lo), eA2, eX)
      +eP3 = Equal.trans(U32, M.ts.bm.at(p, lo), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), lo), M.ts.bm.at(w, lo), eP2, eW)
      %Equal.sym(U32, M.ts.bm.at(p, t), M.ts.bm.at(w, lo), eA3) : {U32.is_eq(_, M.ts.bm.at(p, lo)) == True{} : Bool}
      %Equal.sym(U32, M.ts.bm.at(p, lo), M.ts.bm.at(w, lo), eP3) : {U32.is_eq(M.ts.bm.at(w, lo), _) == True{} : Bool}
      L.tsl.u32_refl(M.ts.bm.at(w, lo))

def bp.agw(n: Nat, +lo: Nat, +w: List<&2, U32>, +p: List<&2, U32>, +s: Nat, +lo0: Nat, +hb0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, s)) == True{} : Bool}, +h_suf: {bp.suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), lo0) == True{} : Bool}, +h_lo: {Nat.is_lt(lo, lo0) == False{} : Bool}, +h_n: {Nat.is_lt(Nat.add(lo, n), 1n+List.length(&2, U32, p)) == True{} : Bool}) -> {M.ts.bm.agree.go(n, p, s, lo) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      +h_n2 = Equal.trans(Bool, Nat.is_lt(Nat.add(1n+lo, k), 1n+List.length(&2, U32, p)), Nat.is_lt(Nat.add(lo, 1n+k), 1n+List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+List.length(&2, U32, p)), 1n+Nat.add(lo, k), Nat.add(lo, 1n+k), Equal.sym(Nat, Nat.add(lo, 1n+k), 1n+Nat.add(lo, k), UL.nat_add_succ(lo, k))), h_n)
      +h_lm = L.tsl.lt_add_l(lo, k, List.length(&2, U32, p), h_n2)
      +h_lo2 = L.tsl.le_nlt(lo0, 1n+lo, L.tsl.lt_weak(lo0, 1n+lo, L.tsl.nlt_le(lo, lo0, h_lo)))
      %Equal.sym(Bool, Bool.or(Nat.is_lt(lo, s), U32.is_eq(M.ts.bm.at(p, Nat.sub(lo, s)), M.ts.bm.at(p, lo))), True{}, bp.agw_h(Nat.is_lt(lo, s), lo, w, p, s, lo0, hb0, h_suf, h_lo, h_lm, {==})) : {Bool.and(_, M.ts.bm.agree.go(k, p, s, 1n+lo)) == True{} : Bool}
      bp.agw(k, 1n+lo, w, p, s, lo0, hb0, h_suf, h_lo2, h_n2)

# Good suffix after a match: an occurrence at s below the shift would make
# s a period
def bp.gsafe_full_h(b0: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == True{} : Bool}, +h_ig: {Nat.is_lt(i, M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)) == True{} : Bool}, +e0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == b0 : Bool}) -> {b0 == False{} : Bool}:
  match b0:
    case True{}:
      +nok = bp.per_nok(List.length(&2, U32, p), 1n, i, p, List.length(&2, U32, p), L.tsl.lt_succ(List.length(&2, U32, p)), bp.pos_nlt1(i, h_i1), h_ig)
      +e_k = L.tsl.nat_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p), h_full)
      +h_lo = Equal.trans(Bool, Nat.is_lt(0n, Nat.sub(List.length(&2, U32, p), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), Nat.is_lt(0n, Nat.sub(List.length(&2, U32, p), List.length(&2, U32, p))), False{}, Equal.cong(Nat, Bool, n => Nat.is_lt(0n, Nat.sub(List.length(&2, U32, p), n)), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p), e_k), Equal.trans(Bool, Nat.is_lt(0n, Nat.sub(List.length(&2, U32, p), List.length(&2, U32, p))), Nat.is_lt(0n, 0n), False{}, Equal.cong(Nat, Bool, n => Nat.is_lt(0n, n), Nat.sub(List.length(&2, U32, p), List.length(&2, U32, p)), 0n, L.tsl.sub_self(List.length(&2, U32, p))), {==}))
      +yes = bp.agw(Nat.sub(List.length(&2, U32, p), 0n), 0n, w, p, i, Nat.sub(List.length(&2, U32, p), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), e0, bp.cf_suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), bp.win_eq(w, p, h_long)), h_lo, L.tsl.sub_le(List.length(&2, U32, p), 0n))
      L.tsl.absurd(Bool, True{}, False{}, Equal.trans(Bool, False{}, M.ts.bm.agree(p, List.length(&2, U32, p), i, 0n), True{}, Equal.sym(Bool, M.ts.bm.agree(p, List.length(&2, U32, p), i, 0n), False{}, nok), yes))
    case False{}:
      {==}

def bp.gsafe_full(+w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == True{} : Bool}, +h_ig: {Nat.is_lt(i, M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  bp.gsafe_full_h(V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)), w, p, i, h_long, h_i1, h_full, h_ig, {==})

# Good suffix after a mismatch at j: an occurrence at s below the shift
# would make s agree with the matched suffix and put a byte other than
# pattern byte j under j

def bp.k_lt(+w: List<&2, U32>, +p: List<&2, U32>, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == False{} : Bool}) -> {Nat.is_lt(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == True{} : Bool}:
  L.tsl.lt_succ_ne(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p), bp.cmr_le(p, List.take(&2, U32, w, List.length(&2, U32, p))), h_full)

def bp.j_lt(+w: List<&2, U32>, +p: List<&2, U32>, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), List.length(&2, U32, p)) == True{} : Bool}:
  L.tsl.lt_le_trans(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), 1n+Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p), L.tsl.sub_le(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), Equal.trans(Bool, Nat.is_lt(1n+Nat.sub(List.length(&2, U32, p), 1n), 1n+List.length(&2, U32, p)), Nat.is_lt(List.length(&2, U32, p), 1n+List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, 1n+List.length(&2, U32, p)), 1n+Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p), L.tsl.succ_pred(List.length(&2, U32, p), h_pos)), L.tsl.lt_succ(List.length(&2, U32, p))))

# m - k is j + 1
def bp.mk(+w: List<&2, U32>, +p: List<&2, U32>, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == False{} : Bool}) -> {Nat.sub(List.length(&2, U32, p), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))) == 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))) : Nat}:
  +e_m = L.tsl.succ_pred(List.length(&2, U32, p), h_pos)
  +h_kc = Equal.trans(Bool, Nat.is_lt(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), 1n+Nat.sub(List.length(&2, U32, p), 1n)), Nat.is_lt(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), n), 1n+Nat.sub(List.length(&2, U32, p), 1n), List.length(&2, U32, p), e_m), bp.k_lt(w, p, h_full))
  %e_m : {Nat.sub(_, bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))) == 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))) : Nat}
  L.tsl.sub_succ_le(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), h_kc)

def bp.okb_h(b2: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +t: Nat, +e_t: {M.ts.bm.at(p, t) == M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))) : U32}, +h_mis: {U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))) == False{} : Bool}, +e2: {U32.is_eq(M.ts.bm.at(p, t), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))) == b2 : Bool}) -> {Bool.not(b2) == True{} : Bool}:
  match b2:
    case True{}:
      +e_pj = L.tsl.u32_eq(M.ts.bm.at(p, t), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), e2)
      +e_eq = Equal.trans(U32, M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(p, t), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), Equal.sym(U32, M.ts.bm.at(p, t), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), e_pj), e_t)
      +bad = Equal.trans(Bool, True{}, U32.is_eq(M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), False{}, Equal.sym(Bool, U32.is_eq(M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), True{}, L.tsl.u32_refl(M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))))), Equal.trans(Bool, U32.is_eq(M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), False{}, Equal.cong(U32, Bool, y => U32.is_eq(y, M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), Equal.sym(U32, M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), e_eq)), h_mis))
      L.tsl.absurd_tf(Bool, False{}, True{}, bad)
    case False{}:
      {==}

def bp.okb(b1: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == False{} : Bool}, +hb0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == True{} : Bool}, +e1: {Nat.is_lt(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i) == b1 : Bool}) -> {Bool.or(b1, Bool.not(U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i)), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))) == True{} : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      +t = Nat.sub(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i)
      +h_jm = bp.j_lt(w, p, h_pos)
      +h_ij = L.tsl.nlt_le(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i, e1)
      +h_tm = L.tsl.lt_le_trans(t, 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), List.length(&2, U32, p), L.tsl.sub_le(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i), h_jm)
      +eA = L.tsl.u32_eq(M.ts.bm.at(p, t), M.ts.bm.at(List.drop(&2, U32, w, i), t), bp.nat_pos(p, List.drop(&2, U32, w, i), t, hb0, h_tm))
      +eX = Equal.trans(U32, M.ts.bm.at(List.drop(&2, U32, w, i), t), M.ts.bm.at(w, Nat.add(i, t)), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), bp.at_drop(w, i, t), Equal.cong(Nat, U32, n => M.ts.bm.at(w, n), Nat.add(i, t), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), L.tsl.add_sub(i, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), h_ij)))
      +e_t = Equal.trans(U32, M.ts.bm.at(p, t), M.ts.bm.at(List.drop(&2, U32, w, i), t), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), eA, eX)
      +h_mis0 = bp.cf_mis(p, List.take(&2, U32, w, List.length(&2, U32, p)), bp.win_eq(w, p, h_long), h_full)
      +h_mis = Equal.trans(Bool, U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), False{}, Equal.cong(U32, Bool, y => U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), y), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), Equal.sym(U32, M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.at(w, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), bp.at_win(w, p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), h_jm))), h_mis0)
      bp.okb_h(U32.is_eq(M.ts.bm.at(p, t), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), w, p, t, e_t, h_mis, {==})

# an occurrence at s makes s consistent with the mismatch
def bp.okw(+w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == False{} : Bool}, +hb0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == True{} : Bool}) -> {M.ts.bm.gs.ok(p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i) == True{} : Bool}:
  +e_mk = bp.mk(w, p, h_pos, h_full)
  +h_suf0 = bp.cf_suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), bp.win_eq(w, p, h_long))
  +h_suf = Equal.trans(Bool, bp.suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), bp.suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), True{}, Equal.cong(Nat, Bool, n => bp.suf(p, List.take(&2, U32, w, List.length(&2, U32, p)), n), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), Nat.sub(List.length(&2, U32, p), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), Equal.sym(Nat, Nat.sub(List.length(&2, U32, p), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), e_mk)), h_suf0)
  +h_n = Equal.trans(Bool, Nat.is_lt(Nat.add(1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), Nat.sub(List.length(&2, U32, p), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), 1n+List.length(&2, U32, p)), Nat.is_lt(List.length(&2, U32, p), 1n+List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, 1n+List.length(&2, U32, p)), Nat.add(1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), Nat.sub(List.length(&2, U32, p), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), List.length(&2, U32, p), L.tsl.add_sub(1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), List.length(&2, U32, p), bp.j_lt(w, p, h_pos))), L.tsl.lt_succ(List.length(&2, U32, p)))
  +ya = bp.agw(Nat.sub(List.length(&2, U32, p), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), w, p, i, 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), hb0, h_suf, L.tsl.lt_irrefl(1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), h_n)
  %Equal.sym(Bool, M.ts.bm.agree(p, List.length(&2, U32, p), i, 1n+Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), True{}, ya) : {Bool.and(_, Bool.or(Nat.is_lt(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i), Bool.not(U32.is_eq(M.ts.bm.at(p, Nat.sub(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i)), M.ts.bm.at(p, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))))))) == True{} : Bool}
  bp.okb(Nat.is_lt(Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i), w, p, i, h_long, h_pos, h_full, hb0, {==})

def bp.gsafe_mis_h(b0: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == False{} : Bool}, +h_ig: {Nat.is_lt(i, M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))) == True{} : Bool}, +e0: {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == b0 : Bool}) -> {b0 == False{} : Bool}:
  match b0:
    case True{}:
      +e_g = bp.tab(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n, Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), bp.j_lt(w, p, h_pos))
      +h_ig2 = Equal.trans(Bool, Nat.is_lt(i, M.ts.bm.gs.least(List.length(&2, U32, p), p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), 1n)), Nat.is_lt(i, M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(i, n), M.ts.bm.gs.least(List.length(&2, U32, p), p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), Equal.sym(Nat, M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))), M.ts.bm.gs.least(List.length(&2, U32, p), p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), 1n), e_g)), h_ig)
      +nok = bp.least_nok(List.length(&2, U32, p), 1n, i, p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), L.tsl.lt_succ(List.length(&2, U32, p)), bp.pos_nlt1(i, h_i1), h_ig2)
      +yes = bp.okw(w, p, i, h_long, h_pos, h_full, e0)
      L.tsl.absurd(Bool, True{}, False{}, Equal.trans(Bool, False{}, M.ts.bm.gs.ok(p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i), True{}, Equal.sym(Bool, M.ts.bm.gs.ok(p, List.length(&2, U32, p), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))), i), False{}, nok), yes))
    case False{}:
      {==}

def bp.gsafe_mis(+w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == False{} : Bool}, +h_ig: {Nat.is_lt(i, M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  bp.gsafe_mis_h(V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)), w, p, i, h_long, h_pos, h_i1, h_full, h_ig, {==})

# Every skipped offset is safe

def bp.gsafe(e: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_full: {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == e : Bool}, +h_ig: {Nat.is_lt(i, M.ts.bm.pick(e, M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))))) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  match e:
    case True{}:
      bp.gsafe_full(w, p, i, h_long, h_i1, h_full, h_ig)
    case False{}:
      bp.gsafe_mis(w, p, i, h_long, h_pos, h_i1, h_full, h_ig)

def bp.hg(e: Bool, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_sh: {Nat.is_lt(i, Nat.max(M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))) == True{} : Bool}, +eh: {Nat.is_lt(i, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))) == e : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  match e:
    case True{}:
      bp.hsafe(w, p, i, h_pos, h_long, h_i1, eh)
    case False{}:
      bp.gsafe(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), w, p, i, h_long, h_pos, h_i1, {==}, bp.max_lt(M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))), i, h_sh, eh))

def bp.safe_long(rule: M.TsBmRule, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_is: {Nat.is_lt(i, Nat.max(M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))))), 1n)) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  match rule:
    case M.TsHorspool{}:
      bp.hsafe(w, p, i, h_pos, h_long, h_i1, bp.max1_lt(M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), i, h_i1, h_is))
    case M.TsGoodSuffix{}:
      bp.hg(Nat.is_lt(i, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n)))), w, p, i, h_long, h_pos, h_i1, bp.max1_lt(Nat.max(M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))))))), i, h_i1, h_is), {==})

def bp.safe_short(+w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_short: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  +h_d = L.tsl.lt_le_trans(Nat.sub(List.length(&2, U32, w), i), 1n+List.length(&2, U32, w), List.length(&2, U32, p), L.tsl.sub_le(List.length(&2, U32, w), i), h_short)
  bp.at_short(False{}, p, List.drop(&2, U32, w, i), Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, List.drop(&2, U32, w, i)), List.length(&2, U32, p)), Nat.is_lt(Nat.sub(List.length(&2, U32, w), i), List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, List.length(&2, U32, p)), List.length(&2, U32, List.drop(&2, U32, w, i)), Nat.sub(List.length(&2, U32, w), i), bp.len_drop(w, i)), h_d))

# The window's look: in a window of m bytes, the code's quantities are the
# ones above
def bp.look_long(+rule: M.TsBmRule, +w: List<&2, U32>, +p: List<&2, U32>, +h_long: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == False{} : Bool}) -> {M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))) == M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))} : M.TsBmLook}:
  +k0 = M.ts.bm.common(False{}, List.reverse(&2, U32, p), List.reverse(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))))
  +e_w = Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), Nat.is_eq(List.length(&2, U32, p), List.length(&2, U32, p)), True{}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, List.length(&2, U32, p)), List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p), bp.win_len(w, p, h_long)), L.tsl.nat_refl(List.length(&2, U32, p)))
  %Equal.sym(Nat, k0, bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), bp.cr(p, List.take(&2, U32, w, List.length(&2, U32, p)), bp.win_eq(w, p, h_long))) : {M.TsBmLook{Bool.and(Nat.is_eq(List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), Nat.is_eq(_, List.length(&2, U32, p))), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Bool.and(Nat.is_eq(List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), Nat.is_eq(_, List.length(&2, U32, p))), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), _))))} == M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))} : M.TsBmLook}
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), True{}, e_w) : {M.TsBmLook{Bool.and(_, Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p))), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Bool.and(_, Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p))), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))} == M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))} : M.TsBmLook}
  {==}

def bp.hit_h(e: Bool, +rule: M.TsBmRule, +w: List<&2, U32>, +p: List<&2, U32>, +es: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == e : Bool}) -> {M.ts.bm.hit(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p)))) == V.ts.naive.at(False{}, p, w) : Bool}:
  match e:
    case True{}:
      +e_len = bp.len_take_short(w, List.length(&2, U32, p), es)
      +e_f = Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), Nat.is_eq(List.length(&2, U32, w), List.length(&2, U32, p)), False{}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, List.length(&2, U32, p)), List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, w), e_len), L.tsl.lt_ne(List.length(&2, U32, w), List.length(&2, U32, p), es))
      %Equal.sym(Bool, V.ts.naive.at(False{}, p, w), False{}, bp.at_short(False{}, p, w, es)) : {M.ts.bm.hit(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p)))) == _ : Bool}
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), False{}, e_f) : {Bool.and(_, Nat.is_eq(M.ts.bm.common(False{}, List.reverse(&2, U32, p), List.reverse(&2, U32, List.take(&2, U32, w, List.length(&2, U32, p)))), List.length(&2, U32, p))) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(M.TsBmLook, M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))), M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))}, bp.look_long(rule, w, p, es)) : {M.ts.bm.hit(_) == V.ts.naive.at(False{}, p, w) : Bool}
      %bp.at_take_p(p, w) : {Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)) == _ : Bool}
      bp.cm(p, List.take(&2, U32, w, List.length(&2, U32, p)), bp.win_eq(w, p, es))

# the window's report is the reference's test
def bp.hit_ok(+rule: M.TsBmRule, +w: List<&2, U32>, +p: List<&2, U32>) -> {M.ts.bm.hit(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p)))) == V.ts.naive.at(False{}, p, w) : Bool}:
  bp.hit_h(Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)), rule, w, p, {==})

def bp.safe_h(e: Bool, +rule: M.TsBmRule, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_is: {Nat.is_lt(i, M.ts.bm.step(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))))) == True{} : Bool}, +es: {Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)) == e : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  match e:
    case True{}:
      bp.safe_short(w, p, i, es)
    case False{}:
      +h_is2 = Equal.trans(Bool, Nat.is_lt(i, M.ts.bm.step(M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))})), Nat.is_lt(i, M.ts.bm.step(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))))), True{}, Equal.cong(M.TsBmLook, Bool, l => Nat.is_lt(i, M.ts.bm.step(l)), M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))}, M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))), Equal.sym(M.TsBmLook, M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))), M.TsBmLook{Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.shift(rule, M.ts.bm.hs(p, List.length(&2, U32, p), M.ts.bm.at(List.take(&2, U32, w, List.length(&2, U32, p)), Nat.sub(List.length(&2, U32, p), 1n))), M.ts.bm.pick(Nat.is_eq(bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p))), List.length(&2, U32, p)), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n), M.ts.bm.nat_at(M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), Nat.sub(Nat.sub(List.length(&2, U32, p), 1n), bp.cmr(p, List.take(&2, U32, w, List.length(&2, U32, p)))))))}, bp.look_long(rule, w, p, es))), h_is)
      bp.safe_long(rule, w, p, i, h_pos, es, h_i1, h_is2)

# no offset 1 to the step minus one holds the pattern
def bp.safe(+rule: M.TsBmRule, +w: List<&2, U32>, +p: List<&2, U32>, +i: Nat, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_i1: {Nat.is_lt(0n, i) == True{} : Bool}, +h_is: {Nat.is_lt(i, M.ts.bm.step(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, w, List.length(&2, U32, p))))) == True{} : Bool}) -> {V.ts.naive.at(False{}, p, List.drop(&2, U32, w, i)) == False{} : Bool}:
  bp.safe_h(Nat.is_lt(List.length(&2, U32, w), List.length(&2, U32, p)), rule, w, p, i, h_pos, h_i1, h_is, {==})

# Skipping the safe offsets

# no offset among the first d of u holds the pattern
def bp.nm(d: Nat, +p: List<&2, U32>, +u: List<&2, U32>) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n+ +k:
      Bool.and(Bool.not(V.ts.naive.at(False{}, p, u)), bp.nm(k, p, List.tail(&2, U32, u)))

def bp.skip(d: Nat, u: List<&2, U32>, +p: List<&2, U32>, +m: Nat, +off: Nat, +h: {bp.nm(d, p, u) == True{} : Bool}) -> {V.ts.naive.go(False{}, p, m, u, off) == V.ts.naive.go(False{}, p, m, List.drop(&2, U32, u, d), Nat.add(off, d)) : List<&2, Nat>}:
  match d:
    case 0n:
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, u, 0n), u, bp.drop0(u)) : {V.ts.naive.go(False{}, p, m, u, off) == V.ts.naive.go(False{}, p, m, _, Nat.add(off, 0n)) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(off, 0n), off, UL.nat_add_zero(off)) : {V.ts.naive.go(False{}, p, m, u, off) == V.ts.naive.go(False{}, p, m, u, _) : List<&2, Nat>}
      {==}
    case 1n+ +k:
      match u:
        case Nil{}:
          {==}
        case Con{+y, +r}:
          +h_at = bp.not_true(V.ts.naive.at(False{}, p, Con{y, r}), L.tsl.and_l(Bool.not(V.ts.naive.at(False{}, p, Con{y, r})), bp.nm(k, p, r), h))
          %Equal.sym(Bool, V.ts.naive.at(False{}, p, Con{y, r}), False{}, h_at) : {V.ts.naive.hit(_, Nat.add(off, m), V.ts.naive.go(False{}, p, m, r, 1n+off)) == V.ts.naive.go(False{}, p, m, List.drop(&2, U32, r, k), Nat.add(off, 1n+k)) : List<&2, Nat>}
          %Equal.sym(Nat, Nat.add(off, 1n+k), 1n+Nat.add(off, k), UL.nat_add_succ(off, k)) : {V.ts.naive.go(False{}, p, m, r, 1n+off) == V.ts.naive.go(False{}, p, m, List.drop(&2, U32, r, k), _) : List<&2, Nat>}
          bp.skip(k, r, p, m, 1n+off, L.tsl.and_r(Bool.not(V.ts.naive.at(False{}, p, Con{y, r})), bp.nm(k, p, r), h))

# the offsets 1 + i0 to i0 + d of x then t are safe
def bp.nmb(d: Nat, +i0: Nat, +rule: M.TsBmRule, +x: U32, +t: List<&2, U32>, +p: List<&2, U32>, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_b: {Nat.is_lt(Nat.add(i0, d), M.ts.bm.step(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, Con{x, t}, List.length(&2, U32, p))))) == True{} : Bool}) -> {bp.nm(d, p, List.drop(&2, U32, t, i0)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +k:
      +S = M.ts.bm.step(M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, Con{x, t}, List.length(&2, U32, p))))
      +h_b2 = Equal.trans(Bool, Nat.is_lt(Nat.add(1n+i0, k), S), Nat.is_lt(Nat.add(i0, 1n+k), S), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, S), 1n+Nat.add(i0, k), Nat.add(i0, 1n+k), Equal.sym(Nat, Nat.add(i0, 1n+k), 1n+Nat.add(i0, k), UL.nat_add_succ(i0, k))), h_b)
      +h_at = bp.safe(rule, Con{x, t}, p, 1n+i0, h_pos, {==}, L.tsl.lt_add_l(1n+i0, k, S, h_b2))
      %Equal.sym(Bool, V.ts.naive.at(False{}, p, List.drop(&2, U32, t, i0)), False{}, h_at) : {Bool.and(Bool.not(_), bp.nm(k, p, List.tail(&2, U32, List.drop(&2, U32, t, i0)))) == True{} : Bool}
      %Equal.sym(List<&2, U32>, List.tail(&2, U32, List.drop(&2, U32, t, i0)), List.drop(&2, U32, t, 1n+i0), bp.drop_tail(t, i0)) : {bp.nm(k, p, _) == True{} : Bool}
      bp.nmb(k, 1n+i0, rule, x, t, p, h_pos, h_b2)

def bp.step_pos(l: M.TsBmLook) -> {Nat.is_lt(0n, M.ts.bm.step(l)) == True{} : Bool}:
  match l:
    case M.TsBmLook{h, +s}:
      bp.max1_pos(s)

def bp.emit_hit(+h: Bool, +e: Nat, +xs: List<&2, Nat>) -> {M.ts.bm.emit(h, e, xs) == V.ts.naive.hit(h, e, xs) : List<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# The scan, exactly: what the reference reports
def bp.main(f: Nat, w: List<&2, U32>, +off: Nat, +rule: M.TsBmRule, +p: List<&2, U32>, +h_pos: {Nat.is_lt(0n, List.length(&2, U32, p)) == True{} : Bool}, +h_f: {Nat.is_lt(List.length(&2, U32, w), f) == True{} : Bool}) -> {M.ts.bm.scan(f, M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, w, off) == V.ts.naive.go(False{}, p, List.length(&2, U32, p), w, off) : List<&2, Nat>}:
  match f:
    case 0n:
      L.tsl.lt_zero_abs(List<&2, Nat>, Nil{}, V.ts.naive.go(False{}, p, List.length(&2, U32, p), w, off), List.length(&2, U32, w), h_f)
    case 1n+ +g:
      match w:
        case Nil{}:
          {==}
        case Con{+x, +t}:
          +l = M.ts.bm.look(M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.take(&2, U32, Con{x, t}, List.length(&2, U32, p)))
          +S = M.ts.bm.step(l)
          +d = Nat.sub(S, 1n)
          +e_S = L.tsl.succ_pred(S, bp.step_pos(l))
          +h_hit = bp.hit_ok(rule, Con{x, t}, p)
          +h_dS = Equal.trans(Bool, Nat.is_lt(d, S), Nat.is_lt(d, 1n+d), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(d, n), S, 1n+d, Equal.sym(Nat, 1n+d, S, e_S)), L.tsl.lt_succ(d))
          +h_nm0 = bp.nmb(d, 0n, rule, x, t, p, h_pos, h_dS)
          +h_nm = Equal.trans(Bool, bp.nm(d, p, t), bp.nm(d, p, List.drop(&2, U32, t, 0n)), True{}, Equal.cong(List<&2, U32>, Bool, u => bp.nm(d, p, u), t, List.drop(&2, U32, t, 0n), Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, bp.drop0(t))), h_nm0)
          +h_skip = bp.skip(d, t, p, List.length(&2, U32, p), 1n+off, h_nm)
          +h_fl = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, List.drop(&2, U32, Con{x, t}, S)), g), Nat.is_lt(List.length(&2, U32, List.drop(&2, U32, t, d)), g), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(List.length(&2, U32, List.drop(&2, U32, Con{x, t}, n)), g), S, 1n+d, Equal.sym(Nat, 1n+d, S, e_S)), Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, List.drop(&2, U32, t, d)), g), Nat.is_lt(Nat.sub(List.length(&2, U32, t), d), g), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, g), List.length(&2, U32, List.drop(&2, U32, t, d)), Nat.sub(List.length(&2, U32, t), d), bp.len_drop(t, d)), L.tsl.lt_le_trans(Nat.sub(List.length(&2, U32, t), d), 1n+List.length(&2, U32, t), g, L.tsl.sub_le(List.length(&2, U32, t), d), h_f)))
          +E = Nat.add(off, List.length(&2, U32, p))
          %Equal.sym(List<&2, Nat>, M.ts.bm.scan(g, M.TsBmConf{False{}, rule, p, List.length(&2, U32, p), M.ts.bm.gs.table(List.length(&2, U32, p), p, List.length(&2, U32, p), 0n), M.ts.bm.gs.period(List.length(&2, U32, p), p, List.length(&2, U32, p), 1n)}, List.drop(&2, U32, Con{x, t}, S), Nat.add(off, S)), V.ts.naive.go(False{}, p, List.length(&2, U32, p), List.drop(&2, U32, Con{x, t}, S), Nat.add(off, S)), bp.main(g, List.drop(&2, U32, Con{x, t}, S), Nat.add(off, S), rule, p, h_pos, h_fl)) : {M.ts.bm.emit(M.ts.bm.hit(l), E, _) == V.ts.naive.go(False{}, p, List.length(&2, U32, p), Con{x, t}, off) : List<&2, Nat>}
          %e_S : {M.ts.bm.emit(M.ts.bm.hit(l), E, V.ts.naive.go(False{}, p, List.length(&2, U32, p), List.drop(&2, U32, Con{x, t}, _), Nat.add(off, _))) == V.ts.naive.go(False{}, p, List.length(&2, U32, p), Con{x, t}, off) : List<&2, Nat>}
          %Equal.sym(Nat, Nat.add(off, 1n+d), 1n+Nat.add(off, d), UL.nat_add_succ(off, d)) : {M.ts.bm.emit(M.ts.bm.hit(l), E, V.ts.naive.go(False{}, p, List.length(&2, U32, p), List.drop(&2, U32, t, d), _)) == V.ts.naive.go(False{}, p, List.length(&2, U32, p), Con{x, t}, off) : List<&2, Nat>}
          %h_skip : {M.ts.bm.emit(M.ts.bm.hit(l), E, _) == V.ts.naive.go(False{}, p, List.length(&2, U32, p), Con{x, t}, off) : List<&2, Nat>}
          %Equal.sym(Bool, M.ts.bm.hit(l), V.ts.naive.at(False{}, p, Con{x, t}), h_hit) : {M.ts.bm.emit(_, E, V.ts.naive.go(False{}, p, List.length(&2, U32, p), t, 1n+off)) == V.ts.naive.go(False{}, p, List.length(&2, U32, p), Con{x, t}, off) : List<&2, Nat>}
          bp.emit_hit(V.ts.naive.at(False{}, p, Con{x, t}), E, V.ts.naive.go(False{}, p, List.length(&2, U32, p), t, 1n+off))

# Ignoring case: the exact search of the folded pattern in the folded text

def bp.take_fold(+icase: Bool, w: List<&2, U32>, n: Nat) -> {List.take(&2, U32, T.ts.fold_all(icase, w), n) == T.ts.fold_all(icase, List.take(&2, U32, w, n)) : List<&2, U32>}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match n:
        case 0n:
          {==}
        case 1n+ +k:
          %bp.take_fold(icase, r, k) : {Con{T.ts.fold(icase, x), List.take(&2, U32, T.ts.fold_all(icase, r), k)} == Con{T.ts.fold(icase, x), _} : List<&2, U32>}
          {==}

def bp.drop_fold(+icase: Bool, w: List<&2, U32>, n: Nat) -> {List.drop(&2, U32, T.ts.fold_all(icase, w), n) == T.ts.fold_all(icase, List.drop(&2, U32, w, n)) : List<&2, U32>}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match n:
        case 0n:
          {==}
        case 1n+ +k:
          bp.drop_fold(icase, r, k)

def bp.revgo_fold(+icase: Bool, xs: List<&2, U32>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, T.ts.fold_all(icase, xs), T.ts.fold_all(icase, acc)) == T.ts.fold_all(icase, List.reverse.go(&2, U32, xs, acc)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      bp.revgo_fold(icase, t, Con{x, acc})

def bp.rev_fold(+icase: Bool, +xs: List<&2, U32>) -> {List.reverse(&2, U32, T.ts.fold_all(icase, xs)) == T.ts.fold_all(icase, List.reverse(&2, U32, xs)) : List<&2, U32>}:
  bp.revgo_fold(icase, xs, Nil{})

def bp.common_fold(+icase: Bool, a: List<&2, U32>, y: List<&2, U32>) -> {M.ts.bm.common(False{}, a, T.ts.fold_all(icase, y)) == M.ts.bm.common(icase, a, y) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+c, +at}:
      match y:
        case Nil{}:
          {==}
        case Con{+b, +bt}:
          %bp.common_fold(icase, at, bt) : {M.ts.bm.pick(U32.is_eq(c, T.ts.fold(icase, b)), 1n+M.ts.bm.common(False{}, at, T.ts.fold_all(icase, bt)), 0n) == M.ts.bm.pick(U32.is_eq(c, T.ts.fold(icase, b)), 1n+_, 0n) : Nat}
          {==}

def bp.fold0(+icase: Bool) -> {T.ts.fold(icase, 0) == 0 : U32}:
  match icase:
    case True{}:
      {==}
    case False{}:
      {==}

def bp.at_fold(+icase: Bool, x: List<&2, U32>, u: Nat) -> {M.ts.bm.at(T.ts.fold_all(icase, x), u) == T.ts.fold(icase, M.ts.bm.at(x, u)) : U32}:
  match x:
    case Nil{}:
      Equal.sym(U32, T.ts.fold(icase, 0), 0, bp.fold0(icase))
    case Con{+c, +r}:
      match u:
        case 0n:
          {==}
        case 1n+ +v:
          bp.at_fold(icase, r, v)

def bp.look_conv(+icase: Bool, +rule: M.TsBmRule, +q: List<&2, U32>, +m: Nat, +gs: List<&2, Nat>, +gsm: Nat, +x: List<&2, U32>) -> {M.ts.bm.look(M.TsBmConf{False{}, rule, q, m, gs, gsm}, T.ts.fold_all(icase, x)) == M.ts.bm.look(M.TsBmConf{icase, rule, q, m, gs, gsm}, x) : M.TsBmLook}:
  +c = Nat.sub(m, 1n)
  +RHS = M.ts.bm.look(M.TsBmConf{icase, rule, q, m, gs, gsm}, x)
  +k1 = M.ts.bm.common(icase, List.reverse(&2, U32, q), List.reverse(&2, U32, x))
  %Equal.sym(Nat, List.length(&2, U32, T.ts.fold_all(icase, x)), List.length(&2, U32, x), L.tsl.fold_len(icase, x)) : {M.TsBmLook{Bool.and(Nat.is_eq(_, m), Nat.is_eq(M.ts.bm.common(False{}, List.reverse(&2, U32, q), List.reverse(&2, U32, T.ts.fold_all(icase, x))), m)), M.ts.bm.shift(rule, M.ts.bm.hs(q, m, M.ts.bm.at(T.ts.fold_all(icase, x), c)), M.ts.bm.pick(Bool.and(Nat.is_eq(_, m), Nat.is_eq(M.ts.bm.common(False{}, List.reverse(&2, U32, q), List.reverse(&2, U32, T.ts.fold_all(icase, x))), m)), gsm, M.ts.bm.nat_at(gs, Nat.sub(c, M.ts.bm.common(False{}, List.reverse(&2, U32, q), List.reverse(&2, U32, T.ts.fold_all(icase, x)))))))} == RHS : M.TsBmLook}
  %Equal.sym(List<&2, U32>, List.reverse(&2, U32, T.ts.fold_all(icase, x)), T.ts.fold_all(icase, List.reverse(&2, U32, x)), bp.rev_fold(icase, x)) : {M.TsBmLook{Bool.and(Nat.is_eq(List.length(&2, U32, x), m), Nat.is_eq(M.ts.bm.common(False{}, List.reverse(&2, U32, q), _), m)), M.ts.bm.shift(rule, M.ts.bm.hs(q, m, M.ts.bm.at(T.ts.fold_all(icase, x), c)), M.ts.bm.pick(Bool.and(Nat.is_eq(List.length(&2, U32, x), m), Nat.is_eq(M.ts.bm.common(False{}, List.reverse(&2, U32, q), _), m)), gsm, M.ts.bm.nat_at(gs, Nat.sub(c, M.ts.bm.common(False{}, List.reverse(&2, U32, q), _)))))} == RHS : M.TsBmLook}
  %Equal.sym(Nat, M.ts.bm.common(False{}, List.reverse(&2, U32, q), T.ts.fold_all(icase, List.reverse(&2, U32, x))), k1, bp.common_fold(icase, List.reverse(&2, U32, q), List.reverse(&2, U32, x))) : {M.TsBmLook{Bool.and(Nat.is_eq(List.length(&2, U32, x), m), Nat.is_eq(_, m)), M.ts.bm.shift(rule, M.ts.bm.hs(q, m, M.ts.bm.at(T.ts.fold_all(icase, x), c)), M.ts.bm.pick(Bool.and(Nat.is_eq(List.length(&2, U32, x), m), Nat.is_eq(_, m)), gsm, M.ts.bm.nat_at(gs, Nat.sub(c, _))))} == RHS : M.TsBmLook}
  %Equal.sym(U32, M.ts.bm.at(T.ts.fold_all(icase, x), c), T.ts.fold(icase, M.ts.bm.at(x, c)), bp.at_fold(icase, x, c)) : {M.TsBmLook{Bool.and(Nat.is_eq(List.length(&2, U32, x), m), Nat.is_eq(k1, m)), M.ts.bm.shift(rule, M.ts.bm.hs(q, m, _), M.ts.bm.pick(Bool.and(Nat.is_eq(List.length(&2, U32, x), m), Nat.is_eq(k1, m)), gsm, M.ts.bm.nat_at(gs, Nat.sub(c, k1))))} == RHS : M.TsBmLook}
  {==}

def bp.conv(f: Nat, w: List<&2, U32>, +off: Nat, +icase: Bool, +rule: M.TsBmRule, +q: List<&2, U32>, +m: Nat, +gs: List<&2, Nat>, +gsm: Nat) -> {M.ts.bm.scan(f, M.TsBmConf{icase, rule, q, m, gs, gsm}, w, off) == M.ts.bm.scan(f, M.TsBmConf{False{}, rule, q, m, gs, gsm}, T.ts.fold_all(icase, w), off) : List<&2, Nat>}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      match w:
        case Nil{}:
          {==}
        case Con{+x, +t}:
          +Ci : M.TsBmConf = M.TsBmConf{icase, rule, q, m, gs, gsm}
          +C0 : M.TsBmConf = M.TsBmConf{False{}, rule, q, m, gs, gsm}
          +X = List.take(&2, U32, Con{x, t}, m)
          +L1 = M.ts.bm.look(Ci, X)
          +FW = T.ts.fold_all(icase, Con{x, t})
          +LHS = M.ts.bm.emit(M.ts.bm.hit(L1), Nat.add(off, m), M.ts.bm.scan(g, Ci, List.drop(&2, U32, Con{x, t}, M.ts.bm.step(L1)), Nat.add(off, M.ts.bm.step(L1))))
          %Equal.sym(List<&2, U32>, List.take(&2, U32, FW, m), T.ts.fold_all(icase, X), bp.take_fold(icase, Con{x, t}, m)) : {LHS == M.ts.bm.emit(M.ts.bm.hit(M.ts.bm.look(C0, _)), Nat.add(off, m), M.ts.bm.scan(g, C0, List.drop(&2, U32, FW, M.ts.bm.step(M.ts.bm.look(C0, _))), Nat.add(off, M.ts.bm.step(M.ts.bm.look(C0, _))))) : List<&2, Nat>}
          %Equal.sym(M.TsBmLook, M.ts.bm.look(C0, T.ts.fold_all(icase, X)), L1, bp.look_conv(icase, rule, q, m, gs, gsm, X)) : {LHS == M.ts.bm.emit(M.ts.bm.hit(_), Nat.add(off, m), M.ts.bm.scan(g, C0, List.drop(&2, U32, FW, M.ts.bm.step(_)), Nat.add(off, M.ts.bm.step(_)))) : List<&2, Nat>}
          %Equal.sym(List<&2, U32>, List.drop(&2, U32, FW, M.ts.bm.step(L1)), T.ts.fold_all(icase, List.drop(&2, U32, Con{x, t}, M.ts.bm.step(L1))), bp.drop_fold(icase, Con{x, t}, M.ts.bm.step(L1))) : {LHS == M.ts.bm.emit(M.ts.bm.hit(L1), Nat.add(off, m), M.ts.bm.scan(g, C0, _, Nat.add(off, M.ts.bm.step(L1)))) : List<&2, Nat>}
          %bp.conv(g, List.drop(&2, U32, Con{x, t}, M.ts.bm.step(L1)), Nat.add(off, M.ts.bm.step(L1)), icase, rule, q, m, gs, gsm) : {LHS == M.ts.bm.emit(M.ts.bm.hit(L1), Nat.add(off, m), _) : List<&2, Nat>}
          {==}

# The law

def bp.ref(+icase: Bool, +rule: M.TsBmRule, p: List<&2, U32>, +xs: List<&2, U32>) -> {M.ts.bm.ends(icase, rule, p, xs) == V.ts.naive.ends(icase, p, xs) : List<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      +fp : List<&2, U32> = Con{T.ts.fold(icase, a), T.ts.fold_all(icase, t)}
      +n : Nat = 1n+List.length(&2, U32, xs)
      +GS = M.ts.bm.gs.table(List.length(&2, U32, fp), fp, List.length(&2, U32, fp), 0n)
      +GSM = M.ts.bm.gs.period(List.length(&2, U32, fp), fp, List.length(&2, U32, fp), 1n)
      +fxs = T.ts.fold_all(icase, xs)
      +h_f = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, fxs), n), Nat.is_lt(List.length(&2, U32, xs), n), True{}, Equal.cong(Nat, Bool, k => Nat.is_lt(k, n), List.length(&2, U32, fxs), List.length(&2, U32, xs), L.tsl.fold_len(icase, xs)), L.tsl.lt_succ(List.length(&2, U32, xs)))
      +e1 = bp.conv(n, xs, 0n, icase, rule, fp, List.length(&2, U32, fp), GS, GSM)
      +e2 = bp.main(n, fxs, 0n, rule, fp, {==}, h_f)
      +e3 = Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, Con{a, t}, List.length(&2, U32, fp), xs, 0n), V.ts.naive.go(False{}, fp, List.length(&2, U32, fp), fxs, 0n), L.tsl.go_fold(icase, Con{a, t}, List.length(&2, U32, fp), xs, 0n))
      %L.tsl.fold_len(icase, t) : {M.ts.bm.ends(icase, rule, Con{a, t}, xs) == V.ts.naive.go(icase, Con{a, t}, 1n+_, xs, 0n) : List<&2, Nat>}
      Equal.trans(List<&2, Nat>, M.ts.bm.scan(n, M.TsBmConf{icase, rule, fp, List.length(&2, U32, fp), GS, GSM}, xs, 0n), M.ts.bm.scan(n, M.TsBmConf{False{}, rule, fp, List.length(&2, U32, fp), GS, GSM}, fxs, 0n), V.ts.naive.go(icase, Con{a, t}, List.length(&2, U32, fp), xs, 0n), e1, Equal.trans(List<&2, Nat>, M.ts.bm.scan(n, M.TsBmConf{False{}, rule, fp, List.length(&2, U32, fp), GS, GSM}, fxs, 0n), V.ts.naive.go(False{}, fp, List.length(&2, U32, fp), fxs, 0n), V.ts.naive.go(icase, Con{a, t}, List.length(&2, U32, fp), xs, 0n), e2, e3))

def Laws.bm_ref(icase, rule, p, xs):
  bp.ref(icase, rule, p, xs)

# Chunks

def bp.lt_dec(+a: Nat, +b: Nat, +h: {Nat.is_lt(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match b:
    case 0n:
      L.tsl.absurd(Bool, Nat.is_lt(a, 0n), True{}, h)
    case 1n+ +c:
      L.tsl.lt_weak(a, c, h)

def bp.nat_app_nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %bp.nat_app_nil(t) : {Con{h, List.append(&2, U32, t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def bp.len_app(xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %bp.len_app(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

def bp.add_sub_cancel(+b: Nat, +l: Nat) -> {Nat.sub(Nat.add(b, l), l) == b : Nat}:
  match l:
    case 0n:
      %Equal.sym(Nat, Nat.add(b, 0n), b, UL.nat_add_zero(b)) : {Nat.sub(_, 0n) == b : Nat}
      L.tsl.sub_zero(b)
    case 1n+ +k:
      %Equal.sym(Nat, Nat.add(b, 1n+k), 1n+Nat.add(b, k), UL.nat_add_succ(b, k)) : {Nat.sub(_, 1n+k) == b : Nat}
      bp.add_sub_cancel(b, k)

def bp.sub_sub_le(+n: Nat, +k: Nat) -> {Nat.is_lt(Nat.sub(n, Nat.sub(n, k)), 1n+k) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +a:
      match k:
        case 0n:
          %Equal.sym(Nat, Nat.sub(a, a), 0n, L.tsl.sub_self(a)) : {Nat.is_lt(_, 1n) == True{} : Bool}
          {==}
        case 1n+ +b:
          %Equal.sym(Nat, Nat.sub(1n+a, Nat.sub(a, b)), 1n+Nat.sub(a, Nat.sub(a, b)), L.tsl.sub_succ_le(a, Nat.sub(a, b), L.tsl.sub_le(a, b))) : {Nat.is_lt(_, 2n+b) == True{} : Bool}
          bp.sub_sub_le(a, b)

def bp.sub_le0(+n: Nat, +k: Nat, +h: {Nat.is_lt(k, n) == False{} : Bool}) -> {Nat.sub(n, k) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +a:
      match k:
        case 0n:
          L.tsl.absurd_tf(Nat, 1n+a, 0n, h)
        case 1n+ +b:
          bp.sub_le0(a, b, h)

# the reference over a text too short for the pattern: nothing
def bp.go_short(+icase: Bool, +q: List<&2, U32>, +mm: Nat, b: List<&2, U32>, +base: Nat, +h: {Nat.is_lt(List.length(&2, U32, b), List.length(&2, U32, q)) == True{} : Bool}) -> {V.ts.naive.go(icase, q, mm, b, base) == Nil{} : List<&2, Nat>}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %Equal.sym(Bool, V.ts.naive.at(icase, q, Con{y, r}), False{}, bp.at_short(icase, q, Con{y, r}, h)) : {V.ts.naive.hit(_, Nat.add(base, mm), V.ts.naive.go(icase, q, mm, r, 1n+base)) == Nil{} : List<&2, Nat>}
      bp.go_short(icase, q, mm, r, 1n+base, bp.lt_dec(List.length(&2, U32, r), List.length(&2, U32, q), h))

def bp.ns_h(e: Bool, +y: U32, +bt: List<&2, U32>, +r: List<&2, U32>, +base: Nat, +icase: Bool, +q: List<&2, U32>, +mm: Nat, +k: Nat, +h_k: {List.length(&2, U32, q) == 1n+k : Nat}, +ek: {Nat.is_lt(k, 1n+List.length(&2, U32, bt)) == e : Bool}, rec: @base2:Nat -> {V.ts.naive.go(icase, q, mm, List.append(&2, U32, bt, r), base2) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, bt, base2), V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, bt, Nat.sub(List.length(&2, U32, bt), k)), r), Nat.add(base2, Nat.sub(List.length(&2, U32, bt), k)))) : List<&2, Nat>}) -> {V.ts.naive.go(icase, q, mm, List.append(&2, U32, Con{y, bt}, r), base) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, Con{y, bt}, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, Con{y, bt}, Nat.sub(List.length(&2, U32, Con{y, bt}), k)), r), Nat.add(base, Nat.sub(List.length(&2, U32, Con{y, bt}), k)))) : List<&2, Nat>}:
  match e:
    case False{}:
      +b : List<&2, U32> = Con{y, bt}
      +h_s = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, b), List.length(&2, U32, q)), Nat.is_lt(List.length(&2, U32, b), 1n+k), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(List.length(&2, U32, b), n), List.length(&2, U32, q), 1n+k, h_k), L.tsl.nlt_le(k, List.length(&2, U32, b), ek))
      %Equal.sym(Nat, Nat.sub(List.length(&2, U32, b), k), 0n, bp.sub_le0(List.length(&2, U32, b), k, L.tsl.le_nlt(List.length(&2, U32, b), k, L.tsl.nlt_le(k, List.length(&2, U32, b), ek)))) : {V.ts.naive.go(icase, q, mm, List.append(&2, U32, b, r), base) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, b, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, b, _), r), Nat.add(base, _))) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(base, 0n), base, UL.nat_add_zero(base)) : {V.ts.naive.go(icase, q, mm, List.append(&2, U32, b, r), base) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, b, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, b, r), _)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, q, mm, b, base), Nil{}, bp.go_short(icase, q, mm, b, base, h_s)) : {V.ts.naive.go(icase, q, mm, List.append(&2, U32, b, r), base) == List.append(&2, Nat, _, V.ts.naive.go(icase, q, mm, List.append(&2, U32, b, r), base)) : List<&2, Nat>}
      {==}
    case True{}:
      +l = List.length(&2, U32, bt)
      +d = Nat.sub(l, k)
      +e_d = L.tsl.sub_succ_le(l, k, ek)
      +h_lq = Equal.trans(Bool, Nat.is_lt(1n+l, List.length(&2, U32, q)), Nat.is_lt(1n+l, 1n+k), False{}, Equal.cong(Nat, Bool, n => Nat.is_lt(1n+l, n), List.length(&2, U32, q), 1n+k, h_k), L.tsl.le_nlt(k, l, ek))
      +e_at = bp.at_app(icase, q, Con{y, bt}, r, h_lq)
      +X = V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, bt, d), r), Nat.add(1n+base, d))
      %Equal.sym(Nat, Nat.sub(1n+l, k), 1n+d, e_d) : {V.ts.naive.go(icase, q, mm, List.append(&2, U32, Con{y, bt}, r), base) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, Con{y, bt}, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, Con{y, bt}, _), r), Nat.add(base, _))) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(base, 1n+d), 1n+Nat.add(base, d), UL.nat_add_succ(base, d)) : {V.ts.naive.go(icase, q, mm, List.append(&2, U32, Con{y, bt}, r), base) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, Con{y, bt}, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, bt, d), r), _)) : List<&2, Nat>}
      %Equal.sym(Bool, V.ts.naive.at(icase, q, List.append(&2, U32, Con{y, bt}, r)), V.ts.naive.at(icase, q, Con{y, bt}), e_at) : {V.ts.naive.hit(_, Nat.add(base, mm), V.ts.naive.go(icase, q, mm, List.append(&2, U32, bt, r), 1n+base)) == List.append(&2, Nat, V.ts.naive.hit(V.ts.naive.at(icase, q, Con{y, bt}), Nat.add(base, mm), V.ts.naive.go(icase, q, mm, bt, 1n+base)), X) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, q, mm, List.append(&2, U32, bt, r), 1n+base), List.append(&2, Nat, V.ts.naive.go(icase, q, mm, bt, 1n+base), X), rec(1n+base)) : {V.ts.naive.hit(V.ts.naive.at(icase, q, Con{y, bt}), Nat.add(base, mm), _) == List.append(&2, Nat, V.ts.naive.hit(V.ts.naive.at(icase, q, Con{y, bt}), Nat.add(base, mm), V.ts.naive.go(icase, q, mm, bt, 1n+base)), X) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, V.ts.naive.hit(V.ts.naive.at(icase, q, Con{y, bt}), Nat.add(base, mm), V.ts.naive.go(icase, q, mm, bt, 1n+base)), X), V.ts.naive.hit(V.ts.naive.at(icase, q, Con{y, bt}), Nat.add(base, mm), List.append(&2, Nat, V.ts.naive.go(icase, q, mm, bt, 1n+base), X)), L.tsl.hit_app(V.ts.naive.at(icase, q, Con{y, bt}), Nat.add(base, mm), V.ts.naive.go(icase, q, mm, bt, 1n+base), X))

# the reference over b then r: the matches inside b, then those starting in
# the last k bytes of b or later (k: the pattern length minus one)
def bp.ns(b: List<&2, U32>, +r: List<&2, U32>, +base: Nat, +icase: Bool, +q: List<&2, U32>, +mm: Nat, +k: Nat, +h_k: {List.length(&2, U32, q) == 1n+k : Nat}) -> {V.ts.naive.go(icase, q, mm, List.append(&2, U32, b, r), base) == List.append(&2, Nat, V.ts.naive.go(icase, q, mm, b, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, List.drop(&2, U32, b, Nat.sub(List.length(&2, U32, b), k)), r), Nat.add(base, Nat.sub(List.length(&2, U32, b), k)))) : List<&2, Nat>}:
  match b:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(base, 0n), base, UL.nat_add_zero(base)) : {V.ts.naive.go(icase, q, mm, r, base) == V.ts.naive.go(icase, q, mm, r, _) : List<&2, Nat>}
      {==}
    case Con{+y, +bt}:
      bp.ns_h(Nat.is_lt(k, 1n+List.length(&2, U32, bt)), y, bt, r, base, icase, q, mm, k, h_k, {==}, base2 => bp.ns(bt, r, base2, icase, q, mm, k, h_k))

# A chunk's scan, ignoring case or not: the reference's matches in it
def bp.scan_ref(+icase: Bool, +rule: M.TsBmRule, +a: U32, +t: List<&2, U32>, +buf: List<&2, U32>, +base: Nat) -> {M.ts.bm.scan(1n+List.length(&2, U32, buf), M.ts.bm.conf(icase, rule, Con{a, t}), buf, base) == V.ts.naive.go(icase, Con{a, t}, 1n+List.length(&2, U32, T.ts.fold_all(icase, t)), buf, base) : List<&2, Nat>}:
  +fp : List<&2, U32> = Con{T.ts.fold(icase, a), T.ts.fold_all(icase, t)}
  +n : Nat = 1n+List.length(&2, U32, buf)
  +GS = M.ts.bm.gs.table(List.length(&2, U32, fp), fp, List.length(&2, U32, fp), 0n)
  +GSM = M.ts.bm.gs.period(List.length(&2, U32, fp), fp, List.length(&2, U32, fp), 1n)
  +fb = T.ts.fold_all(icase, buf)
  +h_f = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, fb), n), Nat.is_lt(List.length(&2, U32, buf), n), True{}, Equal.cong(Nat, Bool, k => Nat.is_lt(k, n), List.length(&2, U32, fb), List.length(&2, U32, buf), L.tsl.fold_len(icase, buf)), L.tsl.lt_succ(List.length(&2, U32, buf)))
  Equal.trans(List<&2, Nat>, M.ts.bm.scan(n, M.TsBmConf{icase, rule, fp, List.length(&2, U32, fp), GS, GSM}, buf, base), M.ts.bm.scan(n, M.TsBmConf{False{}, rule, fp, List.length(&2, U32, fp), GS, GSM}, fb, base), V.ts.naive.go(icase, Con{a, t}, List.length(&2, U32, fp), buf, base), bp.conv(n, buf, base, icase, rule, fp, List.length(&2, U32, fp), GS, GSM), Equal.trans(List<&2, Nat>, M.ts.bm.scan(n, M.TsBmConf{False{}, rule, fp, List.length(&2, U32, fp), GS, GSM}, fb, base), V.ts.naive.go(False{}, fp, List.length(&2, U32, fp), fb, base), V.ts.naive.go(icase, Con{a, t}, List.length(&2, U32, fp), buf, base), bp.main(n, fb, base, rule, fp, {==}, h_f), Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, Con{a, t}, List.length(&2, U32, fp), buf, base), V.ts.naive.go(False{}, fp, List.length(&2, U32, fp), fb, base), L.tsl.go_fold(icase, Con{a, t}, List.length(&2, U32, fp), buf, base))))

def bp.e_pos(+base: Nat, +c: List<&2, U32>, +xs: List<&2, U32>, +k: Nat) -> {Nat.add(Nat.add(base, List.length(&2, U32, c)), List.length(&2, U32, xs)) == Nat.add(Nat.add(base, Nat.sub(List.length(&2, U32, List.append(&2, U32, c, xs)), k)), List.length(&2, U32, List.drop(&2, U32, List.append(&2, U32, c, xs), Nat.sub(List.length(&2, U32, List.append(&2, U32, c, xs)), k)))) : Nat}:
  +buf = List.append(&2, U32, c, xs)
  +n = List.length(&2, U32, buf)
  +d = Nat.sub(n, k)
  %Equal.sym(Nat, Nat.add(Nat.add(base, List.length(&2, U32, c)), List.length(&2, U32, xs)), Nat.add(base, Nat.add(List.length(&2, U32, c), List.length(&2, U32, xs))), UL.nat_add_assoc(base, List.length(&2, U32, c), List.length(&2, U32, xs))) : {_ == Nat.add(Nat.add(base, d), List.length(&2, U32, List.drop(&2, U32, buf, d))) : Nat}
  %bp.len_app(c, xs) : {Nat.add(base, _) == Nat.add(Nat.add(base, d), List.length(&2, U32, List.drop(&2, U32, buf, d))) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, buf, d)), Nat.sub(n, d), bp.len_drop(buf, d)) : {Nat.add(base, n) == Nat.add(Nat.add(base, d), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(base, d), Nat.sub(n, d)), Nat.add(base, Nat.add(d, Nat.sub(n, d))), UL.nat_add_assoc(base, d, Nat.sub(n, d))) : {Nat.add(base, n) == _ : Nat}
  %Equal.sym(Nat, Nat.add(d, Nat.sub(n, d)), n, L.tsl.add_sub(d, n, L.tsl.sub_le(n, k))) : {Nat.add(base, n) == Nat.add(base, _) : Nat}
  {==}

# The chunked search, with the bytes kept from before: what the reference
# finds in them and the chunks
def bp.rg(cs: List<&2, List<&2, U32>>, +carry: List<&2, U32>, +base: Nat, +ms: List<&2, Nat>, +icase: Bool, +rule: M.TsBmRule, +a: U32, +t: List<&2, U32>, +h_c: {Nat.is_lt(List.length(&2, U32, carry), 1n+List.length(&2, U32, T.ts.fold_all(icase, t))) == True{} : Bool}) -> {T.ts.run.go(~M.TsBm, ~M.ts.bm.feed, cs, Nat.add(base, List.length(&2, U32, carry)), (M.TsBm{M.ts.bm.conf(icase, rule, Con{a, t}), carry}, ms)) == List.append(&2, Nat, ms, V.ts.naive.go(icase, Con{a, t}, 1n+List.length(&2, U32, T.ts.fold_all(icase, t)), List.append(&2, U32, carry, T.ts.concat(cs)), base)) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      +k = List.length(&2, U32, T.ts.fold_all(icase, t))
      +q : List<&2, U32> = Con{a, t}
      +mm : Nat = 1n+k
      +h_cq = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, carry), 1n+List.length(&2, U32, t)), Nat.is_lt(List.length(&2, U32, carry), 1n+k), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(List.length(&2, U32, carry), 1n+n), List.length(&2, U32, t), k, Equal.sym(Nat, k, List.length(&2, U32, t), L.tsl.fold_len(icase, t))), h_c)
      %Equal.sym(List<&2, U32>, List.append(&2, U32, carry, Nil{}), carry, bp.nat_app_nil(carry)) : {ms == List.append(&2, Nat, ms, V.ts.naive.go(icase, q, mm, _, base)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, q, mm, carry, base), Nil{}, bp.go_short(icase, q, mm, carry, base, h_cq)) : {ms == List.append(&2, Nat, ms, _) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, ms, Nil{}), ms, L.tsl.app_nil(ms))
    case Con{+xs, +rest}:
      +k = List.length(&2, U32, T.ts.fold_all(icase, t))
      +q : List<&2, U32> = Con{a, t}
      +mm : Nat = 1n+k
      +buf = List.append(&2, U32, carry, xs)
      +n = List.length(&2, U32, buf)
      +d = Nat.sub(n, k)
      +c2 = List.drop(&2, U32, buf, d)
      +b2 = Nat.add(base, d)
      +sc = M.ts.bm.scan(1n+n, M.ts.bm.conf(icase, rule, q), buf, base)
      +R = T.ts.concat(rest)
      +h_c2 = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, c2), 1n+k), Nat.is_lt(Nat.sub(n, d), 1n+k), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+k), List.length(&2, U32, c2), Nat.sub(n, d), bp.len_drop(buf, d)), bp.sub_sub_le(n, k))
      +ih = bp.rg(rest, c2, b2, sc, icase, rule, a, t, h_c2)
      %Equal.sym(Nat, Nat.sub(Nat.add(base, List.length(&2, U32, carry)), List.length(&2, U32, carry)), base, bp.add_sub_cancel(base, List.length(&2, U32, carry))) : {List.append(&2, Nat, ms, T.ts.run.go(~M.TsBm, ~M.ts.bm.feed, rest, Nat.add(Nat.add(base, List.length(&2, U32, carry)), List.length(&2, U32, xs)), (M.TsBm{M.ts.bm.conf(icase, rule, q), c2}, M.ts.bm.scan(1n+n, M.ts.bm.conf(icase, rule, q), buf, _)))) == List.append(&2, Nat, ms, V.ts.naive.go(icase, q, mm, List.append(&2, U32, carry, List.append(&2, U32, xs, R)), base)) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(Nat.add(base, List.length(&2, U32, carry)), List.length(&2, U32, xs)), Nat.add(b2, List.length(&2, U32, c2)), bp.e_pos(base, carry, xs, k)) : {List.append(&2, Nat, ms, T.ts.run.go(~M.TsBm, ~M.ts.bm.feed, rest, _, (M.TsBm{M.ts.bm.conf(icase, rule, q), c2}, sc))) == List.append(&2, Nat, ms, V.ts.naive.go(icase, q, mm, List.append(&2, U32, carry, List.append(&2, U32, xs, R)), base)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, T.ts.run.go(~M.TsBm, ~M.ts.bm.feed, rest, Nat.add(b2, List.length(&2, U32, c2)), (M.TsBm{M.ts.bm.conf(icase, rule, q), c2}, sc)), List.append(&2, Nat, sc, V.ts.naive.go(icase, q, mm, List.append(&2, U32, c2, R), b2)), ih) : {List.append(&2, Nat, ms, _) == List.append(&2, Nat, ms, V.ts.naive.go(icase, q, mm, List.append(&2, U32, carry, List.append(&2, U32, xs, R)), base)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, sc, V.ts.naive.go(icase, q, mm, buf, base), bp.scan_ref(icase, rule, a, t, buf, base)) : {List.append(&2, Nat, ms, List.append(&2, Nat, _, V.ts.naive.go(icase, q, mm, List.append(&2, U32, c2, R), b2))) == List.append(&2, Nat, ms, V.ts.naive.go(icase, q, mm, List.append(&2, U32, carry, List.append(&2, U32, xs, R)), base)) : List<&2, Nat>}
      %bp.app_assoc(carry, xs, R) : {List.append(&2, Nat, ms, List.append(&2, Nat, V.ts.naive.go(icase, q, mm, buf, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, c2, R), b2))) == List.append(&2, Nat, ms, V.ts.naive.go(icase, q, mm, _, base)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, q, mm, List.append(&2, U32, buf, R), base), List.append(&2, Nat, V.ts.naive.go(icase, q, mm, buf, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, c2, R), b2)), bp.ns(buf, R, base, icase, q, mm, k, Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, U32, t), k, Equal.sym(Nat, k, List.length(&2, U32, t), L.tsl.fold_len(icase, t))))) : {List.append(&2, Nat, ms, List.append(&2, Nat, V.ts.naive.go(icase, q, mm, buf, base), V.ts.naive.go(icase, q, mm, List.append(&2, U32, c2, R), b2))) == List.append(&2, Nat, ms, _) : List<&2, Nat>}
      {==}

# an empty pattern: no match in any chunk
def bp.rg0(cs: List<&2, List<&2, U32>>, +pos: Nat, +ms: List<&2, Nat>, +icase: Bool, +rule: M.TsBmRule) -> {T.ts.run.go(~M.TsBm, ~M.ts.bm.feed, cs, pos, (M.TsBm{M.ts.bm.conf(icase, rule, Nil{}), Nil{}}, ms)) == ms : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+xs, +rest}:
      %Equal.sym(List<&2, Nat>, T.ts.run.go(~M.TsBm, ~M.ts.bm.feed, rest, Nat.add(pos, List.length(&2, U32, xs)), (M.TsBm{M.ts.bm.conf(icase, rule, Nil{}), Nil{}}, Nil{})), Nil{}, bp.rg0(rest, Nat.add(pos, List.length(&2, U32, xs)), Nil{}, icase, rule)) : {List.append(&2, Nat, ms, _) == ms : List<&2, Nat>}
      L.tsl.app_nil(ms)

def bp.sref(+icase: Bool, +rule: M.TsBmRule, p: List<&2, U32>, +cs: List<&2, List<&2, U32>>) -> {M.ts.bm.search(icase, rule, p, cs) == V.ts.naive.ends(icase, p, T.ts.concat(cs)) : List<&2, Nat>}:
  match p:
    case Nil{}:
      bp.rg0(cs, 0n, Nil{}, icase, rule)
    case Con{+a, +t}:
      %L.tsl.fold_len(icase, t) : {M.ts.bm.search(icase, rule, Con{a, t}, cs) == V.ts.naive.go(icase, Con{a, t}, 1n+_, T.ts.concat(cs), 0n) : List<&2, Nat>}
      bp.rg(cs, Nil{}, 0n, Nil{}, icase, rule, a, t, {==})

def Laws.bm_search_ref(icase, rule, p, cs):
  bp.sref(icase, rule, p, cs)

def Laws.bm_split(icase, rule, p, cs):
  Equal.trans(List<&2, Nat>, M.ts.bm.search(icase, rule, p, cs), V.ts.naive.ends(icase, p, T.ts.concat(cs)), M.ts.bm.ends(icase, rule, p, T.ts.concat(cs)), bp.sref(icase, rule, p, cs), Equal.sym(List<&2, Nat>, M.ts.bm.ends(icase, rule, p, T.ts.concat(cs)), V.ts.naive.ends(icase, p, T.ts.concat(cs)), bp.ref(icase, rule, p, T.ts.concat(cs))))
