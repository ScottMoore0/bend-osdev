# Proofs of LAWS_errors.bend: Rs.small8 corrects every pattern of at most
# two errors.
#
#   * The syndromes are linear (LAWS.bend's small8_syndromes_linear) and a
#     codeword's are zero (small8_codeword_syndromes), so a codeword plus e
#     has e's syndromes, and the decoder's corrections (Rs.plan) are e's.
#     Applying corrections adds them to the word, so the corrected word is
#     the codeword plus e corrected, and its syndromes are e corrected's:
#     the decoder treats w + e as it treats e (small8_decode_shift).
#   * A codeword with two symbols changed, read modulo 2^3 as the decoder
#     reads it, is the codeword plus the pattern of the two changes
#     (proof_pat8.bend's pat8, with each change read modulo 2^3). Each of
#     the 1079 patterns of at most two errors, corrected alone, gives the
#     zero word (proof_pat8.bend's q8, a computation in a def of its own
#     for each pattern; gen/proof.py writes the file), so it decodes to
#     the zero message (rse.ga), and the reduction does the rest
#     (small8_two_errors).
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as Sy
import ./rs.bend as D
import ./LAWS.bend as RL
import ./PROOF.bend as RP
import ./proof_pat8.bend as Pt
import ./LAWS_errors.bend as Laws

# Contradictions, and Done's argument

def rse.rdisc(r: Result<&2, &2, E.RsError, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def rse.fd(-er: E.RsError, -z: List<&2, U32>, +h: {Fail{er} == Done{z} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> Empty:
  %h : rse.rdisc(_)
  Unit{}

def rse.val(r: Result<&2, &2, E.RsError, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{x}:
      x

def rse.dinj(-a: List<&2, U32>, -b: List<&2, U32>, h: {Done{a} == Done{b} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> {a == b : List<&2, U32>}:
  Equal.cong(Result<&2, &2, E.RsError, List<&2, U32>>, List<&2, U32>, r => rse.val(r), Done{a}, Done{b}, h)

# Elements

def rse.e0() -> {M.Gfm.elt(C.Rs.gf8(), 0) == 0 : U32}:
  {==}

# elt x + 0 = elt x
def rse.a0e(+s: U32) -> {M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s), 0) == M.Gfm.elt(C.Rs.gf8(), s) : U32}:
  Equal.trans(U32, M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s), 0), M.Gfm.elt(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s)), M.Gfm.elt(C.Rs.gf8(), s), RP.rsp.a80(M.Gfm.elt(C.Rs.gf8(), s)), RP.rsp.eid_8(s))

# Horner's rule gives an element
def rse.eso(w: List<&2, U32>, +k: U32, +acc: U32, +h: {M.Gfm.elt(C.Rs.gf8(), acc) == acc : U32}) -> {M.Gfm.elt(C.Rs.gf8(), Sy.rs.syn.one(w, C.Rs.gf8(), k, acc)) == Sy.rs.syn.one(w, C.Rs.gf8(), k, acc) : U32}:
  match w:
    case Nil{}:
      h
    case Con{+s, +t}:
      rse.eso(t, k, M.Gfm.add(C.Rs.gf8(), M.Gfm.mul(C.Rs.gf8(), acc, k), s), RP.rsp.eid_8(U32.xor(M.Gfm.mul(C.Rs.gf8(), acc, k), s)))

def rse.a0s(+x: List<&2, U32>, +k: U32) -> {M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), k, 0)) == Sy.rs.syn.one(x, C.Rs.gf8(), k, 0) : U32}:
  Equal.trans(U32, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), k, 0)), M.Gfm.elt(C.Rs.gf8(), Sy.rs.syn.one(x, C.Rs.gf8(), k, 0)), Sy.rs.syn.one(x, C.Rs.gf8(), k, 0), RP.rsp.a0_8(Sy.rs.syn.one(x, C.Rs.gf8(), k, 0)), rse.eso(x, k, 0, rse.e0()))

# Syndromes: zero ones added change nothing, so a codeword plus x has x's

def rse.z4(+x: List<&2, U32>) -> {P.RsPoly.add(C.Rs.gf8(), [0, 0, 0, 0], Sy.Rs.syndromes(C.Rs.small8(), x)) == Sy.Rs.syndromes(C.Rs.small8(), x) : List<&2, U32>}:
  %RP.rsp.syn8(x) : {P.RsPoly.add(C.Rs.gf8(), [0, 0, 0, 0], _) == Sy.Rs.syndromes(C.Rs.small8(), x) : List<&2, U32>}
  %RP.rsp.syn8(x) : {P.RsPoly.add(C.Rs.gf8(), [0, 0, 0, 0], Sy.rs.syn.all([2, 4, 3, 6], C.Rs.gf8(), x)) == _ : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 2, 0)), Sy.rs.syn.one(x, C.Rs.gf8(), 2, 0), rse.a0s(x, 2)) : {[_, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 4, 0)), M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 3, 0)), M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 6, 0))] == Sy.rs.syn.all([2, 4, 3, 6], C.Rs.gf8(), x) : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 4, 0)), Sy.rs.syn.one(x, C.Rs.gf8(), 4, 0), rse.a0s(x, 4)) : {[Sy.rs.syn.one(x, C.Rs.gf8(), 2, 0), _, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 3, 0)), M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 6, 0))] == Sy.rs.syn.all([2, 4, 3, 6], C.Rs.gf8(), x) : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 3, 0)), Sy.rs.syn.one(x, C.Rs.gf8(), 3, 0), rse.a0s(x, 3)) : {[Sy.rs.syn.one(x, C.Rs.gf8(), 2, 0), Sy.rs.syn.one(x, C.Rs.gf8(), 4, 0), _, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 6, 0))] == Sy.rs.syn.all([2, 4, 3, 6], C.Rs.gf8(), x) : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(C.Rs.gf8(), 0, Sy.rs.syn.one(x, C.Rs.gf8(), 6, 0)), Sy.rs.syn.one(x, C.Rs.gf8(), 6, 0), rse.a0s(x, 6)) : {[Sy.rs.syn.one(x, C.Rs.gf8(), 2, 0), Sy.rs.syn.one(x, C.Rs.gf8(), 4, 0), Sy.rs.syn.one(x, C.Rs.gf8(), 3, 0), _] == Sy.rs.syn.all([2, 4, 3, 6], C.Rs.gf8(), x) : List<&2, U32>}
  {==}

def rse.ss(+w: List<&2, U32>, +x: List<&2, U32>, +hw: {Sy.Rs.syndromes(C.Rs.small8(), w) == [0, 0, 0, 0] : List<&2, U32>}, +same: {List.length(&2, U32, w) == List.length(&2, U32, x) : Nat}) -> {Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, x)) == Sy.Rs.syndromes(C.Rs.small8(), x) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, x)), P.RsPoly.add(C.Rs.gf8(), Sy.Rs.syndromes(C.Rs.small8(), w), Sy.Rs.syndromes(C.Rs.small8(), x)), RL.small8_syndromes_linear(w, x, same)) : {_ == Sy.Rs.syndromes(C.Rs.small8(), x) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, Sy.Rs.syndromes(C.Rs.small8(), w), [0, 0, 0, 0], hw) : {P.RsPoly.add(C.Rs.gf8(), _, Sy.Rs.syndromes(C.Rs.small8(), x)) == Sy.Rs.syndromes(C.Rs.small8(), x) : List<&2, U32>}
  rse.z4(x)

# Sums of words: masking, zeros, associativity, a prefix

def rse.madd(p: List<&2, U32>, q: List<&2, U32>, +same: {List.length(&2, U32, p) == List.length(&2, U32, q) : Nat}) -> {E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), p, q)) == P.RsPoly.add(C.Rs.gf8(), p, q) : List<&2, U32>}:
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), Nil{}, Con{y, t})) == P.RsPoly.add(C.Rs.gf8(), Nil{}, Con{y, t}) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, t), Equal.sym(Nat, 0n, 1n+List.length(&2, U32, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), Con{x, s}, Nil{})) == P.RsPoly.add(C.Rs.gf8(), Con{x, s}, Nil{}) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %RP.rsp.eid_8(U32.xor(x, y)) : {Con{M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y)), E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), s, t))} == Con{_, P.RsPoly.add(C.Rs.gf8(), s, t)} : List<&2, U32>}
      %rse.madd(s, t, RP.rsp.succ_inj(List.length(&2, U32, s), List.length(&2, U32, t), same)) : {Con{M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y)), E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), s, t))} == Con{M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y)), _} : List<&2, U32>}
      {==}

def rse.addm1(p: List<&2, U32>, q: List<&2, U32>, +same: {List.length(&2, U32, p) == List.length(&2, U32, q) : Nat}) -> {P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), p), q) == P.RsPoly.add(C.Rs.gf8(), p, q) : List<&2, U32>}:
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), Nil{}), Con{y, t}) == P.RsPoly.add(C.Rs.gf8(), Nil{}, Con{y, t}) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, t), Equal.sym(Nat, 0n, 1n+List.length(&2, U32, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), Con{x, s}), Nil{}) == P.RsPoly.add(C.Rs.gf8(), Con{x, s}, Nil{}) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %RP.rsp.e1_8(x, y) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), x), y), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), s), t)} == Con{_, P.RsPoly.add(C.Rs.gf8(), s, t)} : List<&2, U32>}
      %rse.addm1(s, t, RP.rsp.succ_inj(List.length(&2, U32, s), List.length(&2, U32, t), same)) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), x), y), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), s), t)} == Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), x), y), _} : List<&2, U32>}
      {==}

def rse.addm2(p: List<&2, U32>, q: List<&2, U32>, +same: {List.length(&2, U32, p) == List.length(&2, U32, q) : Nat}) -> {P.RsPoly.add(C.Rs.gf8(), p, E.Rs.mask(C.Rs.small8(), q)) == P.RsPoly.add(C.Rs.gf8(), p, q) : List<&2, U32>}:
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({P.RsPoly.add(C.Rs.gf8(), Nil{}, E.Rs.mask(C.Rs.small8(), Con{y, t})) == P.RsPoly.add(C.Rs.gf8(), Nil{}, Con{y, t}) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, t), Equal.sym(Nat, 0n, 1n+List.length(&2, U32, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({P.RsPoly.add(C.Rs.gf8(), Con{x, s}, E.Rs.mask(C.Rs.small8(), Nil{})) == P.RsPoly.add(C.Rs.gf8(), Con{x, s}, Nil{}) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %RP.rsp.e2_8(x, y) : {Con{M.Gfm.add(C.Rs.gf8(), x, M.Gfm.elt(C.Rs.gf8(), y)), P.RsPoly.add(C.Rs.gf8(), s, E.Rs.mask(C.Rs.small8(), t))} == Con{_, P.RsPoly.add(C.Rs.gf8(), s, t)} : List<&2, U32>}
      %rse.addm2(s, t, RP.rsp.succ_inj(List.length(&2, U32, s), List.length(&2, U32, t), same)) : {Con{M.Gfm.add(C.Rs.gf8(), x, M.Gfm.elt(C.Rs.gf8(), y)), P.RsPoly.add(C.Rs.gf8(), s, E.Rs.mask(C.Rs.small8(), t))} == Con{M.Gfm.add(C.Rs.gf8(), x, M.Gfm.elt(C.Rs.gf8(), y)), _} : List<&2, U32>}
      {==}

# a word read modulo 2^3, plus zeros, is itself
def rse.az(t: List<&2, U32>) -> {P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), t), E.rs.zeros(List.length(&2, U32, t))) == E.Rs.mask(C.Rs.small8(), t) : List<&2, U32>}:
  match t:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      %rse.az(r) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s), 0), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), r), E.rs.zeros(List.length(&2, U32, r)))} == Con{M.Gfm.elt(C.Rs.gf8(), s), _} : List<&2, U32>}
      %rse.a0e(s) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s), 0), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), r), E.rs.zeros(List.length(&2, U32, r)))} == Con{_, P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), r), E.rs.zeros(List.length(&2, U32, r)))} : List<&2, U32>}
      {==}

def rse.assoc(a: List<&2, U32>, b: List<&2, U32>, d: List<&2, U32>) -> {P.RsPoly.add(C.Rs.gf8(), P.RsPoly.add(C.Rs.gf8(), a, b), d) == P.RsPoly.add(C.Rs.gf8(), a, P.RsPoly.add(C.Rs.gf8(), b, d)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +s}:
      match b:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          match d:
            case Nil{}:
              {==}
            case Con{+z, +r}:
              %RP.rsp.add8_assoc(x, y, z) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y), z), P.RsPoly.add(C.Rs.gf8(), P.RsPoly.add(C.Rs.gf8(), s, t), r)} == Con{_, P.RsPoly.add(C.Rs.gf8(), s, P.RsPoly.add(C.Rs.gf8(), t, r))} : List<&2, U32>}
              %rse.assoc(s, t, r) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y), z), P.RsPoly.add(C.Rs.gf8(), P.RsPoly.add(C.Rs.gf8(), s, t), r)} == Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y), z), _} : List<&2, U32>}
              {==}

def rse.ta(x: List<&2, U32>, y: List<&2, U32>, n: Nat, +same: {List.length(&2, U32, x) == List.length(&2, U32, y) : Nat}) -> {List.take(&2, U32, P.RsPoly.add(C.Rs.gf8(), x, y), n) == P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, x, n), List.take(&2, U32, y, n)) : List<&2, U32>}:
  match x y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      Empty.absurd({List.take(&2, U32, P.RsPoly.add(C.Rs.gf8(), Nil{}, Con{b, t}), n) == P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, Nil{}, n), List.take(&2, U32, Con{b, t}, n)) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, t), Equal.sym(Nat, 0n, 1n+List.length(&2, U32, t), same)))
    case Con{a, s} Nil{}:
      Empty.absurd({List.take(&2, U32, P.RsPoly.add(C.Rs.gf8(), Con{a, s}, Nil{}), n) == P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, Con{a, s}, n), List.take(&2, U32, Nil{}, n)) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, s), same))
    case Con{+a, +s} Con{+b, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          %rse.ta(s, t, k, RP.rsp.succ_inj(List.length(&2, U32, s), List.length(&2, U32, t), same)) : {Con{M.Gfm.add(C.Rs.gf8(), a, b), List.take(&2, U32, P.RsPoly.add(C.Rs.gf8(), s, t), k)} == Con{M.Gfm.add(C.Rs.gf8(), a, b), _} : List<&2, U32>}
          {==}

# Changed symbols as a sum: a word with the symbol at index i changed by u,
# read modulo 2^3, is the word plus the change (read modulo 2^3) at i

def rse.s1(x: List<&2, U32>, i: Nat, +u: U32) -> {E.Rs.mask(C.Rs.small8(), D.Rs.inject(x, i, u)) == P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), x), D.Rs.inject(E.rs.zeros(List.length(&2, U32, x)), i, M.Gfm.elt(C.Rs.gf8(), u))) : List<&2, U32>}:
  match x:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      match i:
        case 0n:
          %Pt.b1(s, u) : {Con{M.Gfm.elt(C.Rs.gf8(), U32.xor(s, u)), E.Rs.mask(C.Rs.small8(), t)} == Con{_, P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), t), E.rs.zeros(List.length(&2, U32, t)))} : List<&2, U32>}
          %Equal.sym(List<&2, U32>, P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), t), E.rs.zeros(List.length(&2, U32, t))), E.Rs.mask(C.Rs.small8(), t), rse.az(t)) : {Con{M.Gfm.elt(C.Rs.gf8(), U32.xor(s, u)), E.Rs.mask(C.Rs.small8(), t)} == Con{M.Gfm.elt(C.Rs.gf8(), U32.xor(s, u)), _} : List<&2, U32>}
          {==}
        case 1n+k:
          %rse.s1(t, k, u) : {Con{M.Gfm.elt(C.Rs.gf8(), s), E.Rs.mask(C.Rs.small8(), D.Rs.inject(t, k, u))} == Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s), 0), _} : List<&2, U32>}
          %rse.a0e(s) : {Con{_, E.Rs.mask(C.Rs.small8(), D.Rs.inject(t, k, u))} == Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), s), 0), E.Rs.mask(C.Rs.small8(), D.Rs.inject(t, k, u))} : List<&2, U32>}
          {==}

def rse.inj7(+i: Nat, +x: U32) -> {List.length(&2, U32, D.Rs.inject(E.rs.zeros(7n), i, x)) == 7n : Nat}:
  RP.rsp.inj_len(E.rs.zeros(7n), i, x)

def rse.pat_len(+i: Nat, +x: U32, +j: Nat, +y: U32) -> {List.length(&2, U32, Pt.pat8(i, x, j, y)) == 7n : Nat}:
  Equal.trans(Nat, List.length(&2, U32, Pt.pat8(i, x, j, y)), List.length(&2, U32, D.Rs.inject(E.rs.zeros(7n), i, x)), 7n, RP.rsp.add_len(D.Rs.inject(E.rs.zeros(7n), i, x), D.Rs.inject(E.rs.zeros(7n), j, y), Equal.trans(Nat, List.length(&2, U32, D.Rs.inject(E.rs.zeros(7n), i, x)), 7n, List.length(&2, U32, D.Rs.inject(E.rs.zeros(7n), j, y)), rse.inj7(i, x), Equal.sym(Nat, List.length(&2, U32, D.Rs.inject(E.rs.zeros(7n), j, y)), 7n, rse.inj7(j, y)))), rse.inj7(i, x))

# a word of 7 symbols with two changed, read modulo 2^3: the word plus the
# pattern of the two changes
def rse.dm(+w: List<&2, U32>, +i: Nat, +u: U32, +j: Nat, +v: U32, +h7: {List.length(&2, U32, w) == 7n : Nat}) -> {E.Rs.mask(C.Rs.small8(), D.Rs.inject(D.Rs.inject(w, i, u), j, v)) == P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, E.Rs.mask(C.Rs.small8(), D.Rs.inject(D.Rs.inject(w, i, u), j, v)), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), D.Rs.inject(w, i, u)), D.Rs.inject(E.rs.zeros(List.length(&2, U32, D.Rs.inject(w, i, u))), j, M.Gfm.elt(C.Rs.gf8(), v))), rse.s1(D.Rs.inject(w, i, u), j, v)) : {_ == P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))) : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, U32, D.Rs.inject(w, i, u)), 7n, Equal.trans(Nat, List.length(&2, U32, D.Rs.inject(w, i, u)), List.length(&2, U32, w), 7n, RP.rsp.inj_len(w, i, u), h7)) : {P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), D.Rs.inject(w, i, u)), D.Rs.inject(E.rs.zeros(_), j, M.Gfm.elt(C.Rs.gf8(), v))) == P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, E.Rs.mask(C.Rs.small8(), D.Rs.inject(w, i, u)), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), D.Rs.inject(E.rs.zeros(List.length(&2, U32, w)), i, M.Gfm.elt(C.Rs.gf8(), u))), rse.s1(w, i, u)) : {P.RsPoly.add(C.Rs.gf8(), _, D.Rs.inject(E.rs.zeros(7n), j, M.Gfm.elt(C.Rs.gf8(), v))) == P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))) : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, U32, w), 7n, h7) : {P.RsPoly.add(C.Rs.gf8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), D.Rs.inject(E.rs.zeros(_), i, M.Gfm.elt(C.Rs.gf8(), u))), D.Rs.inject(E.rs.zeros(7n), j, M.Gfm.elt(C.Rs.gf8(), v))) == P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), w), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))) : List<&2, U32>}
  rse.assoc(E.Rs.mask(C.Rs.small8(), w), D.Rs.inject(E.rs.zeros(7n), i, M.Gfm.elt(C.Rs.gf8(), u)), D.Rs.inject(E.rs.zeros(7n), j, M.Gfm.elt(C.Rs.gf8(), v)))

# Decoding a word reads its length and its symbols modulo 2^3

def rse.deq(+w1: List<&2, U32>, +w2: List<&2, U32>, +hl: {List.length(&2, U32, w1) == List.length(&2, U32, w2) : Nat}, +hm: {E.Rs.mask(C.Rs.small8(), w1) == E.Rs.mask(C.Rs.small8(), w2) : List<&2, U32>}) -> {D.Rs.decode(C.Rs.small8(), w1, Nil{}) == D.Rs.decode(C.Rs.small8(), w2, Nil{}) : Result<&2, &2, E.RsError, List<&2, U32>>}:
  %Equal.sym(Nat, List.length(&2, U32, w1), List.length(&2, U32, w2), hl) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.go(D.Rs.check(C.Rs.small8(), _, Nil{}), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w1), Nil{})) == D.Rs.decode(C.Rs.small8(), w2, Nil{}) : Result<&2, &2, E.RsError, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, E.Rs.mask(C.Rs.small8(), w1), E.Rs.mask(C.Rs.small8(), w2), hm) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.go(D.Rs.check(C.Rs.small8(), List.length(&2, U32, w2), Nil{}), D.Rs.opts(), C.Rs.small8(), _, Nil{})) == D.Rs.decode(C.Rs.small8(), w2, Nil{}) : Result<&2, &2, E.RsError, List<&2, U32>>}
  {==}

# decoding a word of 7 symbols, its steps written out
def rse.unf(+w: List<&2, U32>, +hl: {List.length(&2, U32, w) == 7n : Nat}) -> {D.Rs.decode(C.Rs.small8(), w, Nil{}) == D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w)), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w))) : Result<&2, &2, E.RsError, List<&2, U32>>}:
  %Equal.sym(Nat, List.length(&2, U32, w), 7n, hl) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.go(D.Rs.check(C.Rs.small8(), _, Nil{}), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w), Nil{})) == D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w)), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w))) : Result<&2, &2, E.RsError, List<&2, U32>>}
  %Equal.sym(Nat, List.length(&2, U32, E.Rs.mask(C.Rs.small8(), w)), 7n, Equal.trans(Nat, List.length(&2, U32, E.Rs.mask(C.Rs.small8(), w)), List.length(&2, U32, w), 7n, RP.rsp.mask_len(w), hl)) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w)), Nil{}, U32.from_nat(_)), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w))) == D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w)), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), w))) : Result<&2, &2, E.RsError, List<&2, U32>>}
  {==}

# the zero word passes the final check (closed: the kernel computes closed
# terms far faster than terms with unknowns)
def rse.zck() -> {D.rs.cor.check(True{}, C.Rs.small8(), [0, 0, 0, 0, 0, 0, 0]) == True{} : Bool}:
  {==}

# a pattern that the decoder's corrections turn into the zero word (chk8)
# decodes to the zero message
def rse.gar(r: Result<&2, &2, E.RsError, List<&2, D.RsFix>>, +x: List<&2, U32>, +h: {Pt.chk8r(r, x) == Done{[0, 0, 0, 0, 0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(r, D.Rs.opts(), C.Rs.small8(), x)) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}:
  match r:
    case Fail{er}:
      Empty.absurd({D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(Fail{er}, D.Rs.opts(), C.Rs.small8(), x)) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}, rse.fd(er, [0, 0, 0, 0, 0, 0, 0], h))
    case Done{+fs}:
      %Equal.sym(List<&2, U32>, D.Rs.apply(C.Rs.small8(), fs, x), [0, 0, 0, 0, 0, 0, 0], rse.dinj(D.Rs.apply(C.Rs.small8(), fs, x), [0, 0, 0, 0, 0, 0, 0], h)) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(D.rs.cor.check(True{}, C.Rs.small8(), _), D.Rs.apply(C.Rs.small8(), fs, x), List.length(&2, D.RsFix, fs))) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, D.Rs.apply(C.Rs.small8(), fs, x), [0, 0, 0, 0, 0, 0, 0], rse.dinj(D.Rs.apply(C.Rs.small8(), fs, x), [0, 0, 0, 0, 0, 0, 0], h)) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(D.rs.cor.check(True{}, C.Rs.small8(), [0, 0, 0, 0, 0, 0, 0]), _, List.length(&2, D.RsFix, fs))) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}
      %Equal.sym(Bool, D.rs.cor.check(True{}, C.Rs.small8(), [0, 0, 0, 0, 0, 0, 0]), True{}, rse.zck()) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(_, [0, 0, 0, 0, 0, 0, 0], List.length(&2, D.RsFix, fs))) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}
      {==}

def rse.ga(+e: List<&2, U32>, +he: {List.length(&2, U32, e) == 7n : Nat}, h: {Pt.chk8(E.Rs.mask(C.Rs.small8(), e)) == Done{[0, 0, 0, 0, 0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> {D.Rs.decode(C.Rs.small8(), e, Nil{}) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}:
  %Equal.sym(Result<&2, &2, E.RsError, List<&2, U32>>, D.Rs.decode(C.Rs.small8(), e, Nil{}), D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e)), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e))), rse.unf(e, he)) : {_ == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}
  rse.gar(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e)), Nil{}, 7), E.Rs.mask(C.Rs.small8(), e), h)

# Applying corrections to a sum corrects the second word

def rse.fo_len(w: List<&2, U32>, i: Nat, +v: U32) -> {List.length(&2, U32, D.rs.fix.one(w, i, C.Rs.gf8(), v)) == List.length(&2, U32, w) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match i:
        case 0n:
          {==}
        case 1n+k:
          %rse.fo_len(t, k, v) : {1n+List.length(&2, U32, D.rs.fix.one(t, k, C.Rs.gf8(), v)) == 1n+_ : Nat}
          {==}

def rse.fa_len(fs: List<&2, D.RsFix>, +n: Nat, +w: List<&2, U32>) -> {List.length(&2, U32, D.rs.fix.all(fs, C.Rs.gf8(), n, w)) == List.length(&2, U32, w) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case D.RsFix{+p, +v}:
          Equal.trans(Nat, List.length(&2, U32, D.rs.fix.all(t, C.Rs.gf8(), n, D.rs.fix.one(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v))), List.length(&2, U32, D.rs.fix.one(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v)), List.length(&2, U32, w), rse.fa_len(t, n, D.rs.fix.one(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v)), rse.fo_len(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), v))

def rse.fo(w: List<&2, U32>, e: List<&2, U32>, i: Nat, +v: U32, +same: {List.length(&2, U32, w) == List.length(&2, U32, e) : Nat}) -> {D.rs.fix.one(P.RsPoly.add(C.Rs.gf8(), w, e), i, C.Rs.gf8(), v) == P.RsPoly.add(C.Rs.gf8(), w, D.rs.fix.one(e, i, C.Rs.gf8(), v)) : List<&2, U32>}:
  match w e:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({D.rs.fix.one(P.RsPoly.add(C.Rs.gf8(), Nil{}, Con{y, t}), i, C.Rs.gf8(), v) == P.RsPoly.add(C.Rs.gf8(), Nil{}, D.rs.fix.one(Con{y, t}, i, C.Rs.gf8(), v)) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, t), Equal.sym(Nat, 0n, 1n+List.length(&2, U32, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({D.rs.fix.one(P.RsPoly.add(C.Rs.gf8(), Con{x, s}, Nil{}), i, C.Rs.gf8(), v) == P.RsPoly.add(C.Rs.gf8(), Con{x, s}, D.rs.fix.one(Nil{}, i, C.Rs.gf8(), v)) : List<&2, U32>}, RP.rsp.succ_zero(List.length(&2, U32, s), same))
    case Con{+x, +s} Con{+y, +t}:
      match i:
        case 0n:
          %RP.rsp.add8_assoc(x, y, v) : {Con{M.Gfm.add(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), x, y), v), P.RsPoly.add(C.Rs.gf8(), s, t)} == Con{_, P.RsPoly.add(C.Rs.gf8(), s, t)} : List<&2, U32>}
          {==}
        case 1n+k:
          %rse.fo(s, t, k, v, RP.rsp.succ_inj(List.length(&2, U32, s), List.length(&2, U32, t), same)) : {Con{M.Gfm.add(C.Rs.gf8(), x, y), D.rs.fix.one(P.RsPoly.add(C.Rs.gf8(), s, t), k, C.Rs.gf8(), v)} == Con{M.Gfm.add(C.Rs.gf8(), x, y), _} : List<&2, U32>}
          {==}

def rse.fa(fs: List<&2, D.RsFix>, +n: Nat, +w: List<&2, U32>, +e: List<&2, U32>, +same: {List.length(&2, U32, w) == List.length(&2, U32, e) : Nat}) -> {D.rs.fix.all(fs, C.Rs.gf8(), n, P.RsPoly.add(C.Rs.gf8(), w, e)) == P.RsPoly.add(C.Rs.gf8(), w, D.rs.fix.all(fs, C.Rs.gf8(), n, e)) : List<&2, U32>}:
  match fs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case D.RsFix{+p, +v}:
          %Equal.sym(List<&2, U32>, D.rs.fix.one(P.RsPoly.add(C.Rs.gf8(), w, e), Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v), P.RsPoly.add(C.Rs.gf8(), w, D.rs.fix.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v)), rse.fo(w, e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), v, same)) : {D.rs.fix.all(t, C.Rs.gf8(), n, _) == P.RsPoly.add(C.Rs.gf8(), w, D.rs.fix.all(t, C.Rs.gf8(), n, D.rs.fix.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v))) : List<&2, U32>}
          rse.fa(t, n, w, D.rs.fix.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v), Equal.trans(Nat, List.length(&2, U32, w), List.length(&2, U32, e), List.length(&2, U32, D.rs.fix.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v)), same, Equal.sym(Nat, List.length(&2, U32, D.rs.fix.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), C.Rs.gf8(), v)), List.length(&2, U32, e), rse.fo_len(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), v))))

def rse.ap(+fs: List<&2, D.RsFix>, +w: List<&2, U32>, +e: List<&2, U32>, +same: {List.length(&2, U32, w) == List.length(&2, U32, e) : Nat}) -> {D.Rs.apply(C.Rs.small8(), fs, P.RsPoly.add(C.Rs.gf8(), w, e)) == P.RsPoly.add(C.Rs.gf8(), w, D.Rs.apply(C.Rs.small8(), fs, e)) : List<&2, U32>}:
  %Equal.sym(Nat, List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, e)), List.length(&2, U32, e), Equal.trans(Nat, List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, e)), List.length(&2, U32, w), List.length(&2, U32, e), RP.rsp.add_len(w, e, same), same)) : {D.rs.fix.all(fs, C.Rs.gf8(), _, P.RsPoly.add(C.Rs.gf8(), w, e)) == P.RsPoly.add(C.Rs.gf8(), w, D.rs.fix.all(fs, C.Rs.gf8(), List.length(&2, U32, e), e)) : List<&2, U32>}
  rse.fa(fs, List.length(&2, U32, e), w, e, same)

def rse.ap_len(+fs: List<&2, D.RsFix>, +x: List<&2, U32>) -> {List.length(&2, U32, D.Rs.apply(C.Rs.small8(), fs, x)) == List.length(&2, U32, x) : Nat}:
  rse.fa_len(fs, List.length(&2, U32, x), x)

# The decoder treats w + x as it treats x, when w's syndromes are zero

def rse.t3(+z: List<&2, U32>, +h7: {List.length(&2, U32, z) == 7n : Nat}, ht: {List.take(&2, U32, z, Nat.sub(List.length(&2, U32, z), U32.to_nat(C.Rs.nroots(C.Rs.small8())))) == [0, 0, 0] : List<&2, U32>}) -> {List.take(&2, U32, z, 3n) == [0, 0, 0] : List<&2, U32>}:
  %h7 : {List.take(&2, U32, z, Nat.sub(_, U32.to_nat(C.Rs.nroots(C.Rs.small8())))) == [0, 0, 0] : List<&2, U32>}
  ht

# the final check passes for both or for neither
def rse.h2(b: Bool, +w: List<&2, U32>, +z: List<&2, U32>, +n: Nat, +hl: {List.length(&2, U32, w) == 7n : Nat}, +same: {List.length(&2, U32, w) == List.length(&2, U32, z) : Nat}, h: {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(b, z, n)) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(b, P.RsPoly.add(C.Rs.gf8(), w, z), n)) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}:
  match b:
    case False{}:
      Empty.absurd({D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(False{}, P.RsPoly.add(C.Rs.gf8(), w, z), n)) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}, rse.fd(E.RsUncorrectable{}, [0, 0, 0], h))
    case True{}:
      %Equal.sym(Nat, List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, z)), 7n, Equal.trans(Nat, List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, z)), List.length(&2, U32, w), 7n, RP.rsp.add_len(w, z, same), hl)) : {Done{List.take(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, z), Nat.sub(_, U32.to_nat(C.Rs.nroots(C.Rs.small8()))))} == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, z), 3n), P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), List.take(&2, U32, z, 3n)), rse.ta(w, z, 3n, same)) : {Done{_} == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, z, 3n), [0, 0, 0], rse.t3(z, Equal.trans(Nat, List.length(&2, U32, z), List.length(&2, U32, w), 7n, Equal.sym(Nat, List.length(&2, U32, w), List.length(&2, U32, z), same), hl), rse.dinj(List.take(&2, U32, z, Nat.sub(List.length(&2, U32, z), U32.to_nat(C.Rs.nroots(C.Rs.small8())))), [0, 0, 0], h))) : {Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), _)} == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
      {==}

# the corrections are the same for both (r): a failure fails both
def rse.h(r: Result<&2, &2, E.RsError, List<&2, D.RsFix>>, +w: List<&2, U32>, +x: List<&2, U32>, +hw: {Sy.Rs.syndromes(C.Rs.small8(), w) == [0, 0, 0, 0] : List<&2, U32>}, +hl: {List.length(&2, U32, w) == 7n : Nat}, +same: {List.length(&2, U32, w) == List.length(&2, U32, x) : Nat}, h: {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(r, D.Rs.opts(), C.Rs.small8(), x)) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(r, D.Rs.opts(), C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, x))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}:
  match r:
    case Fail{er}:
      Empty.absurd({D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(Fail{er}, D.Rs.opts(), C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, x))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}, rse.fd(er, [0, 0, 0], h))
    case Done{+fs}:
      %Equal.sym(List<&2, U32>, D.Rs.apply(C.Rs.small8(), fs, P.RsPoly.add(C.Rs.gf8(), w, x)), P.RsPoly.add(C.Rs.gf8(), w, D.Rs.apply(C.Rs.small8(), fs, x)), rse.ap(fs, w, x, same)) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(D.rs.cor.check(True{}, C.Rs.small8(), _), D.Rs.apply(C.Rs.small8(), fs, P.RsPoly.add(C.Rs.gf8(), w, x)), List.length(&2, D.RsFix, fs))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, D.Rs.apply(C.Rs.small8(), fs, P.RsPoly.add(C.Rs.gf8(), w, x)), P.RsPoly.add(C.Rs.gf8(), w, D.Rs.apply(C.Rs.small8(), fs, x)), rse.ap(fs, w, x, same)) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(D.rs.cor.check(True{}, C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, D.Rs.apply(C.Rs.small8(), fs, x))), _, List.length(&2, D.RsFix, fs))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, D.Rs.apply(C.Rs.small8(), fs, x))), Sy.Rs.syndromes(C.Rs.small8(), D.Rs.apply(C.Rs.small8(), fs, x)), rse.ss(w, D.Rs.apply(C.Rs.small8(), fs, x), hw, Equal.trans(Nat, List.length(&2, U32, w), List.length(&2, U32, x), List.length(&2, U32, D.Rs.apply(C.Rs.small8(), fs, x)), same, Equal.sym(Nat, List.length(&2, U32, D.Rs.apply(C.Rs.small8(), fs, x)), List.length(&2, U32, x), rse.ap_len(fs, x))))) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.verify(P.RsPoly.is_zero(C.Rs.field(C.Rs.small8()), _), P.RsPoly.add(C.Rs.gf8(), w, D.Rs.apply(C.Rs.small8(), fs, x)), List.length(&2, D.RsFix, fs))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
      rse.h2(P.RsPoly.is_zero(C.Rs.field(C.Rs.small8()), Sy.Rs.syndromes(C.Rs.small8(), D.Rs.apply(C.Rs.small8(), fs, x))), w, D.Rs.apply(C.Rs.small8(), fs, x), List.length(&2, D.RsFix, fs), hl, Equal.trans(Nat, List.length(&2, U32, w), List.length(&2, U32, x), List.length(&2, U32, D.Rs.apply(C.Rs.small8(), fs, x)), same, Equal.sym(Nat, List.length(&2, U32, D.Rs.apply(C.Rs.small8(), fs, x)), List.length(&2, U32, x), rse.ap_len(fs, x))), h)

def rse.ds(+w: List<&2, U32>, +e: List<&2, U32>, +hw: {Sy.Rs.syndromes(C.Rs.small8(), w) == [0, 0, 0, 0] : List<&2, U32>}, +hl: {List.length(&2, U32, w) == 7n : Nat}, +he: {List.length(&2, U32, e) == 7n : Nat}, hz: {D.Rs.decode(C.Rs.small8(), e, Nil{}) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}) -> {D.Rs.decode(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e), Nil{}) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}:
  %Equal.sym(Result<&2, &2, E.RsError, List<&2, U32>>, D.Rs.decode(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e), Nil{}), D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e))), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e)))), rse.unf(P.RsPoly.add(C.Rs.gf8(), w, e), Equal.trans(Nat, List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), w, e)), List.length(&2, U32, w), 7n, RP.rsp.add_len(w, e, Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he))), hl))) : {_ == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e)), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)), Equal.trans(List<&2, U32>, E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e)), P.RsPoly.add(C.Rs.gf8(), w, e), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)), rse.madd(w, e, Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he))), Equal.sym(List<&2, U32>, P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)), P.RsPoly.add(C.Rs.gf8(), w, e), rse.addm2(w, e, Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he)))))) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), _), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e)))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e)), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)), Equal.trans(List<&2, U32>, E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, e)), P.RsPoly.add(C.Rs.gf8(), w, e), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)), rse.madd(w, e, Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he))), Equal.sym(List<&2, U32>, P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)), P.RsPoly.add(C.Rs.gf8(), w, e), rse.addm2(w, e, Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he)))))) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e))), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), _)) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e))), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e)), rse.ss(w, E.Rs.mask(C.Rs.small8(), e), hw, Equal.trans(Nat, List.length(&2, U32, w), List.length(&2, U32, e), List.length(&2, U32, E.Rs.mask(C.Rs.small8(), e)), Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he)), Equal.sym(Nat, List.length(&2, U32, E.Rs.mask(C.Rs.small8(), e)), List.length(&2, U32, e), RP.rsp.mask_len(e))))) : {D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), _, Nil{}, 7), D.Rs.opts(), C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), w, E.Rs.mask(C.Rs.small8(), e)))) == Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, w, 3n), [0, 0, 0])} : Result<&2, &2, E.RsError, List<&2, U32>>}
  rse.h(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e)), Nil{}, 7), w, E.Rs.mask(C.Rs.small8(), e), hw, hl, Equal.trans(Nat, List.length(&2, U32, w), List.length(&2, U32, e), List.length(&2, U32, E.Rs.mask(C.Rs.small8(), e)), Equal.trans(Nat, List.length(&2, U32, w), 7n, List.length(&2, U32, e), hl, Equal.sym(Nat, List.length(&2, U32, e), 7n, he)), Equal.sym(Nat, List.length(&2, U32, E.Rs.mask(C.Rs.small8(), e)), List.length(&2, U32, e), RP.rsp.mask_len(e))), Equal.trans(Result<&2, &2, E.RsError, List<&2, U32>>, D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e)), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e))), D.Rs.decode(C.Rs.small8(), e, Nil{}), Done{[0, 0, 0]}, Equal.sym(Result<&2, &2, E.RsError, List<&2, U32>>, D.Rs.decode(C.Rs.small8(), e, Nil{}), D.rs.dec.msg(C.Rs.small8(), D.rs.cor.fin(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e)), Nil{}, 7), D.Rs.opts(), C.Rs.small8(), E.Rs.mask(C.Rs.small8(), e))), rse.unf(e, he)), hz))

# Laws

def Laws.small8_syndromes_shift(m, short, e, same):
  rse.ss(E.Rs.codeword(C.Rs.small8(), m), e, RL.small8_codeword_syndromes(m, short), Equal.trans(Nat, List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), m)), Nat.add(List.length(&2, U32, m), 4n), List.length(&2, U32, e), RP.rsp.cwlen8(m), Equal.sym(Nat, List.length(&2, U32, e), Nat.add(List.length(&2, U32, m), 4n), same)))

def rse.short3(+a: U32, +b: U32, +d: U32) -> {Nat.is_le(List.length(&2, U32, [a, b, d]), 3n) == True{} : Bool}:
  {==}

def rse.cwlen3(+a: U32, +b: U32, +d: U32) -> {List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d])) == 7n : Nat}:
  RP.rsp.cwlen8([a, b, d])

def rse.tail(+a: U32, +b: U32, +d: U32) -> {Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d]), 3n), [0, 0, 0])} == Done{E.Rs.mask(C.Rs.small8(), [a, b, d])} : Result<&2, &2, E.RsError, List<&2, U32>>}:
  %Equal.sym(List<&2, U32>, List.take(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d]), List.length(&2, U32, [a, b, d])), E.Rs.mask(C.Rs.small8(), [a, b, d]), RL.codeword_message(C.Rs.small8(), [a, b, d])) : {Done{P.RsPoly.add(C.Rs.gf8(), _, [0, 0, 0])} == Done{E.Rs.mask(C.Rs.small8(), [a, b, d])} : Result<&2, &2, E.RsError, List<&2, U32>>}
  %rse.az([a, b, d]) : {Done{P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), [a, b, d]), [0, 0, 0])} == Done{_} : Result<&2, &2, E.RsError, List<&2, U32>>}
  {==}

def Laws.small8_decode_shift(a, b, d, e, n7, zero):
  Equal.trans(Result<&2, &2, E.RsError, List<&2, U32>>, D.Rs.decode(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), e), Nil{}), Done{P.RsPoly.add(C.Rs.gf8(), List.take(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d]), 3n), [0, 0, 0])}, Done{E.Rs.mask(C.Rs.small8(), [a, b, d])}, rse.ds(E.Rs.codeword(C.Rs.small8(), [a, b, d]), e, RL.small8_codeword_syndromes([a, b, d], rse.short3(a, b, d)), rse.cwlen3(a, b, d), n7, zero), rse.tail(a, b, d))

# the pattern of the two changes has 7 symbols, as the codeword has
def rse.same_pat(+a: U32, +b: U32, +d: U32, +i: Nat, +u: U32, +j: Nat, +v: U32) -> {List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d])) == List.length(&2, U32, Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d])), 7n, List.length(&2, U32, Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), rse.cwlen3(a, b, d), Equal.sym(Nat, List.length(&2, U32, Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), 7n, rse.pat_len(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))))

def Laws.small8_two_errors(a, b, d, i, u, j, v):
  Equal.trans(Result<&2, &2, E.RsError, List<&2, U32>>, D.Rs.decode(C.Rs.small8(), D.Rs.inject(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v), Nil{}), D.Rs.decode(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), Nil{}), Done{E.Rs.mask(C.Rs.small8(), [a, b, d])}, rse.deq(D.Rs.inject(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), Equal.trans(Nat, List.length(&2, U32, D.Rs.inject(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v)), List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d])), List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)))), Equal.trans(Nat, List.length(&2, U32, D.Rs.inject(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v)), List.length(&2, U32, D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u)), List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d])), RP.rsp.inj_len(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v), RP.rsp.inj_len(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u)), Equal.sym(Nat, List.length(&2, U32, P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)))), List.length(&2, U32, E.Rs.codeword(C.Rs.small8(), [a, b, d])), RP.rsp.add_len(E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), rse.same_pat(a, b, d, i, u, j, v)))), Equal.trans(List<&2, U32>, E.Rs.mask(C.Rs.small8(), D.Rs.inject(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v)), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), E.Rs.codeword(C.Rs.small8(), [a, b, d])), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)))), rse.dm(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u, j, v, rse.cwlen3(a, b, d)), Equal.sym(List<&2, U32>, E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)))), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), E.Rs.codeword(C.Rs.small8(), [a, b, d])), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), Equal.trans(List<&2, U32>, E.Rs.mask(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)))), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), E.Rs.codeword(C.Rs.small8(), [a, b, d])), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), rse.madd(E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), rse.same_pat(a, b, d, i, u, j, v)), Equal.sym(List<&2, U32>, P.RsPoly.add(C.Rs.gf8(), E.Rs.mask(C.Rs.small8(), E.Rs.codeword(C.Rs.small8(), [a, b, d])), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v))), rse.addm1(E.Rs.codeword(C.Rs.small8(), [a, b, d]), Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), rse.same_pat(a, b, d, i, u, j, v))))))), Laws.small8_decode_shift(a, b, d, Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), rse.pat_len(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), rse.ga(Pt.pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), rse.pat_len(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)), Pt.q8(i, u, j, v))))
