# Proofs of LAWS_xor.bend: CrXor's stream-cipher laws, by its loop
# (stream.bend's cr.ks.*) and the byte lemmas of proof_bits.bend.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./stream.bend as St
import ./proof_bits.bend as Bits
import ./LAWS_xor.bend as Laws

# Lists: a list reversed onto another, twice

def rev2(l: List<&2, U32>, +a: List<&2, U32>) -> {St.cr.rev_onto(St.cr.rev_onto(l, a), Nil{}) == St.cr.rev_onto(a, l) : List<&2, U32>}:
  match l:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev2(t, Con{h, a})

# Stream ciphers from keystream generators (stream.bend)

# the loop, for every list and state, is the structural output reversed onto
# what it had
def ks_go_ref(~S: Data, ~next: S -> St.CrKsStep<S>, ys: List<&2, U32>, +s: S, +acc: List<&2, U32>) -> {St.cr.ks.go(~S, ~next, ys, s, acc) == St.CrKsRun{St.cr.ks.after(~S, ~next, ys, s), St.cr.rev_onto(St.cr.ks.xs(~S, ~next, ys, s), acc)} : St.CrKsRun<S>}:
  match ys:
    case Nil{}:
      {==}
    case Con{x, t}:
      ks_go_ref(~S, ~next, t, St.CrKsStep.st(~S, next(s)), Con{B.byte(U32.xor(x, St.CrKsStep.k(~S, next(s)))), acc})

def xor_update_ref(~S: Data, ~next: S -> St.CrKsStep<S>, +s: S, +m: B.Octets) -> {St.CrXorOut{St.cr.ks.after(~S, ~next, B.Octets.to_list(m), s), B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s))} == St.CrXor.update(~S, ~next, s, m) : St.CrXorOut<S>}:
  %Equal.sym(St.CrKsRun<S>, St.cr.ks.go(~S, ~next, B.Octets.to_list(m), s, Nil{}), St.CrKsRun{St.cr.ks.after(~S, ~next, B.Octets.to_list(m), s), St.cr.rev_onto(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s), Nil{})}, ks_go_ref(~S, ~next, B.Octets.to_list(m), s, Nil{})) : {St.CrXorOut{St.cr.ks.after(~S, ~next, B.Octets.to_list(m), s), B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s))} == St.cr.ks.out(~S, _) : St.CrXorOut<S>}
  %rev2(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s), Nil{}) : {St.CrXorOut{St.cr.ks.after(~S, ~next, B.Octets.to_list(m), s), B.Octets.of_list(_)} == St.CrXorOut{St.cr.ks.after(~S, ~next, B.Octets.to_list(m), s), B.Octets.of_list(St.cr.rev_onto(St.cr.rev_onto(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s), Nil{}), Nil{}))} : St.CrXorOut<S>}
  {==}

def ks_mask_xs(~S: Data, ~next: S -> St.CrKsStep<S>, ys: List<&2, U32>, +s: S) -> {St.cr.ks.xs(~S, ~next, ys, s) == St.cr.ks.xs(~S, ~next, B.mask(ys), s) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Bits.byte_xor_byte(h, St.CrKsStep.k(~S, next(s))) : {Con{B.byte(U32.xor(h, St.CrKsStep.k(~S, next(s)))), St.cr.ks.xs(~S, ~next, t, St.CrKsStep.st(~S, next(s)))} == Con{_, St.cr.ks.xs(~S, ~next, B.mask(t), St.CrKsStep.st(~S, next(s)))} : List<&2, U32>}
      %ks_mask_xs(~S, ~next, t, St.CrKsStep.st(~S, next(s))) : {Con{B.byte(U32.xor(h, St.CrKsStep.k(~S, next(s)))), St.cr.ks.xs(~S, ~next, t, St.CrKsStep.st(~S, next(s)))} == Con{B.byte(U32.xor(h, St.CrKsStep.k(~S, next(s)))), _} : List<&2, U32>}
      {==}

def ks_xs_xs(~S: Data, ~next: S -> St.CrKsStep<S>, ys: List<&2, U32>, +s: S) -> {B.mask(ys) == St.cr.ks.xs(~S, ~next, St.cr.ks.xs(~S, ~next, ys, s), s) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Bits.byte_xx(h, St.CrKsStep.k(~S, next(s))) : {Con{B.byte(h), B.mask(t)} == Con{_, St.cr.ks.xs(~S, ~next, St.cr.ks.xs(~S, ~next, t, St.CrKsStep.st(~S, next(s))), St.CrKsStep.st(~S, next(s)))} : List<&2, U32>}
      %ks_xs_xs(~S, ~next, t, St.CrKsStep.st(~S, next(s))) : {Con{B.byte(h), B.mask(t)} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def Laws.xor_involution(S, next, s, m):
  %xor_update_ref(~S, ~next, s, m) : {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, St.CrXor.out_data(~S, _))) == m : B.Octets}
  %xor_update_ref(~S, ~next, s, B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s))) : {St.CrXor.out_data(~S, _) == m : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s))), B.mask(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s)), BL.octets_to_of(St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s))) : {B.Octets.of_list(St.cr.ks.xs(~S, ~next, _, s)) == m : B.Octets}
  %ks_mask_xs(~S, ~next, St.cr.ks.xs(~S, ~next, B.Octets.to_list(m), s), s) : {B.Octets.of_list(_) == m : B.Octets}
  %ks_xs_xs(~S, ~next, B.Octets.to_list(m), s) : {B.Octets.of_list(_) == m : B.Octets}
  %BL.octets_to_of(B.Octets.to_list(m)) : {B.Octets.of_list(_) == m : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(m)))), B.Octets.of_list(B.Octets.to_list(m)), BL.octets_of_list_idempotent(B.Octets.to_list(m))) : {_ == m : B.Octets}
  BL.octets_of_to(m)

def ks_after_append(~S: Data, ~next: S -> St.CrKsStep<S>, xs: List<&2, U32>, +ys: List<&2, U32>, +s: S) -> {St.cr.ks.after(~S, ~next, B.append(xs, ys), s) == St.cr.ks.after(~S, ~next, ys, St.cr.ks.after(~S, ~next, xs, s)) : S}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      ks_after_append(~S, ~next, t, ys, St.CrKsStep.st(~S, next(s)))

def ks_xs_append(~S: Data, ~next: S -> St.CrKsStep<S>, xs: List<&2, U32>, +ys: List<&2, U32>, +s: S) -> {St.cr.ks.xs(~S, ~next, B.append(xs, ys), s) == B.append(St.cr.ks.xs(~S, ~next, xs, s), St.cr.ks.xs(~S, ~next, ys, St.cr.ks.after(~S, ~next, xs, s))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %ks_xs_append(~S, ~next, t, ys, St.CrKsStep.st(~S, next(s))) : {Con{B.byte(U32.xor(x, St.CrKsStep.k(~S, next(s)))), St.cr.ks.xs(~S, ~next, B.append(t, ys), St.CrKsStep.st(~S, next(s)))} == Con{B.byte(U32.xor(x, St.CrKsStep.k(~S, next(s)))), _} : List<&2, U32>}
      {==}

def Laws.xor_streaming_state(S, next, s, a, b):
  %xor_update_ref(~S, ~next, s, a) : {St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, _), b)) : S}
  %xor_update_ref(~S, ~next, St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s), b) : {St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == St.CrXor.out_state(~S, _) : S}
  %xor_update_ref(~S, ~next, s, B.Octets.append(a, b)) : {St.CrXor.out_state(~S, _) == St.cr.ks.after(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s)) : S}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {St.cr.ks.after(~S, ~next, _, s) == St.cr.ks.after(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s)) : S}
  ks_after_append(~S, ~next, B.Octets.to_list(a), B.Octets.to_list(b), s)

def Laws.xor_streaming_data(S, next, s, a, b):
  %xor_update_ref(~S, ~next, s, a) : {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == B.Octets.append(St.CrXor.out_data(~S, _), St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, _), b))) : B.Octets}
  %xor_update_ref(~S, ~next, St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s), b) : {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == B.Octets.append(B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(a), s)), St.CrXor.out_data(~S, _)) : B.Octets}
  %xor_update_ref(~S, ~next, s, B.Octets.append(a, b)) : {St.CrXor.out_data(~S, _) == B.Octets.append(B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(a), s)), B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s)))) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {B.Octets.of_list(St.cr.ks.xs(~S, ~next, _, s)) == B.Octets.append(B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(a), s)), B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s)))) : B.Octets}
  %Equal.sym(List<&2, U32>, St.cr.ks.xs(~S, ~next, B.append(B.Octets.to_list(a), B.Octets.to_list(b)), s), B.append(St.cr.ks.xs(~S, ~next, B.Octets.to_list(a), s), St.cr.ks.xs(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s))), ks_xs_append(~S, ~next, B.Octets.to_list(a), B.Octets.to_list(b), s)) : {B.Octets.of_list(_) == B.Octets.append(B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(a), s)), B.Octets.of_list(St.cr.ks.xs(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s)))) : B.Octets}
  Bits.octets_of_append(St.cr.ks.xs(~S, ~next, B.Octets.to_list(a), s), St.cr.ks.xs(~S, ~next, B.Octets.to_list(b), St.cr.ks.after(~S, ~next, B.Octets.to_list(a), s)))
