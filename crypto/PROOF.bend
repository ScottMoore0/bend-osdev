# Proofs of LAWS.bend: the generic laws. Shared lemmas are in proof_bits.bend.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./crypto.bend as Cr
import ./stream.bend as St
import ./modes.bend as Md
import ./xcbc.bend as Xc
import ./vmac.bend as Vm
import ./hmac.bend as Hm
import ./sign.bend as Sg
import ./kex.bend as Kx
import ./pbkdf2.bend as Pb
import ./kbkdf.bend as Kb
import ./proof_bits.bend as Bits
import ./LAWS.bend as Laws

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

# CTR: CrXor over CTR's keystream generator

def Laws.ctr_involution(K, Blk, enc, blk_of, blk_to, s, m):
  Laws.xor_involution(~Md.CrCtrState<K>, ~Md.CrCtr.next(~K, ~Blk, ~enc, ~blk_of, ~blk_to), s, m)

def Laws.ctr_streaming_data(K, Blk, enc, blk_of, blk_to, s, a, b):
  Laws.xor_streaming_data(~Md.CrCtrState<K>, ~Md.CrCtr.next(~K, ~Blk, ~enc, ~blk_of, ~blk_to), s, a, b)

def Laws.ctr_streaming_state(K, Blk, enc, blk_of, blk_to, s, a, b):
  Laws.xor_streaming_state(~Md.CrCtrState<K>, ~Md.CrCtr.next(~K, ~Blk, ~enc, ~blk_of, ~blk_to), s, a, b)

# MACs

def Laws.mac_verify_tag_accepts(K, compute, k, m):
  BL.octets_is_eq_refl(compute(k, m))

def Laws.mac_verify_tag_agrees(K, compute, k, m, t):
  {==}

def Laws.hmac_accepts(digest, kk, m):
  Laws.mac_verify_tag_accepts(~Hm.CrHmacKey, ~Hm.CrHmac.mac(~digest), kk, m)

def Laws.xcbc_accepts(K, Blk, bsize, enc, blk_of, blk_to, kk, m):
  Laws.mac_verify_tag_accepts(~Xc.CrXcbcKey<K>, ~Xc.CrXcbc.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to), kk, m)

def Laws.vmac_accepts(K, Blk, bsize, enc, blk_of, blk_to, nlen, kk, m):
  Laws.mac_verify_tag_accepts(~Vm.CrVmacKey<K>, ~Vm.CrVmac.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen), kk, m)

# AEADs

def Laws.lift_round_trip(E, f, d, r, p, h):
  match r:
    case Fail{e}:
      {==}
    case Done{c}:
      %Equal.sym(Result<&2, &2, E, B.Octets>, d(c), Done{p}, h) : {Cr.CrError.lift(~E, ~B.Octets, ~f, _) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}
      {==}

# Signatures and key agreement

def Laws.sign_verify_bytes_if(SK, PK, public, pk_of, pk_to, sign, verify, sk, m, hf, ha):
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk_to(public(sk))), Done{public(sk)}, hf) : {Sg.cr.sign.check(~PK, ~verify, _, m, sign(sk, m)) == True{} : Bool}
  ha

def Laws.kex_agree_if(SK, PK, secret, public, pk_of, pk_to, shared, a, b, x, y, hx, hy, hfx, hfy, h):
  %Equal.sym(Result<&2, &2, Cr.CrError, SK>, secret(a), Done{x}, hx) : {Kx.cr.kex.with(~SK, ~PK, ~shared, _, pk_of(pk_to(public(y)))) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk_to(public(y))), Done{public(y)}, hfy) : {Kx.cr.kex.with(~SK, ~PK, ~shared, Done{x}, _) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, SK>, secret(b), Done{y}, hy) : {shared(x, public(y)) == Kx.cr.kex.with(~SK, ~PK, ~shared, _, pk_of(pk_to(public(x)))) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk_to(public(x))), Done{public(x)}, hfx) : {shared(x, public(y)) == Kx.cr.kex.with(~SK, ~PK, ~shared, Done{y}, _) : Result<&2, &2, Cr.CrError, B.Octets>}
  h

# PBKDF2: the output generator gives n bytes, whatever the MAC (induction
# on n), and its first n bytes are the same whatever comes after
def pbkdf2_out_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +k: K, +salt: B.Octets, +c: Nat, +i: U32) -> {B.len(Pb.cr.pbkdf2.out(~K, ~compute, n, cur, k, salt, c, i)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %pbkdf2_out_len(~K, ~compute, p, t, k, salt, c, i) : {B.len(Pb.cr.pbkdf2.out(~K, ~compute, 1n+p, Con{h, t}, k, salt, c, i)) == 1n+_ : Nat}
          {==}
        case Nil{}:
          %pbkdf2_out_len(~K, ~compute, p, Pb.cr.pbkdf2.tail(Pb.cr.pbkdf2.block(~K, ~compute, k, salt, c, U32.add(i, 1))), k, salt, c, U32.add(i, 1)) : {B.len(Pb.cr.pbkdf2.out(~K, ~compute, 1n+p, Nil{}, k, salt, c, i)) == 1n+_ : Nat}
          {==}

def pbkdf2_out_prefix(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, +j: Nat, cur: List<&2, U32>, +k: K, +salt: B.Octets, +c: Nat, +i: U32) -> {B.take(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), cur, k, salt, c, i)) == Pb.cr.pbkdf2.out(~K, ~compute, n, cur, k, salt, c, i) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %pbkdf2_out_prefix(~K, ~compute, p, j, t, k, salt, c, i) : {Con{h, B.take(p, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(p, j), t, k, salt, c, i))} == Con{h, _} : List<&2, U32>}
          {==}
        case Nil{}:
          %pbkdf2_out_prefix(~K, ~compute, p, j, Pb.cr.pbkdf2.tail(Pb.cr.pbkdf2.block(~K, ~compute, k, salt, c, U32.add(i, 1))), k, salt, c, U32.add(i, 1)) : {Con{Pb.cr.pbkdf2.head(Pb.cr.pbkdf2.block(~K, ~compute, k, salt, c, U32.add(i, 1))), B.take(p, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(p, j), Pb.cr.pbkdf2.tail(Pb.cr.pbkdf2.block(~K, ~compute, k, salt, c, U32.add(i, 1))), k, salt, c, U32.add(i, 1)))} == Con{Pb.cr.pbkdf2.head(Pb.cr.pbkdf2.block(~K, ~compute, k, salt, c, U32.add(i, 1))), _} : List<&2, U32>}
          {==}

def Laws.pbkdf2_stream_length(K, compute, k, salt, c, n):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))), B.len(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)), Bits.octets_len_of(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))) : {_ == n : Nat}
  pbkdf2_out_len(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)

def pbkdf2_checked_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, zero: Bool, fits: Bool, kr: Result<&2, &2, Cr.CrError, K>, +salt: B.Octets, +c: U32, +n: Nat) -> {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Pb.cr.pbkdf2.checked(~K, ~compute, zero, fits, kr, salt, c, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Pb.cr.pbkdf2.checked(~K, ~compute, zero, fits, kr, salt, c, n)) : Result<&2, &2, Cr.CrError, Nat>}:
  match zero:
    case True{}:
      {==}
    case False{}:
      match fits:
        case False{}:
          {==}
        case True{}:
          match kr:
            case Fail{e}:
              {==}
            case Done{+k}:
              %Laws.pbkdf2_stream_length(~K, ~compute, k, salt, c, n) : {Done{B.Octets.len(Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, n))} == Done{_} : Result<&2, &2, Cr.CrError, Nat>}
              {==}

def Laws.pbkdf2_length(K, key, compute, hlen, p, salt, c, n):
  pbkdf2_checked_len(~K, ~compute, U32.is_eq(c, 0), Pb.cr.pbkdf2.fits(Nat.is_lt(0n, hlen), n, hlen), key(p), salt, c, n)

def Laws.pbkdf2_stream_prefix(K, compute, k, salt, c, n, j):
  %BL.take_drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : {B.Octets.take(n, B.Octets.of_list(_)) == B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : B.Octets}
  %Equal.sym(List<&2, U32>, B.take(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)), Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0), pbkdf2_out_prefix(~K, ~compute, n, j, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : {B.Octets.take(n, B.Octets.of_list(B.append(_, B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))))) == B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0), B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)))), B.Octets.append(B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)), B.Octets.of_list(B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)))), Bits.octets_of_append(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0), B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)))) : {B.Octets.take(n, _) == B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : B.Octets}
  %pbkdf2_out_len(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)), B.Octets.of_list(B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))))) == B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : B.Octets}
  %Bits.octets_len_of(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)), B.Octets.of_list(B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))))) == B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)) : B.Octets}
  BL.octets_take_append(B.Octets.of_list(Pb.cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0)), B.Octets.of_list(B.drop(n, Pb.cr.pbkdf2.out(~K, ~compute, Nat.add(n, j), Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))))

# SP 800-108: the output generators give n bytes, whatever the MAC, and
# their first n bytes are the same whatever comes after

def kb_ctr_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +k: K, +rlen: Nat, +fixed: B.Octets, +i: U32) -> {B.len(Kb.cr.kb.ctr(~K, ~compute, n, cur, k, rlen, fixed, i)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %kb_ctr_len(~K, ~compute, p, t, k, rlen, fixed, i) : {B.len(Kb.cr.kb.ctr(~K, ~compute, 1n+p, Con{h, t}, k, rlen, fixed, i)) == 1n+_ : Nat}
          {==}
        case Nil{}:
          %kb_ctr_len(~K, ~compute, p, Kb.cr.kb.tail(B.Octets.to_list(compute(k, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))), k, rlen, fixed, U32.add(i, 1)) : {B.len(Kb.cr.kb.ctr(~K, ~compute, 1n+p, Nil{}, k, rlen, fixed, i)) == 1n+_ : Nat}
          {==}

def kb_ctr_prefix(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, +j: Nat, cur: List<&2, U32>, +k: K, +rlen: Nat, +fixed: B.Octets, +i: U32) -> {B.take(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), cur, k, rlen, fixed, i)) == Kb.cr.kb.ctr(~K, ~compute, n, cur, k, rlen, fixed, i) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %kb_ctr_prefix(~K, ~compute, p, j, t, k, rlen, fixed, i) : {Con{h, B.take(p, Kb.cr.kb.ctr(~K, ~compute, Nat.add(p, j), t, k, rlen, fixed, i))} == Con{h, _} : List<&2, U32>}
          {==}
        case Nil{}:
          %kb_ctr_prefix(~K, ~compute, p, j, Kb.cr.kb.tail(B.Octets.to_list(compute(k, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))), k, rlen, fixed, U32.add(i, 1)) : {Con{Kb.cr.kb.head(B.Octets.to_list(compute(k, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))), B.take(p, Kb.cr.kb.ctr(~K, ~compute, Nat.add(p, j), Kb.cr.kb.tail(B.Octets.to_list(compute(k, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))), k, rlen, fixed, U32.add(i, 1)))} == Con{Kb.cr.kb.head(B.Octets.to_list(compute(k, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))), _} : List<&2, U32>}
          {==}

def kb_fb_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +k: K, +rlen: Nat, +fixed: B.Octets, +prev: B.Octets, +i: U32) -> {B.len(Kb.cr.kb.fb(~K, ~compute, n, cur, k, rlen, fixed, prev, i)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %kb_fb_len(~K, ~compute, p, t, k, rlen, fixed, prev, i) : {B.len(Kb.cr.kb.fb(~K, ~compute, 1n+p, Con{h, t}, k, rlen, fixed, prev, i)) == 1n+_ : Nat}
          {==}
        case Nil{}:
          %kb_fb_len(~K, ~compute, p, Kb.cr.kb.tail(B.Octets.to_list(compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))))), k, rlen, fixed, compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))), U32.add(i, 1)) : {B.len(Kb.cr.kb.fb(~K, ~compute, 1n+p, Nil{}, k, rlen, fixed, prev, i)) == 1n+_ : Nat}
          {==}

def kb_fb_prefix(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, +j: Nat, cur: List<&2, U32>, +k: K, +rlen: Nat, +fixed: B.Octets, +prev: B.Octets, +i: U32) -> {B.take(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), cur, k, rlen, fixed, prev, i)) == Kb.cr.kb.fb(~K, ~compute, n, cur, k, rlen, fixed, prev, i) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %kb_fb_prefix(~K, ~compute, p, j, t, k, rlen, fixed, prev, i) : {Con{h, B.take(p, Kb.cr.kb.fb(~K, ~compute, Nat.add(p, j), t, k, rlen, fixed, prev, i))} == Con{h, _} : List<&2, U32>}
          {==}
        case Nil{}:
          %kb_fb_prefix(~K, ~compute, p, j, Kb.cr.kb.tail(B.Octets.to_list(compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))))), k, rlen, fixed, compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))), U32.add(i, 1)) : {Con{Kb.cr.kb.head(B.Octets.to_list(compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))))), B.take(p, Kb.cr.kb.fb(~K, ~compute, Nat.add(p, j), Kb.cr.kb.tail(B.Octets.to_list(compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))))), k, rlen, fixed, compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))), U32.add(i, 1)))} == Con{Kb.cr.kb.head(B.Octets.to_list(compute(k, B.Octets.append(prev, B.Octets.append(Kb.CrKbkdf.counter(rlen, U32.add(i, 1)), fixed))))), _} : List<&2, U32>}
          {==}

def Laws.kbkdf_counter_stream_length(K, compute, rlen, k, fixed, n):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0))), B.len(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)), Bits.octets_len_of(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0))) : {_ == n : Nat}
  kb_ctr_len(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)

def Laws.kbkdf_counter_stream_prefix(K, compute, rlen, k, fixed, n, j):
  %BL.take_drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0)) : {B.Octets.take(n, B.Octets.of_list(_)) == B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)) : B.Octets}
  %Equal.sym(List<&2, U32>, B.take(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0)), Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0), kb_ctr_prefix(~K, ~compute, n, j, Nil{}, k, rlen, fixed, 0)) : {B.Octets.take(n, B.Octets.of_list(B.append(_, B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0))))) == B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0), B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0)))), B.Octets.append(B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0)))), Bits.octets_of_append(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0), B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0)))) : {B.Octets.take(n, _) == B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)) : B.Octets}
  %kb_ctr_len(~K, ~compute, n, Nil{}, k, rlen, fixed, 0) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0))))) == B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)) : B.Octets}
  %Bits.octets_len_of(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0))))) == B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)) : B.Octets}
  BL.octets_take_append(B.Octets.of_list(Kb.cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.ctr(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, 0))))

def Laws.kbkdf_feedback_stream_length(K, compute, rlen, k, iv, fixed, n):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0))), B.len(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)), Bits.octets_len_of(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0))) : {_ == n : Nat}
  kb_fb_len(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)

def Laws.kbkdf_feedback_stream_prefix(K, compute, rlen, k, iv, fixed, n, j):
  %BL.take_drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0)) : {B.Octets.take(n, B.Octets.of_list(_)) == B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)) : B.Octets}
  %Equal.sym(List<&2, U32>, B.take(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0)), Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0), kb_fb_prefix(~K, ~compute, n, j, Nil{}, k, rlen, fixed, iv, 0)) : {B.Octets.take(n, B.Octets.of_list(B.append(_, B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0))))) == B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0), B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0)))), B.Octets.append(B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0)))), Bits.octets_of_append(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0), B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0)))) : {B.Octets.take(n, _) == B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)) : B.Octets}
  %kb_fb_len(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0))))) == B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)) : B.Octets}
  %Bits.octets_len_of(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0))))) == B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)) : B.Octets}
  BL.octets_take_append(B.Octets.of_list(Kb.cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0)), B.Octets.of_list(B.drop(n, Kb.cr.kb.fb(~K, ~compute, Nat.add(n, j), Nil{}, k, rlen, fixed, iv, 0))))

def kb_key_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, kr: Result<&2, &2, Cr.CrError, K>, +fixed: B.Octets, +n: Nat) -> {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.cr.kb.key(~K, ~compute, ~rlen, kr, fixed, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.cr.kb.key(~K, ~compute, ~rlen, kr, fixed, n)) : Result<&2, &2, Cr.CrError, Nat>}:
  match kr:
    case Fail{e}:
      {==}
    case Done{+k}:
      %Laws.kbkdf_counter_stream_length(~K, ~compute, ~rlen, k, fixed, n) : {Done{B.Octets.len(Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, n))} == Done{_} : Result<&2, &2, Cr.CrError, Nat>}
      {==}

def kb_checked_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, fits: Bool, kr: Result<&2, &2, Cr.CrError, K>, +fixed: B.Octets, +n: Nat) -> {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.cr.kb.checked(~K, ~compute, ~rlen, fits, kr, fixed, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.cr.kb.checked(~K, ~compute, ~rlen, fits, kr, fixed, n)) : Result<&2, &2, Cr.CrError, Nat>}:
  match fits:
    case False{}:
      {==}
    case True{}:
      kb_key_len(~K, ~compute, ~rlen, kr, fixed, n)

def Laws.kbkdf_counter_length(K, key, compute, hlen, rlen, llen, ki, label, context, n):
  kb_checked_len(~K, ~compute, ~rlen, Kb.cr.kb.fits(hlen, llen, n, Nat.sub(Nat.pow(2n, Nat.mul(8n, rlen)), 1n)), key(ki), Kb.CrKbkdf.fixed(~llen, label, context, n), n)

def kb_fkey_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, kr: Result<&2, &2, Cr.CrError, K>, +iv: B.Octets, +fixed: B.Octets, +n: Nat) -> {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.cr.kb.fkey(~K, ~compute, ~rlen, kr, iv, fixed, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.cr.kb.fkey(~K, ~compute, ~rlen, kr, iv, fixed, n)) : Result<&2, &2, Cr.CrError, Nat>}:
  match kr:
    case Fail{e}:
      {==}
    case Done{+k}:
      %Laws.kbkdf_feedback_stream_length(~K, ~compute, ~rlen, k, iv, fixed, n) : {Done{B.Octets.len(Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, n))} == Done{_} : Result<&2, &2, Cr.CrError, Nat>}
      {==}

def kb_fchecked_len(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, fits: Bool, kr: Result<&2, &2, Cr.CrError, K>, +iv: B.Octets, +fixed: B.Octets, +n: Nat) -> {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.cr.kb.fchecked(~K, ~compute, ~rlen, fits, kr, iv, fixed, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.cr.kb.fchecked(~K, ~compute, ~rlen, fits, kr, iv, fixed, n)) : Result<&2, &2, Cr.CrError, Nat>}:
  match fits:
    case False{}:
      {==}
    case True{}:
      kb_fkey_len(~K, ~compute, ~rlen, kr, iv, fixed, n)

def Laws.kbkdf_feedback_length(K, key, compute, hlen, rlen, llen, ki, iv, label, context, n):
  kb_fchecked_len(~K, ~compute, ~rlen, Kb.cr.kb.fits(hlen, llen, n, 4294967295n), key(ki), iv, Kb.CrKbkdf.fixed(~llen, label, context, n), n)
