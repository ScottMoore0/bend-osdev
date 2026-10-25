import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./rsa.bend as R
import ./mgf1.bend as G
import ./pkcs1.bend as P
import ./keys.bend as K
import ./es15.bend as E
import ./oaep.bend as OA
import ./pss.bend as PS
import ./octets.bend as O
import ./LAWS.bend as Laws
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# Lists and Octets (from bytes' laws)

def mask_len(+xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mask_len(t) : {B.len(B.mask(Con{h, t})) == 1n+_ : Nat}
      {==}

# the length of a list made Octets
def octets_len_of(+xs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(xs)) == B.len(xs) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(xs)), B.len(B.Octets.to_list(B.Octets.of_list(xs))), BL.octets_len_list(B.Octets.of_list(xs))) : {_ == B.len(xs) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {B.len(_) == B.len(xs) : Nat}
  mask_len(xs)

def mask_append(+p: List<&2, U32>, +q: List<&2, U32>) -> {B.mask(B.append(p, q)) == B.append(B.mask(p), B.mask(q)) : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %mask_append(t, q) : {Con{B.byte(h), B.mask(B.append(t, q))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

# Octets.of_list of an append is the append of the Octets
def octets_of_append(+p: List<&2, U32>, +q: List<&2, U32>) -> {B.Octets.of_list(B.append(p, q)) == B.Octets.append(B.Octets.of_list(p), B.Octets.of_list(q)) : B.Octets}:
  %BL.octets_of_to(B.Octets.append(B.Octets.of_list(p), B.Octets.of_list(q))) : {B.Octets.of_list(B.append(p, q)) == _ : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(p), B.Octets.of_list(q))), B.append(B.Octets.to_list(B.Octets.of_list(p)), B.Octets.to_list(B.Octets.of_list(q))), BL.octets_append_list(B.Octets.of_list(p), B.Octets.of_list(q))) : {B.Octets.of_list(B.append(p, q)) == B.Octets.of_list(_) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(p)), B.mask(p), BL.octets_to_of(p)) : {B.Octets.of_list(B.append(p, q)) == B.Octets.of_list(B.append(_, B.Octets.to_list(B.Octets.of_list(q)))) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(q)), B.mask(q), BL.octets_to_of(q)) : {B.Octets.of_list(B.append(p, q)) == B.Octets.of_list(B.append(B.mask(p), _)) : B.Octets}
  %mask_append(p, q) : {B.Octets.of_list(B.append(p, q)) == B.Octets.of_list(_) : B.Octets}
  %BL.octets_to_of(B.append(p, q)) : {B.Octets.of_list(B.append(p, q)) == B.Octets.of_list(_) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(B.append(p, q)))), B.Octets.of_list(B.append(p, q)), BL.octets_of_list_idempotent(B.append(p, q))) : {B.Octets.of_list(B.append(p, q)) == _ : B.Octets}
  {==}

# MGF1: the output generator gives n bytes, whatever the hash (induction on
# n), and its first n bytes are the same whatever comes after

def mgf_out_len(~digest: B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +seed: B.Octets, +i: U32) -> {B.len(G.rsa.mgf.out(~digest, n, cur, seed, i)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %mgf_out_len(~digest, p, t, seed, i) : {B.len(G.rsa.mgf.out(~digest, 1n+p, Con{h, t}, seed, i)) == 1n+_ : Nat}
          {==}
        case Nil{}:
          %mgf_out_len(~digest, p, G.rsa.mgf.tail(B.Octets.to_list(digest(B.Octets.append(seed, B.Octets.be32(i))))), seed, U32.add(i, 1)) : {B.len(G.rsa.mgf.out(~digest, 1n+p, Nil{}, seed, i)) == 1n+_ : Nat}
          {==}

def mgf_out_prefix(~digest: B.Octets -> B.Octets, n: Nat, +j: Nat, cur: List<&2, U32>, +seed: B.Octets, +i: U32) -> {B.take(n, G.rsa.mgf.out(~digest, Nat.add(n, j), cur, seed, i)) == G.rsa.mgf.out(~digest, n, cur, seed, i) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match cur:
        case Con{h, t}:
          %mgf_out_prefix(~digest, p, j, t, seed, i) : {Con{h, B.take(p, G.rsa.mgf.out(~digest, Nat.add(p, j), t, seed, i))} == Con{h, _} : List<&2, U32>}
          {==}
        case Nil{}:
          %mgf_out_prefix(~digest, p, j, G.rsa.mgf.tail(B.Octets.to_list(digest(B.Octets.append(seed, B.Octets.be32(i))))), seed, U32.add(i, 1)) : {Con{G.rsa.mgf.head(B.Octets.to_list(digest(B.Octets.append(seed, B.Octets.be32(i))))), B.take(p, G.rsa.mgf.out(~digest, Nat.add(p, j), G.rsa.mgf.tail(B.Octets.to_list(digest(B.Octets.append(seed, B.Octets.be32(i))))), seed, U32.add(i, 1)))} == Con{G.rsa.mgf.head(B.Octets.to_list(digest(B.Octets.append(seed, B.Octets.be32(i))))), _} : List<&2, U32>}
          {==}

def Laws.mgf1_length(digest, seed, n):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0))), B.len(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)), octets_len_of(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0))) : {_ == n : Nat}
  mgf_out_len(~digest, n, Nil{}, seed, 0)

def Laws.mgf1_prefix(digest, seed, n, j):
  %BL.take_drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0)) : {B.Octets.take(n, B.Octets.of_list(_)) == B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)) : B.Octets}
  %Equal.sym(List<&2, U32>, B.take(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0)), G.rsa.mgf.out(~digest, n, Nil{}, seed, 0), mgf_out_prefix(~digest, n, j, Nil{}, seed, 0)) : {B.Octets.take(n, B.Octets.of_list(B.append(_, B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0))))) == B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0), B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0)))), B.Octets.append(B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)), B.Octets.of_list(B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0)))), octets_of_append(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0), B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0)))) : {B.Octets.take(n, _) == B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)) : B.Octets}
  %mgf_out_len(~digest, n, Nil{}, seed, 0) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)), B.Octets.of_list(B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0))))) == B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)) : B.Octets}
  %octets_len_of(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)) : {B.Octets.take(_, B.Octets.append(B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)), B.Octets.of_list(B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0))))) == B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)) : B.Octets}
  BL.octets_take_append(B.Octets.of_list(G.rsa.mgf.out(~digest, n, Nil{}, seed, 0)), B.Octets.of_list(B.drop(n, G.rsa.mgf.out(~digest, Nat.add(n, j), Nil{}, seed, 0))))

# RSASSA-PKCS1-v1_5: the signature's verification recomputes the encoding
# for the same modulus length, so it compares EM with itself

def k_public(+sk: R.RsaPrivate) -> {R.Rsa.k_of(sk) == R.Rsa.k(R.Rsa.public(sk)) : Nat}:
  match sk:
    case R.RsaPrivate{n, e, d, p, q, dp, dq, qinv}:
      {==}

def Laws.pkcs1_sign_verify_if(digest, prefix, sk, m, em, s, he, hs, hv):
  %Equal.sym(Result<&2, &2, R.RsaError, B.Octets>, P.RsaPkcs1.encode(~digest, prefix, m, R.Rsa.k_of(sk)), Done{em}, he) : {Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => P.RsaPkcs1.verify(~digest, prefix, R.Rsa.public(sk), m, x), Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, _, y => R.Rsa.dp_octets(sk, y))) == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
  %Equal.sym(Result<&2, &2, R.RsaError, B.Octets>, R.Rsa.dp_octets(sk, em), Done{s}, hs) : {Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => P.RsaPkcs1.verify(~digest, prefix, R.Rsa.public(sk), m, x), _) == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
  %Equal.sym(Result<&2, &2, R.RsaError, B.Octets>, R.Rsa.ep_octets(R.Rsa.public(sk), s), Done{em}, hv) : {Done{P.rsa.pkcs1.check(~digest, _, prefix, m, R.Rsa.k(R.Rsa.public(sk)))} == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
  %k_public(sk) : {Done{P.rsa.pkcs1.cmp(P.RsaPkcs1.encode(~digest, prefix, m, _), em)} == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
  %Equal.sym(Result<&2, &2, R.RsaError, B.Octets>, P.RsaPkcs1.encode(~digest, prefix, m, R.Rsa.k_of(sk)), Done{em}, he) : {Done{P.rsa.pkcs1.cmp(_, em)} == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
  %Equal.sym(Bool, B.Octets.is_eq(em, em), True{}, BL.octets_is_eq_refl(em)) : {Done{_} == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
  {==}

# Booleans

def rp.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def rp.absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : rp.bdisc(_)
  Unit{}

def and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, rp.absurd(h))

def and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, rp.absurd(h))

def not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, rp.absurd(h))
    case False{}:
      {==}

# B.Octets.append(B.Octets.of_list([0, 2]), B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m)))E-PKCS1-v1_5: the first zero after a string of nonzero bytes is at its
# length, and what follows it is the message

def zero_at(+xs: List<&2, U32>, +z: U32, ys: List<&2, U32>, hz: {U32.is_zero(z) == True{} : Bool}, +h: {O.rsa.nozero(xs) == True{} : Bool}) -> {E.rsa.es15.zero(B.append(xs, Con{z, ys})) == Some{B.len(xs)} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, U32.is_zero(z), True{}, hz) : {E.rsa.es15.zero.go(_, E.rsa.es15.zero(ys)) == Some{0n} : Maybe<&2, Nat>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, U32.is_zero(x), False{}, not_true(U32.is_zero(x), and_l(Bool.not(U32.is_zero(x)), O.rsa.nozero(t), h))) : {E.rsa.es15.zero.go(_, E.rsa.es15.zero(B.append(t, Con{z, ys}))) == Some{1n+B.len(t)} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, E.rsa.es15.zero(B.append(t, Con{z, ys})), Some{B.len(t)}, zero_at(t, z, ys, hz, and_r(Bool.not(U32.is_zero(x)), O.rsa.nozero(t), h))) : {Maybe.map(&2, Nat, Nat, i => 1n+i, _) == Some{1n+B.len(t)} : Maybe<&2, Nat>}
      {==}

def drop_sep(+xs: List<&2, U32>, +z: U32, +ys: List<&2, U32>) -> {B.drop(Nat.add(B.len(xs), 1n), B.append(xs, Con{z, ys})) == ys : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      drop_sep(t, z, ys)

def es15_dec(+ps: B.Octets, +m: B.Octets, h8: {Nat.is_le(8n, B.Octets.len(ps)) == True{} : Bool}, hz: {O.RsaOct.no_zero(ps) == True{} : Bool}) -> {E.RsaEs15.decode(B.Octets.append(B.Octets.of_list([0, 2]), B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m)))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([0, 2]), B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m)))), B.append(B.Octets.to_list(B.Octets.of_list([0, 2])), B.Octets.to_list(B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m)))), BL.octets_append_list(B.Octets.of_list([0, 2]), B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m)))) : {E.rsa.es15.dec(_) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m))), B.append(B.Octets.to_list(ps), B.Octets.to_list(B.Octets.append(B.Octets.of_list([0]), m))), BL.octets_append_list(ps, B.Octets.append(B.Octets.of_list([0]), m))) : {E.rsa.es15.dec(B.append(B.Octets.to_list(B.Octets.of_list([0, 2])), _)) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([0]), m)), B.append(B.Octets.to_list(B.Octets.of_list([0])), B.Octets.to_list(m)), BL.octets_append_list(B.Octets.of_list([0]), m)) : {E.rsa.es15.dec(B.append(B.Octets.to_list(B.Octets.of_list([0, 2])), B.append(B.Octets.to_list(ps), _))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([0, 2])), B.mask([0, 2]), BL.octets_to_of([0, 2])) : {E.rsa.es15.dec(B.append(_, B.append(B.Octets.to_list(ps), B.append(B.Octets.to_list(B.Octets.of_list([0])), B.Octets.to_list(m))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([0])), B.mask([0]), BL.octets_to_of([0])) : {E.rsa.es15.dec(B.append(B.mask([0, 2]), B.append(B.Octets.to_list(ps), B.append(_, B.Octets.to_list(m))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(Maybe<&2, Nat>, E.rsa.es15.zero(B.append(B.Octets.to_list(ps), Con{B.byte(0), B.Octets.to_list(m)})), Some{B.len(B.Octets.to_list(ps))}, zero_at(B.Octets.to_list(ps), B.byte(0), B.Octets.to_list(m), {==}, hz)) : {E.rsa.es15.dec.msg(_, B.append(B.Octets.to_list(ps), Con{B.byte(0), B.Octets.to_list(m)})) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %BL.octets_len_list(ps) : {E.rsa.es15.dec.len(Nat.is_le(8n, _), B.len(B.Octets.to_list(ps)), B.append(B.Octets.to_list(ps), Con{B.byte(0), B.Octets.to_list(m)})) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(Bool, Nat.is_le(8n, B.Octets.len(ps)), True{}, h8) : {E.rsa.es15.dec.len(_, B.len(B.Octets.to_list(ps)), B.append(B.Octets.to_list(ps), Con{B.byte(0), B.Octets.to_list(m)})) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.drop(Nat.add(B.len(B.Octets.to_list(ps)), 1n), B.append(B.Octets.to_list(ps), Con{B.byte(0), B.Octets.to_list(m)})), B.Octets.to_list(m), drop_sep(B.Octets.to_list(ps), B.byte(0), B.Octets.to_list(m))) : {Done{B.Octets.of_list(_)} == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(m)), m, BL.octets_of_to(m)) : {Done{_} == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  {==}

def es15_case(fits: Bool, good: Bool, +m: B.Octets, +ps: B.Octets, +k: Nat, +hg: {Bool.and(Bool.and(Nat.is_eq(Nat.add(B.Octets.len(ps), Nat.add(B.Octets.len(m), 3n)), k), Nat.is_le(8n, B.Octets.len(ps))), O.RsaOct.no_zero(ps)) == good : Bool}) -> {Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, E.rsa.es15.enc(fits, good, m, ps), em => E.RsaEs15.decode(em)) == Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, em => m, E.rsa.es15.enc(fits, good, m, ps)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match fits good:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      +ha = and_l(Bool.and(Nat.is_eq(Nat.add(B.Octets.len(ps), Nat.add(B.Octets.len(m), 3n)), k), Nat.is_le(8n, B.Octets.len(ps))), O.RsaOct.no_zero(ps), hg)
      es15_dec(ps, m, and_r(Nat.is_eq(Nat.add(B.Octets.len(ps), Nat.add(B.Octets.len(m), 3n)), k), Nat.is_le(8n, B.Octets.len(ps)), ha), and_r(Bool.and(Nat.is_eq(Nat.add(B.Octets.len(ps), Nat.add(B.Octets.len(m), 3n)), k), Nat.is_le(8n, B.Octets.len(ps))), O.RsaOct.no_zero(ps), hg))

def Laws.es15_round_trip(m, ps, k):
  es15_case(Nat.is_le(Nat.add(B.Octets.len(m), 11n), k), Bool.and(Bool.and(Nat.is_eq(Nat.add(B.Octets.len(ps), Nat.add(B.Octets.len(m), 3n)), k), Nat.is_le(8n, B.Octets.len(ps))), O.RsaOct.no_zero(ps)), m, ps, k, {==})

# Byte strings: XOR undoes itself, and keeps the first operand's length

def bxx(a: Bool, b: Bool) -> {Bool.xor(Bool.xor(a, b), b) == a : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def byte_xx(x: U32, y: U32) -> {U32.xor(B.byte(U32.xor(B.byte(x), B.byte(y))), B.byte(y)) == B.byte(x) : U32}:
  match x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      %Equal.sym(Bool, Bool.xor(Bool.xor(a0, b0), b0), a0, bxx(a0, b0)) : {U32{WCon{_, WCon{Bool.xor(Bool.xor(a1, b1), b1), WCon{Bool.xor(Bool.xor(a2, b2), b2), WCon{Bool.xor(Bool.xor(a3, b3), b3), WCon{Bool.xor(Bool.xor(a4, b4), b4), WCon{Bool.xor(Bool.xor(a5, b5), b5), WCon{Bool.xor(Bool.xor(a6, b6), b6), WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a1, b1), b1), a1, bxx(a1, b1)) : {U32{WCon{a0, WCon{_, WCon{Bool.xor(Bool.xor(a2, b2), b2), WCon{Bool.xor(Bool.xor(a3, b3), b3), WCon{Bool.xor(Bool.xor(a4, b4), b4), WCon{Bool.xor(Bool.xor(a5, b5), b5), WCon{Bool.xor(Bool.xor(a6, b6), b6), WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a2, b2), b2), a2, bxx(a2, b2)) : {U32{WCon{a0, WCon{a1, WCon{_, WCon{Bool.xor(Bool.xor(a3, b3), b3), WCon{Bool.xor(Bool.xor(a4, b4), b4), WCon{Bool.xor(Bool.xor(a5, b5), b5), WCon{Bool.xor(Bool.xor(a6, b6), b6), WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a3, b3), b3), a3, bxx(a3, b3)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{_, WCon{Bool.xor(Bool.xor(a4, b4), b4), WCon{Bool.xor(Bool.xor(a5, b5), b5), WCon{Bool.xor(Bool.xor(a6, b6), b6), WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a4, b4), b4), a4, bxx(a4, b4)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{_, WCon{Bool.xor(Bool.xor(a5, b5), b5), WCon{Bool.xor(Bool.xor(a6, b6), b6), WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a5, b5), b5), a5, bxx(a5, b5)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{_, WCon{Bool.xor(Bool.xor(a6, b6), b6), WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a6, b6), b6), a6, bxx(a6, b6)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{_, WCon{Bool.xor(Bool.xor(a7, b7), b7), Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.xor(Bool.xor(a7, b7), b7), a7, bxx(a7, b7)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{_, Word.zero(24n)}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, Word.zero(24n)}}}}}}}}} : U32}
      {==}

def byte_byte(x: U32) -> {B.byte(B.byte(x)) == B.byte(x) : U32}:
  match x:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}}:
      {==}

def mask_xx(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {O.rsa.xor(B.mask(O.rsa.xor(B.mask(xs), B.mask(ys))), B.mask(ys)) == B.mask(xs) : List<&2, U32>}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      %Equal.sym(U32, U32.xor(B.byte(U32.xor(B.byte(x), B.byte(y))), B.byte(y)), B.byte(x), byte_xx(x, y)) : {Con{_, O.rsa.xor(B.mask(O.rsa.xor(B.mask(xt), B.mask(yt))), B.mask(yt))} == Con{B.byte(x), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, O.rsa.xor(B.mask(O.rsa.xor(B.mask(xt), B.mask(yt))), B.mask(yt)), B.mask(xt), mask_xx(xt, yt)) : {Con{B.byte(x), _} == Con{B.byte(x), B.mask(xt)} : List<&2, U32>}
      {==}
    case Con{+x, +xt} Nil{}:
      %Equal.sym(U32, B.byte(B.byte(x)), B.byte(x), byte_byte(x)) : {Con{_, O.rsa.xor(B.mask(O.rsa.xor(B.mask(xt), Nil{})), Nil{})} == Con{B.byte(x), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, O.rsa.xor(B.mask(O.rsa.xor(B.mask(xt), B.mask(Nil{}))), B.mask(Nil{})), B.mask(xt), mask_xx(xt, Nil{})) : {Con{B.byte(x), _} == Con{B.byte(x), B.mask(xt)} : List<&2, U32>}
      {==}

def to_list_mask(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(o)) : {B.Octets.to_list(o) == _ : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {B.Octets.to_list(o) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

def oct_xor_xor(+a: B.Octets, +b: B.Octets) -> {O.RsaOct.xor(O.RsaOct.xor(a, b), b) == a : B.Octets}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b)))), B.mask(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b))), BL.octets_to_of(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b)))) : {B.Octets.of_list(O.rsa.xor(_, B.Octets.to_list(b))) == a : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(a), B.mask(B.Octets.to_list(a)), to_list_mask(a)) : {B.Octets.of_list(O.rsa.xor(B.mask(O.rsa.xor(_, B.Octets.to_list(b))), B.Octets.to_list(b))) == a : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(b), B.mask(B.Octets.to_list(b)), to_list_mask(b)) : {B.Octets.of_list(O.rsa.xor(B.mask(O.rsa.xor(B.mask(B.Octets.to_list(a)), _)), _)) == a : B.Octets}
  %Equal.sym(List<&2, U32>, O.rsa.xor(B.mask(O.rsa.xor(B.mask(B.Octets.to_list(a)), B.mask(B.Octets.to_list(b)))), B.mask(B.Octets.to_list(b))), B.mask(B.Octets.to_list(a)), mask_xx(B.Octets.to_list(a), B.Octets.to_list(b))) : {B.Octets.of_list(_) == a : B.Octets}
  %to_list_mask(a) : {B.Octets.of_list(_) == a : B.Octets}
  BL.octets_of_to(a)

def xor_len(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.len(O.rsa.xor(xs, ys)) == B.len(xs) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Con{y, yt}:
      %xor_len(xt, yt) : {1n+B.len(O.rsa.xor(xt, yt)) == 1n+_ : Nat}
      {==}
    case Con{x, xt} Nil{}:
      %xor_len(xt, Nil{}) : {1n+B.len(O.rsa.xor(xt, Nil{})) == 1n+_ : Nat}
      {==}

def oct_xor_len(+a: B.Octets, +b: B.Octets) -> {B.Octets.len(O.RsaOct.xor(a, b)) == B.Octets.len(a) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b)))), B.len(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b))), octets_len_of(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b)))) : {_ == B.Octets.len(a) : Nat}
  %Equal.sym(Nat, B.len(O.rsa.xor(B.Octets.to_list(a), B.Octets.to_list(b))), B.len(B.Octets.to_list(a)), xor_len(B.Octets.to_list(a), B.Octets.to_list(b))) : {_ == B.Octets.len(a) : Nat}
  Equal.sym(Nat, B.Octets.len(a), B.len(B.Octets.to_list(a)), BL.octets_len_list(a))

def nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, rp.absurd(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, rp.absurd(h))
    case 1n+p 1n+q:
      %nat_eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# EME-OAEP: past zeros, the first nonzero byte is the separator, and what
# follows it is the message

def sep_zeros(n: Nat, +z: U32, +ys: List<&2, U32>, hz: {U32.is_zero(z) == False{} : Bool}, h1: {U32.is_eq(z, 1) == True{} : Bool}) -> {O.rsa.sep(B.append(B.zeros(n), Con{z, ys})) == Some{n} : Maybe<&2, Nat>}:
  match n:
    case 0n:
      %Equal.sym(Bool, U32.is_zero(z), False{}, hz) : {O.rsa.sep.go(_, U32.is_eq(z, 1), O.rsa.sep(ys)) == Some{0n} : Maybe<&2, Nat>}
      %Equal.sym(Bool, U32.is_eq(z, 1), True{}, h1) : {O.rsa.sep.go(False{}, _, O.rsa.sep(ys)) == Some{0n} : Maybe<&2, Nat>}
      {==}
    case 1n+p:
      %Equal.sym(Maybe<&2, Nat>, O.rsa.sep(B.append(B.zeros(p), Con{z, ys})), Some{p}, sep_zeros(p, z, ys, hz, h1)) : {Maybe.map(&2, Nat, Nat, i => 1n+i, _) == Some{1n+p} : Maybe<&2, Nat>}
      {==}

def drop_zeros(n: Nat, +z: U32, +ys: List<&2, U32>) -> {B.drop(Nat.add(n, 1n), B.append(B.zeros(n), Con{z, ys})) == ys : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      drop_zeros(p, z, ys)

def oaep_dec(~mgf: B.Octets -> Nat -> B.Octets, +lhash: B.Octets, +m: B.Octets, +seed: B.Octets, +ps: Nat, +hs: {Nat.is_eq(B.Octets.len(seed), B.Octets.len(lhash)) == True{} : Bool}) -> {OA.rsa.oaep.dec(~mgf, lhash, B.Octets.append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}:
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(B.Octets.of_list([0])), B.Octets.append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))), B.Octets.of_list([0]), BL.octets_take_append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))) : {OA.rsa.oaep.dec2(~mgf, lhash, _, B.Octets.drop(1n, B.Octets.append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(B.Octets.of_list([0])), B.Octets.append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))), BL.octets_drop_append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))) : {OA.rsa.oaep.dec2(~mgf, lhash, B.Octets.of_list([0]), _) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  +lms = Equal.trans(Nat, B.Octets.len(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash)))), B.Octets.len(seed), B.Octets.len(lhash), oct_xor_len(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), nat_eq_true(B.Octets.len(seed), B.Octets.len(lhash), hs))
  %lms : {OA.rsa.oaep.dec3(~mgf, lhash, B.Octets.of_list([0]), B.Octets.take(_, B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))))), B.Octets.drop(_, B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash)))), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))))), O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), BL.octets_take_append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))))) : {OA.rsa.oaep.dec3(~mgf, lhash, B.Octets.of_list([0]), _, B.Octets.drop(B.Octets.len(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash)))), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash)))), B.Octets.append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), BL.octets_drop_append(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))))) : {OA.rsa.oaep.dec3(~mgf, lhash, B.Octets.of_list([0]), O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), _) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, O.RsaOct.xor(O.RsaOct.xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash))), seed, oct_xor_xor(seed, mgf(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.len(lhash)))) : {OA.rsa.oaep.dec4(~mgf, lhash, B.Octets.of_list([0]), _, O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(Nat, B.Octets.len(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))), B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)), oct_xor_len(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))) : {OA.rsa.oaep.dec5(lhash, B.Octets.of_list([0]), O.RsaOct.xor(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), mgf(seed, _))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, O.RsaOct.xor(O.RsaOct.xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps)))), OA.rsa.oaep.db(lhash, m, ps), oct_xor_xor(OA.rsa.oaep.db(lhash, m, ps), mgf(seed, B.Octets.len(OA.rsa.oaep.db(lhash, m, ps))))) : {OA.rsa.oaep.dec5(lhash, B.Octets.of_list([0]), _) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(lhash), OA.rsa.oaep.db(lhash, m, ps)), lhash, BL.octets_take_append(lhash, B.Octets.append(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), m)))) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), B.Octets.is_eq(_, lhash)), O.rsa.sep(B.Octets.to_list(B.Octets.drop(B.Octets.len(lhash), OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.to_list(B.Octets.drop(B.Octets.len(lhash), OA.rsa.oaep.db(lhash, m, ps)))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(Bool, B.Octets.is_eq(lhash, lhash), True{}, BL.octets_is_eq_refl(lhash)) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), _), O.rsa.sep(B.Octets.to_list(B.Octets.drop(B.Octets.len(lhash), OA.rsa.oaep.db(lhash, m, ps)))), B.Octets.to_list(B.Octets.drop(B.Octets.len(lhash), OA.rsa.oaep.db(lhash, m, ps)))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(lhash), OA.rsa.oaep.db(lhash, m, ps)), B.Octets.append(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), m)), BL.octets_drop_append(lhash, B.Octets.append(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), m)))) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), True{}), O.rsa.sep(B.Octets.to_list(_)), B.Octets.to_list(_)) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), m))), B.append(B.Octets.to_list(B.Octets.zeros(ps)), B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), m))), BL.octets_append_list(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), m))) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), True{}), O.rsa.sep(_), _) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(ps)), B.zeros(ps), BL.octets_zeros_list(ps)) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), True{}), O.rsa.sep(B.append(_, B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), m)))), B.append(_, B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), m)))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), m)), B.append(B.Octets.to_list(B.Octets.of_list([1])), B.Octets.to_list(m)), BL.octets_append_list(B.Octets.of_list([1]), m)) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), True{}), O.rsa.sep(B.append(B.zeros(ps), _)), B.append(B.zeros(ps), _)) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([1])), B.mask([1]), BL.octets_to_of([1])) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), True{}), O.rsa.sep(B.append(B.zeros(ps), B.append(_, B.Octets.to_list(m)))), B.append(B.zeros(ps), B.append(_, B.Octets.to_list(m)))) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(Maybe<&2, Nat>, O.rsa.sep(B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(m)})), Some{ps}, sep_zeros(ps, B.byte(1), B.Octets.to_list(m), {==}, {==})) : {OA.rsa.oaep.msg(Bool.and(B.Octets.is_eq(B.Octets.of_list([0]), B.Octets.of_list([0])), True{}), _, B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(m)})) == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.drop(Nat.add(ps, 1n), B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(m)})), B.Octets.to_list(m), drop_zeros(ps, B.byte(1), B.Octets.to_list(m))) : {Done{B.Octets.of_list(_)} == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(m)), m, BL.octets_of_to(m)) : {Done{_} == Done{m} : Result<&2, &2, R.RsaError, B.Octets>}
  {==}

def oaep_case(~mgf: B.Octets -> Nat -> B.Octets, fits: Bool, good: Bool, +lhash: B.Octets, +m: B.Octets, +seed: B.Octets, +k: Nat, +hg: {Nat.is_eq(B.Octets.len(seed), B.Octets.len(lhash)) == good : Bool}) -> {Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, OA.rsa.oaep.enc(~mgf, fits, good, lhash, m, seed, k), em => OA.rsa.oaep.dec(~mgf, lhash, em)) == Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, em => m, OA.rsa.oaep.enc(~mgf, fits, good, lhash, m, seed, k)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match fits good:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      oaep_dec(~mgf, lhash, m, seed, Nat.sub(k, Nat.add(B.Octets.len(m), Nat.add(Nat.mul(2n, B.Octets.len(lhash)), 2n))), hg)

def Laws.oaep_round_trip(digest, mgf, label, m, seed, k):
  oaep_case(~mgf, Nat.is_le(Nat.add(B.Octets.len(m), Nat.add(Nat.mul(2n, B.Octets.len(digest(label))), 2n)), k), Nat.is_eq(B.Octets.len(seed), B.Octets.len(digest(label))), digest(label), m, seed, k, {==})

# EMSA-PSS: verification accepts every encoding

def band_idem(a: Bool, s: Bool) -> {Bool.and(Bool.and(a, s), s) == Bool.and(a, s) : Bool}:
  match a s:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bmask_xx(x: Bool, y: Bool, s: Bool) -> {Bool.and(Bool.xor(Bool.and(Bool.xor(x, y), s), y), s) == Bool.and(x, s) : Bool}:
  match x y s:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def and_idem(x: U32, s: U32) -> {U32.and(U32.and(B.byte(x), s), s) == U32.and(B.byte(x), s) : U32}:
  match x s:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Bool, Bool.and(Bool.and(a0, s0), s0), Bool.and(a0, s0), band_idem(a0, s0)) : {U32{WCon{_, WCon{Bool.and(Bool.and(a1, s1), s1), WCon{Bool.and(Bool.and(a2, s2), s2), WCon{Bool.and(Bool.and(a3, s3), s3), WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a1, s1), s1), Bool.and(a1, s1), band_idem(a1, s1)) : {U32{WCon{Bool.and(a0, s0), WCon{_, WCon{Bool.and(Bool.and(a2, s2), s2), WCon{Bool.and(Bool.and(a3, s3), s3), WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a2, s2), s2), Bool.and(a2, s2), band_idem(a2, s2)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{_, WCon{Bool.and(Bool.and(a3, s3), s3), WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a3, s3), s3), Bool.and(a3, s3), band_idem(a3, s3)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{_, WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a4, s4), s4), Bool.and(a4, s4), band_idem(a4, s4)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{_, WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a5, s5), s5), Bool.and(a5, s5), band_idem(a5, s5)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{_, WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a6, s6), s6), Bool.and(a6, s6), band_idem(a6, s6)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{_, WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a7, s7), s7), Bool.and(a7, s7), band_idem(a7, s7)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      {==}

def and_xx(x: U32, y: U32, s: U32) -> {U32.and(B.byte(U32.xor(B.byte(U32.and(B.byte(U32.xor(B.byte(x), B.byte(y))), s)), B.byte(y))), s) == U32.and(B.byte(x), s) : U32}:
  match x y s:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}} U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a0, b0), s0), b0), s0), Bool.and(a0, s0), bmask_xx(a0, b0, s0)) : {U32{WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a1, b1), s1), b1), s1), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a2, b2), s2), b2), s2), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a3, b3), s3), b3), s3), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a4, b4), s4), b4), s4), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a5, b5), s5), b5), s5), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a1, b1), s1), b1), s1), Bool.and(a1, s1), bmask_xx(a1, b1, s1)) : {U32{WCon{Bool.and(a0, s0), WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a2, b2), s2), b2), s2), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a3, b3), s3), b3), s3), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a4, b4), s4), b4), s4), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a5, b5), s5), b5), s5), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a2, b2), s2), b2), s2), Bool.and(a2, s2), bmask_xx(a2, b2, s2)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a3, b3), s3), b3), s3), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a4, b4), s4), b4), s4), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a5, b5), s5), b5), s5), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a3, b3), s3), b3), s3), Bool.and(a3, s3), bmask_xx(a3, b3, s3)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a4, b4), s4), b4), s4), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a5, b5), s5), b5), s5), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a4, b4), s4), b4), s4), Bool.and(a4, s4), bmask_xx(a4, b4, s4)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a5, b5), s5), b5), s5), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a5, b5), s5), b5), s5), Bool.and(a5, s5), bmask_xx(a5, b5, s5)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a6, b6), s6), b6), s6), Bool.and(a6, s6), bmask_xx(a6, b6, s6)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{_, WCon{Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.xor(Bool.and(Bool.xor(a7, b7), s7), b7), s7), Bool.and(a7, s7), bmask_xx(a7, b7, s7)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      {==}

def and_nil(x: U32, s: U32) -> {U32.and(B.byte(B.byte(U32.and(B.byte(B.byte(x)), s))), s) == U32.and(B.byte(x), s) : U32}:
  match x s:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Bool, Bool.and(Bool.and(a0, s0), s0), Bool.and(a0, s0), band_idem(a0, s0)) : {U32{WCon{_, WCon{Bool.and(Bool.and(a1, s1), s1), WCon{Bool.and(Bool.and(a2, s2), s2), WCon{Bool.and(Bool.and(a3, s3), s3), WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a1, s1), s1), Bool.and(a1, s1), band_idem(a1, s1)) : {U32{WCon{Bool.and(a0, s0), WCon{_, WCon{Bool.and(Bool.and(a2, s2), s2), WCon{Bool.and(Bool.and(a3, s3), s3), WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a2, s2), s2), Bool.and(a2, s2), band_idem(a2, s2)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{_, WCon{Bool.and(Bool.and(a3, s3), s3), WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a3, s3), s3), Bool.and(a3, s3), band_idem(a3, s3)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{_, WCon{Bool.and(Bool.and(a4, s4), s4), WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a4, s4), s4), Bool.and(a4, s4), band_idem(a4, s4)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{_, WCon{Bool.and(Bool.and(a5, s5), s5), WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a5, s5), s5), Bool.and(a5, s5), band_idem(a5, s5)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{_, WCon{Bool.and(Bool.and(a6, s6), s6), WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a6, s6), s6), Bool.and(a6, s6), band_idem(a6, s6)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{_, WCon{Bool.and(Bool.and(a7, s7), s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      %Equal.sym(Bool, Bool.and(Bool.and(a7, s7), s7), Bool.and(a7, s7), band_idem(a7, s7)) : {U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{Bool.and(a0, s0), WCon{Bool.and(a1, s1), WCon{Bool.and(a2, s2), WCon{Bool.and(a3, s3), WCon{Bool.and(a4, s4), WCon{Bool.and(a5, s5), WCon{Bool.and(a6, s6), WCon{Bool.and(a7, s7), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      {==}

def byte_and(x: U32, s: U32) -> {B.byte(U32.and(B.byte(x), s)) == U32.and(B.byte(x), s) : U32}:
  match x s:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def mask_idem(+xs: List<&2, U32>) -> {B.mask(B.mask(xs)) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(U32, B.byte(B.byte(x)), B.byte(x), byte_byte(x)) : {Con{_, B.mask(B.mask(t))} == Con{B.byte(x), B.mask(t)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(t)), B.mask(t), mask_idem(t)) : {Con{B.byte(x), _} == Con{B.byte(x), B.mask(t)} : List<&2, U32>}
      {==}

def xor_nil(+xs: List<&2, U32>) -> {O.rsa.xor(xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %xor_nil(t) : {Con{x, O.rsa.xor(t, Nil{})} == Con{x, _} : List<&2, U32>}
      {==}

def mask1_len(+xs: List<&2, U32>, +s: U32) -> {B.len(O.rsa.mask1(xs, s)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# masking the first byte twice is masking it once
def mask1_mask(+xs: List<&2, U32>, +s: U32) -> {B.mask(O.rsa.mask1(B.mask(xs), s)) == O.rsa.mask1(B.mask(xs), s) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(U32, B.byte(U32.and(B.byte(x), s)), U32.and(B.byte(x), s), byte_and(x, s)) : {Con{_, B.mask(B.mask(t))} == Con{U32.and(B.byte(x), s), B.mask(t)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(t)), B.mask(t), mask_idem(t)) : {Con{U32.and(B.byte(x), s), _} == Con{U32.and(B.byte(x), s), B.mask(t)} : List<&2, U32>}
      {==}

def mask1_idem(+xs: List<&2, U32>, +s: U32) -> {O.rsa.mask1(O.rsa.mask1(B.mask(xs), s), s) == O.rsa.mask1(B.mask(xs), s) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(U32, U32.and(U32.and(B.byte(x), s), s), U32.and(B.byte(x), s), and_idem(x, s)) : {Con{_, B.mask(t)} == Con{U32.and(B.byte(x), s), B.mask(t)} : List<&2, U32>}
      {==}

def oct_mask_first_idem(+o: B.Octets, +s: U32) -> {O.RsaOct.mask_first(O.RsaOct.mask_first(o, s), s) == O.RsaOct.mask_first(o, s) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.rsa.mask1(B.Octets.to_list(o), s))), B.mask(O.rsa.mask1(B.Octets.to_list(o), s)), BL.octets_to_of(O.rsa.mask1(B.Octets.to_list(o), s))) : {B.Octets.of_list(O.rsa.mask1(_, s)) == O.RsaOct.mask_first(o, s) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(o), B.mask(B.Octets.to_list(o)), to_list_mask(o)) : {B.Octets.of_list(O.rsa.mask1(B.mask(O.rsa.mask1(_, s)), s)) == B.Octets.of_list(O.rsa.mask1(_, s)) : B.Octets}
  %Equal.sym(List<&2, U32>, B.mask(O.rsa.mask1(B.mask(B.Octets.to_list(o)), s)), O.rsa.mask1(B.mask(B.Octets.to_list(o)), s), mask1_mask(B.Octets.to_list(o), s)) : {B.Octets.of_list(O.rsa.mask1(_, s)) == B.Octets.of_list(O.rsa.mask1(B.mask(B.Octets.to_list(o)), s)) : B.Octets}
  %Equal.sym(List<&2, U32>, O.rsa.mask1(O.rsa.mask1(B.mask(B.Octets.to_list(o)), s), s), O.rsa.mask1(B.mask(B.Octets.to_list(o)), s), mask1_idem(B.Octets.to_list(o), s)) : {B.Octets.of_list(_) == B.Octets.of_list(O.rsa.mask1(B.mask(B.Octets.to_list(o)), s)) : B.Octets}
  {==}

def oct_mask_first_len(+o: B.Octets, +s: U32) -> {B.Octets.len(O.RsaOct.mask_first(o, s)) == B.Octets.len(o) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(O.rsa.mask1(B.Octets.to_list(o), s))), B.len(O.rsa.mask1(B.Octets.to_list(o), s)), octets_len_of(O.rsa.mask1(B.Octets.to_list(o), s))) : {_ == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.len(O.rsa.mask1(B.Octets.to_list(o), s)), B.len(B.Octets.to_list(o)), mask1_len(B.Octets.to_list(o), s)) : {_ == B.Octets.len(o) : Nat}
  Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o))

# masking, masking the first byte, and masking again with the same mask:
# the first byte keeps only its masked bits, the rest comes back
def pk_list(+xs: List<&2, U32>, +ys: List<&2, U32>, +s: U32) -> {O.rsa.mask1(B.mask(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.mask(xs), B.mask(ys))), s)), B.mask(ys))), s) == O.rsa.mask1(B.mask(xs), s) : List<&2, U32>}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      %Equal.sym(U32, U32.and(B.byte(U32.xor(B.byte(U32.and(B.byte(U32.xor(B.byte(x), B.byte(y))), s)), B.byte(y))), s), U32.and(B.byte(x), s), and_xx(x, y, s)) : {Con{_, B.mask(O.rsa.xor(B.mask(B.mask(O.rsa.xor(B.mask(xt), B.mask(yt)))), B.mask(yt)))} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(O.rsa.xor(B.mask(xt), B.mask(yt)))), B.mask(O.rsa.xor(B.mask(xt), B.mask(yt))), mask_idem(O.rsa.xor(B.mask(xt), B.mask(yt)))) : {Con{U32.and(B.byte(x), s), B.mask(O.rsa.xor(_, B.mask(yt)))} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, O.rsa.xor(B.mask(O.rsa.xor(B.mask(xt), B.mask(yt))), B.mask(yt)), B.mask(xt), mask_xx(xt, yt)) : {Con{U32.and(B.byte(x), s), B.mask(_)} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(xt)), B.mask(xt), mask_idem(xt)) : {Con{U32.and(B.byte(x), s), _} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      {==}
    case Con{+x, +xt} Nil{}:
      %Equal.sym(U32, U32.and(B.byte(B.byte(U32.and(B.byte(B.byte(x)), s))), s), U32.and(B.byte(x), s), and_nil(x, s)) : {Con{_, B.mask(O.rsa.xor(B.mask(B.mask(O.rsa.xor(B.mask(xt), Nil{}))), Nil{}))} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, O.rsa.xor(B.mask(xt), Nil{}), B.mask(xt), xor_nil(B.mask(xt))) : {Con{U32.and(B.byte(x), s), B.mask(O.rsa.xor(B.mask(B.mask(_)), Nil{}))} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, O.rsa.xor(B.mask(B.mask(B.mask(xt))), Nil{}), B.mask(B.mask(B.mask(xt))), xor_nil(B.mask(B.mask(B.mask(xt))))) : {Con{U32.and(B.byte(x), s), B.mask(_)} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(xt)), B.mask(xt), mask_idem(xt)) : {Con{U32.and(B.byte(x), s), B.mask(B.mask(_))} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(xt)), B.mask(xt), mask_idem(xt)) : {Con{U32.and(B.byte(x), s), B.mask(_)} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(B.mask(xt)), B.mask(xt), mask_idem(xt)) : {Con{U32.and(B.byte(x), s), _} == Con{U32.and(B.byte(x), s), B.mask(xt)} : List<&2, U32>}
      {==}

def pk_oct(+d: B.Octets, +mk: B.Octets, +s: U32) -> {O.RsaOct.mask_first(O.RsaOct.xor(O.RsaOct.mask_first(O.RsaOct.xor(d, mk), s), mk), s) == O.RsaOct.mask_first(d, s) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk)))), B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), BL.octets_to_of(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk)))) : {B.Octets.of_list(O.rsa.mask1(B.Octets.to_list(B.Octets.of_list(O.rsa.xor(B.Octets.to_list(B.Octets.of_list(O.rsa.mask1(_, s))), B.Octets.to_list(mk)))), s)) == O.RsaOct.mask_first(d, s) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.rsa.mask1(B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), s))), B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), s)), BL.octets_to_of(O.rsa.mask1(B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), s))) : {B.Octets.of_list(O.rsa.mask1(B.Octets.to_list(B.Octets.of_list(O.rsa.xor(_, B.Octets.to_list(mk)))), s)) == O.RsaOct.mask_first(d, s) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), s)), B.Octets.to_list(mk)))), B.mask(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), s)), B.Octets.to_list(mk))), BL.octets_to_of(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.Octets.to_list(d), B.Octets.to_list(mk))), s)), B.Octets.to_list(mk)))) : {B.Octets.of_list(O.rsa.mask1(_, s)) == O.RsaOct.mask_first(d, s) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(d), B.mask(B.Octets.to_list(d)), to_list_mask(d)) : {B.Octets.of_list(O.rsa.mask1(B.mask(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(_, B.Octets.to_list(mk))), s)), B.Octets.to_list(mk))), s)) == B.Octets.of_list(O.rsa.mask1(_, s)) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(mk), B.mask(B.Octets.to_list(mk)), to_list_mask(mk)) : {B.Octets.of_list(O.rsa.mask1(B.mask(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.mask(B.Octets.to_list(d)), _)), s)), _)), s)) == B.Octets.of_list(O.rsa.mask1(B.mask(B.Octets.to_list(d)), s)) : B.Octets}
  %Equal.sym(List<&2, U32>, O.rsa.mask1(B.mask(O.rsa.xor(B.mask(O.rsa.mask1(B.mask(O.rsa.xor(B.mask(B.Octets.to_list(d)), B.mask(B.Octets.to_list(mk)))), s)), B.mask(B.Octets.to_list(mk)))), s), O.rsa.mask1(B.mask(B.Octets.to_list(d)), s), pk_list(B.Octets.to_list(d), B.Octets.to_list(mk), s)) : {B.Octets.of_list(_) == B.Octets.of_list(O.rsa.mask1(B.mask(B.Octets.to_list(d)), s)) : B.Octets}
  {==}

def cd0(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 0n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd1(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 1n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd2(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 2n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd3(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 3n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd4(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 4n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd5(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 5n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd6(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 6n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cd7(+ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, 7n)) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match ps:
    case 0n:
      {==}
    case 1n+p:
      {==}

# for every emBits, at most 7 bits are cleared, and DB's first byte (0x00 or
# 0x01) keeps its value
def cd_list(e: Nat, +ps: Nat, +xs: List<&2, U32>) -> {O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), xs}), U32.shrn(255, PS.rsa.pss.z(e))) == B.append(B.zeros(ps), Con{B.byte(1), xs}) : List<&2, U32>}:
  match e:
    case 0n:
      cd0(ps, xs)
    case 1n+e1:
      match e1:
        case 0n:
          cd7(ps, xs)
        case 1n+e2:
          match e2:
            case 0n:
              cd6(ps, xs)
            case 1n+e3:
              match e3:
                case 0n:
                  cd5(ps, xs)
                case 1n+e4:
                  match e4:
                    case 0n:
                      cd4(ps, xs)
                    case 1n+e5:
                      match e5:
                        case 0n:
                          cd3(ps, xs)
                        case 1n+e6:
                          match e6:
                            case 0n:
                              cd2(ps, xs)
                            case 1n+e7:
                              match e7:
                                case 0n:
                                  cd1(ps, xs)
                                case 1n+e8:
                                  cd_list(e8, ps, xs)


def len_app(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.len(B.append(xs, ys)) == Nat.add(B.len(xs), B.len(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %len_app(t, ys) : {1n+B.len(B.append(t, ys)) == 1n+_ : Nat}
      {==}

def oct_len_app(+a: B.Octets, +b: B.Octets) -> {B.Octets.len(B.Octets.append(a, b)) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(a, b)), B.len(B.Octets.to_list(B.Octets.append(a, b))), BL.octets_len_list(B.Octets.append(a, b))) : {_ == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {B.len(_) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %Equal.sym(Nat, B.len(B.append(B.Octets.to_list(a), B.Octets.to_list(b))), Nat.add(B.len(B.Octets.to_list(a)), B.len(B.Octets.to_list(b))), len_app(B.Octets.to_list(a), B.Octets.to_list(b))) : {_ == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %Equal.sym(Nat, B.Octets.len(a), B.len(B.Octets.to_list(a)), BL.octets_len_list(a)) : {Nat.add(B.len(B.Octets.to_list(a)), B.len(B.Octets.to_list(b))) == Nat.add(_, B.Octets.len(b)) : Nat}
  %Equal.sym(Nat, B.Octets.len(b), B.len(B.Octets.to_list(b)), BL.octets_len_list(b)) : {Nat.add(B.len(B.Octets.to_list(a)), B.len(B.Octets.to_list(b))) == Nat.add(B.len(B.Octets.to_list(a)), _) : Nat}
  {==}

def sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_add(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, UL.nat_add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      sub_zero(a)
    case 1n+q:
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), UL.nat_add_succ(a, q)) : {Nat.sub(_, 1n+q) == a : Nat}
      sub_add(a, q)

def nat_eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

def tl_db(+ps: Nat, +salt: B.Octets) -> {B.Octets.to_list(PS.rsa.pss.db(ps, salt)) == B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(PS.rsa.pss.db(ps, salt)), B.append(B.Octets.to_list(B.Octets.zeros(ps)), B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), salt))), BL.octets_append_list(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), salt))) : {_ == B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(ps)), B.zeros(ps), BL.octets_zeros_list(ps)) : {B.append(_, B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), salt))) == B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([1]), salt)), B.append(B.Octets.to_list(B.Octets.of_list([1])), B.Octets.to_list(salt)), BL.octets_append_list(B.Octets.of_list([1]), salt)) : {B.append(B.zeros(ps), _) == B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([1])), B.mask([1]), BL.octets_to_of([1])) : {B.append(B.zeros(ps), B.append(_, B.Octets.to_list(salt))) == B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}) : List<&2, U32>}
  {==}

def cd_oct(e: Nat, +ps: Nat, +salt: B.Octets) -> {O.RsaOct.clear_left(PS.rsa.pss.db(ps, salt), PS.rsa.pss.z(e)) == PS.rsa.pss.db(ps, salt) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(PS.rsa.pss.db(ps, salt)), B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}), tl_db(ps, salt)) : {B.Octets.of_list(O.rsa.mask1(_, U32.shrn(255, PS.rsa.pss.z(e)))) == PS.rsa.pss.db(ps, salt) : B.Octets}
  %Equal.sym(List<&2, U32>, O.rsa.mask1(B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}), U32.shrn(255, PS.rsa.pss.z(e))), B.append(B.zeros(ps), Con{B.byte(1), B.Octets.to_list(salt)}), cd_list(e, ps, B.Octets.to_list(salt))) : {B.Octets.of_list(_) == PS.rsa.pss.db(ps, salt) : B.Octets}
  %tl_db(ps, salt) : {B.Octets.of_list(_) == PS.rsa.pss.db(ps, salt) : B.Octets}
  BL.octets_of_to(PS.rsa.pss.db(ps, salt))

def pss_ok(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +mhash: B.Octets, +salt: B.Octets, +embits: Nat, +hf: {Nat.is_le(Nat.add(B.Octets.len(mhash), Nat.add(B.Octets.len(salt), 2n)), PS.RsaPss.em_len(embits)) == True{} : Bool}, +hd: {B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))) == B.Octets.len(mhash) : Nat}) -> {PS.rsa.pss.v0(~digest, ~mgf, mhash, B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), embits, B.Octets.len(salt)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(Nat.add(B.Octets.len(mhash), Nat.add(B.Octets.len(salt), 2n)), PS.RsaPss.em_len(embits)), True{}, hf) : {PS.rsa.pss.v1(~digest, ~mgf, _, mhash, B.Octets.take(Nat.sub(B.Octets.len(B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), B.Octets.drop(Nat.sub(B.Octets.len(B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), Nat.add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), B.Octets.len(B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), oct_len_app(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))) : {PS.rsa.pss.v1(~digest, ~mgf, True{}, mhash, B.Octets.take(Nat.sub(_, Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), B.Octets.drop(Nat.sub(_, Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), Nat.add(B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))), B.Octets.len(B.Octets.of_list([188]))), oct_len_app(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))) : {PS.rsa.pss.v1(~digest, ~mgf, True{}, mhash, B.Octets.take(Nat.sub(Nat.add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), _), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), B.Octets.drop(Nat.sub(Nat.add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), _), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))), B.Octets.len(mhash), hd) : {PS.rsa.pss.v1(~digest, ~mgf, True{}, mhash, B.Octets.take(Nat.sub(Nat.add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), Nat.add(_, B.Octets.len(B.Octets.of_list([188])))), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), B.Octets.drop(Nat.sub(Nat.add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), Nat.add(_, B.Octets.len(B.Octets.of_list([188])))), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), Nat.add(B.Octets.len(mhash), 1n)), Nat.add(B.Octets.len(mhash), 1n)), B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), sub_add(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), Nat.add(B.Octets.len(mhash), 1n))) : {PS.rsa.pss.v1(~digest, ~mgf, True{}, mhash, B.Octets.take(_, B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), B.Octets.drop(_, B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), BL.octets_take_append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))) : {PS.rsa.pss.v1(~digest, ~mgf, True{}, mhash, _, B.Octets.drop(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])), BL.octets_drop_append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188])))) : {PS.rsa.pss.v1(~digest, ~mgf, True{}, mhash, O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), _, embits, B.Octets.len(salt)) == True{} : Bool}
  %hd : {PS.rsa.pss.v2(~digest, ~mgf, True{}, mhash, O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.take(_, B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), B.Octets.drop(_, B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), digest(PS.rsa.pss.mprime(mhash, salt)), BL.octets_take_append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))) : {PS.rsa.pss.v2(~digest, ~mgf, True{}, mhash, O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), _, B.Octets.drop(B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), B.Octets.of_list([188]), BL.octets_drop_append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))) : {PS.rsa.pss.v2(~digest, ~mgf, True{}, mhash, O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), digest(PS.rsa.pss.mprime(mhash, salt)), _, embits, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, O.RsaOct.mask_first(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), U32.shrn(255, PS.rsa.pss.z(embits))), O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), oct_mask_first_idem(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), U32.shrn(255, PS.rsa.pss.z(embits)))) : {PS.rsa.pss.v3(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), B.Octets.is_eq(_, O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))))), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), O.RsaOct.clear_left(O.RsaOct.xor(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))))), PS.rsa.pss.z(embits)), B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Bool, B.Octets.is_eq(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), True{}, BL.octets_is_eq_refl(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)))) : {PS.rsa.pss.v3(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), _)), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), O.RsaOct.clear_left(O.RsaOct.xor(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))))), PS.rsa.pss.z(embits)), B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits))), B.Octets.len(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt))))), oct_mask_first_len(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), U32.shrn(255, PS.rsa.pss.z(embits)))) : {PS.rsa.pss.v3(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), True{})), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), O.RsaOct.clear_left(O.RsaOct.xor(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), _)), PS.rsa.pss.z(embits)), B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt))))), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)), oct_xor_len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt))))) : {PS.rsa.pss.v3(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), True{})), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), O.RsaOct.clear_left(O.RsaOct.xor(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), _)), PS.rsa.pss.z(embits)), B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, O.RsaOct.mask_first(O.RsaOct.xor(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), U32.shrn(255, PS.rsa.pss.z(embits))), O.RsaOct.mask_first(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), U32.shrn(255, PS.rsa.pss.z(embits))), pk_oct(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt))), U32.shrn(255, PS.rsa.pss.z(embits)))) : {PS.rsa.pss.v3(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), True{})), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), _, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(B.Octets, O.RsaOct.clear_left(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), PS.rsa.pss.z(embits)), PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), cd_oct(embits, Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)) : {PS.rsa.pss.v3(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), True{})), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), _, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)), B.append(B.zeros(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n)))), Con{B.byte(1), B.Octets.to_list(salt)}), tl_db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)) : {PS.rsa.pss.v4(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), True{})), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), O.rsa.sep(_), _, B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(Maybe<&2, Nat>, O.rsa.sep(B.append(B.zeros(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n)))), Con{B.byte(1), B.Octets.to_list(salt)})), Some{Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n)))}, sep_zeros(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), B.byte(1), B.Octets.to_list(salt), {==}, {==})) : {PS.rsa.pss.v4(~digest, Bool.and(True{}, Bool.and(B.Octets.is_eq(B.Octets.of_list([188]), B.Octets.of_list([188])), True{})), mhash, digest(PS.rsa.pss.mprime(mhash, salt)), _, B.append(B.zeros(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n)))), Con{B.byte(1), B.Octets.to_list(salt)}), B.Octets.len(salt)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, B.drop(Nat.add(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), 1n), B.append(B.zeros(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n)))), Con{B.byte(1), B.Octets.to_list(salt)})), B.Octets.to_list(salt), drop_zeros(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), B.byte(1), B.Octets.to_list(salt))) : {Bool.and(Nat.is_eq(B.Octets.len(B.Octets.of_list(_)), B.Octets.len(salt)), B.Octets.is_eq(digest(PS.rsa.pss.mprime(mhash, salt)), digest(PS.rsa.pss.mprime(mhash, B.Octets.of_list(_))))) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(salt)), salt, BL.octets_of_to(salt)) : {Bool.and(Nat.is_eq(B.Octets.len(_), B.Octets.len(salt)), B.Octets.is_eq(digest(PS.rsa.pss.mprime(mhash, salt)), digest(PS.rsa.pss.mprime(mhash, _)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(salt), B.Octets.len(salt)), True{}, nat_eq_refl(B.Octets.len(salt))) : {Bool.and(_, B.Octets.is_eq(digest(PS.rsa.pss.mprime(mhash, salt)), digest(PS.rsa.pss.mprime(mhash, salt)))) == True{} : Bool}
  %Equal.sym(Bool, B.Octets.is_eq(digest(PS.rsa.pss.mprime(mhash, salt)), digest(PS.rsa.pss.mprime(mhash, salt))), True{}, BL.octets_is_eq_refl(digest(PS.rsa.pss.mprime(mhash, salt)))) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def pss_case(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, fits: Bool, +mhash: B.Octets, +salt: B.Octets, +embits: Nat, +hf: {Nat.is_le(Nat.add(B.Octets.len(mhash), Nat.add(B.Octets.len(salt), 2n)), PS.RsaPss.em_len(embits)) == fits : Bool}, +hd: {B.Octets.len(digest(PS.rsa.pss.mprime(mhash, salt))) == B.Octets.len(mhash) : Nat}) -> {Result.map(&2, &2, R.RsaError, B.Octets, Bool, em => PS.rsa.pss.v0(~digest, ~mgf, mhash, em, embits, B.Octets.len(salt)), PS.rsa.pss.enc(~digest, ~mgf, fits, mhash, salt, embits)) == Result.map(&2, &2, R.RsaError, B.Octets, Bool, em => True{}, PS.rsa.pss.enc(~digest, ~mgf, fits, mhash, salt, embits)) : Result<&2, &2, R.RsaError, Bool>}:
  match fits:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, PS.rsa.pss.v0(~digest, ~mgf, mhash, B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt), mgf(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.len(PS.rsa.pss.db(Nat.sub(PS.RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n))), salt)))), PS.rsa.pss.z(embits)), B.Octets.append(digest(PS.rsa.pss.mprime(mhash, salt)), B.Octets.of_list([188]))), embits, B.Octets.len(salt)), True{}, pss_ok(~digest, ~mgf, mhash, salt, embits, hf, hd)) : {Done{_} == Done{True{}} : Result<&2, &2, R.RsaError, Bool>}
      {==}

def Laws.pss_round_trip(digest, mgf, m, salt, embits, hd):
  pss_case(~digest, ~mgf, Nat.is_le(Nat.add(B.Octets.len(digest(m)), Nat.add(B.Octets.len(salt), 2n)), PS.RsaPss.em_len(embits)), digest(m), salt, embits, {==}, hd)

# Small-parameter exhaustive laws

# BEGIN GENERATED by gen/exhaustive.py: exhaustive
def ex.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ex.absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : ex.bdisc(_)
  Unit{}

def ex.toy_round_trip.c0() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(0n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c1() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(1n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c2() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(2n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c3() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(3n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c4() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(4n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c5() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(5n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c6() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(6n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c7() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(7n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c8() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(8n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c9() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(9n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c10() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(10n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c11() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(11n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c12() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(12n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c13() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(13n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c14() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(14n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c15() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(15n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c16() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(16n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c17() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(17n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c18() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(18n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c19() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(19n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c20() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(20n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c21() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(21n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c22() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(22n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c23() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(23n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c24() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(24n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c25() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(25n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c26() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(26n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c27() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(27n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c28() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(28n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c29() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(29n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c30() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(30n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c31() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(31n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c32() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(32n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c33() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(33n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c34() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(34n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c35() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(35n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c36() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(36n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c37() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(37n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c38() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(38n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c39() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(39n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c40() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(40n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c41() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(41n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c42() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(42n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c43() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(43n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c44() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(44n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c45() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(45n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c46() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(46n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c47() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(47n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c48() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(48n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c49() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(49n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c50() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(50n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c51() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(51n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c52() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(52n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c53() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(53n)) == True{} : Bool}:
  {==}

def ex.toy_round_trip.c54() -> {Laws.rsalaw.round_trip(Laws.rsalaw.nat(54n)) == True{} : Bool}:
  {==}

def Laws.toy_round_trip(m, hm):
  match m:
    case 0n:
      ex.toy_round_trip.c0()
    case 1n+m0:
      match m0:
        case 0n:
          ex.toy_round_trip.c1()
        case 1n+m1:
          match m1:
            case 0n:
              ex.toy_round_trip.c2()
            case 1n+m2:
              match m2:
                case 0n:
                  ex.toy_round_trip.c3()
                case 1n+m3:
                  match m3:
                    case 0n:
                      ex.toy_round_trip.c4()
                    case 1n+m4:
                      match m4:
                        case 0n:
                          ex.toy_round_trip.c5()
                        case 1n+m5:
                          match m5:
                            case 0n:
                              ex.toy_round_trip.c6()
                            case 1n+m6:
                              match m6:
                                case 0n:
                                  ex.toy_round_trip.c7()
                                case 1n+m7:
                                  match m7:
                                    case 0n:
                                      ex.toy_round_trip.c8()
                                    case 1n+m8:
                                      match m8:
                                        case 0n:
                                          ex.toy_round_trip.c9()
                                        case 1n+m9:
                                          match m9:
                                            case 0n:
                                              ex.toy_round_trip.c10()
                                            case 1n+m10:
                                              match m10:
                                                case 0n:
                                                  ex.toy_round_trip.c11()
                                                case 1n+m11:
                                                  match m11:
                                                    case 0n:
                                                      ex.toy_round_trip.c12()
                                                    case 1n+m12:
                                                      match m12:
                                                        case 0n:
                                                          ex.toy_round_trip.c13()
                                                        case 1n+m13:
                                                          match m13:
                                                            case 0n:
                                                              ex.toy_round_trip.c14()
                                                            case 1n+m14:
                                                              match m14:
                                                                case 0n:
                                                                  ex.toy_round_trip.c15()
                                                                case 1n+m15:
                                                                  match m15:
                                                                    case 0n:
                                                                      ex.toy_round_trip.c16()
                                                                    case 1n+m16:
                                                                      match m16:
                                                                        case 0n:
                                                                          ex.toy_round_trip.c17()
                                                                        case 1n+m17:
                                                                          match m17:
                                                                            case 0n:
                                                                              ex.toy_round_trip.c18()
                                                                            case 1n+m18:
                                                                              match m18:
                                                                                case 0n:
                                                                                  ex.toy_round_trip.c19()
                                                                                case 1n+m19:
                                                                                  match m19:
                                                                                    case 0n:
                                                                                      ex.toy_round_trip.c20()
                                                                                    case 1n+m20:
                                                                                      match m20:
                                                                                        case 0n:
                                                                                          ex.toy_round_trip.c21()
                                                                                        case 1n+m21:
                                                                                          match m21:
                                                                                            case 0n:
                                                                                              ex.toy_round_trip.c22()
                                                                                            case 1n+m22:
                                                                                              match m22:
                                                                                                case 0n:
                                                                                                  ex.toy_round_trip.c23()
                                                                                                case 1n+m23:
                                                                                                  match m23:
                                                                                                    case 0n:
                                                                                                      ex.toy_round_trip.c24()
                                                                                                    case 1n+m24:
                                                                                                      match m24:
                                                                                                        case 0n:
                                                                                                          ex.toy_round_trip.c25()
                                                                                                        case 1n+m25:
                                                                                                          match m25:
                                                                                                            case 0n:
                                                                                                              ex.toy_round_trip.c26()
                                                                                                            case 1n+m26:
                                                                                                              match m26:
                                                                                                                case 0n:
                                                                                                                  ex.toy_round_trip.c27()
                                                                                                                case 1n+m27:
                                                                                                                  match m27:
                                                                                                                    case 0n:
                                                                                                                      ex.toy_round_trip.c28()
                                                                                                                    case 1n+m28:
                                                                                                                      match m28:
                                                                                                                        case 0n:
                                                                                                                          ex.toy_round_trip.c29()
                                                                                                                        case 1n+m29:
                                                                                                                          match m29:
                                                                                                                            case 0n:
                                                                                                                              ex.toy_round_trip.c30()
                                                                                                                            case 1n+m30:
                                                                                                                              match m30:
                                                                                                                                case 0n:
                                                                                                                                  ex.toy_round_trip.c31()
                                                                                                                                case 1n+m31:
                                                                                                                                  match m31:
                                                                                                                                    case 0n:
                                                                                                                                      ex.toy_round_trip.c32()
                                                                                                                                    case 1n+m32:
                                                                                                                                      match m32:
                                                                                                                                        case 0n:
                                                                                                                                          ex.toy_round_trip.c33()
                                                                                                                                        case 1n+m33:
                                                                                                                                          match m33:
                                                                                                                                            case 0n:
                                                                                                                                              ex.toy_round_trip.c34()
                                                                                                                                            case 1n+m34:
                                                                                                                                              match m34:
                                                                                                                                                case 0n:
                                                                                                                                                  ex.toy_round_trip.c35()
                                                                                                                                                case 1n+m35:
                                                                                                                                                  match m35:
                                                                                                                                                    case 0n:
                                                                                                                                                      ex.toy_round_trip.c36()
                                                                                                                                                    case 1n+m36:
                                                                                                                                                      match m36:
                                                                                                                                                        case 0n:
                                                                                                                                                          ex.toy_round_trip.c37()
                                                                                                                                                        case 1n+m37:
                                                                                                                                                          match m37:
                                                                                                                                                            case 0n:
                                                                                                                                                              ex.toy_round_trip.c38()
                                                                                                                                                            case 1n+m38:
                                                                                                                                                              match m38:
                                                                                                                                                                case 0n:
                                                                                                                                                                  ex.toy_round_trip.c39()
                                                                                                                                                                case 1n+m39:
                                                                                                                                                                  match m39:
                                                                                                                                                                    case 0n:
                                                                                                                                                                      ex.toy_round_trip.c40()
                                                                                                                                                                    case 1n+m40:
                                                                                                                                                                      match m40:
                                                                                                                                                                        case 0n:
                                                                                                                                                                          ex.toy_round_trip.c41()
                                                                                                                                                                        case 1n+m41:
                                                                                                                                                                          match m41:
                                                                                                                                                                            case 0n:
                                                                                                                                                                              ex.toy_round_trip.c42()
                                                                                                                                                                            case 1n+m42:
                                                                                                                                                                              match m42:
                                                                                                                                                                                case 0n:
                                                                                                                                                                                  ex.toy_round_trip.c43()
                                                                                                                                                                                case 1n+m43:
                                                                                                                                                                                  match m43:
                                                                                                                                                                                    case 0n:
                                                                                                                                                                                      ex.toy_round_trip.c44()
                                                                                                                                                                                    case 1n+m44:
                                                                                                                                                                                      match m44:
                                                                                                                                                                                        case 0n:
                                                                                                                                                                                          ex.toy_round_trip.c45()
                                                                                                                                                                                        case 1n+m45:
                                                                                                                                                                                          match m45:
                                                                                                                                                                                            case 0n:
                                                                                                                                                                                              ex.toy_round_trip.c46()
                                                                                                                                                                                            case 1n+m46:
                                                                                                                                                                                              match m46:
                                                                                                                                                                                                case 0n:
                                                                                                                                                                                                  ex.toy_round_trip.c47()
                                                                                                                                                                                                case 1n+m47:
                                                                                                                                                                                                  match m47:
                                                                                                                                                                                                    case 0n:
                                                                                                                                                                                                      ex.toy_round_trip.c48()
                                                                                                                                                                                                    case 1n+m48:
                                                                                                                                                                                                      match m48:
                                                                                                                                                                                                        case 0n:
                                                                                                                                                                                                          ex.toy_round_trip.c49()
                                                                                                                                                                                                        case 1n+m49:
                                                                                                                                                                                                          match m49:
                                                                                                                                                                                                            case 0n:
                                                                                                                                                                                                              ex.toy_round_trip.c50()
                                                                                                                                                                                                            case 1n+m50:
                                                                                                                                                                                                              match m50:
                                                                                                                                                                                                                case 0n:
                                                                                                                                                                                                                  ex.toy_round_trip.c51()
                                                                                                                                                                                                                case 1n+m51:
                                                                                                                                                                                                                  match m51:
                                                                                                                                                                                                                    case 0n:
                                                                                                                                                                                                                      ex.toy_round_trip.c52()
                                                                                                                                                                                                                    case 1n+m52:
                                                                                                                                                                                                                      match m52:
                                                                                                                                                                                                                        case 0n:
                                                                                                                                                                                                                          ex.toy_round_trip.c53()
                                                                                                                                                                                                                        case 1n+m53:
                                                                                                                                                                                                                          match m53:
                                                                                                                                                                                                                            case 0n:
                                                                                                                                                                                                                              ex.toy_round_trip.c54()
                                                                                                                                                                                                                            case 1n+m54:
                                                                                                                                                                                                                              match m54:
                                                                                                                                                                                                                                case 0n:
                                                                                                                                                                                                                                  Empty.absurd({Laws.rsalaw.round_trip(Laws.rsalaw.nat(55n)) == True{} : Bool}, ex.absurd(hm))
                                                                                                                                                                                                                                case 1n+mz:
                                                                                                                                                                                                                                  Empty.absurd({Laws.rsalaw.round_trip(Laws.rsalaw.nat(56n+mz)) == True{} : Bool}, ex.absurd(hm))
# END GENERATED: exhaustive

# The keys' raw forms. The reader takes an integer only where the form holds
# exactly the field the writer writes for it (rsa.take.exact: its length,
# then its shortest bytes), so a field written for an integer that reads
# back from its shortest bytes is read back (kr.field, for the conditional
# laws), and every form the reader accepts is the form the writer writes for
# what it read (kr.inv0, for the unconditional ones)

# Nat, words, lists and Octets

def kr.nat_eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      kr.nat_eq_refl(p)

def kr.nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, ex.absurd(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, ex.absurd(h))
    case 1n+p 1n+q:
      %kr.nat_eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def kr.and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ex.absurd(h))

def kr.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, ex.absurd(h))

def kr.u32_eq_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(x, x), Nat.is_eq(U32.to_nat(x), U32.to_nat(x)), UL.u32_eq_value(x, x)) : {_ == True{} : Bool}
  kr.nat_eq_refl(U32.to_nat(x))

def kr.u32_eq_true(+x: U32, +y: U32, h: {U32.is_eq(x, y) == True{} : Bool}) -> {x == y : U32}:
  UL.u32_value_eq(x, y, kr.nat_eq_true(U32.to_nat(x), U32.to_nat(y), Equal.trans(Bool, Nat.is_eq(U32.to_nat(x), U32.to_nat(y)), U32.is_eq(x, y), True{}, Equal.sym(Bool, U32.is_eq(x, y), Nat.is_eq(U32.to_nat(x), U32.to_nat(y)), UL.u32_eq_value(x, y)), h)))

# rsa.same is equality of word lists
def kr.same_refl(+xs: List<&2, U32>) -> {K.rsa.same(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, kr.u32_eq_refl(x)) : {Bool.and(_, K.rsa.same(t, t)) == True{} : Bool}
      kr.same_refl(t)

def kr.same_sound(+xs: List<&2, U32>, +ys: List<&2, U32>, +h: {K.rsa.same(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      %kr.u32_eq_true(x, y, kr.and_l(U32.is_eq(x, y), K.rsa.same(xt, yt), h)) : {Con{x, xt} == Con{_, yt} : List<&2, U32>}
      %kr.same_sound(xt, yt, kr.and_r(U32.is_eq(x, y), K.rsa.same(xt, yt), h)) : {Con{x, xt} == Con{x, _} : List<&2, U32>}
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({Nil{} == Con{y, yt} : List<&2, U32>}, ex.absurd(h))
    case Con{x, xt} Nil{}:
      Empty.absurd({Con{x, xt} == Nil{} : List<&2, U32>}, ex.absurd(h))

# Octets with the same bytes are the same
def kr.oct_eq(+a: B.Octets, +b: B.Octets, h: {B.Octets.to_list(a) == B.Octets.to_list(b) : List<&2, U32>}) -> {a == b : B.Octets}:
  %BL.octets_of_to(a) : {_ == b : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(a), B.Octets.to_list(b), h) : {B.Octets.of_list(_) == b : B.Octets}
  BL.octets_of_to(b)

def kr.len0l(+xs: List<&2, U32>, h: {Nat.is_eq(B.len(xs), 0n) == True{} : Bool}) -> {xs == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, U32>}, ex.absurd(h))

def kr.len0h(+o: B.Octets, h: {Nat.is_eq(B.Octets.len(o), 0n) == True{} : Bool}) -> {Nat.is_eq(B.len(B.Octets.to_list(o)), 0n) == True{} : Bool}:
  %BL.octets_len_list(o) : {Nat.is_eq(_, 0n) == True{} : Bool}
  h

# a byte string of no bytes is the empty one
def kr.len0(+o: B.Octets, h: {Nat.is_eq(B.Octets.len(o), 0n) == True{} : Bool}) -> {o == B.Octets.empty() : B.Octets}:
  %BL.octets_of_to(o) : {_ == B.Octets.empty() : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(o), Nil{}, kr.len0l(B.Octets.to_list(o), kr.len0h(o, h))) : {B.Octets.of_list(_) == B.Octets.empty() : B.Octets}
  {==}

def kr.tail0(+f: B.Octets, +r: B.Octets, h: {Nat.is_eq(B.Octets.len(r), 0n) == True{} : Bool}) -> {f == B.Octets.append(f, r) : B.Octets}:
  %Equal.sym(B.Octets, r, B.Octets.empty(), kr.len0(r, h)) : {f == B.Octets.append(f, _) : B.Octets}
  Equal.sym(B.Octets, B.Octets.append(f, B.Octets.empty()), f, BL.octets_append_empty_r(f))

def kr.val(r: Result<&2, &2, R.RsaError, B.Octets>) -> B.Octets:
  match r:
    case Done{v}:
      v
    case Fail{er}:
      B.Octets.empty()

def kr.done_inj(+a: B.Octets, +b: B.Octets, h: {Done{a} == Done{b} : Result<&2, &2, R.RsaError, B.Octets>}) -> {a == b : B.Octets}:
  Equal.cong(Result<&2, &2, R.RsaError, B.Octets>, B.Octets, r => kr.val(r), Done{a}, Done{b}, h)

# The writer's fields read back: the length at offset 0 (bytes' laws), the
# integer's bytes after it, and the field compared with the writer's

def kr.le4(+v: U32) -> {Nat.is_le(Nat.add(0n, 4n), B.Octets.len(B.Octets.be32(v))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.be32(v)), 4n, BL.octets_len_be32(v)) : {Nat.is_le(4n, _) == True{} : Bool}
  {==}

def kr.drop4(+v: U32, +y: B.Octets) -> {B.Octets.drop(4n, B.Octets.append(B.Octets.be32(v), y)) == y : B.Octets}:
  %BL.octets_len_be32(v) : {B.Octets.drop(_, B.Octets.append(B.Octets.be32(v), y)) == y : B.Octets}
  BL.octets_drop_append(B.Octets.be32(v), y)
# the length field read at the start of a field and what follows it
def kr.read2(+v: U32, +m: B.Octets, +rest: B.Octets) -> {K.rsa.read(B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) == K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.append(m, rest))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}:
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest), B.Octets.append(B.Octets.be32(v), B.Octets.append(m, rest)), BL.octets_append_assoc(B.Octets.be32(v), m, rest)) : {K.rsa.take(B.Octets.be32_at(_, 0n), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) == K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.append(m, rest))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(v), B.Octets.append(m, rest)), 0n), B.Octets.be32_at(B.Octets.be32(v), 0n), BL.octets_be32_at_append_le(B.Octets.be32(v), B.Octets.append(m, rest), 0n, kr.le4(v))) : {K.rsa.take(_, B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) == K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.append(m, rest))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.be32(v), 0n), Some{v}, BL.octets_be32_round_trip(v)) : {K.rsa.take(_, B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) == K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.append(m, rest))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest), B.Octets.append(B.Octets.be32(v), B.Octets.append(m, rest)), BL.octets_append_assoc(B.Octets.be32(v), m, rest)) : {K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.drop(4n, _))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) == K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.append(m, rest))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(B.Octets, B.Octets.drop(4n, B.Octets.append(B.Octets.be32(v), B.Octets.append(m, rest))), B.Octets.append(m, rest), kr.drop4(v, B.Octets.append(m, rest))) : {K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(_)), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) == K.rsa.take.go(Nat.is_le(U32.to_nat(v), B.Octets.len(B.Octets.append(m, rest))), U32.to_nat(v), B.Octets.append(B.Octets.append(B.Octets.be32(v), m), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  {==}
# the integer's bytes after the length, when the length is their count (hl)
# and they read back as the integer (hx)
def kr.go_true(+x: N.BnNat, +rest: B.Octets, +hx: {N.BnNat.of_octets(N.BnNat.to_octets_min(x)) == x : N.BnNat}, +hl: {U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))) == B.Octets.len(N.BnNat.to_octets_min(x)) : Nat}) -> {K.rsa.take.go(Nat.is_le(U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.len(B.Octets.append(N.BnNat.to_octets_min(x), rest))), U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.len(N.BnNat.to_octets_min(x)), hl) : {K.rsa.take.go(Nat.is_le(_, B.Octets.len(B.Octets.append(N.BnNat.to_octets_min(x), rest))), _, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(N.BnNat.to_octets_min(x), rest)), Nat.add(B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.len(rest)), BL.octets_len_append(N.BnNat.to_octets_min(x), rest)) : {K.rsa.take.go(Nat.is_le(B.Octets.len(N.BnNat.to_octets_min(x)), _), B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(Bool, Nat.is_le(B.Octets.len(N.BnNat.to_octets_min(x)), Nat.add(B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.len(rest))), True{}, UO.nat_le_add_r(B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.len(rest))) : {K.rsa.take.go(_, B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest), B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.append(N.BnNat.to_octets_min(x), rest)), BL.octets_append_assoc(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x), rest)) : {K.rsa.take.of(N.BnNat.of_octets(B.Octets.take(B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.drop(4n, _))), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(B.Octets, B.Octets.drop(4n, B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.append(N.BnNat.to_octets_min(x), rest))), B.Octets.append(N.BnNat.to_octets_min(x), rest), kr.drop4(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x))), B.Octets.append(N.BnNat.to_octets_min(x), rest))) : {K.rsa.take.of(N.BnNat.of_octets(B.Octets.take(B.Octets.len(N.BnNat.to_octets_min(x)), _)), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(N.BnNat.to_octets_min(x)), B.Octets.append(N.BnNat.to_octets_min(x), rest)), N.BnNat.to_octets_min(x), BL.octets_take_append(N.BnNat.to_octets_min(x), rest)) : {K.rsa.take.of(N.BnNat.of_octets(_), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(N.BnNat, N.BnNat.of_octets(N.BnNat.to_octets_min(x)), x, hx) : {K.rsa.take.of(_, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) == K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)) : Result<&2, &2, R.RsaError, K.RsaField>}
  {==}
# the writer's field for x, at the start of a form, is taken
def kr.of_field(+x: N.BnNat, +rest: B.Octets) -> {K.rsa.take.of(x, B.Octets.append(K.rsa.field(x), rest)) == Done{K.RsaField{x, rest}} : Result<&2, &2, R.RsaError, K.RsaField>}:
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(K.rsa.field(x)), B.Octets.append(K.rsa.field(x), rest)), K.rsa.field(x), BL.octets_take_append(K.rsa.field(x), rest)) : {K.rsa.take.min(K.rsa.same(B.Octets.to_list(_), B.Octets.to_list(K.rsa.field(x))), x, B.Octets.len(K.rsa.field(x)), B.Octets.append(K.rsa.field(x), rest)) == Done{K.RsaField{x, rest}} : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(Bool, K.rsa.same(B.Octets.to_list(K.rsa.field(x)), B.Octets.to_list(K.rsa.field(x))), True{}, kr.same_refl(B.Octets.to_list(K.rsa.field(x)))) : {K.rsa.take.min(_, x, B.Octets.len(K.rsa.field(x)), B.Octets.append(K.rsa.field(x), rest)) == Done{K.RsaField{x, rest}} : Result<&2, &2, R.RsaError, K.RsaField>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(K.rsa.field(x)), B.Octets.append(K.rsa.field(x), rest)), rest, BL.octets_drop_append(K.rsa.field(x), rest)) : {Done{K.RsaField{x, _}} == Done{K.RsaField{x, rest}} : Result<&2, &2, R.RsaError, K.RsaField>}
  {==}

# a field, and the bytes after it, read back
def kr.field(+x: N.BnNat, +rest: B.Octets, +hx: {N.BnNat.of_octets(N.BnNat.to_octets_min(x)) == x : N.BnNat}, +hl: {U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))) == B.Octets.len(N.BnNat.to_octets_min(x)) : Nat}) -> {K.rsa.read(B.Octets.append(K.rsa.field(x), rest)) == Done{K.RsaField{x, rest}} : Result<&2, &2, R.RsaError, K.RsaField>}:
  Equal.trans(Result<&2, &2, R.RsaError, K.RsaField>, K.rsa.read(B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)), K.rsa.take.go(Nat.is_le(U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.len(B.Octets.append(N.BnNat.to_octets_min(x), rest))), U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)), Done{K.RsaField{x, rest}},
    kr.read2(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x))), N.BnNat.to_octets_min(x), rest),
    Equal.trans(Result<&2, &2, R.RsaError, K.RsaField>, K.rsa.take.go(Nat.is_le(U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.len(B.Octets.append(N.BnNat.to_octets_min(x), rest))), U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)), K.rsa.take.of(x, B.Octets.append(B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))), N.BnNat.to_octets_min(x)), rest)), Done{K.RsaField{x, rest}},
      kr.go_true(x, rest, hx, hl),
      kr.of_field(x, rest)))
def Laws.public_form_round_trip_if(n, e, hn, he, ln, le):
  %Equal.sym(Result<&2, &2, R.RsaError, K.RsaField>, K.rsa.read(B.Octets.append(K.rsa.field(n), K.rsa.field(e))), Done{K.RsaField{n, K.rsa.field(e)}}, kr.field(n, K.rsa.field(e), hn, ln)) : {Result.bind(&2, &2, R.RsaError, K.RsaField, R.RsaPublic, _, a => K.rsa.read.pub(a)) == R.Rsa.public_of(n, e) : Result<&2, &2, R.RsaError, R.RsaPublic>}
  %BL.octets_append_empty_r(K.rsa.field(e)) : {K.rsa.read.pub2(n, K.rsa.read(_)) == R.Rsa.public_of(n, e) : Result<&2, &2, R.RsaError, R.RsaPublic>}
  %Equal.sym(Result<&2, &2, R.RsaError, K.RsaField>, K.rsa.read(B.Octets.append(K.rsa.field(e), B.Octets.empty())), Done{K.RsaField{e, B.Octets.empty()}}, kr.field(e, B.Octets.empty(), he, le)) : {K.rsa.read.pub2(n, _) == R.Rsa.public_of(n, e) : Result<&2, &2, R.RsaError, R.RsaPublic>}
  {==}

def kr.concat5(+a: B.Octets, +b: B.Octets, +c: B.Octets, +d: B.Octets, +f: B.Octets) -> {B.Octets.concat(Con{a, Con{b, Con{c, Con{d, Con{f, Nil{}}}}}}) == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.concat(Con{a, Con{b, Con{c, Con{d, Con{f, Nil{}}}}}}), B.Octets.append(a, B.Octets.concat(Con{b, Con{c, Con{d, Con{f, Nil{}}}}})), BL.octets_concat_cons(a, Con{b, Con{c, Con{d, Con{f, Nil{}}}}})) : {_ == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.concat(Con{b, Con{c, Con{d, Con{f, Nil{}}}}}), B.Octets.append(b, B.Octets.concat(Con{c, Con{d, Con{f, Nil{}}}})), BL.octets_concat_cons(b, Con{c, Con{d, Con{f, Nil{}}}})) : {B.Octets.append(a, _) == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.concat(Con{c, Con{d, Con{f, Nil{}}}}), B.Octets.append(c, B.Octets.concat(Con{d, Con{f, Nil{}}})), BL.octets_concat_cons(c, Con{d, Con{f, Nil{}}})) : {B.Octets.append(a, B.Octets.append(b, _)) == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.concat(Con{d, Con{f, Nil{}}}), B.Octets.append(d, B.Octets.concat(Con{f, Nil{}})), BL.octets_concat_cons(d, Con{f, Nil{}})) : {B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, _))) == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.concat(Con{f, Nil{}}), B.Octets.append(f, B.Octets.concat(Nil{})), BL.octets_concat_cons(f, Nil{})) : {B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, _)))) == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.concat(Nil{}), B.Octets.empty(), BL.octets_concat_nil()) : {B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, _))))) == B.Octets.append(a, B.Octets.append(b, B.Octets.append(c, B.Octets.append(d, B.Octets.append(f, B.Octets.empty()))))) : B.Octets}
  {==}

# a field, and then k more integers, read
def kr.readn(+x: N.BnNat, +rest: B.Octets, +k: Nat, +hx: {N.BnNat.of_octets(N.BnNat.to_octets_min(x)) == x : N.BnNat}, +hl: {U32.to_nat(U32.from_nat(B.Octets.len(N.BnNat.to_octets_min(x)))) == B.Octets.len(N.BnNat.to_octets_min(x)) : Nat}) -> {K.rsa.read.n(1n+k, B.Octets.append(K.rsa.field(x), rest)) == Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x, t}, K.rsa.read.n(k, rest)) : Result<&2, &2, R.RsaError, List<&2, N.BnNat>>}:
  %Equal.sym(Result<&2, &2, R.RsaError, K.RsaField>, K.rsa.read(B.Octets.append(K.rsa.field(x), rest)), Done{K.RsaField{x, rest}}, kr.field(x, rest, hx, hl)) : {Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, _, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(k, K.RsaField.rest(a)))) == Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x, t}, K.rsa.read.n(k, rest)) : Result<&2, &2, R.RsaError, List<&2, N.BnNat>>}
  {==}

def Laws.private_form_round_trip_if(n, e, d, p, q, dp, dq, qinv, hn, he, hd, hp, hq, ln, le, ld, lp, lq):
  %Equal.sym(B.Octets, B.Octets.concat(Con{K.rsa.field(n), Con{K.rsa.field(e), Con{K.rsa.field(d), Con{K.rsa.field(p), Con{K.rsa.field(q), Nil{}}}}}}), B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))), kr.concat5(K.rsa.field(n), K.rsa.field(e), K.rsa.field(d), K.rsa.field(p), K.rsa.field(q))) : {Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, K.rsa.read.n(5n, _), xs => K.rsa.read.priv(xs)) == R.Rsa.private_of(n, e, d, p, q) : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  %Equal.sym(Result<&2, &2, R.RsaError, List<&2, N.BnNat>>, K.rsa.read.n(5n, B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())))))), Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{n, t}, K.rsa.read.n(4n, B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())))))), kr.readn(n, B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())))), 4n, hn, ln)) : {Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, _, xs => K.rsa.read.priv(xs)) == R.Rsa.private_of(n, e, d, p, q) : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  %Equal.sym(Result<&2, &2, R.RsaError, List<&2, N.BnNat>>, K.rsa.read.n(4n, B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))), Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{e, t}, K.rsa.read.n(3n, B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))), kr.readn(e, B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))), 3n, he, le)) : {Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{n, t}, _), xs => K.rsa.read.priv(xs)) == R.Rsa.private_of(n, e, d, p, q) : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  %Equal.sym(Result<&2, &2, R.RsaError, List<&2, N.BnNat>>, K.rsa.read.n(3n, B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())))), Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{d, t}, K.rsa.read.n(2n, B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())))), kr.readn(d, B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())), 2n, hd, ld)) : {Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{n, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{e, t}, _)), xs => K.rsa.read.priv(xs)) == R.Rsa.private_of(n, e, d, p, q) : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  %Equal.sym(Result<&2, &2, R.RsaError, List<&2, N.BnNat>>, K.rsa.read.n(2n, B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))), Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{p, t}, K.rsa.read.n(1n, B.Octets.append(K.rsa.field(q), B.Octets.empty()))), kr.readn(p, B.Octets.append(K.rsa.field(q), B.Octets.empty()), 1n, hp, lp)) : {Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{n, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{e, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{d, t}, _))), xs => K.rsa.read.priv(xs)) == R.Rsa.private_of(n, e, d, p, q) : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  %Equal.sym(Result<&2, &2, R.RsaError, List<&2, N.BnNat>>, K.rsa.read.n(1n, B.Octets.append(K.rsa.field(q), B.Octets.empty())), Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{q, t}, K.rsa.read.n(0n, B.Octets.empty())), kr.readn(q, B.Octets.empty(), 0n, hq, lq)) : {Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{n, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{e, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{d, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{p, t}, _)))), xs => K.rsa.read.priv(xs)) == R.Rsa.private_of(n, e, d, p, q) : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  {==}

# Every form the reader accepts is the writer's: the reader takes a field
# only where the form starts with exactly the writer's field for what it
# read (kr.inv4), so the field and what follows are the form

def kr.inv4(+o: B.Octets, +x: N.BnNat, ok: Bool, +hok: {K.rsa.same(B.Octets.to_list(B.Octets.take(B.Octets.len(K.rsa.field(x)), o)), B.Octets.to_list(K.rsa.field(x))) == ok : Bool}) -> {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), K.rsa.take.min(ok, x, B.Octets.len(K.rsa.field(x)), o)) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, K.rsa.take.min(ok, x, B.Octets.len(K.rsa.field(x)), o)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match ok:
    case True{}:
      %kr.oct_eq(B.Octets.take(B.Octets.len(K.rsa.field(x)), o), K.rsa.field(x), kr.same_sound(B.Octets.to_list(B.Octets.take(B.Octets.len(K.rsa.field(x)), o)), B.Octets.to_list(K.rsa.field(x)), hok)) : {Done{B.Octets.append(_, B.Octets.drop(B.Octets.len(K.rsa.field(x)), o))} == Done{o} : Result<&2, &2, R.RsaError, B.Octets>}
      %Equal.sym(B.Octets, B.Octets.append(B.Octets.take(B.Octets.len(K.rsa.field(x)), o), B.Octets.drop(B.Octets.len(K.rsa.field(x)), o)), o, BL.octets_take_drop(B.Octets.len(K.rsa.field(x)), o)) : {Done{_} == Done{o} : Result<&2, &2, R.RsaError, B.Octets>}
      {==}
    case False{}:
      {==}

def kr.inv3(+o: B.Octets, +x: N.BnNat) -> {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), K.rsa.take.of(x, o)) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, K.rsa.take.of(x, o)) : Result<&2, &2, R.RsaError, B.Octets>}:
  kr.inv4(o, x, K.rsa.same(B.Octets.to_list(B.Octets.take(B.Octets.len(K.rsa.field(x)), o)), B.Octets.to_list(K.rsa.field(x))), {==})

def kr.inv2(+o: B.Octets, +n: Nat, fits: Bool) -> {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), K.rsa.take.go(fits, n, o)) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, K.rsa.take.go(fits, n, o)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match fits:
    case True{}:
      kr.inv3(o, N.BnNat.of_octets(B.Octets.take(n, B.Octets.drop(4n, o))))
    case False{}:
      {==}

def kr.inv1(+o: B.Octets, ml: Maybe<&2, U32>) -> {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), K.rsa.take(ml, o)) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, K.rsa.take(ml, o)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match ml:
    case Some{+l}:
      kr.inv2(o, U32.to_nat(l), Nat.is_le(U32.to_nat(l), B.Octets.len(B.Octets.drop(4n, o))))
    case None{}:
      {==}

def kr.inv0(+o: B.Octets) -> {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), K.rsa.read(o)) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, K.rsa.read(o)) : Result<&2, &2, R.RsaError, B.Octets>}:
  kr.inv1(o, B.Octets.be32_at(o, 0n))
# A public form read and written back

def kr.pw4(+o: B.Octets, +x1: N.BnNat, +x2: N.BnNat, e: {B.Octets.append(K.rsa.field(x1), K.rsa.field(x2)) == o : B.Octets}, c: Result<&2, &2, R.RsaError, Unit>) -> {Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => K.RsaKeys.public_to(pk), Result.map(&2, &2, R.RsaError, Unit, R.RsaPublic, u => R.RsaPublic{x1, x2}, c)) == Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => o, Result.map(&2, &2, R.RsaError, Unit, R.RsaPublic, u => R.RsaPublic{x1, x2}, c)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match c:
    case Done{u}:
      %e : {Done{B.Octets.append(K.rsa.field(x1), K.rsa.field(x2))} == Done{_} : Result<&2, &2, R.RsaError, B.Octets>}
      {==}
    case Fail{er}:
      {==}

def kr.pw3(+o: B.Octets, +x1: N.BnNat, +x2: N.BnNat, +rest2: B.Octets, +e: {B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), rest2)) == o : B.Octets}, b: Bool, +hb: {Nat.is_eq(B.Octets.len(rest2), 0n) == b : Bool}) -> {Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => K.RsaKeys.public_to(pk), Result.bind(&2, &2, R.RsaError, Unit, R.RsaPublic, R.RsaError.check(b, R.RsaBadFormat{}), u => R.Rsa.public_of(x1, x2))) == Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => o, Result.bind(&2, &2, R.RsaError, Unit, R.RsaPublic, R.RsaError.check(b, R.RsaBadFormat{}), u => R.Rsa.public_of(x1, x2))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match b:
    case True{}:
      kr.pw4(o, x1, x2, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), K.rsa.field(x2)), B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), rest2)), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), z), K.rsa.field(x2), B.Octets.append(K.rsa.field(x2), rest2), kr.tail0(K.rsa.field(x2), rest2, hb)), e), R.RsaError.check(Bool.and(Bool.and(N.BnNat.is_odd(x1), N.BnNat.is_lt(R.rsa.three(), x1)), Bool.and(N.BnNat.is_odd(x2), Bool.and(N.BnNat.is_le(R.rsa.three(), x2), N.BnNat.is_lt(x2, x1)))), R.RsaBadKey{}))
    case False{}:
      {==}

def kr.pw2(+o: B.Octets, +x1: N.BnNat, +rest1: B.Octets, +e1: {B.Octets.append(K.rsa.field(x1), rest1) == o : B.Octets}, r2: Result<&2, &2, R.RsaError, K.RsaField>, h2: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r2) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => rest1, r2) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => K.RsaKeys.public_to(pk), K.rsa.read.pub2(x1, r2)) == Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => o, K.rsa.read.pub2(x1, r2)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r2:
    case Done{a2}:
      match a2:
        case K.RsaField{+x2, +rest2}:
          kr.pw3(o, x1, x2, rest2, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), rest2)), B.Octets.append(K.rsa.field(x1), rest1), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), z), B.Octets.append(K.rsa.field(x2), rest2), rest1, kr.done_inj(B.Octets.append(K.rsa.field(x2), rest2), rest1, h2)), e1), Nat.is_eq(B.Octets.len(rest2), 0n), {==})
    case Fail{er}:
      {==}

def kr.pw1(+o: B.Octets, r1: Result<&2, &2, R.RsaError, K.RsaField>, h1: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r1) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, r1) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => K.RsaKeys.public_to(pk), Result.bind(&2, &2, R.RsaError, K.RsaField, R.RsaPublic, r1, a => K.rsa.read.pub(a))) == Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => o, Result.bind(&2, &2, R.RsaError, K.RsaField, R.RsaPublic, r1, a => K.rsa.read.pub(a))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r1:
    case Done{a}:
      match a:
        case K.RsaField{+x1, +rest1}:
          kr.pw2(o, x1, rest1, kr.done_inj(B.Octets.append(K.rsa.field(x1), rest1), o, h1), K.rsa.read(rest1), kr.inv0(rest1))
    case Fail{er}:
      {==}

def Laws.public_form_read_write(o):
  kr.pw1(o, K.rsa.read(o), kr.inv0(o))
# A private form read and written back: its five fields, one at a time

def kv.key3(+o: B.Octets, +n: N.BnNat, +e: N.BnNat, +d: N.BnNat, +p: N.BnNat, +q: N.BnNat, h: {B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))) == o : B.Octets}, qi: Maybe<&2, N.BnNat>) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), R.rsa.crt(n, e, d, p, q, qi)) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, R.rsa.crt(n, e, d, p, q, qi)) : Result<&2, &2, R.RsaError, B.Octets>}:
  match qi:
    case Some{qinv}:
      %Equal.sym(B.Octets, B.Octets.concat(Con{K.rsa.field(n), Con{K.rsa.field(e), Con{K.rsa.field(d), Con{K.rsa.field(p), Con{K.rsa.field(q), Nil{}}}}}}), B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))), kr.concat5(K.rsa.field(n), K.rsa.field(e), K.rsa.field(d), K.rsa.field(p), K.rsa.field(q))) : {Done{_} == Done{o} : Result<&2, &2, R.RsaError, B.Octets>}
      %h : {Done{B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty())))))} == Done{_} : Result<&2, &2, R.RsaError, B.Octets>}
      {==}
    case None{}:
      {==}

def kv.key2(+o: B.Octets, +n: N.BnNat, +e: N.BnNat, +d: N.BnNat, +p: N.BnNat, +q: N.BnNat, h: {B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))) == o : B.Octets}, c2: Result<&2, &2, R.RsaError, Unit>) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, Unit, R.RsaPrivate, c2, u => R.rsa.crt(n, e, d, p, q, Md.BnMod.inv(q, p)))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, Unit, R.RsaPrivate, c2, u => R.rsa.crt(n, e, d, p, q, Md.BnMod.inv(q, p)))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match c2:
    case Done{u}:
      kv.key3(o, n, e, d, p, q, h, Md.BnMod.inv(q, p))
    case Fail{er}:
      {==}

def kv.key1(+o: B.Octets, +n: N.BnNat, +e: N.BnNat, +d: N.BnNat, +p: N.BnNat, +q: N.BnNat, h: {B.Octets.append(K.rsa.field(n), B.Octets.append(K.rsa.field(e), B.Octets.append(K.rsa.field(d), B.Octets.append(K.rsa.field(p), B.Octets.append(K.rsa.field(q), B.Octets.empty()))))) == o : B.Octets}, c1: Result<&2, &2, R.RsaError, R.RsaPublic>) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, R.RsaPublic, R.RsaPrivate, c1, pk => Result.bind(&2, &2, R.RsaError, Unit, R.RsaPrivate, R.RsaError.check(Bool.and(Bool.and(N.BnNat.is_eq(N.BnNat.mul(p, q), n), Bool.and(N.BnNat.is_lt(N.BnNat.one(), p), N.BnNat.is_lt(N.BnNat.one(), q))), Bool.and(N.BnNat.is_eq(Md.BnMod.mul(d, e, R.rsa.minus1(p)), N.BnNat.mod(N.BnNat.one(), R.rsa.minus1(p))), N.BnNat.is_eq(Md.BnMod.mul(d, e, R.rsa.minus1(q)), N.BnNat.mod(N.BnNat.one(), R.rsa.minus1(q))))), R.RsaBadKey{}), u => R.rsa.crt(n, e, d, p, q, Md.BnMod.inv(q, p))))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, R.RsaPublic, R.RsaPrivate, c1, pk => Result.bind(&2, &2, R.RsaError, Unit, R.RsaPrivate, R.RsaError.check(Bool.and(Bool.and(N.BnNat.is_eq(N.BnNat.mul(p, q), n), Bool.and(N.BnNat.is_lt(N.BnNat.one(), p), N.BnNat.is_lt(N.BnNat.one(), q))), Bool.and(N.BnNat.is_eq(Md.BnMod.mul(d, e, R.rsa.minus1(p)), N.BnNat.mod(N.BnNat.one(), R.rsa.minus1(p))), N.BnNat.is_eq(Md.BnMod.mul(d, e, R.rsa.minus1(q)), N.BnNat.mod(N.BnNat.one(), R.rsa.minus1(q))))), R.RsaBadKey{}), u => R.rsa.crt(n, e, d, p, q, Md.BnMod.inv(q, p))))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match c1:
    case Done{pk}:
      kv.key2(o, n, e, d, p, q, h, R.RsaError.check(Bool.and(Bool.and(N.BnNat.is_eq(N.BnNat.mul(p, q), n), Bool.and(N.BnNat.is_lt(N.BnNat.one(), p), N.BnNat.is_lt(N.BnNat.one(), q))), Bool.and(N.BnNat.is_eq(Md.BnMod.mul(d, e, R.rsa.minus1(p)), N.BnNat.mod(N.BnNat.one(), R.rsa.minus1(p))), N.BnNat.is_eq(Md.BnMod.mul(d, e, R.rsa.minus1(q)), N.BnNat.mod(N.BnNat.one(), R.rsa.minus1(q))))), R.RsaBadKey{}))
    case Fail{er}:
      {==}

def kv.end(+o: B.Octets, +x1: N.BnNat, +x2: N.BnNat, +x3: N.BnNat, +x4: N.BnNat, +x5: N.BnNat, +rest5: B.Octets, +e: {B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), B.Octets.append(K.rsa.field(x5), rest5))))) == o : B.Octets}, b: Bool, +hb: {Nat.is_eq(B.Octets.len(rest5), 0n) == b : Bool}) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x3, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x4, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x5, t}, Result.map(&2, &2, R.RsaError, Unit, List<&2, N.BnNat>, u => Nil{}, R.RsaError.check(b, R.RsaBadFormat{}))))))), xs => K.rsa.read.priv(xs))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x3, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x4, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x5, t}, Result.map(&2, &2, R.RsaError, Unit, List<&2, N.BnNat>, u => Nil{}, R.RsaError.check(b, R.RsaBadFormat{}))))))), xs => K.rsa.read.priv(xs))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match b:
    case True{}:
      kv.key1(o, x1, x2, x3, x4, x5, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), B.Octets.append(K.rsa.field(x5), B.Octets.empty()))))), B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), B.Octets.append(K.rsa.field(x5), rest5))))), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), B.Octets.append(K.rsa.field(x5), z))))), B.Octets.empty(), rest5, Equal.sym(B.Octets, rest5, B.Octets.empty(), kr.len0(rest5, hb))), e), R.Rsa.public_of(x1, x2))
    case False{}:
      {==}

def kv.l5(+o: B.Octets, +x1: N.BnNat, +x2: N.BnNat, +x3: N.BnNat, +x4: N.BnNat, +rest4: B.Octets, +e: {B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), rest4)))) == o : B.Octets}, r: Result<&2, &2, R.RsaError, K.RsaField>, h: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => rest4, r) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x3, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x4, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(0n, K.RsaField.rest(a)))))))), xs => K.rsa.read.priv(xs))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x3, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x4, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(0n, K.RsaField.rest(a)))))))), xs => K.rsa.read.priv(xs))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r:
    case Done{a}:
      match a:
        case K.RsaField{+x5, +rest5}:
          kv.end(o, x1, x2, x3, x4, x5, rest5, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), B.Octets.append(K.rsa.field(x5), rest5))))), B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), rest4)))), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), z)))), B.Octets.append(K.rsa.field(x5), rest5), rest4, kr.done_inj(B.Octets.append(K.rsa.field(x5), rest5), rest4, h)), e), Nat.is_eq(B.Octets.len(rest5), 0n), {==})
    case Fail{er}:
      {==}

def kv.l4(+o: B.Octets, +x1: N.BnNat, +x2: N.BnNat, +x3: N.BnNat, +rest3: B.Octets, +e: {B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), rest3))) == o : B.Octets}, r: Result<&2, &2, R.RsaError, K.RsaField>, h: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => rest3, r) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x3, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(1n, K.RsaField.rest(a))))))), xs => K.rsa.read.priv(xs))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x3, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(1n, K.RsaField.rest(a))))))), xs => K.rsa.read.priv(xs))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r:
    case Done{a}:
      match a:
        case K.RsaField{+x4, +rest4}:
          kv.l5(o, x1, x2, x3, x4, rest4, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), B.Octets.append(K.rsa.field(x4), rest4)))), B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), rest3))), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), z))), B.Octets.append(K.rsa.field(x4), rest4), rest3, kr.done_inj(B.Octets.append(K.rsa.field(x4), rest4), rest3, h)), e), K.rsa.read(rest4), kr.inv0(rest4))
    case Fail{er}:
      {==}

def kv.l3(+o: B.Octets, +x1: N.BnNat, +x2: N.BnNat, +rest2: B.Octets, +e: {B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), rest2)) == o : B.Octets}, r: Result<&2, &2, R.RsaError, K.RsaField>, h: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => rest2, r) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(2n, K.RsaField.rest(a)))))), xs => K.rsa.read.priv(xs))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x2, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(2n, K.RsaField.rest(a)))))), xs => K.rsa.read.priv(xs))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r:
    case Done{a}:
      match a:
        case K.RsaField{+x3, +rest3}:
          kv.l4(o, x1, x2, x3, rest3, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), B.Octets.append(K.rsa.field(x3), rest3))), B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), rest2)), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), z)), B.Octets.append(K.rsa.field(x3), rest3), rest2, kr.done_inj(B.Octets.append(K.rsa.field(x3), rest3), rest2, h)), e), K.rsa.read(rest3), kr.inv0(rest3))
    case Fail{er}:
      {==}

def kv.l2(+o: B.Octets, +x1: N.BnNat, +rest1: B.Octets, +e: {B.Octets.append(K.rsa.field(x1), rest1) == o : B.Octets}, r: Result<&2, &2, R.RsaError, K.RsaField>, h: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => rest1, r) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(3n, K.RsaField.rest(a))))), xs => K.rsa.read.priv(xs))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{x1, t}, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(3n, K.RsaField.rest(a))))), xs => K.rsa.read.priv(xs))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r:
    case Done{a}:
      match a:
        case K.RsaField{+x2, +rest2}:
          kv.l3(o, x1, x2, rest2, Equal.trans(B.Octets, B.Octets.append(K.rsa.field(x1), B.Octets.append(K.rsa.field(x2), rest2)), B.Octets.append(K.rsa.field(x1), rest1), o, Equal.cong(B.Octets, B.Octets, z => B.Octets.append(K.rsa.field(x1), z), B.Octets.append(K.rsa.field(x2), rest2), rest1, kr.done_inj(B.Octets.append(K.rsa.field(x2), rest2), rest1, h)), e), K.rsa.read(rest2), kr.inv0(rest2))
    case Fail{er}:
      {==}

def kv.l1(+o: B.Octets, r: Result<&2, &2, R.RsaError, K.RsaField>, h: {Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => B.Octets.append(K.rsa.field(K.RsaField.x(a)), K.RsaField.rest(a)), r) == Result.map(&2, &2, R.RsaError, K.RsaField, B.Octets, a => o, r) : Result<&2, &2, R.RsaError, B.Octets>}) -> {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(4n, K.RsaField.rest(a)))), xs => K.rsa.read.priv(xs))) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, Result.bind(&2, &2, R.RsaError, K.RsaField, List<&2, N.BnNat>, r, +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{K.RsaField.x(a), t}, K.rsa.read.n(4n, K.RsaField.rest(a)))), xs => K.rsa.read.priv(xs))) : Result<&2, &2, R.RsaError, B.Octets>}:
  match r:
    case Done{a}:
      match a:
        case K.RsaField{+x1, +rest1}:
          kv.l2(o, x1, rest1, kr.done_inj(B.Octets.append(K.rsa.field(x1), rest1), o, h), K.rsa.read(rest1), kr.inv0(rest1))
    case Fail{er}:
      {==}

def Laws.private_form_read_write(o):
  kv.l1(o, K.rsa.read(o), kr.inv0(o))

# The form written for a key read is read as the same key

def kr.wr_pub(r: Result<&2, &2, R.RsaError, R.RsaPublic>, +o: B.Octets, h: {Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => K.RsaKeys.public_to(pk), r) == Result.map(&2, &2, R.RsaError, R.RsaPublic, B.Octets, pk => o, r) : Result<&2, &2, R.RsaError, B.Octets>}, hr: {K.RsaKeys.public_of(o) == r : Result<&2, &2, R.RsaError, R.RsaPublic>}) -> {Result.bind(&2, &2, R.RsaError, R.RsaPublic, R.RsaPublic, r, pk => K.RsaKeys.public_of(K.RsaKeys.public_to(pk))) == r : Result<&2, &2, R.RsaError, R.RsaPublic>}:
  match r:
    case Done{+pk}:
      %Equal.sym(B.Octets, K.RsaKeys.public_to(pk), o, kr.done_inj(K.RsaKeys.public_to(pk), o, h)) : {K.RsaKeys.public_of(_) == Done{pk} : Result<&2, &2, R.RsaError, R.RsaPublic>}
      hr
    case Fail{er}:
      {==}

def Laws.public_form_write_read(o):
  kr.wr_pub(K.RsaKeys.public_of(o), o, Laws.public_form_read_write(o), {==})

def kr.wr_priv(r: Result<&2, &2, R.RsaError, R.RsaPrivate>, +o: B.Octets, h: {Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => K.RsaKeys.private_to(sk), r) == Result.map(&2, &2, R.RsaError, R.RsaPrivate, B.Octets, sk => o, r) : Result<&2, &2, R.RsaError, B.Octets>}, hr: {K.RsaKeys.private_of(o) == r : Result<&2, &2, R.RsaError, R.RsaPrivate>}) -> {Result.bind(&2, &2, R.RsaError, R.RsaPrivate, R.RsaPrivate, r, sk => K.RsaKeys.private_of(K.RsaKeys.private_to(sk))) == r : Result<&2, &2, R.RsaError, R.RsaPrivate>}:
  match r:
    case Done{+sk}:
      %Equal.sym(B.Octets, K.RsaKeys.private_to(sk), o, kr.done_inj(K.RsaKeys.private_to(sk), o, h)) : {K.RsaKeys.private_of(_) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
      hr
    case Fail{er}:
      {==}

def Laws.private_form_write_read(o):
  kr.wr_priv(K.RsaKeys.private_of(o), o, Laws.private_form_read_write(o), {==})
