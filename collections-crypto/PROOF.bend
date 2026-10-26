import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../crypto/crypto.bend as Cr
import ../crypto/stream.bend as St
import ../crypto/mac.bend as Mc
import ../crypto/sign.bend as Sg
import ../crypto/kex.bend as Kx
import ../crypto/LAWS_xor.bend as CX
import ../crypto/PROOF_xor.bend as CXP
import ../crypto/LAWS_pk.bend as CK
import ../crypto/PROOF_pk.bend as CKP
import ./collections-crypto.bend as C
import ./aead.bend as Ad
import ./gmac.bend as Gm
import ./poly1305.bend as Po
import ./chacha.bend as Ch
import ./blake.bend as Bl
import ./keccak.bend as Kc
import ./x25519.bend as Xx
import ./ed25519.bend as Ed
import bend-collections-laws-crypto@1.0.0.0/src/crypto/aead.bend as A
import bend-collections-laws-crypto@1.0.0.0/src/crypto/poly1305/poly1305.bend as P
import bend-collections-laws-crypto@1.0.0.0/src/crypto/curve25519/x25519.bend as X
import bend-collections-laws-crypto@1.0.0.0/src/crypto/kex.bend as K
import bend-collections-laws-crypto@1.0.0.0/src/crypto/sign.bend as SG
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/keccak/main.bend as KS
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/poly1305.bend as PR
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/curve25519/field.bend as FS
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/curve25519/x25519.bend as SX
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/kex.bend as SKX
import bend-collections-laws-crypto@1.0.0.0/spec/crypto/ed25519.bend as SE
import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/keccak/laws.bend as KL
import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/keccak/proof.bend as KP
import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/curve25519/proof.bend as CP
import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/ed25519/proof.bend as EP
import ./LAWS.bend as Laws

# Booleans, Maybe and Result: discriminators and injectivity

def cc_bool_disc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def cc_ft_absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : cc_bool_disc(_)
  Unit{}

def cc_maybe_disc(-X: Data, +m: Maybe<&2, X>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def cc_ns_absurd(-X: Data, -x: X, +e: {None{} == Some{x} : Maybe<&2, X>}) -> Empty:
  %e : cc_maybe_disc(X, _)
  Unit{}

def cc_some_inj(-X: Data, +a: X, +b: X, +e: {Some{a} == Some{b} : Maybe<&2, X>}) -> {a == b : X}:
  Equal.cong(Maybe<&2, X>, X, x => Maybe.default(&2, X, x, a), Some{a}, Some{b}, e)

def cc_rdisc(-X: Data, +r: Result<&2, &2, Cr.CrError, X>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{x}:
      Empty

def cc_fd_absurd(-X: Data, -x: Cr.CrError, -y: X, +e: {Fail{x} == Done{y} : Result<&2, &2, Cr.CrError, X>}) -> Empty:
  %e : cc_rdisc(X, _)
  Unit{}

def cc_done_inj(-X: Data, +a: X, +b: X, +e: {Done{a} == Done{b} : Result<&2, &2, Cr.CrError, X>}) -> {a == b : X}:
  Equal.cong(Result<&2, &2, Cr.CrError, X>, X, x => Result.default(&2, &2, Cr.CrError, X, x, a), Done{a}, Done{b}, e)

def cc_and_r(+x: Bool, +y: Bool, h: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      Empty.absurd({y == True{} : Bool}, cc_ft_absurd(h))

# Lists and Octets

def cc_rev_append(xs: List<&2, U32>, +ys: List<&2, U32>, +acc: List<&2, U32>) -> {B.rev_onto(B.append(xs, ys), acc) == B.rev_onto(ys, B.rev_onto(xs, acc)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      cc_rev_append(t, ys, Con{h, acc})

def cc_append_assoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) -> {B.append(B.append(xs, ys), zs) == B.append(xs, B.append(ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %cc_append_assoc(t, ys, zs) : {Con{h, B.append(B.append(t, ys), zs)} == Con{h, _} : List<&2, U32>}
      {==}

# two Octets with the same bytes are the same (bytes' octets_of_to)
def cc_octets_ext(+x: B.Octets, +y: B.Octets, e: {B.Octets.to_list(x) == B.Octets.to_list(y) : List<&2, U32>}) -> {x == y : B.Octets}:
  %BL.octets_of_to(x) : {_ == y : B.Octets}
  %BL.octets_of_to(y) : {B.Octets.of_list(B.Octets.to_list(x)) == _ : B.Octets}
  %e : {B.Octets.of_list(B.Octets.to_list(x)) == B.Octets.of_list(_) : B.Octets}
  {==}

def cc_octets_assoc(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.append(B.Octets.append(a, b), c) == B.Octets.append(a, B.Octets.append(b, c)) : B.Octets}:
  +l = Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.append(a, b), c)), B.append(B.Octets.to_list(B.Octets.append(a, b)), B.Octets.to_list(c)), B.append(B.append(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)), BL.octets_append_list(B.Octets.append(a, b), c), Equal.cong(List<&2, U32>, List<&2, U32>, x => B.append(x, B.Octets.to_list(c)), B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)))
  +r = Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c))), B.append(B.Octets.to_list(a), B.Octets.to_list(B.Octets.append(b, c))), B.append(B.Octets.to_list(a), B.append(B.Octets.to_list(b), B.Octets.to_list(c))), BL.octets_append_list(a, B.Octets.append(b, c)), Equal.cong(List<&2, U32>, List<&2, U32>, x => B.append(B.Octets.to_list(a), x), B.Octets.to_list(B.Octets.append(b, c)), B.append(B.Octets.to_list(b), B.Octets.to_list(c)), BL.octets_append_list(b, c)))
  +m = cc_append_assoc(B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c))
  cc_octets_ext(B.Octets.append(B.Octets.append(a, b), c), B.Octets.append(a, B.Octets.append(b, c)), Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.append(a, b), c)), B.append(B.append(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)), B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c))), l, Equal.trans(List<&2, U32>, B.append(B.append(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)), B.append(B.Octets.to_list(a), B.append(B.Octets.to_list(b), B.Octets.to_list(c))), B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c))), m, Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c))), B.append(B.Octets.to_list(a), B.append(B.Octets.to_list(b), B.Octets.to_list(c))), r))))

# Buffered hashing

def Laws.buf_streaming(s, a, b):
  match s:
    case C.CcBuf{+r}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {C.CcBuf{B.rev_onto(_, r)} == C.CcBuf{B.rev_onto(B.Octets.to_list(b), B.rev_onto(B.Octets.to_list(a), r))} : C.CcBuf}
      Equal.cong(List<&2, U32>, C.CcBuf, x => C.CcBuf{x}, B.rev_onto(B.append(B.Octets.to_list(a), B.Octets.to_list(b)), r), B.rev_onto(B.Octets.to_list(b), B.rev_onto(B.Octets.to_list(a), r)), cc_rev_append(B.Octets.to_list(a), B.Octets.to_list(b), r))

def Laws.buf_final(digest, m):
  %Equal.sym(List<&2, U32>, B.rev(B.rev(B.Octets.to_list(m))), B.Octets.to_list(m), BL.rev_rev(B.Octets.to_list(m))) : {digest(B.Octets.of_list(_)) == digest(m) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(m)), m, BL.octets_of_to(m)) : {digest(_) == digest(m) : B.Octets}
  {==}

def Laws.buf_split(digest, a, b):
  %Laws.buf_streaming(C.CcBuf.init(), a, b) : {C.CcBuf.final(~digest, _) == digest(B.Octets.append(a, b)) : B.Octets}
  Laws.buf_final(~digest, B.Octets.append(a, b))

def Laws.buf_split3(digest, a, b, c):
  %Laws.buf_streaming(C.CcBuf.init(), a, b) : {C.CcBuf.final(~digest, C.CcBuf.update(_, c)) == digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %Laws.buf_streaming(C.CcBuf.init(), B.Octets.append(a, b), c) : {C.CcBuf.final(~digest, _) == digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %Equal.sym(B.Octets, C.CcBuf.final(~digest, C.CcBuf.update(C.CcBuf.init(), B.Octets.append(B.Octets.append(a, b), c))), digest(B.Octets.append(B.Octets.append(a, b), c)), Laws.buf_final(~digest, B.Octets.append(B.Octets.append(a, b), c))) : {_ == digest(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  Equal.cong(B.Octets, B.Octets, x => digest(x), B.Octets.append(B.Octets.append(a, b), c), B.Octets.append(a, B.Octets.append(b, c)), cc_octets_assoc(a, b, c))

# The AEAD round trip

# open's answer on bend-collections' ciphertext and tag c, when its encrypt
# gave c (hm), its decrypt gives the plaintext back from c (hr), and c is a
# byte string (hb); v is bend-collections' check of the key and nonce
# lengths, which hm shows is passed
def cc_aead_valid(+alg: A.Alg, +key: List<&2, U32>, +n: B.Octets, +a: B.Octets, +p: B.Octets, +c: List<&2, U32>, hm: {A.encrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p)) == Some{c} : Maybe<&2, List<&2, U32>>}, hr: {A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), c) == Some{B.Octets.to_list(p)} : Maybe<&2, List<&2, U32>>}, hb: {B.mask(c) == c : List<&2, U32>}, +v: Bool, +hv: {A.valid(alg, key, B.Octets.to_list(n)) == v : Bool}) -> {Ad.CcAead.open(Ad.CcAeadKey{alg, key}, n, a, B.Octets.of_list(c)) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}:
  match v:
    case False{}:
      +none = Equal.cong(Bool, Maybe<&2, List<&2, U32>>, x => A.when_open(x, A.seal(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p))), A.valid(alg, key, B.Octets.to_list(n)), False{}, hv)
      Empty.absurd({Ad.CcAead.open(Ad.CcAeadKey{alg, key}, n, a, B.Octets.of_list(c)) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}, cc_ns_absurd(List<&2, U32>, c, Equal.trans(Maybe<&2, List<&2, U32>>, None{}, A.encrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p)), Some{c}, Equal.sym(Maybe<&2, List<&2, U32>>, A.encrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p)), None{}, none), hm)))
    case True{}:
      +nb = cc_and_r(Nat.is_eq(List.length(&2, U32, key), A.key_size(alg)), Nat.is_eq(List.length(&2, U32, B.Octets.to_list(n)), A.nonce_size(alg)), hv)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, B.Octets.to_list(n)), A.nonce_size(alg)), True{}, nb) : {Ad.cc.aead.open(_, alg, key, n, a, B.Octets.of_list(c)) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(c)), B.mask(c), BL.octets_to_of(c)) : {C.CcRes.of_maybe(Cr.CrTagMismatch{}, A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), _)) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}
      %Equal.sym(List<&2, U32>, B.mask(c), c, hb) : {C.CcRes.of_maybe(Cr.CrTagMismatch{}, A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), _)) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}
      %Equal.sym(Maybe<&2, List<&2, U32>>, A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), c), Some{B.Octets.to_list(p)}, hr) : {C.CcRes.of_maybe(Cr.CrTagMismatch{}, _) == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}
      %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(p)), p, BL.octets_of_to(p)) : {Done{_} == Done{p} : Result<&2, &2, Cr.CrError, B.Octets>}
      {==}

# the round trip over bend-collections' answer m to encrypt
def cc_aead_m(+alg: A.Alg, +key: List<&2, U32>, +n: B.Octets, +a: B.Octets, +p: B.Octets, +m: Maybe<&2, List<&2, U32>>, hm: {A.encrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p)) == m : Maybe<&2, List<&2, U32>>}, hr: {Maybe.bind(&2, List<&2, U32>, List<&2, U32>, m, c => A.decrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), c)) == Maybe.map(&2, List<&2, U32>, List<&2, U32>, c => B.Octets.to_list(p), m) : Maybe<&2, List<&2, U32>>}, h: {Ad.cc.aead.mask(m) == m : Maybe<&2, List<&2, U32>>}) -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, C.CcRes.of_maybe(Cr.CrBadNonceLength{B.Octets.len(n)}, m), c => Ad.CcAead.open(Ad.CcAeadKey{alg, key}, n, a, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, C.CcRes.of_maybe(Cr.CrBadNonceLength{B.Octets.len(n)}, m)) : Result<&2, &2, Cr.CrError, B.Octets>}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      cc_aead_valid(alg, key, n, a, p, c, hm, hr, cc_some_inj(List<&2, U32>, B.mask(c), c, h), A.valid(alg, key, B.Octets.to_list(n)), {==})

def Laws.aead_round_trip_if(k, n, a, p, hr, h):
  match k:
    case Ad.CcAeadKey{+alg, +key}:
      cc_aead_m(alg, key, n, a, p, A.encrypt(alg, key, B.Octets.to_list(n), B.Octets.to_list(a), B.Octets.to_list(p)), {==}, hr, h)

# The specifications, from bend-collections-laws-crypto's laws

def cc_nat_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cc_nat_refl(p)

# a length check on bytes of that length passes
def cc_len_true(+o: B.Octets, +n: Nat, +h: {B.Octets.len(o) == n : Nat}) -> {Nat.is_eq(B.Octets.len(o), n) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(o), n, h) : {Nat.is_eq(_, n) == True{} : Bool}
  cc_nat_refl(n)

def cc_mask_len(xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, x => 1n+x, B.len(B.mask(t)), B.len(t), cc_mask_len(t))

def cc_octets_len_of(+xs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(xs)) == B.len(xs) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(xs)), B.len(B.Octets.to_list(B.Octets.of_list(xs))), BL.octets_len_list(B.Octets.of_list(xs))) : {_ == B.len(xs) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {B.len(_) == B.len(xs) : Nat}
  cc_mask_len(xs)

# every element of a masked list is below 256 (bytes' byte_below_256)
def cc_valid_mask(xs: List<&2, U32>) -> {X.valid_bytes(B.len(xs), B.mask(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Bool, U32.is_lt(B.byte(h), 256), True{}, BL.byte_below_256(h)) : {Bool.and(_, X.valid_bytes(B.len(t), B.mask(t))) == True{} : Bool}
      cc_valid_mask(t)

# an Octets' bytes are their own mask
def cc_mask_self(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.mask(B.Octets.to_list(o)), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o))), Equal.cong(B.Octets, List<&2, U32>, x => B.Octets.to_list(x), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)))

# n bytes of an Octets are n values below 256, as bend-collections' curve
# laws take them (FS.bytes_ok; FS.tight for n = 32)
def cc_bytes_ok(+o: B.Octets, +n: Nat, +h: {B.Octets.len(o) == n : Nat}) -> {FS.bytes_ok(n, B.Octets.to_list(o)) == True{} : Bool}:
  %h : {FS.bytes_ok(_, B.Octets.to_list(o)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)) : {FS.bytes_ok(_, B.Octets.to_list(o)) == True{} : Bool}
  %cc_mask_self(o) : {FS.bytes_ok(B.len(B.Octets.to_list(o)), _) == True{} : Bool}
  %CP.valid_eq(B.len(B.Octets.to_list(o)), B.mask(B.Octets.to_list(o))) : {_ == True{} : Bool}
  cc_valid_mask(B.Octets.to_list(o))

def Laws.keccak256_spec(o):
  %KL.ethereum_keccak256(Bl.CcBlake.pack(o), B.Octets.len(o)) : {Kc.CcKeccak.keccak256(o) == Bl.CcBlake.out(8n, _) : B.Octets}
  {==}

# keys of 32 bytes parse

def cc_x25519_sk_ok(+a: B.Octets, +ha: {B.Octets.len(a) == 32n : Nat}) -> {Xx.CcX25519.secret(a) == Done{Xx.CcX25519Sk{B.Octets.to_list(a)}} : Result<&2, &2, Cr.CrError, Xx.CcX25519Sk>}:
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(a), 32n), True{}, cc_len_true(a, 32n, ha)) : {Xx.cc.x25519.secret(_, a) == Done{Xx.CcX25519Sk{B.Octets.to_list(a)}} : Result<&2, &2, Cr.CrError, Xx.CcX25519Sk>}
  {==}

def cc_x25519_pk_ok(+u: B.Octets, +hu: {B.Octets.len(u) == 32n : Nat}) -> {Xx.CcX25519.pk_of(u) == Done{Xx.CcX25519Pk{u}} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}:
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(u), 32n), True{}, cc_len_true(u, 32n, hu)) : {Xx.cc.x25519.pk(_, u) == Done{Xx.CcX25519Pk{u}} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}
  {==}

def cc_ed_pk_ok(+pk: B.Octets, +hp: {B.Octets.len(pk) == 32n : Nat}) -> {Ed.CcEd25519.pk_of(pk) == Done{Ed.CcEdPk{pk}} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}:
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(pk), 32n), True{}, cc_len_true(pk, 32n, hp)) : {Ed.cc.ed.pk(_, pk) == Done{Ed.CcEdPk{pk}} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}
  {==}

def Laws.x25519_public_spec(one, h1, o, h):
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(o), 32n), True{}, cc_len_true(o, 32n, h)) : {Result.map(&2, &2, Cr.CrError, Xx.CcX25519Sk, B.Octets, k => Xx.CcX25519.pk_to(Xx.CcX25519.public(k)), Xx.cc.x25519.secret(_, o)) == Done{B.Octets.of_list(SX.x25519(one, B.Octets.to_list(o), SKX.base()))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, X.x25519(B.Octets.to_list(o), X.base()), Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(FS.tight(B.Octets.to_list(o)), FS.tight(X.base())), Some{SX.x25519(one, B.Octets.to_list(o), X.base())}, None{}), CP.x25519_checked(one, h1, B.Octets.to_list(o), X.base())) : {Done{C.CcRes.or_empty(_)} == Done{B.Octets.of_list(SX.x25519(one, B.Octets.to_list(o), SKX.base()))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Bool, FS.bytes_ok(32n, B.Octets.to_list(o)), True{}, cc_bytes_ok(o, 32n, h)) : {Done{C.CcRes.or_empty(Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(_, FS.tight(X.base())), Some{SX.x25519(one, B.Octets.to_list(o), X.base())}, None{}))} == Done{B.Octets.of_list(SX.x25519(one, B.Octets.to_list(o), SKX.base()))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Bool, FS.tight(X.base()), True{}, CP.base_tight()) : {Done{C.CcRes.or_empty(Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(True{}, _), Some{SX.x25519(one, B.Octets.to_list(o), X.base())}, None{}))} == Done{B.Octets.of_list(SX.x25519(one, B.Octets.to_list(o), SKX.base()))} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def Laws.x25519_shared_spec(one, h1, a, u, ha, hu):
  +S = SKX.unless_zero(SX.x25519(one, B.Octets.to_list(a), B.Octets.to_list(u)), Nat.is_eq(FS.value(SX.x25519(one, B.Octets.to_list(a), B.Octets.to_list(u))), 0n))
  %Equal.sym(Result<&2, &2, Cr.CrError, B.Octets>, Kx.CrKex.agree(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, a, u), Xx.CcX25519.shared(Xx.CcX25519Sk{B.Octets.to_list(a)}, Xx.CcX25519Pk{u}), CK.kex_agree_done(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.shared, a, u, Xx.CcX25519Sk{B.Octets.to_list(a)}, Xx.CcX25519Pk{u}, cc_x25519_sk_ok(a, ha), cc_x25519_pk_ok(u, hu))) : {_ == C.CcRes.of_maybe(Cr.CrBadKey{}, S) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, K.shared_secret(B.Octets.to_list(a), B.Octets.to_list(u)), S, CP.kex_shared(one, h1, B.Octets.to_list(a), B.Octets.to_list(u), cc_bytes_ok(a, 32n, ha), cc_bytes_ok(u, 32n, hu))) : {C.CcRes.of_maybe(Cr.CrBadKey{}, _) == C.CcRes.of_maybe(Cr.CrBadKey{}, S) : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def Laws.ed25519_public_spec(one, h1, o, h):
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(o), 32n), True{}, cc_len_true(o, 32n, h)) : {Result.map(&2, &2, Cr.CrError, Ed.CcEdSk, B.Octets, k => Ed.CcEd25519.pk_to(Ed.CcEd25519.public(k)), Ed.cc.ed.secret(_, o)) == Done{B.Octets.of_list(SE.public_key(one, B.Octets.to_list(o)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Maybe<&2, SG.Keypair>, SG.generate_keypair(B.Octets.to_list(o)), Some{SG.Keypair{B.Octets.to_list(o), SE.public_key(one, B.Octets.to_list(o))}}, EP.sign_keypair(one, h1, B.Octets.to_list(o), cc_bytes_ok(o, 32n, h))) : {Done{Ed.CcEd25519.pk_to(Ed.cc.ed.public(_))} == Done{B.Octets.of_list(SE.public_key(one, B.Octets.to_list(o)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def Laws.ed25519_sign_spec(one, h1, o, m, h):
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(o), 32n), True{}, cc_len_true(o, 32n, h)) : {Result.map(&2, &2, Cr.CrError, Ed.CcEdSk, B.Octets, k => Ed.CcEd25519.sign(k, m), Ed.cc.ed.secret(_, o)) == Done{B.Octets.of_list(SE.sign(one, B.Octets.to_list(o), B.Octets.to_list(m)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, SG.sign(B.Octets.to_list(o), B.Octets.to_list(m)), Some{SE.sign(one, B.Octets.to_list(o), B.Octets.to_list(m))}, EP.sign_sign(one, h1, B.Octets.to_list(o), B.Octets.to_list(m), cc_bytes_ok(o, 32n, h))) : {Done{C.CcRes.or_empty(_)} == Done{B.Octets.of_list(SE.sign(one, B.Octets.to_list(o), B.Octets.to_list(m)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def Laws.ed25519_verify_spec(one, h1, pk, m, s, hp, hs):
  %Equal.sym(Bool, Sg.CrSign.verify_bytes(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, pk, m, s), Ed.CcEd25519.verify(Ed.CcEdPk{pk}, m, s), CK.sign_verify_bytes_done(~Ed.CcEdPk, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.verify, pk, m, s, Ed.CcEdPk{pk}, cc_ed_pk_ok(pk, hp))) : {_ == SE.verify(one, B.Octets.to_list(pk), B.Octets.to_list(m), B.Octets.to_list(s)) : Bool}
  EP.sign_verify(one, h1, B.Octets.to_list(pk), B.Octets.to_list(m), B.Octets.to_list(s), cc_bytes_ok(pk, 32n, hp), cc_bytes_ok(s, 64n, hs))

# Vectors

def Laws.chacha20_rfc8439_block():
  {==}

def Laws.poly1305_rfc8439():
  {==}

def Laws.blake2s_rfc7693():
  {==}

def Laws.blake3_empty():
  {==}

def Laws.chacha20_key_length():
  {==}

def Laws.gcm_key_length():
  {==}

def Laws.x25519_pk_length():
  {==}

# The instances

# BEGIN GENERATED by gen/instances.py: proofs
def Laws.blake2b_hash_split(a, b):
  Laws.buf_split(~Bl.CcBlake.blake2b, a, b)

def Laws.blake2b_hash_split3(a, b, c):
  Laws.buf_split3(~Bl.CcBlake.blake2b, a, b, c)

def Laws.blake2s_hash_split(a, b):
  Laws.buf_split(~Bl.CcBlake.blake2s, a, b)

def Laws.blake2s_hash_split3(a, b, c):
  Laws.buf_split3(~Bl.CcBlake.blake2s, a, b, c)

def Laws.blake3_hash_split(a, b):
  Laws.buf_split(~Bl.CcBlake.blake3, a, b)

def Laws.blake3_hash_split3(a, b, c):
  Laws.buf_split3(~Bl.CcBlake.blake3, a, b, c)

def Laws.blake2b_n_hash_split(nn, a, b):
  Laws.buf_split(~Bl.CcBlake.blake2b_n(~nn), a, b)

def Laws.blake2b_n_hash_split3(nn, a, b, c):
  Laws.buf_split3(~Bl.CcBlake.blake2b_n(~nn), a, b, c)

def Laws.keccak256_hash_split(a, b):
  Laws.buf_split(~Kc.CcKeccak.keccak256, a, b)

def Laws.keccak256_hash_split3(a, b, c):
  Laws.buf_split3(~Kc.CcKeccak.keccak256, a, b, c)

def Laws.chacha_stream_involution(r, s, m):
  CX.xor_involution(~Ch.CcChaState, ~Ch.CcChacha.next(~r), s, m)

def Laws.chacha_stream_streaming_data(r, s, a, b):
  CX.xor_streaming_data(~Ch.CcChaState, ~Ch.CcChacha.next(~r), s, a, b)

def Laws.chacha_stream_streaming_state(r, s, a, b):
  CX.xor_streaming_state(~Ch.CcChaState, ~Ch.CcChacha.next(~r), s, a, b)

def Laws.poly1305_accepts(k, m):
  BL.octets_is_eq_refl(Po.CcPoly1305.mac(k, m))

def Laws.poly1305_agrees(k, m, t):
  {==}

def Laws.gmac_accepts(k, m):
  BL.octets_is_eq_refl(Gm.CcGmac.mac(k, m))

def Laws.gmac_agrees(k, m, t):
  {==}

def Laws.ed25519_verify_bytes_if(sk, m, hf, ha):
  CK.sign_verify_bytes_if(~Ed.CcEdSk, ~Ed.CcEdPk, ~Ed.CcEd25519.public, ~Ed.CcEd25519.pk_of, ~Ed.CcEd25519.pk_to, ~Ed.CcEd25519.sign, ~Ed.CcEd25519.verify, sk, m, hf, ha)

def Laws.x25519_agree_if(a, b, x, y, hx, hy, hfx, hfy, h):
  CK.kex_agree_if(~Xx.CcX25519Sk, ~Xx.CcX25519Pk, ~Xx.CcX25519.secret, ~Xx.CcX25519.public, ~Xx.CcX25519.pk_of, ~Xx.CcX25519.pk_to, ~Xx.CcX25519.shared, a, b, x, y, hx, hy, hfx, hfy, h)

def cc_x25519_fmt(+v: Bool, +o: B.Octets, +p: Xx.CcX25519Pk, +hv: {Nat.is_eq(B.Octets.len(o), 32n) == v : Bool}, h: {Xx.cc.x25519.pk(v, o) == Done{p} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}) -> {Xx.cc.x25519.pk(Nat.is_eq(B.Octets.len(Xx.CcX25519.pk_to(p)), 32n), Xx.CcX25519.pk_to(p)) == Done{p} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}:
  match v:
    case False{}:
      Empty.absurd({Xx.cc.x25519.pk(Nat.is_eq(B.Octets.len(Xx.CcX25519.pk_to(p)), 32n), Xx.CcX25519.pk_to(p)) == Done{p} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}, cc_fd_absurd(Xx.CcX25519Pk, Cr.CrBadPublicKey{}, p, h))
    case True{}:
      %cc_done_inj(Xx.CcX25519Pk, Xx.CcX25519Pk{o}, p, h) : {Xx.cc.x25519.pk(Nat.is_eq(B.Octets.len(Xx.CcX25519.pk_to(_)), 32n), Xx.CcX25519.pk_to(_)) == Done{_} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(o), 32n), True{}, hv) : {Xx.cc.x25519.pk(_, o) == Done{Xx.CcX25519Pk{o}} : Result<&2, &2, Cr.CrError, Xx.CcX25519Pk>}
      {==}

def Laws.x25519_pk_format(o, p, h):
  cc_x25519_fmt(Nat.is_eq(B.Octets.len(o), 32n), o, p, {==}, h)

def cc_ed25519_fmt(+v: Bool, +o: B.Octets, +p: Ed.CcEdPk, +hv: {Nat.is_eq(B.Octets.len(o), 32n) == v : Bool}, h: {Ed.cc.ed.pk(v, o) == Done{p} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}) -> {Ed.cc.ed.pk(Nat.is_eq(B.Octets.len(Ed.CcEd25519.pk_to(p)), 32n), Ed.CcEd25519.pk_to(p)) == Done{p} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}:
  match v:
    case False{}:
      Empty.absurd({Ed.cc.ed.pk(Nat.is_eq(B.Octets.len(Ed.CcEd25519.pk_to(p)), 32n), Ed.CcEd25519.pk_to(p)) == Done{p} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}, cc_fd_absurd(Ed.CcEdPk, Cr.CrBadPublicKey{}, p, h))
    case True{}:
      %cc_done_inj(Ed.CcEdPk, Ed.CcEdPk{o}, p, h) : {Ed.cc.ed.pk(Nat.is_eq(B.Octets.len(Ed.CcEd25519.pk_to(_)), 32n), Ed.CcEd25519.pk_to(_)) == Done{_} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(o), 32n), True{}, hv) : {Ed.cc.ed.pk(_, o) == Done{Ed.CcEdPk{o}} : Result<&2, &2, Cr.CrError, Ed.CcEdPk>}
      {==}

def Laws.ed25519_pk_format(o, p, h):
  cc_ed25519_fmt(Nat.is_eq(B.Octets.len(o), 32n), o, p, {==}, h)
# END GENERATED: proofs
