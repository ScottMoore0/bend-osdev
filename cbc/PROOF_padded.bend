import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../mode-core/mode-core.bend as M
import ../pkcs7/pkcs7.bend as P
import ./cbc.bend as C
import ./LAWS.bend as CML
import ./PROOF.bend as CMP
import ../pkcs7/LAWS.bend as PL
import ../pkcs7/PROOF.bend as PP
import ./LAWS_padded.bend as Laws

# How the proof goes. Encryption pads m to M' (whole blocks:
# pkcs7_pad_blocks) and encrypts M'; cbc_round_trip gives M' back from the
# ciphertext c, and pkcs7_round_trip gives m back from M'. What is left is
# decrypt_padded's first check, that c is not empty: if it were, decryption
# would give the empty string, and unpadding the empty string is refused,
# where unpadding M' gives m.

# From bend-osdev-pkcs7's proofs (private there): False is not True, and
# unpad with its two checks as arguments

def pk.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def pk.empty(h: {False{} == True{} : Bool}) -> Empty:
  %h : pk.disc(_)
  Unit{}

def pk.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, pk.empty(h))

def pk.ug(+bs: Nat, +m: B.Octets, +n: Nat, +md: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    M.cm.check(Nat.is_lt(0n, n), M.CmTooShort{n})
    M.cm.check(Nat.is_eq(md, 0n), M.CmNotBlockMultiple{n})
    P.pkcs7.unpad.oct(bs, m, n)

# Results

def pd.disc(-A: Data, r: Result<&2, &2, M.CmError, A>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def pd.fd(-A: Data, +e: M.CmError, +x: A, h: {Fail{e} == Done{x} : Result<&2, &2, M.CmError, A>}) -> Empty:
  %h : pd.disc(A, _)
  Unit{}

def pd.val(-A: Data, r: Result<&2, &2, M.CmError, A>, d: A) -> A:
  match r:
    case Fail{e}:
      d
    case Done{x}:
      x

def pd.inj(-A: Data, +a: A, +b: A, h: {Done{a} == Done{b} : Result<&2, &2, M.CmError, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, M.CmError, A>, A, r => pd.val(A, r, a), Done{a}, Done{b}, h)

# Naturals and lists

def pd.ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def pd.nd(+p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : pd.ndisc(_)
  Unit{}

def pd.len0(+x: Nat) -> {Nat.is_lt(0n, x) == False{} : Bool} -> {x == 0n : Nat}:
  match x:
    case 0n:
      h => {==}
    case 1n+p:
      h => pk.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, True{}, False{}, h))

def pd.nil(xs: List<&2, U32>) -> {B.len(xs) == 0n : Nat} -> {xs == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{x, t}:
      h => Empty.absurd({Con{x, t} == Nil{} : List<&2, U32>}, pd.nd(B.len(t), h))

# CBC decryption of no bytes, under any IV, is no bytes
def pd.e0(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +mp: B.Octets) -> {C.cbc.d1.fast(~K, ~dec, k, r, Nil{}) == Done{mp} : Result<&2, &2, M.CmError, B.Octets>} -> {B.Octets.len(mp) == 0n : Nat}:
  match r:
    case Fail{e}:
      h => Empty.absurd({B.Octets.len(mp) == 0n : Nat}, pd.fd(B.Octets, e, mp, h))
    case Done{v}:
      h => Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Nil{})), B.Octets.len(mp), Equal.cong(B.Octets, Nat, o => B.Octets.len(o), B.Octets.of_list(Nil{}), mp, pd.inj(B.Octets, B.Octets.of_list(Nil{}), mp, h)))

# decrypt_padded with its first check as an argument
def pd.dpx(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, +c: B.Octets, ok: Bool) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    M.cm.check(ok, M.CmTooShort{B.Octets.len(c)})
    padded : B.Octets <- C.Cbc.decrypt(~K, ~dec, k, iv, c)
    P.Pkcs7.unpad(16n, padded)

# an empty ciphertext cannot decrypt to M': its decryption is empty, and
# unpadding the empty string is refused
def pd.dc0(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +mp: B.Octets, +m: B.Octets, e2: {P.Pkcs7.unpad(16n, mp) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}, +c: B.Octets, eo: {Nat.is_lt(0n, B.Octets.len(c)) == False{} : Bool}, e1: {C.Cbc.decrypt(~K, ~dec, k, iv, c) == Done{mp} : Result<&2, &2, M.CmError, B.Octets>}) -> {C.Cbc.decrypt_padded(~K, ~dec, k, iv, c) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}:
  # c is empty
  +z = pd.len0(B.Octets.len(c))(eo)
  +nl = pd.nil(B.Octets.to_list(c))(Equal.trans(Nat, B.len(B.Octets.to_list(c)), B.Octets.len(c), 0n, Equal.sym(Nat, B.Octets.len(c), B.len(B.Octets.to_list(c)), BL.octets_len_list(c)), z))
  # so M' is empty
  +e3 = Equal.trans(Result<&2, &2, M.CmError, B.Octets>, C.cbc.d1.fast(~K, ~dec, k, C.cbc.iv(iv), Nil{}), C.Cbc.decrypt(~K, ~dec, k, iv, c), Done{mp}, Equal.cong(List<&2, U32>, Result<&2, &2, M.CmError, B.Octets>, l => C.cbc.d1.fast(~K, ~dec, k, C.cbc.iv(iv), l), Nil{}, B.Octets.to_list(c), Equal.sym(List<&2, U32>, B.Octets.to_list(c), Nil{}, nl)), e1)
  +z2 = pd.e0(~K, ~dec, k, C.cbc.iv(iv), mp)(e3)
  # and unpadding it is refused
  +e4 = Equal.trans(Result<&2, &2, M.CmError, B.Octets>, Fail{M.CmTooShort{0n}}, P.Pkcs7.unpad(16n, mp), Done{m}, Equal.cong(Nat, Result<&2, &2, M.CmError, B.Octets>, n => pk.ug(16n, mp, n, Nat.mod(n, 16n)), 0n, B.Octets.len(mp), Equal.sym(Nat, B.Octets.len(mp), 0n, z2)), e2)
  Empty.absurd({C.Cbc.decrypt_padded(~K, ~dec, k, iv, c) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}, pd.fd(B.Octets, M.CmTooShort{0n}, m, e4))

# from the ciphertext c, decrypting gives M' and unpadding M' gives m
def pd.dc(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +mp: B.Octets, +m: B.Octets, e2: {P.Pkcs7.unpad(16n, mp) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}, +c: B.Octets, ok: Bool) -> {Nat.is_lt(0n, B.Octets.len(c)) == ok : Bool} -> {C.Cbc.decrypt(~K, ~dec, k, iv, c) == Done{mp} : Result<&2, &2, M.CmError, B.Octets>} -> {C.Cbc.decrypt_padded(~K, ~dec, k, iv, c) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}:
  match ok:
    case True{}:
      eo => e1 => %Equal.sym(Bool, Nat.is_lt(0n, B.Octets.len(c)), True{}, eo) : {pd.dpx(~K, ~dec, k, iv, c, _) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
        %Equal.sym(Result<&2, &2, M.CmError, B.Octets>, C.Cbc.decrypt(~K, ~dec, k, iv, c), Done{mp}, e1) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, padded => P.Pkcs7.unpad(16n, padded)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
        e2
    case False{}:
      eo => e1 => pd.dc0(~K, ~dec, k, iv, mp, m, e2, c, eo, e1)

def pd.go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +mp: B.Octets, +m: B.Octets, e2: {P.Pkcs7.unpad(16n, mp) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}, r: Result<&2, &2, M.CmError, B.Octets>) -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, c => C.Cbc.decrypt(~K, ~dec, k, iv, c)) == Done{mp} : Result<&2, &2, M.CmError, B.Octets>} -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, c => C.Cbc.decrypt_padded(~K, ~dec, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      e1 => Empty.absurd({Fail{e} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}, pd.fd(B.Octets, e, mp, e1))
    case Done{+c}:
      e1 => pd.dc(~K, ~dec, k, iv, mp, m, e2, c, Nat.is_lt(0n, B.Octets.len(c)))({==})(e1)

def Laws.cbc_padded_round_trip(K, enc, dec, k, inv, iv, m, hi):
  # the padded message is whole blocks
  +hm = pd.inj(Nat, Nat.mod(B.Octets.len(P.pkcs7.pad.oct(16n, m)), 16n), 0n, PL.pkcs7_pad_blocks(16n, m))
  pd.go(~K, ~dec, k, iv, P.pkcs7.pad.oct(16n, m), m, PL.pkcs7_round_trip(16n, m), C.Cbc.encrypt(~K, ~enc, k, iv, P.pkcs7.pad.oct(16n, m)))(CML.cbc_round_trip(~K, ~enc, ~dec, k, inv, iv, P.pkcs7.pad.oct(16n, m), hi, hm))
