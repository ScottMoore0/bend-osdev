# Proofs of LAWS_pk.bend: sign.bend's and kex.bend's helpers, unfolded.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./sign.bend as Sg
import ./kex.bend as Kx
import ./LAWS_pk.bend as Laws

def Laws.sign_verify_bytes_done(PK, pk_of, verify, pk, m, sig, p, hp):
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk), Done{p}, hp) : {Sg.cr.sign.check(~PK, ~verify, _, m, sig) == verify(p, m, sig) : Bool}
  {==}

def Laws.sign_verify_bytes_if(SK, PK, public, pk_of, pk_to, sign, verify, sk, m, hf, ha):
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk_to(public(sk))), Done{public(sk)}, hf) : {Sg.cr.sign.check(~PK, ~verify, _, m, sign(sk, m)) == True{} : Bool}
  ha

def Laws.kex_agree_done(SK, PK, secret, pk_of, shared, sk, peer, x, p, hx, hp):
  %Equal.sym(Result<&2, &2, Cr.CrError, SK>, secret(sk), Done{x}, hx) : {Kx.cr.kex.with(~SK, ~PK, ~shared, _, pk_of(peer)) == shared(x, p) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(peer), Done{p}, hp) : {Kx.cr.kex.with(~SK, ~PK, ~shared, Done{x}, _) == shared(x, p) : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def Laws.kex_agree_if(SK, PK, secret, public, pk_of, pk_to, shared, a, b, x, y, hx, hy, hfx, hfy, h):
  %Equal.sym(Result<&2, &2, Cr.CrError, SK>, secret(a), Done{x}, hx) : {Kx.cr.kex.with(~SK, ~PK, ~shared, _, pk_of(pk_to(public(y)))) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk_to(public(y))), Done{public(y)}, hfy) : {Kx.cr.kex.with(~SK, ~PK, ~shared, Done{x}, _) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, SK>, secret(b), Done{y}, hy) : {shared(x, public(y)) == Kx.cr.kex.with(~SK, ~PK, ~shared, _, pk_of(pk_to(public(x)))) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, PK>, pk_of(pk_to(public(x))), Done{public(x)}, hfx) : {shared(x, public(y)) == Kx.cr.kex.with(~SK, ~PK, ~shared, Done{y}, _) : Result<&2, &2, Cr.CrError, B.Octets>}
  h
