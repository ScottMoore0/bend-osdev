import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../bignum/LAWS_mont.bend as NM
import ../bignum/PROOF_mont.bend as NMP
import ./dh.bend as D
import ./LAWS_agree.bend as Laws

# Both primitives exponentiate modulo p: (g^y mod p)^x and (g^x mod p)^y,
# which are the same number by bignum's exp_exp_comm

def Laws.agree(p, g, q, x, y, hp, hpo, hp1, hg, hx, hy):
  %NM.exp_exp_comm(g, y, x, p, hg, hy, hx, hp, hpo, hp1) : {D.dh.prim(D.DhGroup{p, g, q}, Md.BnMod.exp(Md.BnMod.exp(g, y, p), x, p)) == D.dh.prim(D.DhGroup{p, g, q}, _) : Result<&2, &2, D.DhError, B.Octets>}
  {==}
