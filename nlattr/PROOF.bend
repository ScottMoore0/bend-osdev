# Proofs of bend-osdev-nlattr's laws. Parse after build goes attribute by
# attribute: the masked header bytes read back as the length and the type
# with its flags (through proof_byte's byte lemmas), then the payload is
# taken, the padding dropped, and the rest parsed. Reading within the buffer
# goes the same way over any parse that succeeds.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./header.bend as H
import ./nlattr.bend as N
import ./policy.bend as P
import ./proof_byte.bend as NB
import ./proof_nat.bend as NN
import ./proof_list.bend as NQ
import ./LAWS.bend as Laws

# The 16-bit fields: a value whose high byte is below 256, written as two
# bytes and masked, reads back as itself

def pr.u16_le(+n: Nat, +hn: {H.nla.fits16(n) == True{} : Bool}) -> {H.nla.u16_value(H.NlLittle{}, B.byte(H.nla.byte(Nat.mod(n, 256n))), B.byte(H.nla.byte(Nat.div(n, 256n)))) == n : Nat}:
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.div(n, 256n)))), Nat.div(n, 256n), NB.nb.byte(Nat.div(n, 256n), hn)) : {Nat.add(Nat.mul(_, 256n), U32.to_nat(B.byte(U32.from_nat(Nat.mod(n, 256n))))) == n : Nat}
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.mod(n, 256n)))), Nat.mod(n, 256n), NB.nb.byte(Nat.mod(n, 256n), NN.nn.mod_lt(n))) : {Nat.add(Nat.mul(Nat.div(n, 256n), 256n), _) == n : Nat}
  NN.nn.recon(n)

def pr.u16_be(+n: Nat, +hn: {H.nla.fits16(n) == True{} : Bool}) -> {H.nla.u16_value(H.NlBig{}, B.byte(H.nla.byte(Nat.div(n, 256n))), B.byte(H.nla.byte(Nat.mod(n, 256n)))) == n : Nat}:
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.div(n, 256n)))), Nat.div(n, 256n), NB.nb.byte(Nat.div(n, 256n), hn)) : {Nat.add(Nat.mul(_, 256n), U32.to_nat(B.byte(U32.from_nat(Nat.mod(n, 256n))))) == n : Nat}
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.mod(n, 256n)))), Nat.mod(n, 256n), NB.nb.byte(Nat.mod(n, 256n), NN.nn.mod_lt(n))) : {Nat.add(Nat.mul(Nat.div(n, 256n), 256n), _) == n : Nat}
  NN.nn.recon(n)


# The type field: a type below 16384 and its flags read back from the two
# bytes (only constants up to 256 appear, so nothing large is expanded)

def pr.hi_lt(+t: Nat, nd: Bool, nb: Bool, +ht: {H.nla.type_ok(t) == True{} : Bool}) -> {Nat.is_lt(H.nla.type_hi(t, nd, nb), 256n) == True{} : Bool}:
  match nd nb:
    case True{} True{}:
      ht
    case True{} False{}:
      NN.nn.lt_le_trans(Nat.div(t, 256n), 64n, 128n, ht, {==})
    case False{} True{}:
      NN.nn.lt_le_trans(Nat.div(t, 256n), 64n, 192n, ht, {==})
    case False{} False{}:
      NN.nn.lt_le_trans(Nat.div(t, 256n), 64n, 256n, ht, {==})

def pr.dec_tt(+t: Nat, -xs: List<&2, U32>) -> {N.nla.parse.attr1(H.nla.has(H.nla.type_hi(t, True{}, True{}), 128n), Nat.mod(t, 256n), xs) == N.NlAttr{t, True{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}:
  +d = Nat.div(t, 256n)
  %Equal.sym(Bool, Nat.is_le(64n, Nat.add(64n, d)), True{}, NN.nn.le_add(64n, d)) : {N.nla.parse.attr2(H.nla.has.go(Nat.add(64n, d), 64n, _), True{}, Nat.mod(t, 256n), xs) == N.NlAttr{t, True{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.sub(Nat.add(64n, d), 64n), d, NN.nn.sub_add_l(64n, d)) : {N.NlAttr{Nat.add(Nat.mul(_, 256n), Nat.mod(t, 256n)), True{}, True{}, B.Octets.of_list(xs)} == N.NlAttr{t, True{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.add(Nat.mul(d, 256n), Nat.mod(t, 256n)), t, NN.nn.recon(t)) : {N.NlAttr{_, True{}, True{}, B.Octets.of_list(xs)} == N.NlAttr{t, True{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  {==}

def pr.dec_tf(+t: Nat, -xs: List<&2, U32>, +ht: {H.nla.type_ok(t) == True{} : Bool}) -> {N.nla.parse.attr1(H.nla.has(H.nla.type_hi(t, True{}, False{}), 128n), Nat.mod(t, 256n), xs) == N.NlAttr{t, True{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}:
  +d = Nat.div(t, 256n)
  %Equal.sym(Bool, Nat.is_le(128n, Nat.add(128n, d)), True{}, NN.nn.le_add(128n, d)) : {N.nla.parse.attr1(H.nla.has.go(Nat.add(128n, d), 128n, _), Nat.mod(t, 256n), xs) == N.NlAttr{t, True{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.sub(Nat.add(128n, d), 128n), d, NN.nn.sub_add_l(128n, d)) : {N.nla.parse.attr2(H.nla.has(_, 64n), True{}, Nat.mod(t, 256n), xs) == N.NlAttr{t, True{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Bool, Nat.is_le(64n, d), False{}, NN.nn.lt_nle(d, 64n, ht)) : {N.nla.parse.attr2(H.nla.has.go(d, 64n, _), True{}, Nat.mod(t, 256n), xs) == N.NlAttr{t, True{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.add(Nat.mul(d, 256n), Nat.mod(t, 256n)), t, NN.nn.recon(t)) : {N.NlAttr{_, True{}, False{}, B.Octets.of_list(xs)} == N.NlAttr{t, True{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  {==}

def pr.dec_ft(+t: Nat, -xs: List<&2, U32>, +ht: {H.nla.type_ok(t) == True{} : Bool}) -> {N.nla.parse.attr1(H.nla.has(H.nla.type_hi(t, False{}, True{}), 128n), Nat.mod(t, 256n), xs) == N.NlAttr{t, False{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}:
  +d = Nat.div(t, 256n)
  %Equal.sym(Bool, Nat.is_le(128n, Nat.add(64n, d)), False{}, NN.nn.lt_nle(d, 64n, ht)) : {N.nla.parse.attr1(H.nla.has.go(Nat.add(64n, d), 128n, _), Nat.mod(t, 256n), xs) == N.NlAttr{t, False{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Bool, Nat.is_le(64n, Nat.add(64n, d)), True{}, NN.nn.le_add(64n, d)) : {N.nla.parse.attr2(H.nla.has.go(Nat.add(64n, d), 64n, _), False{}, Nat.mod(t, 256n), xs) == N.NlAttr{t, False{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.sub(Nat.add(64n, d), 64n), d, NN.nn.sub_add_l(64n, d)) : {N.NlAttr{Nat.add(Nat.mul(_, 256n), Nat.mod(t, 256n)), False{}, True{}, B.Octets.of_list(xs)} == N.NlAttr{t, False{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.add(Nat.mul(d, 256n), Nat.mod(t, 256n)), t, NN.nn.recon(t)) : {N.NlAttr{_, False{}, True{}, B.Octets.of_list(xs)} == N.NlAttr{t, False{}, True{}, B.Octets.of_list(xs)} : N.NlAttr}
  {==}

def pr.dec_ff(+t: Nat, -xs: List<&2, U32>, +ht: {H.nla.type_ok(t) == True{} : Bool}) -> {N.nla.parse.attr1(H.nla.has(H.nla.type_hi(t, False{}, False{}), 128n), Nat.mod(t, 256n), xs) == N.NlAttr{t, False{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}:
  +d = Nat.div(t, 256n)
  %Equal.sym(Bool, Nat.is_le(128n, d), False{}, NN.nn.lt_nle(d, 128n, NN.nn.lt_le_trans(d, 64n, 128n, ht, {==}))) : {N.nla.parse.attr1(H.nla.has.go(d, 128n, _), Nat.mod(t, 256n), xs) == N.NlAttr{t, False{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Bool, Nat.is_le(64n, d), False{}, NN.nn.lt_nle(d, 64n, ht)) : {N.nla.parse.attr2(H.nla.has.go(d, 64n, _), False{}, Nat.mod(t, 256n), xs) == N.NlAttr{t, False{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, Nat.add(Nat.mul(d, 256n), Nat.mod(t, 256n)), t, NN.nn.recon(t)) : {N.NlAttr{_, False{}, False{}, B.Octets.of_list(xs)} == N.NlAttr{t, False{}, False{}, B.Octets.of_list(xs)} : N.NlAttr}
  {==}

def pr.dec(+t: Nat, nd: Bool, nb: Bool, -xs: List<&2, U32>, +ht: {H.nla.type_ok(t) == True{} : Bool}) -> {N.nla.parse.attr1(H.nla.has(H.nla.type_hi(t, nd, nb), 128n), Nat.mod(t, 256n), xs) == N.NlAttr{t, nd, nb, B.Octets.of_list(xs)} : N.NlAttr}:
  match nd nb:
    case True{} True{}:
      pr.dec_tt(t, xs)
    case True{} False{}:
      pr.dec_tf(t, xs, ht)
    case False{} True{}:
      pr.dec_ft(t, xs, ht)
    case False{} False{}:
      pr.dec_ff(t, xs, ht)

# the masked type field bytes read back
def pr.attr_bytes(+t: Nat, +nd: Bool, +nb: Bool, -xs: List<&2, U32>, +ht: {H.nla.type_ok(t) == True{} : Bool}) -> {N.nla.parse.attr(B.byte(H.nla.byte(H.nla.type_hi(t, nd, nb))), B.byte(H.nla.byte(Nat.mod(t, 256n))), xs) == N.NlAttr{t, nd, nb, B.Octets.of_list(xs)} : N.NlAttr}:
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(H.nla.type_hi(t, nd, nb)))), H.nla.type_hi(t, nd, nb), NB.nb.byte(H.nla.type_hi(t, nd, nb), pr.hi_lt(t, nd, nb, ht))) : {N.nla.parse.attr1(H.nla.has(_, 128n), U32.to_nat(B.byte(U32.from_nat(Nat.mod(t, 256n)))), xs) == N.NlAttr{t, nd, nb, B.Octets.of_list(xs)} : N.NlAttr}
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.mod(t, 256n)))), Nat.mod(t, 256n), NB.nb.byte(Nat.mod(t, 256n), NN.nn.mod_lt(t))) : {N.nla.parse.attr1(H.nla.has(H.nla.type_hi(t, nd, nb), 128n), _, xs) == N.NlAttr{t, nd, nb, B.Octets.of_list(xs)} : N.NlAttr}
  pr.dec(t, nd, nb, xs, ht)

# One attribute: its masked bytes parse back, then the rest

# the bytes after the header: the payload, the padding, and the rest
def pr.body(+o: H.NlOrder, +pay: B.Octets, +l: List<&2, U32>) -> {B.mask(List.append(&2, U32, B.Octets.to_list(pay), List.append(&2, U32, B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))))), l))) == List.append(&2, U32, B.Octets.to_list(pay), List.append(&2, U32, B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))))), B.mask(l))) : List<&2, U32>}:
  +p = B.Octets.to_list(pay)
  +z = B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, p))))
  %Equal.sym(List<&2, U32>, B.mask(List.append(&2, U32, p, List.append(&2, U32, z, l))), List.append(&2, U32, B.mask(p), B.mask(List.append(&2, U32, z, l))), NQ.nq.mask_app(p, List.append(&2, U32, z, l))) : {_ == List.append(&2, U32, p, List.append(&2, U32, z, B.mask(l))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(p), p, NQ.nq.mask_to(pay)) : {List.append(&2, U32, _, B.mask(List.append(&2, U32, z, l))) == List.append(&2, U32, p, List.append(&2, U32, z, B.mask(l))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(List.append(&2, U32, z, l)), List.append(&2, U32, B.mask(z), B.mask(l)), NQ.nq.mask_app(z, l)) : {List.append(&2, U32, p, _) == List.append(&2, U32, p, List.append(&2, U32, z, B.mask(l))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(z), z, NQ.nq.mask_zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, p))))) : {List.append(&2, U32, p, List.append(&2, U32, _, B.mask(l))) == List.append(&2, U32, p, List.append(&2, U32, z, B.mask(l))) : List<&2, U32>}
  {==}

def pr.step(+o: H.NlOrder, +s: Bool, +f: Nat, +t: Nat, +nd: Bool, +nb: Bool, +pay: B.Octets, +l: List<&2, U32>, +b2: U32, +b3: U32, -ts: List<&2, N.NlAttr>, +hattr: {N.nla.parse.attr_o(o, b2, b3, B.Octets.to_list(pay)) == N.NlAttr{t, nd, nb, B.Octets.of_list(B.Octets.to_list(pay))} : N.NlAttr}, +ih: {N.nla.parse.go(f, N.NlOpts{o, s}, B.mask(l)) == Done{ts} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {N.nla.parse.check(Bool.and(Nat.is_le(4n, Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay)))), Nat.is_le(Nat.sub(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))), 4n), List.length(&2, U32, B.mask(List.append(&2, U32, B.Octets.to_list(pay), List.append(&2, U32, B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))))), l)))))), o, b2, b3, Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))), B.mask(List.append(&2, U32, B.Octets.to_list(pay), List.append(&2, U32, B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))))), l))), N.nla.parse.go(f, N.NlOpts{o, s}, N.nla.parse.rest(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))), B.mask(List.append(&2, U32, B.Octets.to_list(pay), List.append(&2, U32, B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, B.Octets.to_list(pay))))), l)))))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}:
  +p = B.Octets.to_list(pay)
  +lp = List.length(&2, U32, p)
  +n = Nat.add(4n, lp)
  +z = B.zeros(H.nla.pad(n))
  +r = List.append(&2, U32, p, List.append(&2, U32, z, B.mask(l)))
  +rr = B.mask(List.append(&2, U32, p, List.append(&2, U32, z, l)))
  %Equal.sym(List<&2, U32>, rr, r, pr.body(o, pay, l)) : {N.nla.parse.check(Bool.and(Nat.is_le(4n, n), Nat.is_le(Nat.sub(n, 4n), List.length(&2, U32, _))), o, b2, b3, n, _, N.nla.parse.go(f, N.NlOpts{o, s}, N.nla.parse.rest(n, _))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(Nat, Nat.sub(n, 4n), lp, NN.nn.sub_add_l(4n, lp)) : {N.nla.parse.check(Bool.and(Nat.is_le(4n, n), Nat.is_le(_, List.length(&2, U32, r))), o, b2, b3, n, r, N.nla.parse.go(f, N.NlOpts{o, s}, List.drop(&2, U32, List.drop(&2, U32, r, _), H.nla.pad(n)))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  +lenr = NQ.nq.app_len(p, List.append(&2, U32, z, B.mask(l)))
  +okr = Equal.trans(Bool, Nat.is_le(lp, List.length(&2, U32, r)), Nat.is_le(lp, Nat.add(lp, List.length(&2, U32, List.append(&2, U32, z, B.mask(l))))), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(lp, x), List.length(&2, U32, r), Nat.add(lp, List.length(&2, U32, List.append(&2, U32, z, B.mask(l)))), lenr), NN.nn.le_add(lp, List.length(&2, U32, List.append(&2, U32, z, B.mask(l)))))
  %Equal.sym(Bool, Bool.and(Nat.is_le(4n, n), Nat.is_le(lp, List.length(&2, U32, r))), True{}, NN.nn.and_i(Nat.is_le(4n, n), Nat.is_le(lp, List.length(&2, U32, r)), NN.nn.le_add(4n, lp), okr)) : {N.nla.parse.check(_, o, b2, b3, n, r, N.nla.parse.go(f, N.NlOpts{o, s}, List.drop(&2, U32, List.drop(&2, U32, r, lp), H.nla.pad(n)))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(Nat, Nat.sub(n, 4n), lp, NN.nn.sub_add_l(4n, lp)) : {N.nla.parse.cons(N.nla.parse.attr_o(o, b2, b3, List.take(&2, U32, r, _)), N.nla.parse.go(f, N.NlOpts{o, s}, List.drop(&2, U32, List.drop(&2, U32, r, lp), H.nla.pad(n)))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, r, lp), p, NQ.nq.take_app(p, List.append(&2, U32, z, B.mask(l)))) : {N.nla.parse.cons(N.nla.parse.attr_o(o, b2, b3, _), N.nla.parse.go(f, N.NlOpts{o, s}, List.drop(&2, U32, List.drop(&2, U32, r, lp), H.nla.pad(n)))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, r, lp), List.append(&2, U32, z, B.mask(l)), NQ.nq.drop_app(p, List.append(&2, U32, z, B.mask(l)))) : {N.nla.parse.cons(N.nla.parse.attr_o(o, b2, b3, p), N.nla.parse.go(f, N.NlOpts{o, s}, List.drop(&2, U32, _, H.nla.pad(n)))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %NQ.nq.zeros_len(H.nla.pad(n)) : {N.nla.parse.cons(N.nla.parse.attr_o(o, b2, b3, p), N.nla.parse.go(f, N.NlOpts{o, s}, List.drop(&2, U32, List.append(&2, U32, z, B.mask(l)), _))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.append(&2, U32, z, B.mask(l)), List.length(&2, U32, z)), B.mask(l), NQ.nq.drop_app(z, B.mask(l))) : {N.nla.parse.cons(N.nla.parse.attr_o(o, b2, b3, p), N.nla.parse.go(f, N.NlOpts{o, s}, _)) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(N.NlAttr, N.nla.parse.attr_o(o, b2, b3, p), N.NlAttr{t, nd, nb, B.Octets.of_list(p)}, hattr) : {N.nla.parse.cons(_, N.nla.parse.go(f, N.NlOpts{o, s}, B.mask(l))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(B.Octets, B.Octets.of_list(p), pay, BL.octets_of_to(pay)) : {N.nla.parse.cons(N.NlAttr{t, nd, nb, _}, N.nla.parse.go(f, N.NlOpts{o, s}, B.mask(l))) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  %Equal.sym(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, N.nla.parse.go(f, N.NlOpts{o, s}, B.mask(l)), Done{ts}, ih) : {N.nla.parse.cons(N.NlAttr{t, nd, nb, pay}, _) == Done{Con{N.NlAttr{t, nd, nb, pay}, ts}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  {==}

# Parse after build

def pr.mdisc(m: Maybe<&2, N.NlError>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def pr.sn(-x: N.NlError, e: {Some{x} == None{} : Maybe<&2, N.NlError>}) -> Empty:
  %e : pr.mdisc(_)
  Unit{}

def pr.fe_ok(b: Bool, -a: N.NlAttr, -r: Maybe<&2, N.NlError>, +h: {N.nla.first_err.pick(b, a, r) == None{} : Maybe<&2, N.NlError>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, pr.sn(N.nla.err(a), h))

def pr.fe_rest(b: Bool, -a: N.NlAttr, -r: Maybe<&2, N.NlError>, +h: {N.nla.first_err.pick(b, a, r) == None{} : Maybe<&2, N.NlError>}) -> {r == None{} : Maybe<&2, N.NlError>}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({r == None{} : Maybe<&2, N.NlError>}, pr.sn(N.nla.err(a), h))

def pr.le_app(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {Nat.is_le(List.length(&2, U32, ys), List.length(&2, U32, List.append(&2, U32, xs, ys))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, xs, ys)), Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)), NQ.nq.app_len(xs, ys)) : {Nat.is_le(List.length(&2, U32, ys), _) == True{} : Bool}
  NN.nn.le_add_l(List.length(&2, U32, xs), List.length(&2, U32, ys))

def pr.rt(+as: List<&2, N.NlAttr>, +o: H.NlOrder, +s: Bool, +fu: Nat, +ha: {N.nla.first_err(as) == None{} : Maybe<&2, N.NlError>}, +hf: {Nat.is_le(List.length(&2, U32, N.nla.enc_all(o, as)), fu) == True{} : Bool}) -> {N.nla.parse.go(fu, N.NlOpts{o, s}, B.mask(N.nla.enc_all(o, as))) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}:
  match as:
    case Nil{}:
      match fu:
        case 0n:
          {==}
        case 1n+f:
          {==}
    case Con{N.NlAttr{+t0, +nd, +nb, +pay}, +rest}:
      match o fu:
        case H.NlLittle{} 0n:
          Empty.absurd({N.nla.parse.go(0n, N.NlOpts{H.NlLittle{}, s}, B.mask(N.nla.enc_all(H.NlLittle{}, Con{N.NlAttr{t0, nd, nb, pay}, rest}))) == Done{Con{N.NlAttr{t0, nd, nb, pay}, rest}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}, NN.nn.ft(hf))
        case H.NlBig{} 0n:
          Empty.absurd({N.nla.parse.go(0n, N.NlOpts{H.NlBig{}, s}, B.mask(N.nla.enc_all(H.NlBig{}, Con{N.NlAttr{t0, nd, nb, pay}, rest}))) == Done{Con{N.NlAttr{t0, nd, nb, pay}, rest}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}, NN.nn.ft(hf))
        case H.NlLittle{} 1n+ +f:
          +a : N.NlAttr = N.NlAttr{t0, nd, nb, pay}
          +p = B.Octets.to_list(pay)
          +n = Nat.add(4n, List.length(&2, U32, p))
          +et = N.nla.enc_all(H.NlLittle{}, rest)
          +w = List.append(&2, U32, p, List.append(&2, U32, B.zeros(H.nla.pad(n)), et))
          +hok = pr.fe_ok(N.nla.ok(a), a, N.nla.first_err(rest), ha)
          +ht = NN.nn.and_l(H.nla.type_ok(t0), H.nla.fits16(N.nla.len_of(a)), hok)
          +hn = Equal.trans(Bool, H.nla.fits16(n), H.nla.fits16(N.nla.len_of(a)), True{}, Equal.cong(Nat, Bool, x => H.nla.fits16(Nat.add(4n, x)), List.length(&2, U32, p), B.Octets.len(pay), Equal.sym(Nat, B.Octets.len(pay), List.length(&2, U32, p), NQ.nq.olen(pay))), NN.nn.and_r(H.nla.type_ok(t0), H.nla.fits16(N.nla.len_of(a)), hok))
          +het = NN.nn.le_trans(List.length(&2, U32, et), List.length(&2, U32, List.append(&2, U32, B.zeros(H.nla.pad(n)), et)), List.length(&2, U32, w), pr.le_app(B.zeros(H.nla.pad(n)), et), pr.le_app(p, List.append(&2, U32, B.zeros(H.nla.pad(n)), et)))
          +ih = pr.rt(rest, H.NlLittle{}, s, f, pr.fe_rest(N.nla.ok(a), a, N.nla.first_err(rest), ha), NN.nn.le_trans(List.length(&2, U32, et), List.length(&2, U32, w), f, het, NN.nn.le_trans(List.length(&2, U32, w), Nat.add(3n, List.length(&2, U32, w)), f, NN.nn.le_add_l(3n, List.length(&2, U32, w)), hf)))
          +b2 = B.byte(H.nla.byte(Nat.mod(t0, 256n)))
          +b3 = B.byte(H.nla.byte(H.nla.type_hi(t0, nd, nb)))
          +nv = H.nla.u16_value(H.NlLittle{}, B.byte(H.nla.byte(Nat.mod(n, 256n))), B.byte(H.nla.byte(Nat.div(n, 256n))))
          %Equal.sym(Nat, nv, n, pr.u16_le(n, hn)) : {N.nla.parse.check(Bool.and(Nat.is_le(4n, _), Nat.is_le(Nat.sub(_, 4n), List.length(&2, U32, B.mask(w)))), H.NlLittle{}, b2, b3, _, B.mask(w), N.nla.parse.go(f, N.NlOpts{H.NlLittle{}, s}, N.nla.parse.rest(_, B.mask(w)))) == Done{Con{N.NlAttr{t0, nd, nb, pay}, rest}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
          pr.step(H.NlLittle{}, s, f, t0, nd, nb, pay, et, b2, b3, rest, pr.attr_bytes(t0, nd, nb, p, ht), ih)
        case H.NlBig{} 1n+ +f:
          +a : N.NlAttr = N.NlAttr{t0, nd, nb, pay}
          +p = B.Octets.to_list(pay)
          +n = Nat.add(4n, List.length(&2, U32, p))
          +et = N.nla.enc_all(H.NlBig{}, rest)
          +w = List.append(&2, U32, p, List.append(&2, U32, B.zeros(H.nla.pad(n)), et))
          +hok = pr.fe_ok(N.nla.ok(a), a, N.nla.first_err(rest), ha)
          +ht = NN.nn.and_l(H.nla.type_ok(t0), H.nla.fits16(N.nla.len_of(a)), hok)
          +hn = Equal.trans(Bool, H.nla.fits16(n), H.nla.fits16(N.nla.len_of(a)), True{}, Equal.cong(Nat, Bool, x => H.nla.fits16(Nat.add(4n, x)), List.length(&2, U32, p), B.Octets.len(pay), Equal.sym(Nat, B.Octets.len(pay), List.length(&2, U32, p), NQ.nq.olen(pay))), NN.nn.and_r(H.nla.type_ok(t0), H.nla.fits16(N.nla.len_of(a)), hok))
          +het = NN.nn.le_trans(List.length(&2, U32, et), List.length(&2, U32, List.append(&2, U32, B.zeros(H.nla.pad(n)), et)), List.length(&2, U32, w), pr.le_app(B.zeros(H.nla.pad(n)), et), pr.le_app(p, List.append(&2, U32, B.zeros(H.nla.pad(n)), et)))
          +ih = pr.rt(rest, H.NlBig{}, s, f, pr.fe_rest(N.nla.ok(a), a, N.nla.first_err(rest), ha), NN.nn.le_trans(List.length(&2, U32, et), List.length(&2, U32, w), f, het, NN.nn.le_trans(List.length(&2, U32, w), Nat.add(3n, List.length(&2, U32, w)), f, NN.nn.le_add_l(3n, List.length(&2, U32, w)), hf)))
          +b2 = B.byte(H.nla.byte(H.nla.type_hi(t0, nd, nb)))
          +b3 = B.byte(H.nla.byte(Nat.mod(t0, 256n)))
          +nv = H.nla.u16_value(H.NlBig{}, B.byte(H.nla.byte(Nat.div(n, 256n))), B.byte(H.nla.byte(Nat.mod(n, 256n))))
          %Equal.sym(Nat, nv, n, pr.u16_be(n, hn)) : {N.nla.parse.check(Bool.and(Nat.is_le(4n, _), Nat.is_le(Nat.sub(_, 4n), List.length(&2, U32, B.mask(w)))), H.NlBig{}, b2, b3, _, B.mask(w), N.nla.parse.go(f, N.NlOpts{H.NlBig{}, s}, N.nla.parse.rest(_, B.mask(w)))) == Done{Con{N.NlAttr{t0, nd, nb, pay}, rest}} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
          pr.step(H.NlBig{}, s, f, t0, nd, nb, pay, et, b2, b3, rest, pr.attr_bytes(t0, nd, nb, p, ht), ih)

def pr.odisc(r: Result<&2, &2, N.NlError, B.Octets>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def pr.ofd(-x: N.NlError, -y: B.Octets, e: {Fail{x} == Done{y} : Result<&2, &2, N.NlError, B.Octets>}) -> Empty:
  %Equal.sym(Result<&2, &2, N.NlError, B.Octets>, Fail{x}, Done{y}, e) : pr.odisc(_)
  Unit{}

def pr.od(r: Result<&2, &2, N.NlError, B.Octets>) -> B.Octets:
  match r:
    case Fail{x}:
      B.Octets.empty()
    case Done{y}:
      y

def pr.pb(m: Maybe<&2, N.NlError>, +o: H.NlOrder, +s: Bool, +as: List<&2, N.NlAttr>, -b: B.Octets, +em: {N.nla.first_err(as) == m : Maybe<&2, N.NlError>}, +e: {N.nla.build.go(m, o, as) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}) -> {N.nla.parse(N.NlOpts{o, s}, b) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}:
  match m:
    case None{}:
      +ee = N.nla.enc_all(o, as)
      %Equal.cong(Result<&2, &2, N.NlError, B.Octets>, B.Octets, z => pr.od(z), Done{B.Octets.of_list(ee)}, Done{b}, e) : {N.nla.parse(N.NlOpts{o, s}, _) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(ee)), B.mask(ee), BL.octets_to_of(ee)) : {N.nla.parse.go(List.length(&2, U32, _), N.NlOpts{o, s}, _) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
      pr.rt(as, o, s, List.length(&2, U32, B.mask(ee)), em, Equal.trans(Bool, Nat.is_le(List.length(&2, U32, ee), List.length(&2, U32, B.mask(ee))), Nat.is_le(List.length(&2, U32, ee), List.length(&2, U32, ee)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(List.length(&2, U32, ee), z), List.length(&2, U32, B.mask(ee)), List.length(&2, U32, ee), NQ.nq.mask_len(ee)), NN.nn.le_refl(List.length(&2, U32, ee))))
    case Some{x}:
      Empty.absurd({N.nla.parse(N.NlOpts{o, s}, b) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}, pr.ofd(x, b, e))

def Laws.parse_build(o, s, as, b, e):
  pr.pb(N.nla.first_err(as), o, s, as, b, {==}, e)

# One built attribute: its header, its payload, then its zero padding

def pr.app_nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pr.app_nil(t) : {Con{h, List.append(&2, U32, t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def pr.app_assoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pr.app_assoc(t, ys, zs) : {Con{h, List.append(&2, U32, List.append(&2, U32, t, ys), zs)} == Con{h, _} : List<&2, U32>}
      {==}

def pr.hdr(o: H.NlOrder, +n: Nat, +t: Nat, +nd: Bool, +nb: Bool, -xs: List<&2, U32>) -> {H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, xs)) == List.append(&2, U32, H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, Nil{})), xs) : List<&2, U32>}:
  match o:
    case H.NlLittle{}:
      {==}
    case H.NlBig{}:
      {==}

def pr.hdr_len(o: H.NlOrder, +n: Nat, +t: Nat, +nd: Bool, +nb: Bool) -> {List.length(&2, U32, H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, Nil{}))) == 4n : Nat}:
  match o:
    case H.NlLittle{}:
      {==}
    case H.NlBig{}:
      {==}

# the Octets of a joined list join the Octets of its parts
def pr.oapp(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.Octets.of_list(List.append(&2, U32, xs, ys)) == B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys)) : B.Octets}:
  +ox = B.Octets.of_list(xs)
  +oy = B.Octets.of_list(ys)
  +z = List.append(&2, U32, xs, ys)
  %BL.octets_of_to(B.Octets.append(ox, oy)) : {B.Octets.of_list(z) == _ : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(ox, oy)), B.append(B.Octets.to_list(ox), B.Octets.to_list(oy)), BL.octets_append_list(ox, oy)) : {B.Octets.of_list(z) == B.Octets.of_list(_) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(ox), B.mask(xs), BL.octets_to_of(xs)) : {B.Octets.of_list(z) == B.Octets.of_list(List.append(&2, U32, _, B.Octets.to_list(oy))) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(oy), B.mask(ys), BL.octets_to_of(ys)) : {B.Octets.of_list(z) == B.Octets.of_list(List.append(&2, U32, B.mask(xs), _)) : B.Octets}
  %NQ.nq.mask_app(xs, ys) : {B.Octets.of_list(z) == B.Octets.of_list(_) : B.Octets}
  %BL.octets_to_of(z) : {B.Octets.of_list(z) == B.Octets.of_list(_) : B.Octets}
  Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(z))), B.Octets.of_list(z), BL.octets_of_list_idempotent(z))

def pr.odrop(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.Octets.drop(List.length(&2, U32, xs), B.Octets.of_list(List.append(&2, U32, xs, ys))) == B.Octets.of_list(ys) : B.Octets}:
  +ox = B.Octets.of_list(xs)
  +oy = B.Octets.of_list(ys)
  %Equal.sym(B.Octets, B.Octets.of_list(List.append(&2, U32, xs, ys)), B.Octets.append(ox, oy), pr.oapp(xs, ys)) : {B.Octets.drop(List.length(&2, U32, xs), _) == oy : B.Octets}
  %NQ.nq.olen_of(xs) : {B.Octets.drop(_, B.Octets.append(ox, oy)) == oy : B.Octets}
  BL.octets_drop_append(ox, oy)

def pr.ozeros(+k: Nat) -> {B.Octets.of_list(B.zeros(k)) == B.Octets.zeros(k) : B.Octets}:
  %BL.octets_zeros_list(k) : {B.Octets.of_list(_) == B.Octets.zeros(k) : B.Octets}
  BL.octets_of_to(B.Octets.zeros(k))

# an attribute's bytes split as header and payload, then padding
def pr.enc_split(+o: H.NlOrder, +t: Nat, +nd: Bool, +nb: Bool, +ps: List<&2, U32>) -> {H.nla.u16_bytes(o, Nat.add(4n, List.length(&2, U32, ps)), H.nla.type_bytes(o, t, nd, nb, List.append(&2, U32, ps, List.append(&2, U32, B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, ps)))), Nil{})))) == List.append(&2, U32, List.append(&2, U32, H.nla.u16_bytes(o, Nat.add(4n, List.length(&2, U32, ps)), H.nla.type_bytes(o, t, nd, nb, Nil{})), ps), B.zeros(H.nla.pad(Nat.add(4n, List.length(&2, U32, ps))))) : List<&2, U32>}:
  +n = Nat.add(4n, List.length(&2, U32, ps))
  +z = B.zeros(H.nla.pad(n))
  +hd = H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, Nil{}))
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd, ps), z), List.append(&2, U32, hd, List.append(&2, U32, ps, z)), pr.app_assoc(hd, ps, z)) : {H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, List.append(&2, U32, ps, List.append(&2, U32, z, Nil{})))) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, z, Nil{}), z, pr.app_nil(z)) : {H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, List.append(&2, U32, ps, _))) == List.append(&2, U32, hd, List.append(&2, U32, ps, z)) : List<&2, U32>}
  pr.hdr(o, n, t, nd, nb, List.append(&2, U32, ps, z))

def pr.xlen(+o: H.NlOrder, +t: Nat, +nd: Bool, +nb: Bool, +ps: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, H.nla.u16_bytes(o, Nat.add(4n, List.length(&2, U32, ps)), H.nla.type_bytes(o, t, nd, nb, Nil{})), ps)) == Nat.add(4n, List.length(&2, U32, ps)) : Nat}:
  +n = Nat.add(4n, List.length(&2, U32, ps))
  +hd = H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, Nil{}))
  Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, hd, ps)), Nat.add(List.length(&2, U32, hd), List.length(&2, U32, ps)), n, NQ.nq.app_len(hd, ps), Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, U32, ps)), List.length(&2, U32, hd), 4n, pr.hdr_len(o, n, t, nd, nb)))

def pr.pz(m: Maybe<&2, N.NlError>, +o: H.NlOrder, +t: Nat, +nd: Bool, +nb: Bool, +pay: B.Octets, -b: B.Octets, +e: {N.nla.build.go(m, o, [N.NlAttr{t, nd, nb, pay}]) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}) -> {B.Octets.drop(N.nla.len_of(N.NlAttr{t, nd, nb, pay}), b) == B.Octets.zeros(H.nla.pad(N.nla.len_of(N.NlAttr{t, nd, nb, pay}))) : B.Octets}:
  match m:
    case None{}:
      +ps = B.Octets.to_list(pay)
      +n = Nat.add(4n, List.length(&2, U32, ps))
      +k = H.nla.pad(n)
      +hd = H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, Nil{}))
      +x = List.append(&2, U32, hd, ps)
      +ee = N.nla.enc_all(o, [N.NlAttr{t, nd, nb, pay}])
      %Equal.cong(Result<&2, &2, N.NlError, B.Octets>, B.Octets, z => pr.od(z), Done{B.Octets.of_list(ee)}, Done{b}, e) : {B.Octets.drop(N.nla.len_of(N.NlAttr{t, nd, nb, pay}), _) == B.Octets.zeros(H.nla.pad(N.nla.len_of(N.NlAttr{t, nd, nb, pay}))) : B.Octets}
      %Equal.sym(Nat, Nat.add(4n, B.Octets.len(pay)), n, Equal.cong(Nat, Nat, y => Nat.add(4n, y), B.Octets.len(pay), List.length(&2, U32, ps), NQ.nq.olen(pay))) : {B.Octets.drop(_, B.Octets.of_list(ee)) == B.Octets.zeros(H.nla.pad(_)) : B.Octets}
      %Equal.sym(List<&2, U32>, ee, List.append(&2, U32, x, B.zeros(k)), pr.enc_split(o, t, nd, nb, ps)) : {B.Octets.drop(n, B.Octets.of_list(_)) == B.Octets.zeros(k) : B.Octets}
      %pr.xlen(o, t, nd, nb, ps) : {B.Octets.drop(_, B.Octets.of_list(List.append(&2, U32, x, B.zeros(k)))) == B.Octets.zeros(k) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.drop(List.length(&2, U32, x), B.Octets.of_list(List.append(&2, U32, x, B.zeros(k)))), B.Octets.of_list(B.zeros(k)), pr.odrop(x, B.zeros(k))) : {_ == B.Octets.zeros(k) : B.Octets}
      pr.ozeros(k)
    case Some{er}:
      Empty.absurd({B.Octets.drop(N.nla.len_of(N.NlAttr{t, nd, nb, pay}), b) == B.Octets.zeros(H.nla.pad(N.nla.len_of(N.NlAttr{t, nd, nb, pay}))) : B.Octets}, pr.ofd(er, b, e))

def pr.pl(m: Maybe<&2, N.NlError>, +o: H.NlOrder, +t: Nat, +nd: Bool, +nb: Bool, +pay: B.Octets, -b: B.Octets, +e: {N.nla.build.go(m, o, [N.NlAttr{t, nd, nb, pay}]) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}) -> {B.Octets.len(b) == H.nla.align(N.nla.len_of(N.NlAttr{t, nd, nb, pay})) : Nat}:
  match m:
    case None{}:
      +ps = B.Octets.to_list(pay)
      +n = Nat.add(4n, List.length(&2, U32, ps))
      +k = H.nla.pad(n)
      +hd = H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, Nil{}))
      +x = List.append(&2, U32, hd, ps)
      +ee = N.nla.enc_all(o, [N.NlAttr{t, nd, nb, pay}])
      +y = List.append(&2, U32, x, B.zeros(k))
      %Equal.cong(Result<&2, &2, N.NlError, B.Octets>, B.Octets, z => pr.od(z), Done{B.Octets.of_list(ee)}, Done{b}, e) : {B.Octets.len(_) == H.nla.align(N.nla.len_of(N.NlAttr{t, nd, nb, pay})) : Nat}
      %Equal.sym(Nat, Nat.add(4n, B.Octets.len(pay)), n, Equal.cong(Nat, Nat, w => Nat.add(4n, w), B.Octets.len(pay), List.length(&2, U32, ps), NQ.nq.olen(pay))) : {B.Octets.len(B.Octets.of_list(ee)) == H.nla.align(_) : Nat}
      %Equal.sym(List<&2, U32>, ee, y, pr.enc_split(o, t, nd, nb, ps)) : {B.Octets.len(B.Octets.of_list(_)) == H.nla.align(n) : Nat}
      %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(y)), List.length(&2, U32, y), NQ.nq.olen_of(y)) : {_ == H.nla.align(n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, y), Nat.add(List.length(&2, U32, x), List.length(&2, U32, B.zeros(k))), NQ.nq.app_len(x, B.zeros(k))) : {_ == H.nla.align(n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, x), n, pr.xlen(o, t, nd, nb, ps)) : {Nat.add(_, List.length(&2, U32, B.zeros(k))) == H.nla.align(n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, B.zeros(k)), k, NQ.nq.zeros_len(k)) : {Nat.add(n, _) == H.nla.align(n) : Nat}
      {==}
    case Some{er}:
      Empty.absurd({B.Octets.len(b) == H.nla.align(N.nla.len_of(N.NlAttr{t, nd, nb, pay})) : Nat}, pr.ofd(er, b, e))

def pr.pz0(a: N.NlAttr, +o: H.NlOrder, -b: B.Octets, +e: {N.nla.put(o, a) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}) -> {B.Octets.drop(N.nla.len_of(a), b) == B.Octets.zeros(H.nla.pad(N.nla.len_of(a))) : B.Octets}:
  match a:
    case N.NlAttr{+t, +nd, +nb, +pay}:
      pr.pz(N.nla.first_err([N.NlAttr{t, nd, nb, pay}]), o, t, nd, nb, pay, b, e)

def pr.pl0(a: N.NlAttr, +o: H.NlOrder, -b: B.Octets, +e: {N.nla.put(o, a) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}) -> {B.Octets.len(b) == H.nla.align(N.nla.len_of(a)) : Nat}:
  match a:
    case N.NlAttr{+t, +nd, +nb, +pay}:
      pr.pl(N.nla.first_err([N.NlAttr{t, nd, nb, pay}]), o, t, nd, nb, pay, b, e)

def Laws.pad_zero(o, a, b, e):
  pr.pz0(a, o, b, e)

def Laws.put_len(o, a, b, e):
  pr.pl0(a, o, b, e)

# A successful parse reads nothing past the buffer

def pr.rdisc(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def pr.rfd(-x: N.NlError, -y: List<&2, N.NlAttr>, e: {Fail{x} == Done{y} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> Empty:
  %Equal.sym(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, Fail{x}, Done{y}, e) : pr.rdisc(_)
  Unit{}

def pr.rd(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>) -> List<&2, N.NlAttr>:
  match r:
    case Fail{x}:
      Nil{}
    case Done{y}:
      y

# a parsed attribute's length is its header and the bytes it was given
def pr.la2(r: Nat & Bool, nd: Bool, +lo: Nat, -xs: List<&2, U32>) -> {N.nla.len_of(N.nla.parse.attr2(r, nd, lo, xs)) == Nat.add(4n, B.Octets.len(B.Octets.of_list(xs))) : Nat}:
  match r:
    case (h, nb):
      {==}

def pr.la1(r: Nat & Bool, +lo: Nat, -xs: List<&2, U32>) -> {N.nla.len_of(N.nla.parse.attr1(r, lo, xs)) == Nat.add(4n, B.Octets.len(B.Octets.of_list(xs))) : Nat}:
  match r:
    case (+h, nd):
      pr.la2(H.nla.has(h, 64n), nd, lo, xs)

def pr.lao(o: H.NlOrder, +a: U32, +b: U32, -xs: List<&2, U32>) -> {N.nla.len_of(N.nla.parse.attr_o(o, a, b, xs)) == Nat.add(4n, B.Octets.len(B.Octets.of_list(xs))) : Nat}:
  match o:
    case H.NlLittle{}:
      pr.la1(H.nla.has(U32.to_nat(b), 128n), U32.to_nat(a), xs)
    case H.NlBig{}:
      pr.la1(H.nla.has(U32.to_nat(a), 128n), U32.to_nat(b), xs)

def pr.nil_sw(-as: List<&2, N.NlAttr>, +k: Nat, +e: {Done{Nil{}} == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {Nat.is_le(N.nla.span(as), k) == True{} : Bool}:
  %Equal.cong(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, List<&2, N.NlAttr>, z => pr.rd(z), Done{Nil{}}, Done{as}, e) : {Nat.is_le(N.nla.span(_), k) == True{} : Bool}
  NN.nn.le_zero(k)

def pr.short_sw(p: N.NlOpts, -as: List<&2, N.NlAttr>, +k: Nat, +e: {N.nla.parse.short(N.nla.opts.strict(p)) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {Nat.is_le(N.nla.span(as), k) == True{} : Bool}:
  match p:
    case N.NlOpts{o, s}:
      match s:
        case True{}:
          Empty.absurd({Nat.is_le(N.nla.span(as), k) == True{} : Bool}, pr.rfd(N.NlTrailing{}, as, e))
        case False{}:
          pr.nil_sw(as, k, e)

# one attribute read: its header, its payload and padding, then the rest
def pr.swc(ok: Bool, +o: H.NlOrder, +b2: U32, +b3: U32, +n: Nat, +rest: List<&2, U32>, r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, -as: List<&2, N.NlAttr>, +hok: {Bool.and(Nat.is_le(4n, n), Nat.is_le(Nat.sub(n, 4n), List.length(&2, U32, rest))) == ok : Bool}, ih: @as2:List<&2, N.NlAttr> -> {r == Done{as2} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>} -> {Nat.is_le(N.nla.span(as2), List.length(&2, U32, N.nla.parse.rest(n, rest))) == True{} : Bool}, +e: {N.nla.parse.check(ok, o, b2, b3, n, rest, r) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {Nat.is_le(N.nla.span(as), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Nat.is_le(N.nla.span(as), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}, pr.rfd(N.NlBadLength{}, as, e))
    case True{}:
      match r:
        case Fail{x}:
          Empty.absurd({Nat.is_le(N.nla.span(as), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}, pr.rfd(x, as, e))
        case Done{+ys}:
          +k = Nat.sub(n, 4n)
          +xs = List.take(&2, U32, rest, k)
          +a : N.NlAttr = N.nla.parse.attr_o(o, b2, b3, xs)
          +d = List.drop(&2, U32, rest, k)
          +h2 = NN.nn.and_r(Nat.is_le(4n, n), Nat.is_le(k, List.length(&2, U32, rest)), hok)
          +sy = N.nla.span(ys)
          +ld = List.length(&2, U32, d)
          +hs = NN.nn.le_trans(sy, List.length(&2, U32, List.drop(&2, U32, d, H.nla.pad(n))), ld, ih(ys, {==}), NQ.nq.drop_le(d, H.nla.pad(n)))
          %Equal.cong(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, List<&2, N.NlAttr>, z => pr.rd(z), Done{Con{a, ys}}, Done{as}, e) : {Nat.is_le(N.nla.span(_), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}
          %Equal.sym(Nat, N.nla.len_of(a), Nat.add(4n, B.Octets.len(B.Octets.of_list(xs))), pr.lao(o, b2, b3, xs)) : {Nat.is_le(Nat.add(_, sy), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}
          %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(xs)), List.length(&2, U32, xs), NQ.nq.olen_of(xs)) : {Nat.is_le(Nat.add(Nat.add(4n, _), sy), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}
          %Equal.sym(Nat, List.length(&2, U32, xs), k, NQ.nq.len_take(rest, k, h2)) : {Nat.is_le(Nat.add(Nat.add(4n, _), sy), Nat.add(4n, List.length(&2, U32, rest))) == True{} : Bool}
          %NQ.nq.len_drop(rest, k, h2) : {Nat.is_le(Nat.add(Nat.add(4n, k), sy), Nat.add(4n, _)) == True{} : Bool}
          Equal.trans(Bool, Nat.is_le(Nat.add(4n, Nat.add(k, sy)), Nat.add(4n, Nat.add(k, ld))), Nat.is_le(Nat.add(k, sy), Nat.add(k, ld)), True{}, NN.nn.cancel_le(4n, Nat.add(k, sy), Nat.add(k, ld)), Equal.trans(Bool, Nat.is_le(Nat.add(k, sy), Nat.add(k, ld)), Nat.is_le(sy, ld), True{}, NN.nn.cancel_le(k, sy, ld), hs))

def pr.sw(fu: Nat, +p: N.NlOpts, xs: List<&2, U32>, -as: List<&2, N.NlAttr>, +e: {N.nla.parse.go(fu, p, xs) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {Nat.is_le(N.nla.span(as), List.length(&2, U32, xs)) == True{} : Bool}:
  match fu xs:
    case 0n Nil{}:
      pr.nil_sw(as, 0n, e)
    case 1n+f Nil{}:
      pr.nil_sw(as, 0n, e)
    case 0n Con{+x, +t}:
      pr.short_sw(p, as, List.length(&2, U32, Con{x, t}), e)
    case 1n+ +f Con{+b0, Con{+b1, Con{+b2, Con{+b3, +rest}}}}:
      +o = N.nla.opts.order(p)
      +n = H.nla.u16_value(o, b0, b1)
      pr.swc(Bool.and(Nat.is_le(4n, n), Nat.is_le(Nat.sub(n, 4n), List.length(&2, U32, rest))), o, b2, b3, n, rest, N.nla.parse.go(f, p, N.nla.parse.rest(n, rest)), as, {==}, as2 => e2 => pr.sw(f, p, N.nla.parse.rest(n, rest), as2, e2), e)
    case 1n+f Con{x, Nil{}}:
      pr.short_sw(p, as, 1n, e)
    case 1n+f Con{x, Con{y, Nil{}}}:
      pr.short_sw(p, as, 2n, e)
    case 1n+f Con{x, Con{y, Con{z, Nil{}}}}:
      pr.short_sw(p, as, 3n, e)

def pr.within(+p: N.NlOpts, +buf: B.Octets, -as: List<&2, N.NlAttr>, +e: {N.nla.parse(p, buf) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {Nat.is_le(N.nla.span(as), B.Octets.len(buf)) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(buf), List.length(&2, U32, B.Octets.to_list(buf)), NQ.nq.olen(buf)) : {Nat.is_le(N.nla.span(as), _) == True{} : Bool}
  pr.sw(List.length(&2, U32, B.Octets.to_list(buf)), p, B.Octets.to_list(buf), as, e)

def Laws.parse_within(p, buf, as, e):
  pr.within(p, buf, as, e)

# A parse with a policy answers what the plain parse answers

def pr.mapc(v: Result<&2, &2, N.NlError, Unit>, -ys: List<&2, N.NlAttr>, -as: List<&2, N.NlAttr>, +e: {Result.map(&2, &2, N.NlError, Unit, List<&2, N.NlAttr>, u2 => ys, v) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {ys == as : List<&2, N.NlAttr>}:
  match v:
    case Fail{x}:
      Empty.absurd({ys == as : List<&2, N.NlAttr>}, pr.rfd(x, as, e))
    case Done{u}:
      Equal.cong(Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, List<&2, N.NlAttr>, z => pr.rd(z), Done{ys}, Done{as}, e)

def pr.pp(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, +c: P.NlCheck, +set: List<&2, P.NlPolicy>, +pol: Nat, +fuel: Nat, -as: List<&2, N.NlAttr>, +e: {P.nla.parse_policy.go(r, c, set, pol, fuel) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}) -> {r == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}, pr.rfd(x, as, e))
    case Done{+ys}:
      %pr.mapc(P.nla.validate(c, set, pol, fuel, ys), ys, as, e) : {Done{ys} == Done{_} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
      {==}

def Laws.parse_policy_parse(c, set, pol, buf, as, e):
  pr.pp(N.nla.parse(P.nla.check.parse(c), buf), c, set, pol, Nat.add(Nat.mul(2n, B.Octets.len(buf)), 2n), as, e)

def Laws.parse_policy_within(c, set, pol, buf, as, e):
  pr.within(P.nla.check.parse(c), buf, as, pr.pp(N.nla.parse(P.nla.check.parse(c), buf), c, set, pol, Nat.add(Nat.mul(2n, B.Octets.len(buf)), 2n), as, e))

# Vectors

def Laws.vec_u32():
  {==}

def Laws.vec_string():
  {==}

def Laws.vec_flags():
  {==}

def Laws.vec_parse():
  {==}

def Laws.vec_errors():
  {==}
