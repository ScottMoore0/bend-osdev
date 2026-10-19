# Proofs of bend-osdev-asn1's laws. The lemmas are in the proof_*.bend
# files: proof_enc.bend (decoding what the encoder wrote), proof_head.bend
# (headers), proof_num.bend (numbers in octets), proof_byte.bend (generated:
# single octets), proof_u32.bend, proof_list.bend and proof_nat.bend.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./asn1.bend as A
import ./proof_enc.bend as PE
import ./proof_within.bend as PW
import ./proof_canon.bend as PC
import ./proof_oid.bend as PO
import ./oidval.bend as O
import ./LAWS.bend as Laws

def Laws.decode_encode(r, n, b, e, hc):
  PE.pe.de(En.a1.enc_err([n]), r, n, b, {==}, e, hc)

def Laws.encode_decode(r, hm, hi, ht, b, n, e):
  PC.pc.ed(r, hm, hi, ht, b, n, e)

def Laws.der_unique(b, n, e):
  PC.pc.ed(R.Asn1Rules.der(), {==}, {==}, {==}, b, n, e)

def Laws.decode_within(r, b, n, e):
  +xs = B.Octets.to_list(b)
  %PW.pw.blen(b) : {Nat.is_le(N.Asn1.span(n), _) == True{} : Bool}
  PW.pw.top_inv(r, A.a1.run(r, A.A1One{}, xs), n, List.length(&2, U32, xs), PW.pw.run(r, A.A1One{}, xs), e)

def Laws.prefix_within(r, b, n, rest, e):
  +xs = B.Octets.to_list(b)
  %PW.pw.blen(b) : {Nat.is_le(Nat.add(N.Asn1.span(n), B.Octets.len(rest)), _) == True{} : Bool}
  PW.pw.read_inv(A.a1.run(r, A.A1One{}, xs), n, rest, List.length(&2, U32, xs), PW.pw.run(r, A.A1One{}, xs), e)

def Laws.all_within(r, b, ns, e):
  +xs = B.Octets.to_list(b)
  %PW.pw.blen(b) : {Nat.is_le(N.Asn1.spans(ns), _) == True{} : Bool}
  PW.pw.all_inv(A.a1.run(r, A.A1All{}, xs), ns, List.length(&2, U32, xs), PW.pw.run(r, A.A1All{}, xs), e)

def Laws.oid_round_trip(arcs, o, e):
  PO.po.rt(O.Asn1.oid_valid(arcs), arcs, o, {==}, e)

def Laws.oid_canonical(o, arcs, e):
  PO.po.canonical(o, arcs, e)

def Laws.vec_sequence():
  {==}

def Laws.vec_tagging():
  {==}

def Laws.vec_oid():
  {==}

def Laws.vec_length():
  {==}

def Laws.vec_indefinite():
  {==}
