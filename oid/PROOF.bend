# Proofs of bend-osdev-oid's laws. The lemmas are in proof_der.bend (the
# DER form, on bend-osdev-asn1's laws), proof_text.bend (the dotted text)
# and proof_nat.bend.
import Base
import ../bytes/bytes.bend as B
import ./oid.bend as O
import ./text.bend as T
import ./proof_der.bend as OD
import ./LAWS.bend as Laws

def Laws.der_round_trip(o, b, e):
  OD.od.der_rt(o, b, e)

def Laws.der_canonical(b, o, e):
  OD.od.can(b, o, e)

def Laws.text_round_trip(r, o, hv):
  OD.od.text_rt(r, o, hv)

def Laws.valid_of_der(b, o, e):
  OD.od.valid_der(b, o, e)

def Laws.valid_of_text(r, s, o, e):
  OD.od.valid_text(r, s, o, e)

def Laws.der_text_der(r, b, o, e):
  OD.od.der_text_der(r, b, o, e)

def Laws.text_der_text(r, s, o, e):
  OD.od.text_der_text(r, s, o, e)

def Laws.vec_cn_der():
  {==}

def Laws.vec_cn_text():
  {==}

def Laws.vec_bc_text():
  {==}

def Laws.vec_bad_text():
  {==}
