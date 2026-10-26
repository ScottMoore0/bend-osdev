# The whole round trips, for every input: a table AcpiSdt.build writes is
# read back by AcpiSdt.parse, its checks passing (Length from 36 to the
# bytes given, the bytes summing to zero modulo 256: LAWS_checksum.bend),
# and so is each table whose body LAWS_tables.bend reads back, through its
# parse: the HPET, BGRT, XSDT, RSDT, MCFG and a DSDT or SSDT.
#
# The header read back is the header given with the fields build computes:
# the signature build writes, the Length (the table's length) and the
# Checksum (the byte at offset 9 of the table). The text fields must have
# their sizes and the revision must be a byte, and the table's length must
# fit the 32-bit Length field (no more than a U32's value; the HPET and the
# BGRT are 56 bytes long, so their laws need no such hypothesis).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./gas.bend as G
import ./hpet.bend as Hp
import ./bgrt.bend as Bg
import ./rsdt.bend as R
import ./mcfg.bend as Mc
import ./dsdt.bend as Ds
import ./LAWS_tables.bend as TL

# the header h with the signature sig and the fields build computes for the
# table o: Length the length of o, Checksum the byte at offset 9 of o
def acpilaw.written(sig: B.Octets, h: H.AcpiHeader, +o: B.Octets) -> H.AcpiHeader:
  match h:
    case H.AcpiHeader{s, l, r, c, oi, t, orv, ci, cr}:
      H.AcpiHeader{sig, U32.from_nat(B.Octets.len(o)), r, Maybe.default(&2, U32, B.Octets.at(o, 9n), 0), oi, t, orv, ci, cr}

# Any table: its header and body back
law sdt_round_trip:
  for +h: H.AcpiHeader
  for +sig4: {B.Octets.len(H.AcpiHeader.signature(h)) == 4n : Nat}
  for +oem6: {B.Octets.len(H.AcpiHeader.oem_id(h)) == 6n : Nat}
  for +tid8: {B.Octets.len(H.AcpiHeader.oem_table_id(h)) == 8n : Nat}
  for +cid4: {B.Octets.len(H.AcpiHeader.creator_id(h)) == 4n : Nat}
  for +rev8: {B.byte(H.AcpiHeader.revision(h)) == H.AcpiHeader.revision(h) : U32}
  for +body: B.Octets
  for +z: U32
  for +fit: {Nat.is_le(B.Octets.len(H.AcpiSdt.build(h, body)), U32.to_nat(z)) == True{} : Bool}
  {H.AcpiSdt.parse(H.AcpiSdt.build(h, body)) == Done{H.AcpiSdt{acpilaw.written(H.AcpiHeader.signature(h), h, H.AcpiSdt.build(h, body)), body}} : Result<&2, &2, E.AcpiError, H.AcpiSdt>}

# The HPET table
law hpet_whole:
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +rev8b: {B.byte(H.AcpiHeader.revision(h0)) == H.AcpiHeader.revision(h0) : U32}
  for +id: U32
  for +gs: U32
  for +gw: U32
  for +go: U32
  for +ga: U32
  for +gaddr: W.W64
  for +n: U32
  for +m: U32
  for +p: U32
  for +gs8: {B.byte(gs) == gs : U32}
  for +gw8: {B.byte(gw) == gw : U32}
  for +go8: {B.byte(go) == go : U32}
  for +ga8: {B.byte(ga) == ga : U32}
  for +n8: {B.byte(n) == n : U32}
  for +m16: {B.low16(m) == m : U32}
  for +p8: {B.byte(p) == p : U32}
  {Hp.AcpiHpet.parse(Hp.AcpiHpet.build(Hp.AcpiHpet{h0, id, G.AcpiGas{gs, gw, go, ga, gaddr}, n, m, p})) == Done{Hp.AcpiHpet{acpilaw.written(B.Octets.of_string("HPET"), h0, Hp.AcpiHpet.build(Hp.AcpiHpet{h0, id, G.AcpiGas{gs, gw, go, ga, gaddr}, n, m, p})), id, G.AcpiGas{gs, gw, go, ga, gaddr}, n, m, p}} : Result<&2, &2, E.AcpiError, Hp.AcpiHpet>}

# The BGRT table
law bgrt_whole:
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +rev8b: {B.byte(H.AcpiHeader.revision(h0)) == H.AcpiHeader.revision(h0) : U32}
  for +v: U32
  for +st: U32
  for +it: U32
  for +a: W.W64
  for +x: U32
  for +y: U32
  for +v16: {B.low16(v) == v : U32}
  for +st8: {B.byte(st) == st : U32}
  for +it8: {B.byte(it) == it : U32}
  {Bg.AcpiBgrt.parse(Bg.AcpiBgrt.build(Bg.AcpiBgrt{h0, v, st, it, a, x, y})) == Done{Bg.AcpiBgrt{acpilaw.written(B.Octets.of_string("BGRT"), h0, Bg.AcpiBgrt.build(Bg.AcpiBgrt{h0, v, st, it, a, x, y})), v, st, it, a, x, y}} : Result<&2, &2, E.AcpiError, Bg.AcpiBgrt>}

# The XSDT
law xsdt_whole:
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +rev8b: {B.byte(H.AcpiHeader.revision(h0)) == H.AcpiHeader.revision(h0) : U32}
  for +xs: List<&2, W.W64>
  for +z: U32
  for +fit: {Nat.is_le(B.Octets.len(R.AcpiXsdt.build(h0, xs)), U32.to_nat(z)) == True{} : Bool}
  {R.AcpiXsdt.parse(R.AcpiXsdt.build(h0, xs)) == Done{R.AcpiSdtList{acpilaw.written(B.Octets.of_string("XSDT"), h0, R.AcpiXsdt.build(h0, xs)), xs}} : Result<&2, &2, E.AcpiError, R.AcpiSdtList>}

# The RSDT: each address's low 32 bits
law rsdt_whole:
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +rev8b: {B.byte(H.AcpiHeader.revision(h0)) == H.AcpiHeader.revision(h0) : U32}
  for +xs: List<&2, W.W64>
  for +z: U32
  for +fit: {Nat.is_le(B.Octets.len(R.AcpiRsdt.build(h0, xs)), U32.to_nat(z)) == True{} : Bool}
  {R.AcpiRsdt.parse(R.AcpiRsdt.build(h0, xs)) == Done{R.AcpiSdtList{acpilaw.written(B.Octets.of_string("RSDT"), h0, R.AcpiRsdt.build(h0, xs)), TL.acpilaw.low32(xs)}} : Result<&2, &2, E.AcpiError, R.AcpiSdtList>}

# The MCFG: its allocation structures as stored
law mcfg_whole:
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +rev8b: {B.byte(H.AcpiHeader.revision(h0)) == H.AcpiHeader.revision(h0) : U32}
  for +es: List<&2, Mc.AcpiMcfgEntry>
  for +z: U32
  for +fit: {Nat.is_le(B.Octets.len(Mc.AcpiMcfg.build(Mc.AcpiMcfg{h0, es})), U32.to_nat(z)) == True{} : Bool}
  {Mc.AcpiMcfg.parse(Mc.AcpiMcfg.build(Mc.AcpiMcfg{h0, es})) == Done{Mc.AcpiMcfg{acpilaw.written(B.Octets.of_string("MCFG"), h0, Mc.AcpiMcfg.build(Mc.AcpiMcfg{h0, es})), TL.acpilaw.mcfg_fit(es)}} : Result<&2, &2, E.AcpiError, Mc.AcpiMcfg>}

# A DSDT or SSDT (AcpiAml.parse, which takes either signature)
law aml_whole:
  for +h0: H.AcpiHeader
  for +sig4b: {B.Octets.len(H.AcpiHeader.signature(h0)) == 4n : Nat}
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +rev8b: {B.byte(H.AcpiHeader.revision(h0)) == H.AcpiHeader.revision(h0) : U32}
  for +a: B.Octets
  for +z: U32
  for +fit: {Nat.is_le(B.Octets.len(Ds.AcpiAml.build(Ds.AcpiAml{h0, a})), U32.to_nat(z)) == True{} : Bool}
  {Ds.AcpiAml.parse(Ds.AcpiAml.build(Ds.AcpiAml{h0, a})) == Done{Ds.AcpiAml{acpilaw.written(H.AcpiHeader.signature(h0), h0, Ds.AcpiAml.build(Ds.AcpiAml{h0, a})), a}} : Result<&2, &2, E.AcpiError, Ds.AcpiAml>}

# the hypotheses hold at an example: a header AcpiHeader.make fits, and a
# 39-byte table
law whole_example:
  {(B.Octets.len(H.AcpiHeader.signature(H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.of_string("BEND"), B.Octets.of_string("TABLE")))), B.Octets.len(H.AcpiHeader.oem_id(H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.of_string("BEND"), B.Octets.of_string("TABLE")))), B.Octets.len(H.AcpiHeader.oem_table_id(H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.of_string("BEND"), B.Octets.of_string("TABLE")))), B.Octets.len(H.AcpiHeader.creator_id(H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.of_string("BEND"), B.Octets.of_string("TABLE")))), B.byte(H.AcpiHeader.revision(H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.of_string("BEND"), B.Octets.of_string("TABLE")))), Nat.is_le(B.Octets.len(H.AcpiSdt.build(H.AcpiHeader.make(B.Octets.of_string("SSDT"), 2, B.Octets.of_string("BEND"), B.Octets.of_string("TABLE")), B.Octets.of_list([1, 2, 3]))), U32.to_nat(39))) == (4n, 6n, 8n, 4n, 2, True{}) : Nat & Nat & Nat & Nat & U32 & Bool}
