# The structures inside the tables, for every input: each reads back as it
# is written.
#
#   - a Generic Address Structure at any offset of any bytes (5.2.3.2);
#   - the body that AcpiHpet.build and AcpiBgrt.build write (everything
#     after the 36-byte header) is read back by of_sdt, whatever header it
#     is read with, when the text fields of the headers have their sizes,
#     byte fields are bytes and 16-bit fields fit 16 bits;
#   - the same for the XSDT's entries, the RSDT's (each address's low 32
#     bits, which is what an RSDT entry holds), the MCFG's structures (each
#     segment's low 16 bits and each bus number's low 8 bits), and a DSDT's
#     or SSDT's definition block;
#   - a FACS reads back through AcpiFacs.parse (it has no header and no
#     checksum), its Length being the 64 that build writes.
#
# A table's whole round trip, parse(build(t)), also needs build's checksum
# byte to make the bytes sum to zero modulo 256, for every content: that is
# LAWS_checksum.bend, and the whole round trips are LAWS_whole.bend.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./gas.bend as G
import ./hpet.bend as Hp
import ./bgrt.bend as Bg
import ./facs.bend as Fa
import ./rsdt.bend as R
import ./mcfg.bend as Mc
import ./dsdt.bend as Ds

# A Generic Address Structure, at offset len(a) of a ++ encode(g) ++ b
law gas_round_trip:
  for +a: B.Octets
  for +s: U32
  for +w: U32
  for +off: U32
  for +acc: U32
  for +addr: W.W64
  for +b: B.Octets
  for +s8: {B.byte(s) == s : U32}
  for +w8: {B.byte(w) == w : U32}
  for +off8: {B.byte(off) == off : U32}
  for +acc8: {B.byte(acc) == acc : U32}
  {G.AcpiGas.at(B.Octets.append(a, B.Octets.append(G.AcpiGas.encode(G.AcpiGas{s, w, off, acc, addr}), b)), B.Octets.len(a)) == G.AcpiGas{s, w, off, acc, addr} : G.AcpiGas}

# The HPET table's body, read back with any header h
law hpet_round_trip:
  for +h: H.AcpiHeader
  for +sig4: {B.Octets.len(H.AcpiHeader.signature(h)) == 4n : Nat}
  for +oem6: {B.Octets.len(H.AcpiHeader.oem_id(h)) == 6n : Nat}
  for +tid8: {B.Octets.len(H.AcpiHeader.oem_table_id(h)) == 8n : Nat}
  for +cid4: {B.Octets.len(H.AcpiHeader.creator_id(h)) == 4n : Nat}
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
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
  {Hp.AcpiHpet.of_sdt(H.AcpiSdt{h, B.Octets.drop(36n, Hp.AcpiHpet.build(Hp.AcpiHpet{h0, id, G.AcpiGas{gs, gw, go, ga, gaddr}, n, m, p}))}) == Done{Hp.AcpiHpet{h, id, G.AcpiGas{gs, gw, go, ga, gaddr}, n, m, p}} : Result<&2, &2, E.AcpiError, Hp.AcpiHpet>}

# The BGRT table's body, read back with any header h
law bgrt_round_trip:
  for +h: H.AcpiHeader
  for +sig4: {B.Octets.len(H.AcpiHeader.signature(h)) == 4n : Nat}
  for +oem6: {B.Octets.len(H.AcpiHeader.oem_id(h)) == 6n : Nat}
  for +tid8: {B.Octets.len(H.AcpiHeader.oem_table_id(h)) == 8n : Nat}
  for +cid4: {B.Octets.len(H.AcpiHeader.creator_id(h)) == 4n : Nat}
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +v: U32
  for +st: U32
  for +it: U32
  for +a: W.W64
  for +x: U32
  for +y: U32
  for +v16: {B.low16(v) == v : U32}
  for +st8: {B.byte(st) == st : U32}
  for +it8: {B.byte(it) == it : U32}
  {Bg.AcpiBgrt.of_sdt(H.AcpiSdt{h, B.Octets.drop(36n, Bg.AcpiBgrt.build(Bg.AcpiBgrt{h0, v, st, it, a, x, y}))}) == Done{Bg.AcpiBgrt{h, v, st, it, a, x, y}} : Result<&2, &2, E.AcpiError, Bg.AcpiBgrt>}

# The FACS: parsed back as built, with the Length 64 that build writes
law facs_round_trip:
  for +l: U32
  for +hs: U32
  for +wv: U32
  for +gl: U32
  for +fl: U32
  for +xw: W.W64
  for +v: U32
  for +of: U32
  for +v8: {B.byte(v) == v : U32}
  {Fa.AcpiFacs.parse(Fa.AcpiFacs.build(Fa.AcpiFacs{l, hs, wv, gl, fl, xw, v, of})) == Done{Fa.AcpiFacs{64, hs, wv, gl, fl, xw, v, of}} : Result<&2, &2, E.AcpiError, Fa.AcpiFacs>}

# the low 32 bits of each address, as a W64 (what an RSDT entry holds)
def acpilaw.low32(xs: List<&2, W.W64>) -> List<&2, W.W64>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{W.W64.from_u32(W.W64.lo(x)), acpilaw.low32(t)}

# each MCFG structure as it is stored: the segment group's low 16 bits, the
# bus numbers' low 8 bits
def acpilaw.mcfg_fit(es: List<&2, Mc.AcpiMcfgEntry>) -> List<&2, Mc.AcpiMcfgEntry>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      match e:
        case Mc.AcpiMcfgEntry{b, s, lo, hi}:
          Con{Mc.AcpiMcfgEntry{b, B.low16(s), B.byte(lo), B.byte(hi)}, acpilaw.mcfg_fit(t)}

# The XSDT's entries, read back with any header h
law xsdt_round_trip:
  for +h: H.AcpiHeader
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +xs: List<&2, W.W64>
  {R.AcpiXsdt.of_sdt(H.AcpiSdt{h, B.Octets.drop(36n, R.AcpiXsdt.build(h0, xs))}) == Done{R.AcpiSdtList{h, xs}} : Result<&2, &2, E.AcpiError, R.AcpiSdtList>}

# The RSDT's entries: each address's low 32 bits
law rsdt_round_trip:
  for +h: H.AcpiHeader
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +xs: List<&2, W.W64>
  {R.AcpiRsdt.of_sdt(H.AcpiSdt{h, B.Octets.drop(36n, R.AcpiRsdt.build(h0, xs))}) == Done{R.AcpiSdtList{h, acpilaw.low32(xs)}} : Result<&2, &2, E.AcpiError, R.AcpiSdtList>}

# The MCFG's allocation structures, as stored
law mcfg_round_trip:
  for +h: H.AcpiHeader
  for +h0: H.AcpiHeader
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +es: List<&2, Mc.AcpiMcfgEntry>
  {Mc.AcpiMcfg.of_sdt(H.AcpiSdt{h, B.Octets.drop(36n, Mc.AcpiMcfg.build(Mc.AcpiMcfg{h0, es}))}) == Done{Mc.AcpiMcfg{h, acpilaw.mcfg_fit(es)}} : Result<&2, &2, E.AcpiError, Mc.AcpiMcfg>}

# A DSDT's or SSDT's definition block (the header's signature is kept, so
# it too must have its size)
law aml_round_trip:
  for +h: H.AcpiHeader
  for +h0: H.AcpiHeader
  for +sig4b: {B.Octets.len(H.AcpiHeader.signature(h0)) == 4n : Nat}
  for +oem6b: {B.Octets.len(H.AcpiHeader.oem_id(h0)) == 6n : Nat}
  for +tid8b: {B.Octets.len(H.AcpiHeader.oem_table_id(h0)) == 8n : Nat}
  for +cid4b: {B.Octets.len(H.AcpiHeader.creator_id(h0)) == 4n : Nat}
  for +a: B.Octets
  {Ds.AcpiAml.of_sdt(H.AcpiSdt{h, B.Octets.drop(36n, Ds.AcpiAml.build(Ds.AcpiAml{h0, a}))}) == Done{Ds.AcpiAml{h, a}} : Result<&2, &2, E.AcpiError, Ds.AcpiAml>}
