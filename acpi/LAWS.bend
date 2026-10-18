# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
#   - the AML encodings read back as written: a PkgLength below 2^28, and a
#     NameString of NameSegs (at most 255, not rooted and going up at once),
#     whatever follows them;
#   - a system description table header reads back as written, when its
#     text fields have their sizes and its byte fields are bytes;
#   - every table accepted sums to zero modulo 256: what AcpiSdt.check
#     answers, and every table AcpiTable.parse reads through any registry;
#     the RSDP's first 20 bytes, and all its bytes for revision 2;
#   - the interpreter never takes more steps than its bound, nor do loading
#     a definition block and evaluating an object.
# Witnesses that every hypothesis can hold, then vectors: the boundaries
# of PkgLength, NameStrings of each form, EISA IDs and AML encodings from
# the specification's examples, checksums, and a method evaluated.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./aml_pkglength.bend as K
import ./aml_name.bend as N
import ./header.bend as H
import ./checksum.bend as C
import ./fields.bend as F
import ./rsdp.bend as P
import ./registry.bend as R
import ./aml_value.bend as V
import ./aml_host.bend as Hs
import ./aml_interp.bend as I
import ./aml.bend as A
import ./aml_term.bend as T
import ./aml_device.bend as Dv
import ./mcfg.bend as Mc
import ./example.bend as X

# The AML encodings (20.2.4, 20.2.2)

law pkglength_round_trip:
  for +v: U32
  for +rest: B.Octets
  for +fits: {K.AmlPkgLength.fits(v) == True{} : Bool}
  {K.AmlPkgLength.decode(B.Octets.append(K.AmlPkgLength.encode(v), rest)) == Done{K.AmlPkgLen{v, rest}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}

law namestring_round_trip:
  for +n: N.AmlName
  for +rest: B.Octets
  for +ok: {N.AmlName.valid(n) == True{} : Bool}
  {N.AmlName.decode(B.Octets.append(N.AmlName.encode(n), rest)) == Done{N.AmlNameParsed{n, rest}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}

# The table header (5.2.6)

law header_round_trip:
  for +h: H.AcpiHeader
  for +sig4: {B.Octets.len(H.AcpiHeader.signature(h)) == 4n : Nat}
  for +oem6: {B.Octets.len(H.AcpiHeader.oem_id(h)) == 6n : Nat}
  for +tid8: {B.Octets.len(H.AcpiHeader.oem_table_id(h)) == 8n : Nat}
  for +cid4: {B.Octets.len(H.AcpiHeader.creator_id(h)) == 4n : Nat}
  for +rev8: {B.byte(H.AcpiHeader.revision(h)) == H.AcpiHeader.revision(h) : U32}
  for +ck8: {B.byte(H.AcpiHeader.checksum(h)) == H.AcpiHeader.checksum(h) : U32}
  {H.AcpiHeader.decode(H.AcpiHeader.encode(h)) == Done{h} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}

# Checksums: every table accepted sums to zero modulo 256

law sdt_check_sums:
  for +o: B.Octets
  for +raw: B.Octets
  for +e: {H.AcpiSdt.check(o) == Done{raw} : Result<&2, &2, E.AcpiError, B.Octets>}
  {C.AcpiChecksum.ok(raw) == True{} : Bool}

law table_checksums:
  for +reg: R.AcpiRegistry
  for +o: B.Octets
  for +t: R.AcpiTable<R.AcpiNoExt>
  for +e: {R.AcpiTable.parse(reg, o) == Done{t} : Result<&2, &2, E.AcpiError, R.AcpiTable<R.AcpiNoExt>>}
  {C.AcpiChecksum.ok(H.AcpiSdt.bytes(o)) == True{} : Bool}

law rsdp_checksum:
  for +o: B.Octets
  for +r: P.AcpiRsdp
  for +e: {P.AcpiRsdp.parse(o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}
  {C.AcpiChecksum.ok(B.Octets.take(20n, o)) == True{} : Bool}

law rsdp_ext_checksum:
  for +o: B.Octets
  for +r: P.AcpiRsdp
  for +e: {P.AcpiRsdp.parse(o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}
  {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}

# The interpreter never takes more steps than its bound, whatever the
# machine (a step reads one opcode or gives one value), and so neither does
# loading a definition block or evaluating an object

law run_steps_bound:
  for +n: Nat
  for +m: I.AmlMachine<Hs.AmlMemHost>
  {Nat.is_le(I.AmlRun.steps(Hs.AmlMemHost, I.AmlM.run(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, n, m)), n) == True{} : Bool}

law load_steps_bound:
  for +s: A.AmlSystem<Hs.AmlMemHost>
  for +aml: B.Octets
  for +n: Nat
  {Nat.is_le(A.AmlOutcome.steps(Hs.AmlMemHost, A.Aml.load(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, aml, n)), n) == True{} : Bool}

law eval_steps_bound:
  for +s: A.AmlSystem<Hs.AmlMemHost>
  for +p: String
  for +args: List<&2, V.AmlValue>
  for +n: Nat
  {Nat.is_le(A.AmlOutcome.steps(Hs.AmlMemHost, A.Aml.eval(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, p, args, n)), n) == True{} : Bool}

# Satisfiability witnesses: each hypothesis above holds for an ordinary
# input, so no law is vacuous. The first three are the laws themselves at
# an example, their hypotheses proved by computation.

law pkglength_example:
  {K.AmlPkgLength.decode(B.Octets.append(K.AmlPkgLength.encode(1000), B.Octets.of_string("AML"))) == Done{K.AmlPkgLen{1000, B.Octets.of_string("AML")}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}

law namestring_example:
  {N.AmlName.decode(B.Octets.append(N.AmlName.encode(N.AmlName.of_text("\\_SB.PCI0.LPCB")), B.Octets.of_string("x"))) == Done{N.AmlNameParsed{N.AmlName.of_text("\\_SB.PCI0.LPCB"), B.Octets.of_string("x")}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}

law header_example:
  {H.AcpiHeader.decode(H.AcpiHeader.encode(X.ex.hdr("APIC", 5))) == Done{X.ex.hdr("APIC", 5)} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}

# the checks pass for a table and an RSDP of each revision
law check_example:
  {Result.is_done(&2, &2, E.AcpiError, B.Octets, H.AcpiSdt.check(Mc.AcpiMcfg.build(X.AcpiExample.mcfg()))) == True{} : Bool}

law parse_example:
  {Result.is_done(&2, &2, E.AcpiError, R.AcpiTable<R.AcpiNoExt>, R.AcpiTable.parse(R.AcpiRegistry.default(), Mc.AcpiMcfg.build(X.AcpiExample.mcfg()))) == True{} : Bool}

law rsdp_example:
  {Result.is_done(&2, &2, E.AcpiError, P.AcpiRsdp, P.AcpiRsdp.parse(P.AcpiRsdp.build(X.AcpiExample.rsdp()))) == True{} : Bool}

law rsdp_v1_example:
  {Result.is_done(&2, &2, E.AcpiError, P.AcpiRsdp, P.AcpiRsdp.parse(P.AcpiRsdp.build(P.AcpiRsdp{B.Octets.of_string("BENDOS"), 0, 4096, None{}}))) == True{} : Bool}

# Vectors

# PkgLength (20.2.4): the boundaries of the four forms
law pkglength_63:
  {B.Octets.hex(K.AmlPkgLength.encode(63)) == "3f" : String}

law pkglength_64:
  {B.Octets.hex(K.AmlPkgLength.encode(64)) == "4004" : String}

law pkglength_4095:
  {B.Octets.hex(K.AmlPkgLength.encode(4095)) == "4fff" : String}

law pkglength_4096:
  {B.Octets.hex(K.AmlPkgLength.encode(4096)) == "800001" : String}

law pkglength_max:
  {B.Octets.hex(K.AmlPkgLength.encode(268435455)) == "cfffffff" : String}

# bits 5-4 set in a multi-byte form
law pkglength_reserved:
  {K.AmlPkgLength.decode(B.Octets.of_list([112, 0])) == Fail{E.AcpiAmlBadPkgLength{}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}

# NameString (20.2.2): a DualNamePath, a MultiNamePath, parent prefixes,
# the root alone (NullName), and a segment that is not a NameSeg
law name_dual:
  {B.Octets.hex(N.AmlName.encode(N.AmlName.of_text("\\_SB.PCI0"))) == "5c2e5f53425f50434930" : String}

law name_multi:
  {B.Octets.hex(N.AmlName.encode(N.AmlName.of_text("\\_SB.PCI0.LPCB"))) == "5c2f035f53425f504349304c504342" : String}

law name_parents:
  {B.Octets.hex(N.AmlName.encode(N.AmlName.of_text("^^_STA"))) == "5e5e5f535441" : String}

law name_root:
  {B.Octets.hex(N.AmlName.encode(N.AmlName.of_text("\\"))) == "5c00" : String}

law name_bad_seg:
  {N.AmlName.decode(B.Octets.of_string("1ABC")) == Fail{E.AcpiAmlBadName{}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}

# EISAID (chapter 19, the ASL operator), with the IDs of the examples of
# 6.1.5 (the power button) and 6.1.2 (a PCI root bridge's compatible ID)
law eisaid_power_button:
  {T.AmlT.eisaid_value("PNP0C0C") == 202166337 : U32}

law eisaid_pci:
  {Dv.AmlEisaId.text(51040321) == "PNP0A03" : String}

# AML encodings (20.2.5.2, DefName; 20.2.5.2, DefMethod; 20.2.5.3,
# DefReturn): Name (_HID, EISAID ("PNP0C0C")) and
# Method (_STA) { Return (0x0F) }, as ASL compilers write them
law aml_name_hid:
  {B.Octets.hex(T.AmlT.encode1(T.AmlT.name("_HID", T.AmlT.eisaid("PNP0C0C")))) == "085f4849440c41d00c0c" : String}

law aml_method_sta:
  {B.Octets.hex(T.AmlT.encode1(T.AmlT.method("_STA", 0n, False{}, [T.AmlT.ret(T.AmlT.int32(15))]))) == "14095f53544100a40a0f" : String}

# Checksums: a table built here sums to zero; one byte changed, it does not
law checksum_built:
  {C.AcpiChecksum.ok(Mc.AcpiMcfg.build(X.AcpiExample.mcfg())) == True{} : Bool}

law checksum_broken:
  {C.AcpiChecksum.ok(B.Octets.append(Mc.AcpiMcfg.build(X.AcpiExample.mcfg()), B.Octets.of_list([1]))) == False{} : Bool}

# the interpreter: Method (_STA) { Return (0x0F) } loaded at the root, and
# called
law aml_eval_sta:
  {A.AmlOutcome.result(Hs.AmlMemHost, A.Aml.eval_mem(A.AmlSystem.after(Hs.AmlMemHost, A.Aml.mem_system(True{}), A.Aml.load_mem(A.Aml.mem_system(True{}), T.AmlT.encode([T.AmlT.method("_STA", 0n, False{}, [T.AmlT.ret(T.AmlT.int32(15))])]), 100n)), "\\_STA", Nil{}, 100n)) == Done{V.AmlInt{W.W64.from_u32(15)}} : Result<&2, &2, E.AcpiError, V.AmlValue>}
