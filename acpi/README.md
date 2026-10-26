# bend-osdev-acpi

ACPI, the firmware tables an operating system reads at boot to learn the
machine. The package reads and writes the tables: the RSDP, RSDT and XSDT,
MADT, FADT, FACS, HPET, MCFG, SRAT, SLIT, BGRT, and the DSDT and SSDTs as
blocks of AML byte code. It finds them in physical memory through a reader
the caller supplies. It also encodes and decodes AML and runs it: an
interpreter over a namespace, with a step bound. Operation regions reach
the hardware through a host the caller supplies, and a pure in-memory host
is the default. Helpers evaluate a device's `_STA`, `_HID`, `_CRS` and
`_PRT`. Byte strings are `Octets` (bend-osdev-bytes); 64-bit values are
`W64` (bend-osdev-word64).

## Specification

* *Advanced Configuration and Power Interface (ACPI) Specification*,
  version 6.5 (UEFI Forum, August 2022):
  * chapter 5, the tables: the Generic Address Structure (5.2.3.2), the
    RSDP (5.2.5, and 5.2.5.1 for where firmware puts it), the common
    header and its checksum (5.2.6), the RSDT (5.2.7), the XSDT (5.2.8),
    the FADT (5.2.9, with its flags in 5.2.9.3 to 5.2.9.4), the FACS
    (5.2.10), the DSDT and SSDTs (5.2.11.1, 5.2.11.2), the MADT and its
    entries (5.2.12: Local APIC, I/O APIC, Interrupt Source Override, NMI
    Source, Local APIC NMI, Local APIC Address Override, x2APIC, x2APIC NMI,
    GICC, GICD), the SRAT (5.2.16), the SLIT (5.2.17) and the BGRT
    (5.2.23). The namespace OSPM starts with (5.3.1) and the predefined
    objects `\_OS`, `\_REV` and `\_OSI` (5.7);
  * chapter 6, device configuration: `_HID` and EISA IDs (6.1.5), `_STA`
    (6.3.7), `_CRS` (6.2.2), `_PRT` (6.2.13), and the resource data types
    (6.4);
  * chapter 19, ASL: the meaning of every operator the interpreter runs,
    and the ASL operators the term builder mirrors (`EISAID`,
    `DefinitionBlock`'s compliance revision);
  * chapter 20, AML: the grammar (20.2), the name strings (20.2.2), the
    PkgLength encoding (20.2.4), and the opcode tables.
* *IA-PC HPET (High Precision Event Timers) Specification*, revision 1.0a
  (Intel, 2004), section 3.2.4: the HPET table, whose signature ACPI 6.5
  reserves.
* *PCI Firmware Specification*, revision 3.3 (PCI-SIG), section 4.1.2: the
  MCFG table and its ECAM allocations.
* *Boot Graphics Resource Table* fields as ACPI 6.5, 5.2.23 gives them.

The package was written from these documents alone. No ACPICA source and no
Linux ACPI source was read. ACPICA's `iasl`, run as a black box, is one of
the optional references of the differential test (Tests).

Choices this package makes where the specification leaves room:

* **Tables are checked before they are read.** A table must be at least as
  long as its header and its Length field, Length at least 36, and all
  Length bytes sum to 0 modulo 256 (`AcpiSdt.check`). Bytes after Length
  are ignored. The RSDP checks its first checksum over 20 bytes, and for
  revision 2 or later a Length from 36 to the bytes given and the extended
  checksum over Length bytes. Header revisions are not checked against the
  table types: firmware in the field ships every value.
* **Revision-dependent tables.** The FADT is read up to its Length: the
  ACPI 1.0 part, then the ACPI 2.0 extension (the X_ fields), the sleep
  registers and the hypervisor vendor identity, each `Maybe`.
  `AcpiFadt.block` gives a register block as a Generic Address, the X_ form
  when it is present and not zero and the 32-bit block (as a system I/O
  address) otherwise. `AcpiFadt.dsdt_address` and `facs_address` follow the
  same rule (X_DSDT over DSDT, X_FIRMWARE_CTRL over FIRMWARE_CTRL).
* **Entries of unknown kinds** in the MADT and SRAT are kept as their bytes
  (`AcpiMadtOther`, `AcpiSratOther`), not refused. An entry whose length
  is below 2 or runs past the table is refused (`AcpiBadEntry`).
* **The loader** (`AcpiTables.load`) uses the XSDT when the RSDP has one
  (5.2.5.3) and the RSDT otherwise, or always the RSDT if
  `AcpiLoadOptions.prefer_xsdt` is false. The RSDP and the root table
  must read and check, or the load fails. Then each table the root table
  lists, the DSDT (from the FADT's address) and the FACS are read through
  the caller's memory reader, 8 bytes first and then their Length, and
  parsed. A table that fails to read or to check is kept as its error in
  the result; the loader does not stop.
* **Integer width.** A definition block of header revision below 2 uses
  32-bit integers, 64-bit otherwise (chapter 19, `DefinitionBlock`).
  Results are cut to the width, and arguments passed in by the caller are
  too.
* **Interpreter choices.** Shifts by 64 or more give 0. A String converted
  to a Buffer gets its NUL. A store into a Buffer keeps the Buffer's length
  (zero-filled or cut). A method that ends without `Return` gives
  `AmlUninit{}`. Defining a name twice is `AcpiAmlDuplicate`. A
  `PCI_Config` region's address is the segment, bus, device and function
  of its device's `_ADR` and the parent bus's `_SEG` and `_BBN` (missing
  ones are 0), with the offset (`AmlPci.address` gives the layout). Field
  accesses of type AnyAcc are byte accesses. A write to part of an access
  unit reads it first and keeps the other bits (Preserve), or writes ones or
  zeros (WriteAsOnes, WriteAsZeros), by the field's update rule. An
  IndexField write writes zeros in the unit's other bits. `^` in a method
  body searches from the method's own scope, as in a `Scope`. NameStrings
  must be in their shortest form (a 1-segment name is not written as a
  MultiNamePath) or they are `AcpiAmlUnsupported`; ASL compilers write the
  shortest form.
* **What a step is.** The interpreter is a small-step machine. One step
  reads one opcode (or a name, or a constant) or applies one operator to its
  operands. `Aml.load` and `Aml.eval` take a step bound `n` and answer
  `AcpiAmlStepLimit` when it runs out. The bound is a law (Laws).

## Files

| File | Holds |
|---|---|
| `acpi.bend` | the entry: `AcpiMemImage`, `AcpiLoadOptions`, `AcpiTables.load` / `load_with`, `AcpiTableSet` |
| `error.bend` | `AcpiError` |
| `checksum.bend` | `AcpiChecksum`: the 8-bit sum, and fixing a checksum byte |
| `header.bend` | the common header `AcpiHeader`, and `AcpiSdt` (header and body, checked) |
| `gas.bend` | `AcpiGas`, the Generic Address Structure |
| `entries.bend` | `AcpiRawEntry`: the type-length entry lists the MADT and SRAT share |
| `rsdp.bend` | `AcpiRsdp`: reading, writing, finding in a memory region |
| `rsdt.bend` | `AcpiRsdt`, `AcpiXsdt` (`AcpiSdtList`) |
| `madt.bend` | `AcpiMadt` ("APIC"), `AcpiMadtEntry` |
| `fadt.bend` | `AcpiFadt` ("FACP") and its parts |
| `facs.bend` | `AcpiFacs` |
| `hpet.bend` | `AcpiHpet` |
| `mcfg.bend` | `AcpiMcfg` |
| `srat.bend` | `AcpiSrat`, `AcpiSratEntry` |
| `slit.bend` | `AcpiSlit` |
| `bgrt.bend` | `AcpiBgrt` |
| `dsdt.bend` | `AcpiAml`: a DSDT or SSDT, its header and AML bytes |
| `registry.bend` | `AcpiRegistry` (signature to parser), `AcpiTable<X>`, `AcpiTable.parse` |
| `show.bend` | `AcpiShow`: one-line dumps of tables and errors |
| `aml_pkglength.bend` | `AmlPkgLength`: the PkgLength encoding |
| `aml_name.bend` | `AmlName`: NameStrings, encoded, decoded and as text |
| `aml_term.bend` | `AmlTerm`, `AmlT`: building AML, with an ASL-like constructor per operator |
| `aml_value.bend` | `AmlValue`, `AmlLoc`, conversions and comparison |
| `aml_ns.bend` | `AmlObject`, `AmlNs` (the namespace), `AmlPath`, name resolution |
| `aml_host.bend` | the host interface (`AmlAccess`, `AmlHostOp`, `AmlHostAns`), `AmlPci.address`, the in-memory host `AmlMemHost` |
| `aml_field.bend` | field units: reading and writing bits through access units, index fields, buffer fields |
| `aml_interp.bend` | the interpreter: `AmlOptions`, `AmlMachine`, `AmlM.step`, `AmlM.run` |
| `aml.bend` | the entry for AML: `AmlSystem`, `Aml.load`, `Aml.eval`, `Aml.boot` |
| `aml_resource.bend` | `AmlResource`: resource templates (`_CRS` buffers) read and written |
| `aml_device.bend` | `AmlDevice`: `_STA`, `_HID`, `_CRS`, `_PRT` of a device, device lists |
| `example.bend` | `AcpiExample`: a sample machine (tables, a DSDT and an SSDT, its memory and host) |
| `fields.bend` | internal: little-endian fields at offsets |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `LAWS_tables.bend`, `PROOF_tables.bend` | the structures' round trips (GAS, HPET, BGRT, FACS, XSDT, RSDT, MCFG, DSDT/SSDT) and their proofs, checked in a process of their own |
| `LAWS_checksum.bend`, `PROOF_checksum.bend` | the checksum law (`AcpiChecksum.fix` makes the bytes sum to zero) and its proof |
| `LAWS_whole.bend`, `PROOF_whole.bend` | the tables' whole round trips, `parse(build(t))` (any table through `AcpiSdt`, HPET, BGRT, XSDT, RSDT, MCFG, DSDT/SSDT) and their proofs |
| `LAWS_rsdp.bend`, `PROOF_rsdp.bend` | the RSDP's whole round trip, both revisions, and its proof |
| `check.bend` | examples with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/runner.bend` | the differential test |

## Public interface

`acpi.bend`:

| Def or type | Meaning |
|---|---|
| `AcpiMemImage{regions}`, `AcpiMemRegion{base, bytes}`, `AcpiMemImage.of_list(rs)` | physical memory as regions of bytes, the default memory |
| `AcpiMemImage.read(m, addr, n) -> Result<…, Octets>` | `n` bytes at `addr`, `AcpiNotMapped{addr}` if no region holds them all |
| `AcpiLoadOptions{prefer_xsdt, registry}`, `AcpiLoadOptions.default()` | the XSDT preferred, the default registry |
| `AcpiTables.read_rsdp(~M, ~read, m, addr)` | the RSDP at `addr` |
| `AcpiTables.read_table(~M, ~read, m, addr)` | a table's bytes: 8 bytes, then Length |
| `AcpiTables.load_with(~M, ~read, ~X, ~ext, opts, m, rsdp_addr) -> Result<…, AcpiTableSet<X>>` | every table the root table lists, each parsed through the registry |
| `AcpiTables.load(~M, ~read, m, rsdp_addr)` | the same with the default options and no extension parser |
| `AcpiTableSet{rsdp, root, tables, facs}`, `AcpiLoaded{address, table}` | what was loaded; each table as its result |
| `AcpiTableSet.tables(s)`, `AcpiTableSet.find(s, "APIC")` | the tables; the first good table with a signature |

`read` is any `M -> W64 -> Nat -> Result<&2, &2, AcpiError, Octets>`;
`AcpiMemImage.read` is the default.

`error.bend`: `AcpiError`, one constructor per failure: `AcpiTooShort{need,
got}`, `AcpiBadSignature{got}`, `AcpiBadLength{length}`,
`AcpiBadChecksum{sum}`, `AcpiRsdpBadChecksum{sum}`,
`AcpiRsdpBadExtChecksum{sum}`, `AcpiBadRevision{revision}`, `AcpiBadEntry{offset,
kind}`, `AcpiBadSize{size}`, `AcpiNotMapped{address}`,
`AcpiTableMissing{signature}`, and
for AML `AcpiAmlTruncated`, `AcpiAmlBadOpcode{opcode}`,
`AcpiAmlBadPkgLength`, `AcpiAmlBadName`, `AcpiAmlUndefined{path}`,
`AcpiAmlDuplicate{path}`, `AcpiAmlBadOperand{opcode}`, `AcpiAmlBadType{what}`,
`AcpiAmlRange`, `AcpiAmlDivZero`, `AcpiAmlBadControl`, `AcpiAmlFatal{kind, code, arg}`
(the AML `Fatal` operator), `AcpiAmlUnsupported{what}`, `AcpiAmlStepLimit`,
`AcpiAmlHost{code}` (each documented in the file).

`checksum.bend`: `AcpiChecksum.sum(o) -> U32` (modulo 256),
`AcpiChecksum.ok(o)` (the sum is 0), `AcpiChecksum.byte_for(o)`,
`AcpiChecksum.fix(i, o)` (byte `i` set so that `o` sums to 0).

`header.bend`: `AcpiHeader{signature, length, revision, checksum, oem_id,
oem_table_id, oem_revision, creator_id, creator_revision}` and an accessor
for each field; `AcpiHeader.size()` (36); `AcpiHeader.encode(h)`,
`AcpiHeader.decode(o)` (the 36 bytes as they are); `AcpiHeader.make(sig,
rev, oem, tid)`; `AcpiSdt{header, body}`, `AcpiSdt.header`, `.body`;
`AcpiSdt.check(o) -> Result<…, Octets>` (the table's Length bytes, checked
as above); `AcpiSdt.bytes(o)` (the bytes the checks cover);
`AcpiSdt.parse(o)`, `AcpiSdt.parse_sig(sig, o)` (also the signature);
`AcpiSdt.build(h, body)` (Length and checksum computed).

`gas.bend`: `AcpiGas{space, bit_width, bit_offset, access_size, address}`;
`AcpiGas.at(o, i)`, `encode`, `zero`, `is_null`, `address`, `space`,
`size`, `io_block(port, n)`, `show`; the space IDs `space_memory`,
`space_io`, `space_pci_config`, `space_ec`, `space_ffixedhw`.

`entries.bend`: `AcpiRawEntry{kind, data}`, `AcpiRawEntry.split(o, off)`
(a run of type-length entries), `AcpiRawEntry.encode`.

`rsdp.bend`: `AcpiRsdp{oem_id, revision, rsdt_address, ext}`,
`AcpiRsdpExt{length, xsdt_address}`; `AcpiRsdp.parse(o)`,
`AcpiRsdp.build(r)` (20 or 36 bytes, both checksums computed),
`AcpiRsdp.find(o) -> Maybe<Nat>` (the first 16-byte-aligned offset with
the signature and a good first checksum), `AcpiRsdp.checked(r)` (how many
bytes the checksums cover), `revision`, `rsdt_address`, `xsdt_address`,
`ext`, `signature`.

`rsdt.bend`: `AcpiSdtList{header, entries}` (`entries`: `W64` addresses);
`AcpiRsdt.parse`, `AcpiXsdt.parse`, `of_sdt`, `build`.

`madt.bend`: `AcpiMadt{header, lapic_address, flags, entries}` (the 32-bit field),
`AcpiMadtEntry`: `AcpiMadtLapic`, `AcpiMadtIoApic`, `AcpiMadtIso`,
`AcpiMadtNmiSource`, `AcpiMadtLapicNmi`, `AcpiMadtLapicOverride`,
`AcpiMadtX2apic`, `AcpiMadtX2apicNmi`, `AcpiMadtGicc` (with
`AcpiGiccAddrs`), `AcpiMadtGicd`, `AcpiMadtOther{kind, data}`;
`AcpiMadt.parse`, `of_sdt`, `build`, `entries`, `flags`, `lapic_address32`,
`AcpiMadt.lapic_address(t)` (the override's 64-bit address when there is
one), `AcpiMadtEntry.of_raw`, `AcpiMadtEntry.encode`.

`fadt.bend`: `AcpiFadt{header, core, ext, sleep, hypervisor}` with
`AcpiFadtCore` (every ACPI 1.0 field, with `AcpiFadtBlocks` and
`AcpiFadtLens`), `AcpiFadtExt` (reset register, ARM boot flags, minor
version, X_FIRMWARE_CTRL, X_DSDT, the X_ blocks `AcpiFadtX`),
`AcpiFadtSleep`; `AcpiFadt.parse`, `of_sdt`, `build`, `core`, `ext`,
`sleep`, `hypervisor`, `flags`, `flag(f, bit)`, `hw_reduced`,
`dsdt_address`, `facs_address`, `block(f, AcpiFadtBlock)` with
`AcpiFadtPm1aEvt{}` … `AcpiFadtGpe1{}`.

`facs.bend`: `AcpiFacs{length, hardware_signature, waking_vector,
global_lock, flags, x_waking_vector, version, ospm_flags}`,
`AcpiFacs.parse`, `build`.

`hpet.bend`: `AcpiHpet{header, block_id, base, number, min_tick,
page_protection}`, `AcpiHpet.parse`, `of_sdt`, `build`, `block_id`, `base`,
and the Event Timer Block ID's fields `vendor_id`, `comparators`,
`counter_64`, `legacy_capable`.

`mcfg.bend`: `AcpiMcfg{header, entries}`, `AcpiMcfgEntry{base, segment,
start_bus, end_bus}`, `AcpiMcfg.parse`, `of_sdt`, `build`, `entries`,
`AcpiMcfg.ecam_address(t, seg, bus, dev, fun, off) -> Maybe<W64>`.

`srat.bend`: `AcpiSrat{header, entries}`, `AcpiSratEntry`:
`AcpiSratLapic`, `AcpiSratMemory`, `AcpiSratX2apic`, `AcpiSratGicc`,
`AcpiSratGicIts`, `AcpiSratGeneric`, `AcpiSratOther`; `AcpiSrat.parse`,
`of_sdt`, `build`, `entries`, `AcpiSratEntry.of_raw`, `encode`.

`slit.bend`: `AcpiSlit{header, count, matrix}`, `AcpiSlit.parse`, `of_sdt`,
`build`, `count`, `AcpiSlit.distance(t, i, j) -> Maybe<U32>`.

`bgrt.bend`: `AcpiBgrt{header, version, status, image_type, image_address,
offset_x, offset_y}`, `AcpiBgrt.parse`, `of_sdt`, `build`.

`dsdt.bend`: `AcpiAml{header, aml}`, `AcpiAml.parse` (DSDT or SSDT),
`parse_dsdt`, `of_sdt`, `build`, `header`, `aml`, `wide` (64-bit
integers).

`registry.bend`: `AcpiKind`: `AcpiKRsdt{}`, `AcpiKXsdt{}`, `AcpiKMadt{}`,
`AcpiKFadt{}`, `AcpiKHpet{}`, `AcpiKMcfg{}`, `AcpiKSrat{}`, `AcpiKSlit{}`,
`AcpiKBgrt{}`, `AcpiKAml{}`, `AcpiKRaw{}`, `AcpiKExt{tag}`;
`AcpiRegistry`, `AcpiRegistry.default()` (every table above by its
signature), `empty()`, `set(r, sig, k)`, `remove(r, sig)`,
`lookup(r, sig)` (`AcpiKRaw{}` if absent); `AcpiTable<X>`: `AcpiTRsdt`,
`AcpiTXsdt`, `AcpiTMadt`, `AcpiTFadt`, `AcpiTHpet`, `AcpiTMcfg`,
`AcpiTSrat`, `AcpiTSlit`, `AcpiTBgrt`, `AcpiTAml`, `AcpiTRaw` (an
`AcpiSdt`), `AcpiTExt{tag, x}`; `AcpiTable.parse_with(~X, ~ext, reg, o)`
(checked, then parsed by the registry's kind; `ext` parses `AcpiKExt`
tables), `AcpiTable.parse(reg, o)` (no extension, `AcpiNoExt`),
`AcpiTable.name(t)`.

`show.bend`: `AcpiShow.error`, `header`, `gas`, `rsdp`, `sdt_list`,
`madt_entry`, `madt`, `fadt`, `facs`, `hpet`, `mcfg`, `srat_entry`, `srat`,
`slit`, `bgrt`, `aml`, `table`, `result`: one line of text each, the format
`ref/gen.py` prints too.

`aml_pkglength.bend`: `AmlPkgLength.encode(v)` (the shortest form),
`AmlPkgLength.decode(o) -> Result<…, AmlPkgLen{value, rest}>`,
`AmlPkgLength.fits(v)` (below 2^28), `size_for(n)`, `wrap(body)` (a
PkgLength that counts itself, then the body).

`aml_name.bend`: `AmlName{root, up, segs}` (segments as 4-byte `Octets`);
`AmlName.encode`, `AmlName.decode(o) -> Result<…, AmlNameParsed{name,
rest}>`, `AmlName.valid(n)` (what encodes: NameSegs, at most 255, not both
rooted and going up), `size`, `of_text("\\_SB.PCI0")` (short segments padded
with `_`), `show`, `seg`, `seg_ok`, `segs_ok`, `name_char`, the lead-byte
classifier `AmlLead.classify` / `is_seg`.

`aml_term.bend`: `AmlTerm`: `AmlTInt`, `AmlTStr`, `AmlTRaw`,
`AmlTOp{code, args}`, `AmlTPkg{code, head, body}`; `AmlFieldElem`;
`AmlT.encode(ts)`, `AmlT.encode1(t)`; and one constructor per ASL
operator: data (`int`, `int32`, `zero`, `one`, `ones`, `str`, `buffer`,
`buf`, `package`, `var_package`, `eisaid`, `eisaid_value`, `revision`),
names (`nm`, `call`, `local`, `arg`, `debug`, `none`), definitions
(`name`, `scope`, `device`, `method`, `processor`, `power_resource`,
`thermal_zone`, `region`, `field`, `field_flags`, `index_field`, `fnamed`,
`mutex`, `event`, `alias`, `external`, `create_field`,
`create_dword_field`), control (`if_`, `if_else`, `while_`, `ret`, `brk`,
`cont`, `noop`, `notify`, `sleep`, `stall`, `acquire`, `release`) and
expressions (`store`, `copy_object`, the arithmetic, bitwise and logical
operators, `increment`, `decrement`, `concat`, `ref_of`, `deref_of`,
`index`, `cond_ref_of`, `size_of`, `object_type`, `to_integer`,
`to_buffer`), and `AmlT.op(code, args)` for any other.

`aml_value.bend`: `AmlValue`: `AmlUninit`, `AmlInt{v: W64}`, `AmlStr`,
`AmlBuf`, `AmlPkg`, `AmlRef{loc}`, `AmlObj{path, kind}`; `AmlLoc`:
`AmlLName`, `AmlLLocal`, `AmlLArg`, `AmlLIndex`, `AmlLElem`, `AmlLDebug`,
`AmlLNone`; `AmlValue.type`, `to_int(wide, v)`, `to_buf`, `to_str`,
`parse_int`, `compare`, `show`, `show_int`, `element`; `AmlInt.fit`,
`ones`, `of_bool`, `width_bytes`.

`aml_ns.bend`: `AmlObject` (`AmlOData`, `AmlOMethod`, `AmlOScope`,
`AmlORegion`, `AmlOField`, the index and buffer fields, mutexes, events,
aliases, `AmlOBuiltin`; each documented), `AmlObject.type`; `AmlNs`,
`AmlNs.empty`, `initial(os, rev)` (`\_GPE`, `\_PR_`, `\_SB_`, `\_SI_`,
`\_TZ_`, `\_OS_`, `\_REV`, `\_OSI`), `get`, `set`, `has`, `remove`,
`paths`, `resolve(ns, scope, name)` (the search rules of 5.3); `AmlPath`
(absolute paths as `String`): `root`, `is_root`, `child`, `parent`,
`last`, `of_name`.

`aml_host.bend`: `AmlAccess{space, address, width}`, `AmlHostOp`:
`AmlHRead{a}`, `AmlHWrite{a, v}`; `AmlHostAns<H>{host, value}`;
`AmlPci.address(seg, bus, dev, fun, off)`; `AmlMemHost` (every address
space as a map of bytes, with a log of accesses), `AmlMemHost.new()`,
`io` (the host function), `poke`, `peek`, `log`, `show_log`,
`AmlHostOp.show`.

`aml_field.bend`: `AmlFieldDesc`, `AmlField.read_int`, `write_int`,
`read_buf`, `write_buf`, `read_indexed`, `write_indexed`, `unit`,
`update_rule`; `AmlUnit` (an access unit) and its helpers;
`AmlBits.get`, `set`, `get_buf` (bit ranges of a buffer).

`aml_interp.bend`: `AmlOptions{osi, os, rev}`, `AmlOptions.default()`
(see Extension points); `AmlMachine<H>` and its parts (`AmlMode`,
`AmlCur`, `AmlFrame`, `AmlWorld`, `AmlEnv`, `AmlNote{path, value}` for a
`Notify`), `AmlMachine.mode`, `world`, `halted`; `AmlWorld.ctx`, `ns`,
`env`, `host`; `AmlM.step(~H, ~io, m)` (one step), `AmlM.run(~H, ~io, n,
m) -> AmlRun<H>` (at most `n` steps), `AmlRun.steps`, `AmlRun.machine`.
The other types there (`AmlOp`, `AmlCtx`, `AmlArgK`, `AmlB`, `AmlRead`,
`AmlPut`, …) are the machine's state, open for inspection, not for
building.

`aml.bend`: `AmlSystem<H>{opts, wide, ns, host}`, `AmlSystem.new(H, opts,
wide, host)`, `ns`, `host`, `wide`, `after(s, outcome)` (the system with
the outcome's namespace and host); `AmlOutcome<H>{result, ns, host, steps,
notes, debug}` and accessors; `Aml.load(~H, ~io, s, aml, n)` (run a
definition block's terms at the root, at most `n` steps); `Aml.eval(~H,
~io, s, path, args, n)` (evaluate an object: call a method with arguments,
or read a data object or field); `Aml.boot(~H, ~io, opts, host, tables, n)`
(the DSDT, then each SSDT in order); `Aml.mem_system(wide)`, `load_mem`,
`eval_mem` (the same with `AmlMemHost`); `AmlSystem.loader`,
`AmlSystem.caller` (the machines `load` and `eval` run, for stepping one by
one).

`aml_resource.bend`: `AmlResource`: `AmlRIrq`, `AmlRDma`, `AmlRIo`,
`AmlRFixedIo`, `AmlRMem32`, `AmlRMem32Fixed`, the address space
descriptors `AmlRAddr` (Word, DWord, QWord, with an `AmlRange`), `AmlRExtIrq`, and
`AmlROther` for the rest (as bytes); `AmlResource.parse(o)` (up to the End
Tag), `encode`, `template(rs)` (with the End Tag and its checksum), `show`.

`aml_device.bend`: `AmlDevice.status(~H, ~io, s, dev, n)` (`_STA`, or 0x0F
when the device has none, 6.3.7); `AmlDevice.hid` (a string, or the EISA ID
as text); `AmlDevice.crs` (the resources); `AmlDevice.prt` (`AmlPrtEntry
{address, pin, source, index}`); `AmlDevice.get(…, dev, seg, n)` (any child
object, evaluated); `AmlDevice.list(ns)` (every device's path);
`AmlEisaId.text(v)`.

`example.bend`: `AcpiExample.rsdp()`, `fadt()`, `facs()`, `madt()`,
`hpet()`, `mcfg()`, `srat()`, `slit()`, `bgrt()`, `dsdt()`, `ssdt()`,
`dsdt_terms()`, `dsdt_aml()`, `memory()` (all of them at their addresses,
from `rsdp_address()`), `host()` (an `AmlMemHost` with the sample's PCI
interrupt routing registers and embedded-controller bytes), `pieces`,
`region`, `base`. The DSDT has a PCI root bridge with an LPC bridge, a
`PCI_Config` field of interrupt routing registers and a link device read
through it, an embedded controller with an EC region and a query method
that notifies, a thermal zone, `_OSI` tests and loops.

Everything else (the `hd.*`, `sdt.*`, `rs.*`, `madt.*`, `fadt.*`, `ld.*`,
`reg.*`, `pk.*`, `nm.*`, `in.*`, `fl.*`, `cur.*`, `aml.*`, `res.*`, `dev.*`,
`ex.*` defs and `fields.bend`) is internal.

## Extension points

* **Memory.** `AcpiTables.load_with` and `read_table` take the memory
  type and its reader as template arguments: a kernel passes its physical
  memory mapper, a tool passes files. `AcpiMemImage` is the default.
* **Tables.** The registry maps signatures to parsers and is a value:
  `AcpiRegistry.set(reg, "XXXX", AcpiKExt{tag})` sends a table to the
  caller's parser (`AcpiTable.parse_with`'s `~ext`, which gets the tag and
  the checked `AcpiSdt`), `remove` leaves one raw, and `empty()` reads
  everything raw. Each table type also parses on its own (`AcpiMadt.parse`
  and so on).
* **The host.** The interpreter reaches operation regions only through
  `~io: H -> AmlHostOp -> Result<…, AmlHostAns<H>>`: a read or write of a
  width at an address in an address space (system memory, system I/O, PCI
  configuration space, embedded controller, CMOS, …). A kernel passes real
  port and memory accesses; `AmlMemHost` (with `AmlMemHost.io`) is the pure
  default and logs every access. A host error stops the interpreter with
  that error.
* **What the firmware sees.** `AmlOptions` sets the strings `\_OSI`
  answers true for (by default the Windows releases firmware tests for, and
  "Module Device", "Processor Device", "3.0 Thermal Model", "Extended Address
  Space Descriptor"), `\_OS` ("Microsoft Windows NT") and `\_REV` (2).
* **The step bound** is a parameter of every call, and `AmlM.step` /
  `AmlSystem.loader` / `caller` let a caller run the machine a step at a
  time (to interleave it with other work, or to trace it).
* **The loader's policy**: `AcpiLoadOptions` (XSDT or RSDT, the registry).
* **Streaming.** Tables arrive one at a time, through the reader, each
  read as 8 bytes then its Length, so nothing larger than one table is held
  at once. A definition block is not streamed: AML's PkgLengths and forward
  references (a method may be called before the lines that define names it
  uses are reached) need the whole block, and firmware hands it over whole.
* **Building AML.** `AmlT` builds definition blocks term by term (the
  tests and `example.bend` use it), and `AmlT.op` and `AmlTRaw` reach any
  encoding the builder lacks.
* **Not supported yet** (each answers `AcpiAmlUnsupported{what}`, naming
  it): `BankField`, `DataTableRegion`, `Load`, `LoadTable`, `Unload`,
  `ConcatenateResTemplate`, `Match`, `ToDecimalString`, `ToHexString`,
  `ToString`, `Mid`, `FromBCD`, `ToBCD`, `Connection` in a field list
  (`ConnectField`), a buffer field of a package element or of a buffer
  that has no name, and NameStrings not in their shortest form. Also:
  `Mutex` and `Event` exist but `Acquire` and `Wait` always succeed at
  once and `Release`, `Signal` and `Reset` do nothing (there is one
  thread); `Sleep` and `Stall` advance the virtual clock `Timer` reads and
  do not wait; `_INI` and `_REG` methods are not run by `Aml.load` (a
  caller evaluates them); writes through an `Index` reference into a
  package nested inside another are not written back; an IndexField wider
  than 64 bits; `Aml.load` stops at the first error rather than skipping
  the term. Resource descriptors other than those listed are kept as
  bytes.

## Laws

`LAWS.bend` has 35 laws.

**Properties, for every input (10):**

* `pkglength_round_trip`: for every `U32` below 2^28 and any bytes after
  it, `AmlPkgLength.decode(append(encode(v), rest)) == Done{AmlPkgLen{v,
  rest}}`.
* `namestring_round_trip`: for every name `AmlName.valid` admits and any
  bytes after it, `AmlName.decode(append(encode(n), rest)) ==
  Done{AmlNameParsed{n, rest}}`.
* `header_round_trip`: `AcpiHeader.decode(encode(h)) == Done{h}` when the
  text fields have their sizes (4, 6, 8, 4 bytes) and revision and
  checksum are bytes.
* `sdt_check_sums`: whatever `AcpiSdt.check` accepts sums to 0 modulo 256;
  `table_checksums`: so does every table `AcpiTable.parse` reads, through
  any registry; `rsdp_checksum`, `rsdp_ext_checksum`: every RSDP
  `AcpiRsdp.parse` accepts has its first 20 bytes, and all the bytes its
  checksums cover (`AcpiRsdp.checked`: Length for revision 2), summing to 0.
* `run_steps_bound`: `AmlM.run` never takes more than `n` steps, for every
  machine; `load_steps_bound`, `eval_steps_bound`: neither do `Aml.load`
  and `Aml.eval`, for every system, block, path and arguments. These are
  stated for the default host `AmlMemHost` (a law cannot quantify over a
  template argument), and the proof does not look at the host.

**Satisfiability witnesses (7):** each hypothesis above holds for an
ordinary input: `pkglength_example`, `namestring_example`,
`header_example` (the laws at an example), `check_example`,
`parse_example`, `rsdp_example`, `rsdp_v1_example` (the checks pass for a
table and an RSDP of each revision).

**Vectors (18):** the boundaries of the four PkgLength forms (63, 64,
4095, 4096, 2^28 - 1) and a reserved-bits refusal; NameStrings of each
form (dual, multi, parent prefixes, the root alone) and a bad segment; the
EISA IDs `PNP0C0C` and `PNP0A03` (6.1.5 and 6.1.2's examples); the bytes
of `Name (_HID, EISAID ("PNP0C0C"))` and `Method (_STA) { Return (0x0F) }`
as ASL compilers write them; a built table's checksum, and one byte
appended breaking it; that method loaded and evaluated.

`LAWS_tables.bend` has 8 laws, proved in `PROOF_tables.bend` (checked in
a process of its own; it imports bytes' and word64's proofs, not
`PROOF.bend`), for every input:

* `gas_round_trip`: a Generic Address Structure reads back at offset
  `len(a)` of `a ++ AcpiGas.encode(g) ++ b`, whatever is around it, when
  its four byte fields are bytes.
* `hpet_round_trip`, `bgrt_round_trip`, `xsdt_round_trip`,
  `rsdt_round_trip`, `mcfg_round_trip`, `aml_round_trip`: the body that
  each table's `build` writes (`B.Octets.drop(36n, build(t))`, everything
  after the header) is read back by its `of_sdt`, with any header `h`:
  `of_sdt(AcpiSdt{h, drop(36, build(t))}) == Done{t'}`, `t'` being `t`
  with its header `h`. The header `build` was given must have text fields
  of their sizes (OEMID 6, OEM table ID 8, creator ID 4 bytes; for a DSDT
  or SSDT, whose signature is kept, also the signature 4), and, for the
  HPET and BGRT, which read their fields through the whole table, so must
  `h`. The HPET's and BGRT's byte fields must be bytes and their 16-bit
  fields 16 bits. The RSDT reads back each address's low 32 bits
  (`acpilaw.low32`: what an RSDT entry holds), the MCFG each structure
  with its segment group's low 16 bits and its bus numbers' low 8 bits
  (`acpilaw.mcfg_fit`), the XSDT the addresses, and a DSDT or SSDT its
  definition block, as written. Every table built by `AcpiSdt.build`
  rests on one lemma (`tb.sdt_body`): its header is 36 bytes, and the
  checksum byte that `AcpiChecksum.fix` writes is byte 9, inside it, so
  the bytes after the header are the body as given.
* `facs_round_trip`: `AcpiFacs.parse(AcpiFacs.build(f))` gives `f` back,
  its Length being the 64 that `build` writes, when the version is a
  byte. The FACS has no header and no checksum, so this is the whole
  round trip.

`LAWS_checksum.bend` has 2 laws, proved in `PROOF_checksum.bend`:

* `fix_ok`: for every byte string `o` and every offset `i < len(o)`,
  `AcpiChecksum.ok(AcpiChecksum.fix(i, o)) == True`, whatever the bytes
  are. The proof reads the U32 sum as a sum of `Nat`s modulo 256 (u32's
  `u32_add_wrap` and `u32_sub_wrap`: the 2^32 a wrap or a borrow adds does
  not change the low 8 bits), splits `o` into `take(i, o)`, its byte `i`
  and `drop(1 + i, o)` through bytes' laws, and cancels byte `i` modulo
  256.
* `fix_example`: the hypothesis and the law at an example.

`LAWS_whole.bend` has 8 laws, proved in `PROOF_whole.bend` (which imports
`PROOF_tables.bend` and `PROOF_checksum.bend`), for every input:

* `sdt_round_trip`: `AcpiSdt.parse(AcpiSdt.build(h, body)) ==
  Done{AcpiSdt{written(h), body}}`, for any header `h` whose text fields
  have their sizes (signature 4, OEMID 6, OEM table ID 8, creator ID 4
  bytes) and whose revision is a byte, and any body, when the table's
  length is no more than a U32's value (`Nat.is_le(len(build(h, body)),
  U32.to_nat(z))` for some `z`). `written(h)` (`acpilaw.written(sig, h,
  o)`) is `h` with the fields `build` computes: Length the table's length
  and Checksum the byte at offset 9 of the table. Both checks pass: the
  Length field reads back as the table's length, and the bytes sum to zero
  (`fix_ok`).
* `hpet_whole`, `bgrt_whole`, `xsdt_whole`, `rsdt_whole`, `mcfg_whole`,
  `aml_whole`: each table's `parse(build(t))` gives `t` back, with its
  header `written` (the signature `build` writes) and its contents as the
  body laws of `LAWS_tables.bend` read them (the RSDT's addresses' low 32
  bits, the MCFG's structures fitted), under those laws' hypotheses on the
  header and the fields, the revision being a byte, and, but for the HPET
  and the BGRT (56 bytes), the length fitting a U32. The DSDT and SSDT law
  is for `AcpiAml.parse`, which takes any signature.
* `whole_example`: the hypotheses at an example (a header from
  `AcpiHeader.make` and a 39-byte table).

`LAWS_rsdp.bend` has 3 laws, proved in `PROOF_rsdp.bend` (which imports
`PROOF_whole.bend`):

* `rsdp_v1_round_trip`: `AcpiRsdp.parse(AcpiRsdp.build(r)) == Done{r}`
  for a revision 0 or 1 RSDP (`ext` `None`) whose OEMID is 6 bytes and
  whose revision is a byte;
* `rsdp_v2_round_trip`: the same for revision 2 or later, the Length read
  back being the 36 that `build` writes; both checksums pass;
* `rsdp_round_trip_example`: the hypotheses at an example.

**What is not proved.** The tables not covered yet, most used first: the
MADT (its entry list is split by length bytes with fuel and offsets, and
each of its 15 entry kinds needs its own read-back, plus a rule for
`AcpiMadtOther` entries whose type is a known one), the FADT (about 50
fields and 15 GASes in versioned parts; `None` parts are written as zeros
and read back as present, so the law needs a normalisation of every part),
the SRAT (an entry list like the MADT's) and the SLIT (an `n` by `n`
matrix fitted to `n * n` bytes); for each, the checksum and header part of
the whole round trip is `sdt_round_trip`, and the body's read-back is what
is missing.
The interpreter's semantics, the resource templates and the device
helpers are covered by `check.bend` and the differential test, not by laws
for every input.

## Tests

`check.bend` (28 checks) loads the sample machine from its memory image
through the RSDP and XSDT and dumps every table, reads the MADT, FADT
blocks, HPET, MCFG and SLIT, refuses broken tables (checksum, length,
signature, RSDP checksums), and runs the DSDT and SSDT: the device list
with each `_HID` and `_STA`, `_CRS` templates, a link device's `_CRS`
read from a `PCI_Config` field (with the host's access log), `_PRT`, a
thermal zone's `_TMP` read through the EC region, `_OSI`, a loop of 2,145
steps, `Notify`, the step limit, an undefined name and 32-bit integers in
a revision 1 block.

`ref/run.sh` compares the package with `ref/gen.py`, an independent
reader, writer and evaluator written in Python from the same
specification. `gen.py` writes `ref/cases.txt` (one case per line) and
`ref/expected.txt`; `ref/runner.bend` reads the cases and prints its
answers (a single generated Bend file of the cases needed more than 3 GB
to build natively). With seed 2026, 409 cases:

* **checksum** (10), **header** (8), **rsdp** (16: both revisions,
  corrupted checksums, signatures, lengths);
* **table** (70): every table type, built by the Python writer with random
  fields, half of them corrupted; the package's dump must match the Python
  reader's, or its error;
* **machine** (5): memory images of a whole table set, loaded through the
  RSDP;
* **pkenc**, **pkdec** (40 + 40), **nameenc**, **namedec** (40 + 40): the
  encodings both ways, including malformed bytes;
* **aml** (60): random definition blocks (names, methods, arithmetic,
  loops, packages, buffers, fields, references), built by the Python
  builder from the same random program, loaded and evaluated on both sides,
  with results, namespaces and host logs compared;
* **build** (30): the package's `AmlT` must give the bytes Python's encoder
  gives;
* **field** (25): field reads and writes of every access type and update
  rule against a Python bit-level model;
* **res** (25): resource templates read and written.

Seeds 1 to 60 were also run, and matched. When `$ACPI_TABLES` names a
directory of `acpidump -b` output, or `/sys/firmware/acpi/tables` is
readable (it needs root), `run.sh` adds those real tables: each read
through the registry, and the DSDT and SSDTs loaded, with the devices
compared with a static walk of the AML by `gen.py`. When `iasl` is
installed it also compiles ASL programs and compares the package's
evaluation of the AML with Python's.

The Python reference **shares an author with the package**: it was
written from the same reading of the specification, so it catches slips of
implementation but not a shared misreading. `iasl` and real firmware
tables do not share that weakness, but neither was available where the
package was written: there was no QEMU, no `iasl`, and the machine's
`/sys/firmware/acpi/tables` needed root, which was not used. The real-table
path was run on table files written by `gen.py`. `run.sh` exits 77 (skip)
when `python3` is missing, and after the Python cases pass when `iasl` is
missing. CI needs the apt package `acpica-tools` (`iasl`, and `acpidump`
to provide `$ACPI_TABLES`).

## Limitations

* The proofs reach `Octets` only through bytes' interface laws
  (`octets_to_of`, `octets_of_to`, `octets_append_list`,
  `octets_len_list`, `octets_split_at_append`, `octets_le32_round_trip`)
  and its list layer, and `W64` only through word64's public defs. The
  PkgLength and header proofs compute through `B.mask`, `B.byte` and
  `B.le32` on words split into their bits, as bytes' own proofs do, and
  the closed vectors compute through the package's code. The proofs in
  `PROOF_tables.bend` also use bytes' laws for fields read at offsets
  inside joined, cut and dropped bytes (`octets_le64_at_append_add`,
  `octets_drop_append_add`, `octets_concat_cons`, ...), and compute the
  tables' bodies on words split into their bits; a W64 field is split
  through word64's `parts_of` into `W64.from_parts` of its halves, which
  `le64` and `from_parts` then compute through word64's definitions.
  `PROOF_checksum.bend`, `PROOF_whole.bend` and `PROOF_rsdp.bend` reach
  bytes the same way (`octets_take_drop`, `octets_at_drop`,
  `octets_drop_append_add`, ...), and `PROOF_checksum.bend` computes
  `B.byte` of a word's low 8 bits on the word split into its bits.
  These proofs would need revisiting if those packages' representations
  changed; the laws would not change.
* The step-bound laws are stated for `AmlMemHost` only (above).
* The interpreter's semantics are tested, not proved.

## Speed and size

Measured natively (Bend 2.0.37, `bend file.bend -o prog`, WSL2, a shared
machine): a synthetic DSDT of 1,500 devices (120 KB of AML) is built with `AmlT`, loaded in 36,003
steps, and every device's `_STA` evaluated in 2.06 s, 26 MB peak RAM. Building `check.bend`
natively takes 40 to 75 s. The test runner builds in 72 s (2 GB) and runs the 409
cases in 0.04 s.

The namespace is a `Map` keyed by absolute path, so a lookup is
logarithmic in its size; name resolution walks up the scope (5.3). The
interpreter is a loop over steps: its depth does not grow with the
program, only its frame list does, by one per nested term or call. Lists
of entries, tables and resources are walked once each. Sizes and offsets
are `Nat`.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and of the order (`LAWS_order.bend`).

## Status

Bend 2.0.39, native (`VERDICT=1` with `scripts/check.sh`'s native runner):
`PROOF.bend`, `PROOF_tables.bend`, `PROOF_checksum.bend`,
`PROOF_whole.bend` and `PROOF_rsdp.bend` ALL PROOFS CHECK, `--verdict` ALL
PROOFS CHECK, `check.bend` passes, `ref/run.sh` 415 cases match (the Python reference's, and 6
programs compiled by `iasl`; real tables not tested), `scripts/deps.sh
acpi` ok.
