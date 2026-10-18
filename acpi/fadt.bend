# bend-osdev-acpi, fadt.bend: the Fixed ACPI Description Table, "FACP"
# (ACPI 6.5, section 5.2.9). Every field of revision 6 (276
# bytes), grouped by the version that added it; a group is present when the
# table's length covers all of it:
#
#   bytes    group                                           since
#   36-115   AcpiFadtCore: FIRMWARE_CTRL, DSDT, the ACPI 1.0  ACPI 1.0 (116)
#            register blocks and lengths, latencies, RTC
#            alarms, IAPC_BOOT_ARCH, Flags
#   116-243  AcpiFadtExt: RESET_REG, RESET_VALUE,             ACPI 2.0 (244)
#            ARM_BOOT_ARCH, FADT Minor Version, X_FIRMWARE_CTRL,
#            X_DSDT and the eight X_ register blocks
#   244-267  AcpiFadtSleep: SLEEP_CONTROL_REG,                ACPI 5.0 (268)
#            SLEEP_STATUS_REG
#   268-275  Hypervisor Vendor Identity                       ACPI 6.0 (276)
#
# (ARM_BOOT_ARCH and the minor version came in ACPI 5.1 in bytes that were
# reserved before, so older tables read 0 there.) Section 5.2.9 says the X_
# forms supersede the 32-bit ones when their address is non-zero; the
# AcpiFadt.* queries below choose that way.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./fields.bend as F
import ./gas.bend as G

# the ACPI 1.0 register blocks: I/O port addresses
type AcpiFadtBlocks is Data:
  AcpiFadtBlocks{pm1a_evt: U32, pm1b_evt: U32, pm1a_cnt: U32, pm1b_cnt: U32, pm2_cnt: U32, pm_tmr: U32, gpe0: U32, gpe1: U32}

# their lengths in bytes, and GPE1_BASE
type AcpiFadtLens is Data:
  AcpiFadtLens{pm1_evt: U32, pm1_cnt: U32, pm2_cnt: U32, pm_tmr: U32, gpe0: U32, gpe1: U32, gpe1_base: U32}

# bytes 36 to 115. int_model is byte 44, reserved since ACPI 2.0
type AcpiFadtCore is Data:
  AcpiFadtCore{firmware_ctrl: U32, dsdt: U32, int_model: U32, pm_profile: U32, sci_int: U32, smi_cmd: U32, acpi_enable: U32, acpi_disable: U32, s4bios_req: U32, pstate_cnt: U32, blocks: AcpiFadtBlocks, lens: AcpiFadtLens, cst_cnt: U32, p_lvl2_lat: U32, p_lvl3_lat: U32, flush_size: U32, flush_stride: U32, duty_offset: U32, duty_width: U32, day_alrm: U32, mon_alrm: U32, century: U32, iapc_boot_arch: U32, flags: U32}

# the X_ register blocks (Generic Address Structures)
type AcpiFadtX is Data:
  AcpiFadtX{pm1a_evt: G.AcpiGas, pm1b_evt: G.AcpiGas, pm1a_cnt: G.AcpiGas, pm1b_cnt: G.AcpiGas, pm2_cnt: G.AcpiGas, pm_tmr: G.AcpiGas, gpe0: G.AcpiGas, gpe1: G.AcpiGas}

# bytes 116 to 243
type AcpiFadtExt is Data:
  AcpiFadtExt{reset_reg: G.AcpiGas, reset_value: U32, arm_boot_arch: U32, minor_version: U32, x_firmware_ctrl: W.W64, x_dsdt: W.W64, x: AcpiFadtX}

# bytes 244 to 267
type AcpiFadtSleep is Data:
  AcpiFadtSleep{control: G.AcpiGas, status: G.AcpiGas}

type AcpiFadt is Data:
  AcpiFadt{header: H.AcpiHeader, core: AcpiFadtCore, ext: Maybe<&2, AcpiFadtExt>, sleep: Maybe<&2, AcpiFadtSleep>, hypervisor: Maybe<&2, W.W64>}

# Reading (o: the whole table; offsets from its start)

def fadt.core(+o: B.Octets) -> AcpiFadtCore:
  +blocks = {AcpiFadtBlocks{F.AcpiF.u32(o, 56n), F.AcpiF.u32(o, 60n), F.AcpiF.u32(o, 64n), F.AcpiF.u32(o, 68n), F.AcpiF.u32(o, 72n), F.AcpiF.u32(o, 76n), F.AcpiF.u32(o, 80n), F.AcpiF.u32(o, 84n)} : AcpiFadtBlocks}
  +lens = {AcpiFadtLens{F.AcpiF.u8(o, 88n), F.AcpiF.u8(o, 89n), F.AcpiF.u8(o, 90n), F.AcpiF.u8(o, 91n), F.AcpiF.u8(o, 92n), F.AcpiF.u8(o, 93n), F.AcpiF.u8(o, 94n)} : AcpiFadtLens}
  AcpiFadtCore{F.AcpiF.u32(o, 36n), F.AcpiF.u32(o, 40n), F.AcpiF.u8(o, 44n), F.AcpiF.u8(o, 45n), F.AcpiF.u16(o, 46n), F.AcpiF.u32(o, 48n), F.AcpiF.u8(o, 52n), F.AcpiF.u8(o, 53n), F.AcpiF.u8(o, 54n), F.AcpiF.u8(o, 55n), blocks, lens, F.AcpiF.u8(o, 95n), F.AcpiF.u16(o, 96n), F.AcpiF.u16(o, 98n), F.AcpiF.u16(o, 100n), F.AcpiF.u16(o, 102n), F.AcpiF.u8(o, 104n), F.AcpiF.u8(o, 105n), F.AcpiF.u8(o, 106n), F.AcpiF.u8(o, 107n), F.AcpiF.u8(o, 108n), F.AcpiF.u16(o, 109n), F.AcpiF.u32(o, 112n)}

def fadt.x(+o: B.Octets) -> AcpiFadtX:
  AcpiFadtX{G.AcpiGas.at(o, 148n), G.AcpiGas.at(o, 160n), G.AcpiGas.at(o, 172n), G.AcpiGas.at(o, 184n), G.AcpiGas.at(o, 196n), G.AcpiGas.at(o, 208n), G.AcpiGas.at(o, 220n), G.AcpiGas.at(o, 232n)}

def fadt.ext(has: Bool, +o: B.Octets) -> Maybe<&2, AcpiFadtExt>:
  match has:
    case False{}:
      None{}
    case True{}:
      Some{AcpiFadtExt{G.AcpiGas.at(o, 116n), F.AcpiF.u8(o, 128n), F.AcpiF.u16(o, 129n), F.AcpiF.u8(o, 131n), F.AcpiF.u64(o, 132n), F.AcpiF.u64(o, 140n), fadt.x(o)}}

def fadt.sleep(has: Bool, +o: B.Octets) -> Maybe<&2, AcpiFadtSleep>:
  match has:
    case False{}:
      None{}
    case True{}:
      Some{AcpiFadtSleep{G.AcpiGas.at(o, 244n), G.AcpiGas.at(o, 256n)}}

def fadt.hyp(has: Bool, +o: B.Octets) -> Maybe<&2, W.W64>:
  match has:
    case False{}:
      None{}
    case True{}:
      Some{F.AcpiF.u64(o, 268n)}

def fadt.read(ok: Bool, +h: H.AcpiHeader, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiFadt>:
  match ok:
    case False{}:
      Fail{E.AcpiTooShort{116n, B.Octets.len(o)}}
    case True{}:
      +n = B.Octets.len(o)
      Done{AcpiFadt{h, fadt.core(o), fadt.ext(Nat.is_le(244n, n), o), fadt.sleep(Nat.is_le(268n, n), o), fadt.hyp(Nat.is_le(276n, n), o)}}

# a checked table as an FADT (at least the 116 bytes of ACPI 1.0)
def AcpiFadt.of_sdt(t: H.AcpiSdt) -> Result<&2, &2, E.AcpiError, AcpiFadt>:
  match t:
    case H.AcpiSdt{+h, body}:
      +o = B.Octets.append(H.AcpiHeader.encode(h), body)
      fadt.read(Nat.is_le(116n, B.Octets.len(o)), h, o)

def fadt.parse(r: Result<&2, &2, E.AcpiError, H.AcpiSdt>) -> Result<&2, &2, E.AcpiError, AcpiFadt>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      AcpiFadt.of_sdt(t)

# the FADT at the front of o: checked (length, checksum, signature "FACP"),
# then read
def AcpiFadt.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AcpiFadt>:
  fadt.parse(H.AcpiSdt.parse_sig(B.Octets.of_string("FACP"), o))

# Fields

def AcpiFadt.core(f: AcpiFadt) -> AcpiFadtCore:
  match f:
    case AcpiFadt{h, c, x, s, v}:
      c

def AcpiFadt.ext(f: AcpiFadt) -> Maybe<&2, AcpiFadtExt>:
  match f:
    case AcpiFadt{h, c, x, s, v}:
      x

def AcpiFadt.sleep(f: AcpiFadt) -> Maybe<&2, AcpiFadtSleep>:
  match f:
    case AcpiFadt{h, c, x, s, v}:
      s

def AcpiFadt.hypervisor(f: AcpiFadt) -> Maybe<&2, W.W64>:
  match f:
    case AcpiFadt{h, c, x, s, v}:
      v

# The fixed register blocks, by name
type AcpiFadtBlock is Data:
  AcpiFadtPm1aEvt{}
  AcpiFadtPm1bEvt{}
  AcpiFadtPm1aCnt{}
  AcpiFadtPm1bCnt{}
  AcpiFadtPm2Cnt{}
  AcpiFadtPmTmr{}
  AcpiFadtGpe0{}
  AcpiFadtGpe1{}

def fadt.legacy(b: AcpiFadtBlocks, l: AcpiFadtLens, k: AcpiFadtBlock) -> G.AcpiGas:
  match b l:
    case AcpiFadtBlocks{e1a, e1b, c1a, c1b, c2, tm, g0, g1} AcpiFadtLens{le, lc, l2, lt, lg0, lg1, gb}:
      match k:
        case AcpiFadtPm1aEvt{}:
          G.AcpiGas.io_block(e1a, le)
        case AcpiFadtPm1bEvt{}:
          G.AcpiGas.io_block(e1b, le)
        case AcpiFadtPm1aCnt{}:
          G.AcpiGas.io_block(c1a, lc)
        case AcpiFadtPm1bCnt{}:
          G.AcpiGas.io_block(c1b, lc)
        case AcpiFadtPm2Cnt{}:
          G.AcpiGas.io_block(c2, l2)
        case AcpiFadtPmTmr{}:
          G.AcpiGas.io_block(tm, lt)
        case AcpiFadtGpe0{}:
          G.AcpiGas.io_block(g0, lg0)
        case AcpiFadtGpe1{}:
          G.AcpiGas.io_block(g1, lg1)

def fadt.xblock(x: AcpiFadtX, k: AcpiFadtBlock) -> G.AcpiGas:
  match x:
    case AcpiFadtX{e1a, e1b, c1a, c1b, c2, tm, g0, g1}:
      match k:
        case AcpiFadtPm1aEvt{}:
          e1a
        case AcpiFadtPm1bEvt{}:
          e1b
        case AcpiFadtPm1aCnt{}:
          c1a
        case AcpiFadtPm1bCnt{}:
          c1b
        case AcpiFadtPm2Cnt{}:
          c2
        case AcpiFadtPmTmr{}:
          tm
        case AcpiFadtGpe0{}:
          g0
        case AcpiFadtGpe1{}:
          g1

def fadt.core.flags(c: AcpiFadtCore) -> U32:
  match c:
    case AcpiFadtCore{fc, d, im, pp, sci, smi, en, dis, s4, ps, bl, ln, cst, l2, l3, fs, fst, doff, dw, da, ma, ce, ia, fl}:
      fl

def fadt.core.dsdt(c: AcpiFadtCore) -> U32:
  match c:
    case AcpiFadtCore{fc, d, im, pp, sci, smi, en, dis, s4, ps, bl, ln, cst, l2, l3, fs, fst, doff, dw, da, ma, ce, ia, fl}:
      d

def fadt.core.facs(c: AcpiFadtCore) -> U32:
  match c:
    case AcpiFadtCore{fc, d, im, pp, sci, smi, en, dis, s4, ps, bl, ln, cst, l2, l3, fs, fst, doff, dw, da, ma, ce, ia, fl}:
      fc

def fadt.core.legacy(k: AcpiFadtBlock, c: AcpiFadtCore) -> G.AcpiGas:
  match c:
    case AcpiFadtCore{fc, d, im, pp, sci, smi, en, dis, s4, ps, bl, ln, cst, l2, l3, fs, fst, doff, dw, da, ma, ce, ia, fl}:
      fadt.legacy(bl, ln, k)

def AcpiFadt.flags(f: AcpiFadt) -> U32:
  fadt.core.flags(AcpiFadt.core(f))

# Flags, bit numbers: 0 WBINVD, 1 WBINVD_FLUSH, 2 PROC_C1,
# 3 P_LVL2_UP, 4 PWR_BUTTON, 5 SLP_BUTTON, 6 FIX_RTC, 7 RTC_S4,
# 8 TMR_VAL_EXT, 9 DCK_CAP, 10 RESET_REG_SUP, 11 SEALED_CASE, 12 HEADLESS,
# 13 CPU_SW_SLP, 14 PCI_EXP_WAK, 15 USE_PLATFORM_CLOCK,
# 16 S4_RTC_STS_VALID, 17 REMOTE_POWER_ON_CAPABLE, 18 FORCE_APIC_CLUSTER_MODEL,
# 19 FORCE_APIC_PHYSICAL_DESTINATION_MODE, 20 HW_REDUCED_ACPI,
# 21 LOW_POWER_S0_IDLE_CAPABLE, 22-23 PERSISTENT_CPU_CACHES
def AcpiFadt.flag(+f: AcpiFadt, bit: Nat) -> Bool:
  F.AcpiF.bit(AcpiFadt.flags(f), bit)

def AcpiFadt.hw_reduced(+f: AcpiFadt) -> Bool:
  AcpiFadt.flag(f, 20n)

def fadt.pick64(nz: Bool, +x: W.W64, lo: U32) -> W.W64:
  match nz:
    case True{}:
      x
    case False{}:
      W.W64.from_u32(lo)

def fadt.dsdt.go(m: Maybe<&2, AcpiFadtExt>, +lo: U32) -> W.W64:
  match m:
    case None{}:
      W.W64.from_u32(lo)
    case Some{AcpiFadtExt{rr, rv, ab, mv, xfc, +xd, xx}}:
      fadt.pick64(Bool.not(W.W64.is_zero(xd)), xd, lo)

def fadt.facs.go(m: Maybe<&2, AcpiFadtExt>, +lo: U32) -> W.W64:
  match m:
    case None{}:
      W.W64.from_u32(lo)
    case Some{AcpiFadtExt{rr, rv, ab, mv, +xfc, xd, xx}}:
      fadt.pick64(Bool.not(W.W64.is_zero(xfc)), xfc, lo)

# the DSDT's address: X_DSDT when present and non-zero, else DSDT
def AcpiFadt.dsdt_address(+f: AcpiFadt) -> W.W64:
  fadt.dsdt.go(AcpiFadt.ext(f), fadt.core.dsdt(AcpiFadt.core(f)))

# the FACS's address: X_FIRMWARE_CTRL when present and non-zero, else
# FIRMWARE_CTRL (zero on hardware-reduced systems without a FACS)
def AcpiFadt.facs_address(+f: AcpiFadt) -> W.W64:
  fadt.facs.go(AcpiFadt.ext(f), fadt.core.facs(AcpiFadt.core(f)))

def fadt.choose(nz: Bool, +x: G.AcpiGas, +legacy: G.AcpiGas) -> G.AcpiGas:
  match nz:
    case True{}:
      x
    case False{}:
      legacy

def fadt.block.go(+k: AcpiFadtBlock, m: Maybe<&2, AcpiFadtExt>, +legacy: G.AcpiGas) -> G.AcpiGas:
  match m:
    case None{}:
      legacy
    case Some{AcpiFadtExt{rr, rv, ab, mv, xfc, xd, xx}}:
      +g = fadt.xblock(xx, k)
      fadt.choose(Bool.not(G.AcpiGas.is_null(g)), g, legacy)

# a register block as a Generic Address: the X_ block when present and its
# address is non-zero, else the 32-bit port with its length (a system I/O
# block; address 0 when the block is absent)
def AcpiFadt.block(+f: AcpiFadt, +k: AcpiFadtBlock) -> G.AcpiGas:
  fadt.block.go(k, AcpiFadt.ext(f), fadt.core.legacy(k, AcpiFadt.core(f)))

# Writing: the 276 bytes of revision 6 (absent groups written as zeros)

def fadt.u8(v: U32) -> B.Octets:
  B.Octets.of_list([v])

def fadt.enc.core(c: AcpiFadtCore) -> B.Octets:
  match c:
    case AcpiFadtCore{fc, d, im, pp, sci, smi, en, dis, s4, ps, AcpiFadtBlocks{e1a, e1b, c1a, c1b, c2, tm, g0, g1}, AcpiFadtLens{le, lc, l2, lt, lg0, lg1, gb}, cst, p2, p3, fs, fst, doff, dw, da, ma, ce, ia, fl}:
      B.Octets.concat([B.Octets.le32(fc), B.Octets.le32(d), fadt.u8(im), fadt.u8(pp), B.Octets.le16(sci), B.Octets.le32(smi), fadt.u8(en), fadt.u8(dis), fadt.u8(s4), fadt.u8(ps), B.Octets.le32(e1a), B.Octets.le32(e1b), B.Octets.le32(c1a), B.Octets.le32(c1b), B.Octets.le32(c2), B.Octets.le32(tm), B.Octets.le32(g0), B.Octets.le32(g1), B.Octets.of_list([le, lc, l2, lt, lg0, lg1, gb, cst]), B.Octets.le16(p2), B.Octets.le16(p3), B.Octets.le16(fs), B.Octets.le16(fst), B.Octets.of_list([doff, dw, da, ma, ce]), B.Octets.le16(ia), B.Octets.zeros(1n), B.Octets.le32(fl)])

def fadt.enc.ext(m: Maybe<&2, AcpiFadtExt>) -> B.Octets:
  match m:
    case None{}:
      B.Octets.zeros(128n)
    case Some{AcpiFadtExt{rr, rv, ab, mv, xfc, xd, AcpiFadtX{e1a, e1b, c1a, c1b, c2, tm, g0, g1}}}:
      B.Octets.concat([G.AcpiGas.encode(rr), fadt.u8(rv), B.Octets.le16(ab), fadt.u8(mv), B.Octets.le64(xfc), B.Octets.le64(xd), G.AcpiGas.encode(e1a), G.AcpiGas.encode(e1b), G.AcpiGas.encode(c1a), G.AcpiGas.encode(c1b), G.AcpiGas.encode(c2), G.AcpiGas.encode(tm), G.AcpiGas.encode(g0), G.AcpiGas.encode(g1)])

def fadt.enc.sleep(m: Maybe<&2, AcpiFadtSleep>) -> B.Octets:
  match m:
    case None{}:
      B.Octets.zeros(24n)
    case Some{AcpiFadtSleep{c, s}}:
      B.Octets.append(G.AcpiGas.encode(c), G.AcpiGas.encode(s))

def fadt.enc.hyp(m: Maybe<&2, W.W64>) -> B.Octets:
  match m:
    case None{}:
      B.Octets.zeros(8n)
    case Some{v}:
      B.Octets.le64(v)

# the table (signature "FACP", revision as in the header, length 276,
# checksum computed)
def AcpiFadt.build(f: AcpiFadt) -> B.Octets:
  match f:
    case AcpiFadt{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}, core, x, sl, hv}:
      H.AcpiSdt.build(H.AcpiHeader{B.Octets.of_string("FACP"), l, r, c, o, t, orv, ci, cr}, B.Octets.concat([fadt.enc.core(core), fadt.enc.ext(x), fadt.enc.sleep(sl), fadt.enc.hyp(hv)]))
