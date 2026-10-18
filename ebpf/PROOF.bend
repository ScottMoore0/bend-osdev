import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bpf/insn.bend as C
import ./insn.bend as I
import ./alu.bend as A
import ./memory.bend as M
import ./helpers.bend as H
import ./interp.bend as R
import ./cfg.bend as G
import ./verifier.bend as V
import ./ebpf.bend as E
import ./LAWS.bend as Laws

# Memory safety. A load or store fails when its byte range is out of bounds.
# load/store unfold to load.len/store.len on the region's length and area;
# with the length Some{l} and the in-bounds test False, the check fails.

def load_oob_len(len: Maybe<&2, U32>, area: M.EbpfArea, order: C.BpfOrder, addr: W.W64, s: I.EbpfSize, l: U32, hlen: {len == Some{l} : Maybe<&2, U32>}, hob: {M.ebpf_in_bounds(l, addr, M.EbpfSize.bytes(s)) == False{} : Bool}) -> {M.EbpfMem.load.len(len, area, order, addr, s) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfValue>}:
  %Equal.sym(Maybe<&2, U32>, len, Some{l}, hlen) : {M.EbpfMem.load.len(_, area, order, addr, s) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfValue>}
  %Equal.sym(Bool, M.ebpf_in_bounds(l, addr, M.EbpfSize.bytes(s)), False{}, hob) : {M.EbpfMem.load.chk(_, area, order, addr, s) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfValue>}
  {==}

def Laws.load_oob(m, r, addr, s, l, hlen, hob):
  load_oob_len(M.EbpfMem.region_len(m, r), M.EbpfMem.area(m, r), M.EbpfMem.order(m), addr, s, l, hlen, hob)

def store_oob_len(len: Maybe<&2, U32>, m: M.EbpfMem, r: M.EbpfRegion, area: M.EbpfArea, addr: W.W64, s: I.EbpfSize, v: M.EbpfValue, l: U32, hlen: {len == Some{l} : Maybe<&2, U32>}, hob: {M.ebpf_in_bounds(l, addr, M.EbpfSize.bytes(s)) == False{} : Bool}) -> {M.EbpfMem.store.len(len, m, r, area, addr, s, v) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfMem>}:
  %Equal.sym(Maybe<&2, U32>, len, Some{l}, hlen) : {M.EbpfMem.store.len(_, m, r, area, addr, s, v) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfMem>}
  %Equal.sym(Bool, M.ebpf_in_bounds(l, addr, M.EbpfSize.bytes(s)), False{}, hob) : {M.EbpfMem.store.chk(_, m, r, area, addr, s, v) == Fail{I.EbpfMemOutOfBounds{U32.to_nat(M.EbpfSize.bytes(s))}} : Result<&2, &2, I.EbpfMemError, M.EbpfMem>}
  {==}

def Laws.store_oob(m, r, addr, s, v, l, hlen, hob):
  store_oob_len(M.EbpfMem.region_len(m, r), m, r, M.EbpfMem.area(m, r), addr, s, v, l, hlen, hob)

# a stored program with a byte at offset max is refused (same shape as
# bend-osdev-bpf's octets_over_limit)
def Laws.octets_over_limit(max, order, o, b, e):
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(o, max), Some{b}, e) : {I.ebpf_of_octets.fits(_, max, order, o) == Fail{I.EbpfErrStoredTooLong{max}} : Result<&2, &2, I.EbpfError, List<&2, I.EbpfRaw>>}
  {==}

# Witnesses

def Laws.witness_load_oob():
  (M.EbpfMem.new(C.BpfLittle{}, B.Octets.zeros(4n), B.Octets.empty(), Nil{}), ({==}, {==}))

def Laws.witness_octets_over():
  (B.Octets.zeros(9n), {==})

# RFC arithmetic, by computation

def Laws.alu_add_wraps():
  {==}

def Laws.alu_sub_borrows():
  {==}

def Laws.alu_add32_zext():
  {==}

def Laws.alu_lsh_masks():
  {==}

def Laws.alu_arsh_signed():
  {==}

def Laws.alu_sdiv_neg():
  {==}

def Laws.alu_bswap64():
  {==}

# encode/decode round trip, over the sample program

def Laws.round_trip():
  {==}

# the interpreter and the verifier, by computation

def Laws.run_mov():
  {==}

def Laws.run_stack():
  {==}

def Laws.run_divzero():
  {==}

def Laws.verify_accepts():
  {==}

def Laws.verify_rejects_uninit():
  {==}

def Laws.verify_rejects_oob():
  {==}

def Laws.verify_rejects_leak():
  {==}
