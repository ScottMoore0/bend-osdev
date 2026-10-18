# bend-osdev-ebpf: an eBPF interpreter and verifier, written from RFC 9669
# ("BPF Instruction Set Architecture (ISA)", T. Thaler, Ed., 2024) and the
# Linux kernel's verifier documentation page (Documentation/bpf/verifier.rst,
# a documentation page, used as documentation; no kernel source was read).
#
# This entry file ties the pieces together: it decodes a stored program, runs
# the control-flow and register/stack/bounds verifier, and runs the verified
# program in the interpreter. The pieces live in:
#   insn.bend      instructions, encoding and decoding, stored programs
#   alu.bend       the arithmetic of each instruction (RFC 9669, 4)
#   memory.bend    the region + offset memory model, bounds checked
#   helpers.bend   the helper-call interface and a standard table
#   interp.bend    the interpreter: registers, frames, the step loop
#   cfg.bend       the control-flow checks (verifier, first half)
#   verifier.bend  register-type tracking, stack init, bounds (second half)
# The public interface is what this README lists; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../bpf/insn.bend as C
import ./insn.bend as I
import ./alu.bend as A
import ./memory.bend as M
import ./helpers.bend as H
import ./interp.bend as R
import ./cfg.bend as G
import ./verifier.bend as V

def ebpf_prepare.checked(v: Result<&2, &2, I.EbpfError, Unit>, prog: List<&2, I.EbpfInsn>) -> Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>:
  match v:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{prog}

def ebpf_prepare.after(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, opts: V.EbpfVerifyOptions, d: Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>) -> Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>:
  match d:
    case Fail{e}:
      Fail{e}
    case Done{+prog}:
      ebpf_prepare.checked(V.ebpf_verify_with(~sigs, opts, prog), prog)

# Prepare: decode a stored program and verify it (control flow, then
# register types, stack init and bounds), with helper signatures ~sigs and
# these options. The verified instructions, ready to run, or the failure.
def ebpf_prepare_with(~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, opts: V.EbpfVerifyOptions, raws: List<&2, I.EbpfRaw>) -> Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>:
  ebpf_prepare.after(~sigs, opts, I.ebpf_decode(raws))

# the same, with the standard helper table's signatures and default options
def ebpf_prepare(raws: List<&2, I.EbpfRaw>) -> Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>:
  ebpf_prepare_with(~H.ebpf_helper_sigs.std, V.EbpfVerifyOptions.default(), raws)

def ebpf_load_and_run.go(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, d: Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>, fuel: Nat, mem: M.EbpfMem) -> Result<&2, &2, I.EbpfError, R.EbpfOutcome>:
  match d:
    case Fail{e}:
      Fail{e}
    case Done{prog}:
      Done{R.ebpf_run_with(~helpers, R.ebpf_max_frames(), fuel, prog, mem)}

# Decode, verify and run a stored program over memory, with a helper table
# ~helpers and its signatures ~sigs (which must agree), the verifier options,
# and the step limit. (A caller that wants to run an already-decoded,
# already-verified program calls R.ebpf_run_with directly.)
def ebpf_load_and_run(~helpers: U32 -> List<&2, M.EbpfValue> -> M.EbpfMem -> H.EbpfHelperOut, ~sigs: U32 -> Maybe<&2, H.EbpfHelperSig>, opts: V.EbpfVerifyOptions, fuel: Nat, raws: List<&2, I.EbpfRaw>, mem: M.EbpfMem) -> Result<&2, &2, I.EbpfError, R.EbpfOutcome>:
  ebpf_load_and_run.go(~helpers, ebpf_prepare_with(~sigs, opts, raws), fuel, mem)
