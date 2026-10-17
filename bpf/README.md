# bend-osdev-bpf

Classic BPF (the BSD Packet Filter) and seccomp filters: the instruction
encoding, the validator, the interpreter, and seccomp's input, actions and
filter stacking.

## Specifications

* The BSD `bpf(4)` manual page (the instruction set, its encoding as
  `struct bpf_insn` / `struct sock_filter`, the validation rules, and the
  EXAMPLES section), and S. McCanne and V. Jacobson, "The BSD Packet Filter:
  A New Architecture for User-level Packet Capture", USENIX Winter 1993.
* The Linux `seccomp(2)` manual page: `struct seccomp_data`, the
  `SECCOMP_RET_*` actions, their precedence when several filters are
  installed, `MAX_INSNS_PER_PATH`, and its EXAMPLES section.

No GPL source was read (neither the Linux kernel's filter or seccomp code nor
libseccomp). Where the documents are silent, the running kernel was observed
by executing filters (see Tests), and the choice is listed under Choices.

**Where the examples come from.** The seccomp(2) example program, its
constants (`AUDIT_ARCH_X86_64` 0xC000003E, `AUDIT_ARCH_I386` 0x40000003,
`X32_SYSCALL_BIT` 0x40000000, errno 99) and its runs (execve 59, write 1,
preadv 295) were checked against the installed manual page (man-pages,
`/usr/share/man/man2/seccomp.2.gz`). Its instruction [3] is
`JGT upper_nr_limit` with `upper_nr_limit = X32_SYSCALL_BIT - 1`, as the page
has it. The page's prose says another architecture makes system calls fail
with ENOSYS, but its program answers `SECCOMP_RET_KILL_PROCESS`; the vectors
follow the program. The three bpf(4) examples (RARP, the IP host pair, TCP
finger) were written from the FreeBSD/OpenBSD bpf(4) page as remembered (the
page is not installed here), and are checked only by the independent Python
model and, for the instruction semantics, the kernel. `ETHERTYPE_REVARP` is
0x8035.

## Files and public interface

Everything not listed here is internal.

| File | Holds |
|---|---|
| `insn.bend` | instructions: `BpfRaw` (struct sock_filter), `BpfOp` (decoded), encoding and decoding, stored programs as `Octets`, `BpfError` |
| `validate.bend` | `BpfValidateOptions`, `bpf_validate_with`, `bpf_validate`, `bpf_prepare_with`, `bpf_prepare`, `bpf_maxinsns` |
| `bpf.bend` (entry) | the interpreter: `BpfInput`, `bpf_packet`, `bpf_run` |
| `seccomp.bend` | `SeccompData`, `SeccompAction`, `seccomp_combine`, `seccomp_validate_with`, `seccomp_validate`, `seccomp_run`, `seccomp_eval`, `seccomp_install`, `SeccompLimits` |

### insn.bend

| Def or type | Meaning |
|---|---|
| `BpfRaw{code, jt, jf, k}` | one `struct sock_filter`; open type |
| `bpf_stmt(code, k)`, `bpf_jump(code, k, jt, jf)` | the C macros `BPF_STMT` and `BPF_JUMP` |
| `BpfOp` | a decoded instruction (open type): `BpfLdAbs{size, k}`, `BpfLdInd{size, k}`, `BpfLdImm{k}`, `BpfLdLen{}`, `BpfLdMem{k}`, `BpfLdxImm{k}`, `BpfLdxMem{k}`, `BpfLdxLen{}`, `BpfLdxMsh{k}`, `BpfSt{k}`, `BpfStx{k}`, `BpfAlu{op, src}`, `BpfNeg{}`, `BpfJa{k}`, `BpfJmp{cond, src, jt, jf}`, `BpfRet{rval}`, `BpfTax{}`, `BpfTxa{}` |
| `BpfSize` (`BpfW` `BpfH` `BpfB`), `BpfAluOp` (`BpfAdd` … `BpfXor`), `BpfCond` (`BpfJeq` `BpfJgt` `BpfJge` `BpfJset`), `BpfSrc` (`BpfK{k}`, `BpfX{}`), `BpfRval` (`BpfRetK{k}`, `BpfRetA{}`) | the parts of an instruction (open types) |
| `BpfOp.encode(op)`, `BpfRaw.decode(r)` | one instruction; `decode` answers `None` for an opcode classic BPF does not define |
| `bpf_encode(ops)`, `bpf_decode(raws)` | a program; `bpf_decode` fails with `BpfErrBadCode{pc, code}` |
| `BpfOrder` (`BpfBig{}`, `BpfLittle{}`) | a byte order |
| `bpf_to_octets(order, raws)`, `bpf_of_octets(order, o)` | a stored program, 8 bytes per instruction |
| `bpf_memwords()` | 16, the size of the scratch memory |
| `BpfError`, `BpfError.show` | every failure, one constructor each (open type) |

### validate.bend

| Def | Meaning |
|---|---|
| `BpfValidateOptions{max_insns, require_mem_init}` | the validator's choices (open type) |
| `BpfValidateOptions.default()` | what Linux checks: 4096 instructions, scratch memory written before it is read |
| `BpfValidateOptions.permissive()` | bpf(4)'s rules alone: 4096 instructions, scratch memory may be read first |
| `bpf_validate_with(opts, ops)` | `Done{Unit{}}`, or the first rule broken: `BpfErrEmpty`, `BpfErrTooLong{len}`, then per instruction in order `BpfErrScratch{pc}` (index ≥ 16), `BpfErrDivZero{pc}` (division or modulo by a constant 0), `BpfErrJumpField{pc}` (`jt` or `jf` over 255), `BpfErrJump{pc}` (a jump past the last instruction), `BpfErrNoReturn{pc}` (the last instruction is not a return), then, if `require_mem_init`, `BpfErrMemInit{pc}` (a scratch read not preceded by a write on every path) |
| `bpf_validate(limit, ops)` | the default options with this instruction limit |
| `bpf_maxinsns()` | 4096 (`BPF_MAXINSNS`), the usual `limit` |
| `bpf_prepare_with(opts, raws)`, `bpf_prepare(limit, raws)` | decode, then validate: the instructions, ready to run |

### bpf.bend

| Def or type | Meaning |
|---|---|
| `BpfInput{order, data}` | what a filter runs over: bytes (`Octets`) and the byte order of its loads |
| `bpf_packet(o)` | a packet: big-endian loads |
| `bpf_run(inp, ops)` | the program's answer. A load outside the input and a division or modulo by `X = 0` end it with 0. Its errors (`BpfErrFellOff`, `BpfErrBadScratch{k}`) are what only an unvalidated program can do |

### seccomp.bend

| Def or type | Meaning |
|---|---|
| `SeccompData{nr, arch, ip, a0, …, a5}` | `struct seccomp_data` (`ip` and the arguments are `W64`) |
| `SeccompData.to_octets(order, d)`, `SeccompData.input(order, d)` | its 64 bytes; the `BpfInput` a filter runs over |
| `seccomp_order()` | little-endian (x86-64, arm64) |
| `seccomp_data_size()`, `seccomp_arch_x86_64()`, `seccomp_arch_i386()`, `seccomp_arch_aarch64()`, `seccomp_x32_syscall_bit()` | constants |
| `SeccompAction` | `SeccompKillProcess{}`, `SeccompKillThread{}`, `SeccompTrap{data}`, `SeccompErrno{data}`, `SeccompUserNotif{}`, `SeccompTrace{data}`, `SeccompLog{}`, `SeccompAllow{}` (open type) |
| `SeccompAction.of_u32(v)`, `.to_u32(a)`, `.clip(a)`, `.rank(a)`, `.show(a)` | a return value's action (an unnamed action is `KILL_PROCESS`); the return value of an action; the data cut to 16 bits; the precedence, 0 (KILL_PROCESS) to 7 (ALLOW) |
| `seccomp_combine(newer, older)` | two filters' answers together: the higher precedence, the newer on a tie |
| `seccomp_validate_with(opts, ops)`, `seccomp_validate(limit, ops)` | `bpf_validate_with` (the default options for `seccomp_validate`), then `BpfErrSeccompLoad{pc}` for any load but an aligned 32-bit `BPF_ABS` inside `seccomp_data`, and `BpfErrSeccompInsn{pc}` for `BPF_MOD` |
| `seccomp_run(order, ops, d)` | one filter's action |
| `seccomp_eval(stack, order, d)` | a stack of filters, newest first: every filter runs, and the answers combine; no filter allows |
| `SeccompLimits{filter, path}`, `seccomp_limits()` | the limits on one filter and on a thread's filters together (4096 and `MAX_INSNS_PER_PATH`, 32768, where each installed filter counts 4 more) |
| `seccomp_install(lim, stack, raws)` | decode, validate for seccomp, check the path limit (`BpfErrPathTooLong{total}`), and push |

## Choices where the documents are silent

* A, X and the scratch memory start at 0.
* Scratch memory written before it is read (`require_mem_init`, on in
  `BpfValidateOptions.default()`): Linux refuses a filter that may read a
  scratch slot before writing it, socket filters and seccomp alike; bpf(4)
  has no such rule, so `permissive()` turns it off. "May" is decided over
  paths from the start, where code after a jump is reached only by the jumps
  to it, but the instruction after a return counts as reached from the
  return: that is what the running kernel does (two vectors and three fixed
  kernel cases pin both).
* A shift by 32 or more gives 0. `BPF_IND` offsets `X + k` do not wrap.
* `BPF_MOD` and `BPF_XOR` are included (later BSDs and Linux have them);
  the running Linux kernel refuses `BPF_MOD` in a seccomp filter, so
  `seccomp_validate` does too.
* Data of 16 bits: `to_u32` keeps the low 16 bits of an action's data.
* Precedence uses the action each filter's value decodes to, so an unnamed
  action counts as `KILL_PROCESS`, as seccomp(2) says it is treated.

## Extension points

* **The input is a parameter:** `BpfInput` pairs any `Octets` with the byte
  order of the loads; `bpf_packet` and `SeccompData.input` are the two usual
  ones. Another kind of input (another context struct) is another
  `BpfInput`.
* **Validation is a parameter:** `BpfValidateOptions` (the instruction
  limit, and the scratch-memory rule) with `default()` matching Linux and
  `permissive()` matching bpf(4); `bpf_validate(limit, …)` is the default
  with another limit. `SeccompLimits` with `seccomp_limits()`.
* **The byte order** of stored programs and of seccomp data is a parameter
  (`BpfOrder`), with `seccomp_order()` the usual host's.
* **Programs can be built either way:** as raw `BpfRaw` lines (the C
  macros) or as `BpfOp` values; `bpf_decode`/`bpf_encode` convert, with a law
  that they round-trip.
* **A fast interpreter** (or a JIT) can be added beside `bpf_run`, kept to it
  by a law or the differential test. The interpreter is the reference: one
  pass over the instructions, each visited at most once.
* **Streaming:** none. A filter reads its input at any offset, so it needs
  the whole input, as BPF itself does.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer). For every input:

* `validated_returns`: for every set of options, program and input, if
  `bpf_validate_with` accepts the program (so also `bpf_validate`), `bpf_run` answers `Done` (the run
  always ends in a return value; it never falls off the end or misuses
  scratch memory). `seccomp_validated_acts` is the same for seccomp filters.
* `validated_ignores_tail`: instructions appended after a validated program
  change nothing (the run never goes past its last instruction).
* `ret_k`: the program `RET k` answers `k`, for every `k` and input.
* `ja_skips`, `jeq_taken_skips`, `jeq_not_taken_skips`: jumps move forward
  over exactly the instructions they skip, whatever those are: `JA k`
  followed by any `k` instructions and then `rest` answers what `rest` does;
  the same for a conditional jump that starts a program (A is 0), taken
  (`JEQ #0`, over `jt` instructions) and not taken (`JEQ #1`, over `jf`).
* `insn_round_trip`, `program_round_trip`: decoding the encoding of any
  instruction or program gives it back.
* `most_restrictive`: for every pair of actions, the combined precedence is
  the higher of the two (`rank` is the minimum); `combine_newer` and
  `combine_older` characterise `seccomp_combine` completely (the newer wins
  ties, with its data); `combine_assoc`: the grouping of a stack does not
  matter; `action_round_trip`: `of_u32(to_u32(a)) == clip(a)`.

Vectors: the three `bpf(4)` example filters on hand-built frames (RARP,
the IP host pair, TCP finger with `MSH` and `IND`), the `seccomp(2)` example
filter (execve, write and preadv as on the page, another architecture, an x32
call), each validation error including the scratch-memory rule (on a path,
after a jump, after a return, and turned off), a bad opcode, the stored
bytes, filter stacking (ties, precedence, the empty stack), an unnamed
action, and the path limit.

Witnesses: every hypothesis of a law holds for some input, so no law is
vacuous: `witness_skip_length` (a three-instruction `skipped` list of length
`to_nat(3)`, the form of the hypotheses of `ja_skips`, `jeq_taken_skips` and
`jeq_not_taken_skips`), `witness_rank_le` (for `combine_newer`),
`witness_rank_lt` (for `combine_older`), and `validate_accepts`,
`validate_permissive` and `seccomp_example_valid` (for the validation
hypotheses).

## Tests

`check.bend` prints the documentation's examples. `ref/run.sh` runs
`ref/gen.py` (seed 2026), which writes 1070 cases to `ref/cases.bend` and the
answers of an independent Python implementation, written from the same
documents, to `ref/expected.txt` (both generated and not kept: see
`ref/.gitignore`):

* 260 random validated packet filters over random packets;
* 90 random programs that break a rule or do not decode;
* unvalidated programs that run off their end or use a bad scratch index;
* 150 random seccomp filters (all actions, unnamed ones, `RET A`) over
  random `seccomp_data`, and stacks of one to three filters;
* seccomp validation, including refused loads, `BPF_MOD`, and filters
  that read scratch memory before writing it on some path.

**The kernel as a reference.** On Linux x86-64, 80 random stacks of
seccomp filters answering only ERRNO or ALLOW are installed in a forked child
(`PR_SET_NO_NEW_PRIVS`, then `PR_SET_SECCOMP` with `SECCOMP_MODE_FILTER`, via
ctypes), which calls getppid, getpgrp, getuid, getgid, geteuid or getegid
with chosen arguments (320 calls) and reports which failed with which errno;
each must match the model, as the Bend output must. 181 more filters
(broken ones, filters with some of their first stores removed, and three
fixed cases for code after a jump and after a return) check that the kernel
accepts exactly the filters `seccomp_validate` accepts, both ways. If
installing a filter is not permitted, the rest runs and `run.sh` exits 77.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 1070 cases match and the kernel agrees
(80 stacks, 320 system calls, 181 validation cases; WSL2 kernel 6.6).
