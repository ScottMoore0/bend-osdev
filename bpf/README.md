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
| `bpf_encode(ops)`, `bpf_decode(raws)` | a program; `bpf_decode` fails with `BpfErrBadCode{pc, code}` (the first such instruction) |
| `BpfOrder` (`BpfBig{}`, `BpfLittle{}`) | a byte order |
| `bpf_to_octets(order, raws)` | a stored program, 8 bytes per instruction |
| `bpf_of_octets_with(max, order, o)` | a stored program's instructions: `BpfErrStoredTooLong{max}` if `o` has more than `max` bytes (checked first, by looking for the byte at offset `max`, so the rest of a longer input is never read), then `BpfErrTruncated{len}` if its length is not a multiple of 8 |
| `bpf_of_octets(order, o)`, `bpf_octets_max()` | the same with the default limit, `bpf_octets_max()` = 32768 bytes (8 × `bpf_maxinsns()`, the longest program the default validation accepts) |
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
* **The size limit on stored programs** is a parameter of
  `bpf_of_octets_with`, with `bpf_of_octets` using the default
  `bpf_octets_max()` (8 × `bpf_maxinsns()` bytes). A caller that raises the
  instruction limit of validation raises this one to match.
* **Programs can be built either way:** as raw `BpfRaw` lines (the C
  macros) or as `BpfOp` values; `bpf_decode`/`bpf_encode` convert, with a law
  that they round-trip.
* **A fast interpreter** (or a JIT) can be added beside `bpf_run`, kept to it
  by a law or the differential test. The interpreter is the reference: one
  pass over the instructions, each visited at most once.
* **Reference and tail forms.** `bpf_encode`, `bpf_decode` and the
  validator's instruction checks run as tail calls; their structural forms
  (`bpf_encode.ref`, `bpf_decode.ref`, `bpf_check.all`, internal) are what
  the proofs reason about, and `PROOF.bend` proves each pair equal for every
  input (`F_encode`, `F_decode`, `F_check`, with `F_count` for the length).
* **Streaming:** none. A filter reads its input at any offset, so it needs
  the whole input, as BPF itself does.

## Laws

`LAWS.bend`. For every input:

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
* `octets_over_limit`: for every limit, byte order and input with a byte at
  offset `max` (so more than `max` bytes), `bpf_of_octets_with` answers
  `BpfErrStoredTooLong{max}`, whatever the input's bytes.
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
action, the path limit, and stored programs over and at a limit
(`octets_limit_refuses`, `octets_limit_accepts`), with
`octets_max_default` tying `bpf_octets_max()` to 8 × `bpf_maxinsns()`.

Witnesses: every hypothesis of a law holds for some input, so no law is
vacuous: `witness_skip_length` (a three-instruction `skipped` list of length
`to_nat(3)`, the form of the hypotheses of `ja_skips`, `jeq_taken_skips` and
`jeq_not_taken_skips`), `witness_rank_le` (for `combine_newer`),
`witness_rank_lt` (for `combine_older`), `witness_octets_over` (for
`octets_over_limit`), and `validate_accepts`,
`validate_permissive` and `seccomp_example_valid` (for the validation
hypotheses).

## Tests

`check.bend` prints the documentation's examples, a 4096-instruction
program stored, read back, prepared and run on 64 KB, and, as a regression
test for untrusted input, a 32,768-instruction program (256 KB): refused by
`bpf_of_octets` at its default limit, and, read with a limit of 1 MB,
decoded and refused by validation as too long. `ref/run.sh` runs
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

## Sizes

**Lanes.** Measured on Bend 2.0.37 (WSL2, 16 threads) natively
(`bend file.bend -o prog`, clang 22) and on bend's JavaScript lane
(`bend file.bend`, which runs `main` inside the bend process: a small stack,
several times the memory, and a 3 GB cap on the process; see AGENTS.md,
"Runtime and checker limits"). Times and peaks include building the input.

A packet is read only at the offsets a program loads from (through bytes'
tail-recursive `Octets` operations), so its size has no limit beyond memory.
A 4096-instruction program (`BPF_MAXINSNS`: loads, ALU, scratch memory,
jumps), written as 32 KB of `Octets` with `bpf_to_octets`, read back with
`bpf_of_octets`, prepared (decoded and validated) and run on a 64 KB packet,
the answer checked against `ref/gen.py`'s model, with the rest of
`check.bend`: 0.5 s and 35 MB natively, 1.4 s and 390 MB on the JavaScript
lane.

**Long and untrusted programs.** Every program-wide loop is a tail call over
an accumulator, reversed at the end where order matters: `bpf_encode`,
`bpf_decode`, `bpf_to_octets`, `bpf_of_octets`, the validator's instruction
checks (which count the instructions once, instead of once per instruction)
and its scratch-memory pass, and seccomp's checks. So a program's length is
limited by memory alone, on both lanes. Validation runs each pass only once
the ones before it hold, so a program over the instruction limit is refused
after one count. `bpf_of_octets` refuses more than `bpf_octets_max()` bytes
before decoding anything, by looking for the byte at offset 32768, so its
cost does not grow with the input: refusing the same 8 MB input ten times
costs 0.01 s more than refusing it once natively (0.1 s a refusal on the
JavaScript lane).

| Input | Path | Answer | Native | JavaScript lane |
|---|---|---|---|---|
| 32,768 instructions (256 KB, the regression filter) | `bpf_of_octets` | `BpfErrStoredTooLong{32768}` | 0.22 s, 29 MB | 0.8 s, 245 MB |
| | `bpf_of_octets_with` (256 KB), `bpf_prepare(4096, …)` | `BpfErrTooLong{32768}` | 0.41 s, 29 MB | 1.2 s, 400 MB |
| | the same, `bpf_prepare(32768, …)` (every check, the scratch-memory pass) | `Done` | 0.43 s, 29 MB | 1.3 s, 420 MB |
| 200,000 `ld #0` (1.6 MB) | `bpf_of_octets_with`, `bpf_prepare(4096, …)` | `BpfErrTooLong{200000}` | 1.2 s, 58 MB | 4.1 s, 1.1 GB |
| | the same, `bpf_prepare(200000, …)` | `BpfErrNoReturn{199999}` | 1.3 s, 58 MB | 6.4 s, 1.0 GB |
| 1,000,000 `ld #0` (8 MB) | `bpf_of_octets` | `BpfErrStoredTooLong{32768}` | 0.31 s, 250 MB | 4.5 s, 1.4 GB |
| | `bpf_of_octets_with` (8 MB), `bpf_prepare(4096, …)` | `BpfErrTooLong{1000000}` | 5.9 s, 280 MB | over the 3 GB cap |
| | the same, `bpf_prepare(1000000, …)` | `BpfErrNoReturn{999999}` | 5.8 s, 280 MB | over the 3 GB cap |

Building the 8 MB input alone takes 0.1 s and 130 MB natively, 3.7 s and
1.4 GB on the JavaScript lane, so a million decoded instructions do not fit
under the JavaScript lane's 3 GB cap; that is memory, not the stack. Before
these loops were tail calls, the 32,768-instruction regression filter
overflowed the JavaScript lane's stack ("memory fault (machine stack
overflow?)"), and natively took 1.9 s, the instruction checks counting the
rest of the program at every instruction.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`).

## Status

Bend 2.0.37, `VERDICT=1 scripts/check.sh bpf` with native builds:
`PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK, `check.bend`
passes (natively), `ref/run.sh` 1070 cases match and the kernel agrees (80
stacks, 320 system calls, 181 validation cases; WSL2 kernel 6.6);
`scripts/deps.sh bpf` passes.
