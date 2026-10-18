# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
#   * a validated program always answers, whatever the validator's options:
#     bpf_run gives Done, whatever the input (it never runs past its end or
#     misuses scratch memory), and
#     instructions after it are never reached; the same for seccomp filters;
#   * RET k answers k;
#   * jumps move forward over exactly the instructions they skip;
#   * decoding an encoded instruction or program gives it back;
#   * a stored program longer than the limit is refused, whatever its bytes;
#   * stacked seccomp filters answer the most restrictive action, the newer
#     filter's on a tie, and the grouping does not matter.
#
# Vectors: the bpf(4) and seccomp(2) examples, one case of each rule, and a
# witness for each hypothesis.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./insn.bend as I
import ./validate.bend as V
import ./bpf.bend as R
import ./seccomp.bend as S

law validated_returns:
  for +opts: V.BpfValidateOptions
  for +prog: List<&2, I.BpfOp>
  for +inp: R.BpfInput
  for +ok: {V.bpf_validate_with(opts, prog) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}
  {Result.is_done(&2, &2, I.BpfError, U32, R.bpf_run(inp, prog)) == True{} : Bool}

law validated_ignores_tail:
  for +opts: V.BpfValidateOptions
  for +prog: List<&2, I.BpfOp>
  for +rest: List<&2, I.BpfOp>
  for +inp: R.BpfInput
  for +ok: {V.bpf_validate_with(opts, prog) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}
  {R.bpf_run(inp, List.append(&2, I.BpfOp, prog, rest)) == R.bpf_run(inp, prog) : Result<&2, &2, I.BpfError, U32>}

law ret_k:
  for k: U32
  for +inp: R.BpfInput
  {R.bpf_run(inp, [I.BpfRet{I.BpfRetK{k}}]) == Done{k} : Result<&2, &2, I.BpfError, U32>}

law ja_skips:
  for k: U32
  for +skipped: List<&2, I.BpfOp>
  for +rest: List<&2, I.BpfOp>
  for +inp: R.BpfInput
  for e: {List.length(&2, I.BpfOp, skipped) == U32.to_nat(k) : Nat}
  {R.bpf_run(inp, Con{I.BpfJa{k}, List.append(&2, I.BpfOp, skipped, rest)}) == R.bpf_run(inp, rest) : Result<&2, &2, I.BpfError, U32>}

law jeq_taken_skips:
  for jt: U32
  for jf: U32
  for +skipped: List<&2, I.BpfOp>
  for +rest: List<&2, I.BpfOp>
  for +inp: R.BpfInput
  for e: {List.length(&2, I.BpfOp, skipped) == U32.to_nat(jt) : Nat}
  {R.bpf_run(inp, Con{I.BpfJmp{I.BpfJeq{}, I.BpfK{0}, jt, jf}, List.append(&2, I.BpfOp, skipped, rest)}) == R.bpf_run(inp, rest) : Result<&2, &2, I.BpfError, U32>}

law jeq_not_taken_skips:
  for jt: U32
  for jf: U32
  for +skipped: List<&2, I.BpfOp>
  for +rest: List<&2, I.BpfOp>
  for +inp: R.BpfInput
  for e: {List.length(&2, I.BpfOp, skipped) == U32.to_nat(jf) : Nat}
  {R.bpf_run(inp, Con{I.BpfJmp{I.BpfJeq{}, I.BpfK{1}, jt, jf}, List.append(&2, I.BpfOp, skipped, rest)}) == R.bpf_run(inp, rest) : Result<&2, &2, I.BpfError, U32>}

law insn_round_trip:
  for op: I.BpfOp
  {I.BpfRaw.decode(I.BpfOp.encode(op)) == Some{op} : Maybe<&2, I.BpfOp>}

law program_round_trip:
  for +prog: List<&2, I.BpfOp>
  {I.bpf_decode(I.bpf_encode(prog)) == Done{prog} : Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>}

# a stored program with a byte at offset max (so more than max bytes) is
# refused, whatever its bytes
law octets_over_limit:
  for +max: Nat
  for +order: I.BpfOrder
  for +o: B.Octets
  for b: U32
  for e: {B.Octets.at(o, max) == Some{b} : Maybe<&2, U32>}
  {I.bpf_of_octets_with(max, order, o) == Fail{I.BpfErrStoredTooLong{max}} : Result<&2, &2, I.BpfError, List<&2, I.BpfRaw>>}

law most_restrictive:
  for a: S.SeccompAction
  for b: S.SeccompAction
  {S.SeccompAction.rank(S.seccomp_combine(a, b)) == Nat.min(S.SeccompAction.rank(a), S.SeccompAction.rank(b)) : Nat}

law combine_newer:
  for +a: S.SeccompAction
  for +b: S.SeccompAction
  for e: {Nat.is_le(S.SeccompAction.rank(a), S.SeccompAction.rank(b)) == True{} : Bool}
  {S.seccomp_combine(a, b) == a : S.SeccompAction}

law combine_older:
  for +a: S.SeccompAction
  for +b: S.SeccompAction
  for e: {Nat.is_lt(S.SeccompAction.rank(b), S.SeccompAction.rank(a)) == True{} : Bool}
  {S.seccomp_combine(a, b) == b : S.SeccompAction}

law combine_assoc:
  for a: S.SeccompAction
  for b: S.SeccompAction
  for c: S.SeccompAction
  {S.seccomp_combine(a, S.seccomp_combine(b, c)) == S.seccomp_combine(S.seccomp_combine(a, b), c) : S.SeccompAction}

law action_round_trip:
  for a: S.SeccompAction
  {S.SeccompAction.of_u32(S.SeccompAction.to_u32(a)) == S.SeccompAction.clip(a) : S.SeccompAction}

law seccomp_validated_acts:
  for +opts: V.BpfValidateOptions
  for +order: I.BpfOrder
  for +prog: List<&2, I.BpfOp>
  for +d: S.SeccompData
  for +ok: {S.seccomp_validate_with(opts, prog) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}
  {Result.is_done(&2, &2, I.BpfError, S.SeccompAction, S.seccomp_run(order, prog, d)) == True{} : Bool}

# Vectors: the documentation's examples, and one case of each rule

# bpf(4), EXAMPLES: accept only Reverse ARP requests, as the manual writes it
# with BPF_STMT and BPF_JUMP (0x8035, ETHERTYPE_REVARP; 3, REVARP_REQUEST)
def rarp() -> List<&2, I.BpfRaw>:
  [I.bpf_stmt(40, 12), I.bpf_jump(21, 32821, 0, 3), I.bpf_stmt(40, 20), I.bpf_jump(21, 3, 0, 1), I.bpf_stmt(6, 42), I.bpf_stmt(6, 0)]

def rarp_ops() -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfH{}, 12}, I.BpfJmp{I.BpfJeq{}, I.BpfK{32821}, 0, 3}, I.BpfLdAbs{I.BpfH{}, 20}, I.BpfJmp{I.BpfJeq{}, I.BpfK{3}, 0, 1}, I.BpfRet{I.BpfRetK{42}}, I.BpfRet{I.BpfRetK{0}}]

# bpf(4): accept IP packets between 128.3.112.15 and 128.3.112.35
def hosts() -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfH{}, 12}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2048}, 0, 8}, I.BpfLdAbs{I.BpfW{}, 26}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708943}, 0, 2}, I.BpfLdAbs{I.BpfW{}, 30}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708963}, 3, 4}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708963}, 0, 3}, I.BpfLdAbs{I.BpfW{}, 30}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708943}, 0, 1}, I.BpfRet{I.BpfRetK{4294967295}}, I.BpfRet{I.BpfRetK{0}}]

# bpf(4): accept TCP finger packets (port 79), skipping IP fragments, with
# the IP header length from BPF_LDX | BPF_MSH
def finger() -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfH{}, 12}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2048}, 0, 10}, I.BpfLdAbs{I.BpfB{}, 23}, I.BpfJmp{I.BpfJeq{}, I.BpfK{6}, 0, 8}, I.BpfLdAbs{I.BpfH{}, 20}, I.BpfJmp{I.BpfJset{}, I.BpfK{8191}, 6, 0}, I.BpfLdxMsh{14}, I.BpfLdInd{I.BpfH{}, 14}, I.BpfJmp{I.BpfJeq{}, I.BpfK{79}, 2, 0}, I.BpfLdInd{I.BpfH{}, 16}, I.BpfJmp{I.BpfJeq{}, I.BpfK{79}, 0, 1}, I.BpfRet{I.BpfRetK{4294967295}}, I.BpfRet{I.BpfRetK{0}}]

# Ethernet frames: a RARP request, an ARP request, and IPv4 TCP packets
def pkt_rarp() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 128, 53, 0, 1, 8, 0, 6, 4, 0, 3, 2, 0, 0, 0, 0, 1, 10, 0, 0, 1, 0, 0, 0, 0, 0, 0, 10, 0, 0, 2])

def pkt_arp() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 6, 0, 1, 8, 0, 6, 4, 0, 1, 2, 0, 0, 0, 0, 1, 10, 0, 0, 1, 0, 0, 0, 0, 0, 0, 10, 0, 0, 2])

# from 128.3.112.15 to 128.3.112.35, and from 128.3.112.15 to 10.0.0.1
def pkt_ab() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 128, 3, 112, 15, 128, 3, 112, 35, 3, 232, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_ac() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 128, 3, 112, 15, 10, 0, 0, 1, 3, 232, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

# to TCP port 79; to port 80; a fragment to port 79; and to port 79 after a
# 24-byte IP header
def pkt_finger() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 3, 255, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_web() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 3, 255, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_frag() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 32, 1, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 3, 255, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_finger_opts() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 70, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 1, 2, 3, 4, 0, 79, 3, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

law rarp_prepares:
  {V.bpf_prepare(V.bpf_maxinsns(), rarp()) == Done{rarp_ops()} : Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>}

law rarp_accepts:
  {R.bpf_run(R.bpf_packet(pkt_rarp()), rarp_ops()) == Done{42} : Result<&2, &2, I.BpfError, U32>}

law rarp_rejects_arp:
  {R.bpf_run(R.bpf_packet(pkt_arp()), rarp_ops()) == Done{0} : Result<&2, &2, I.BpfError, U32>}

law hosts_accepts:
  {R.bpf_run(R.bpf_packet(pkt_ab()), hosts()) == Done{4294967295} : Result<&2, &2, I.BpfError, U32>}

law hosts_rejects:
  {R.bpf_run(R.bpf_packet(pkt_ac()), hosts()) == Done{0} : Result<&2, &2, I.BpfError, U32>}

law finger_accepts:
  {R.bpf_run(R.bpf_packet(pkt_finger()), finger()) == Done{4294967295} : Result<&2, &2, I.BpfError, U32>}

law finger_accepts_options:
  {R.bpf_run(R.bpf_packet(pkt_finger_opts()), finger()) == Done{4294967295} : Result<&2, &2, I.BpfError, U32>}

law finger_rejects_port:
  {R.bpf_run(R.bpf_packet(pkt_web()), finger()) == Done{0} : Result<&2, &2, I.BpfError, U32>}

law finger_rejects_fragment:
  {R.bpf_run(R.bpf_packet(pkt_frag()), finger()) == Done{0} : Result<&2, &2, I.BpfError, U32>}

# a load past the end of the input answers 0
law short_packet:
  {R.bpf_run(R.bpf_packet(B.Octets.of_list([8, 0, 69])), finger()) == Done{0} : Result<&2, &2, I.BpfError, U32>}

# so does a division by X = 0
law divide_by_zero_x:
  {R.bpf_run(R.bpf_packet(pkt_arp()), [I.BpfLdImm{7}, I.BpfAlu{I.BpfDiv{}, I.BpfX{}}, I.BpfRet{I.BpfRetK{1}}]) == Done{0} : Result<&2, &2, I.BpfError, U32>}

law length_load:
  {R.bpf_run(R.bpf_packet(pkt_rarp()), [I.BpfLdLen{}, I.BpfRet{I.BpfRetA{}}]) == Done{42} : Result<&2, &2, I.BpfError, U32>}

# M[15] = 5; X = 3; A = M[15] * X = 15; M[0] = X; X = M[15]; A = -(A - X)
law scratch_and_alu:
  {R.bpf_run(R.bpf_packet(pkt_rarp()), [I.BpfLdImm{5}, I.BpfSt{15}, I.BpfLdxImm{3}, I.BpfLdMem{15}, I.BpfAlu{I.BpfMul{}, I.BpfX{}}, I.BpfStx{0}, I.BpfLdxMem{15}, I.BpfAlu{I.BpfSub{}, I.BpfX{}}, I.BpfNeg{}, I.BpfRet{I.BpfRetA{}}]) == Done{4294967286} : Result<&2, &2, I.BpfError, U32>}

law validate_accepts:
  {V.bpf_validate(V.bpf_maxinsns(), finger()) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}

law validate_empty:
  {V.bpf_validate(V.bpf_maxinsns(), []) == Fail{I.BpfErrEmpty{}} : Result<&2, &2, I.BpfError, Unit>}

law validate_too_long:
  {V.bpf_validate(12n, finger()) == Fail{I.BpfErrTooLong{13n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_jump_out:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfJa{1}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrJump{0n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_no_return:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfRet{I.BpfRetA{}}, I.BpfLdImm{1}]) == Fail{I.BpfErrNoReturn{1n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_scratch:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfSt{16}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrScratch{0n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_div_zero:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfAlu{I.BpfMod{}, I.BpfK{0}}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrDivZero{0n}} : Result<&2, &2, I.BpfError, Unit>}

law decode_bad_opcode:
  {I.bpf_decode([I.bpf_stmt(6, 0), I.bpf_stmt(14, 0)]) == Fail{I.BpfErrBadCode{1n, 14}} : Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>}

law program_bytes:
  {B.Octets.hex(I.bpf_to_octets(I.BpfLittle{}, rarp())) == "280000000c000000150000033580000028000000140000001500000103000000060000002a0000000600000000000000" : String}

law program_bytes_back:
  {I.bpf_of_octets(I.BpfBig{}, I.bpf_to_octets(I.BpfBig{}, rarp())) == Done{rarp()} : Result<&2, &2, I.BpfError, List<&2, I.BpfRaw>>}

# the default limit on stored programs: 8 bytes for each of BPF_MAXINSNS
# instructions (compared as U32, which holds both)
law octets_max_default:
  {U32.from_nat(I.bpf_octets_max()) == U32.mul(8, U32.from_nat(V.bpf_maxinsns())) : U32}

law octets_limit_refuses:
  {I.bpf_of_octets_with(16n, I.BpfBig{}, B.Octets.zeros(17n)) == Fail{I.BpfErrStoredTooLong{16n}} : Result<&2, &2, I.BpfError, List<&2, I.BpfRaw>>}

law octets_limit_accepts:
  {I.bpf_of_octets_with(16n, I.BpfLittle{}, I.bpf_to_octets(I.BpfLittle{}, [I.bpf_stmt(6, 1), I.bpf_stmt(22, 0)])) == Done{[I.bpf_stmt(6, 1), I.bpf_stmt(22, 0)]} : Result<&2, &2, I.BpfError, List<&2, I.BpfRaw>>}

# seccomp(2), EXAMPLES, install_filter(syscall_nr, t_arch, f_errno) with
# t_arch = AUDIT_ARCH_X86_64, so upper_nr_limit = X32_SYSCALL_BIT - 1: the
# call syscall_nr fails with f_errno, other calls are allowed, and another
# architecture or an x32 call (nr above the limit) kills the process
def seccomp_example(nr: U32, e: U32) -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfW{}, 4}, I.BpfJmp{I.BpfJeq{}, I.BpfK{S.seccomp_arch_x86_64()}, 0, 5}, I.BpfLdAbs{I.BpfW{}, 0}, I.BpfJmp{I.BpfJgt{}, I.BpfK{U32.sub(S.seccomp_x32_syscall_bit(), 1)}, 3, 0}, I.BpfJmp{I.BpfJeq{}, I.BpfK{nr}, 0, 1}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompErrno{e})}}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompAllow{})}}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompKillProcess{})}}]

def sc_call(nr: U32, arch: U32) -> S.SeccompData:
  S.SeccompData{nr, arch, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero()}

# ERRNO(e) for system call nr, ALLOW for the others
def deny(nr: U32, e: U32) -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfW{}, 0}, I.BpfJmp{I.BpfJeq{}, I.BpfK{nr}, 0, 1}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompErrno{e})}}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompAllow{})}}]

law seccomp_example_valid:
  {S.seccomp_validate(V.bpf_maxinsns(), seccomp_example(59, 99)) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}

law seccomp_example_errno:
  {S.seccomp_run(S.seccomp_order(), seccomp_example(59, 99), sc_call(59, S.seccomp_arch_x86_64())) == Done{S.SeccompErrno{99}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law seccomp_example_allow:
  {S.seccomp_run(S.seccomp_order(), seccomp_example(59, 99), sc_call(1, S.seccomp_arch_x86_64())) == Done{S.SeccompAllow{}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law seccomp_example_other_arch:
  {S.seccomp_run(S.seccomp_order(), seccomp_example(59, 99), sc_call(59, S.seccomp_arch_i386())) == Done{S.SeccompKillProcess{}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law seccomp_example_x32:
  {S.seccomp_run(S.seccomp_order(), seccomp_example(59, 99), sc_call(1073741883, S.seccomp_arch_x86_64())) == Done{S.SeccompKillProcess{}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law seccomp_rejects_byte_load:
  {S.seccomp_validate(V.bpf_maxinsns(), finger()) == Fail{I.BpfErrSeccompLoad{0n}} : Result<&2, &2, I.BpfError, Unit>}

law seccomp_rejects_unaligned:
  {S.seccomp_validate(V.bpf_maxinsns(), [I.BpfLdAbs{I.BpfW{}, 6}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrSeccompLoad{0n}} : Result<&2, &2, I.BpfError, Unit>}

# two filters with the same action: the newer one wins, with its data
law stack_newest_on_tie:
  {S.seccomp_eval([deny(39, 1), deny(39, 2)], S.seccomp_order(), sc_call(39, S.seccomp_arch_x86_64())) == Done{S.SeccompErrno{1}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law stack_most_restrictive:
  {S.seccomp_eval([deny(39, 1), [I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompTrap{5})}}], deny(110, 3)], S.seccomp_order(), sc_call(39, S.seccomp_arch_x86_64())) == Done{S.SeccompTrap{5}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law stack_empty_allows:
  {S.seccomp_eval([], S.seccomp_order(), sc_call(39, S.seccomp_arch_x86_64())) == Done{S.SeccompAllow{}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law unknown_action_kills:
  {S.SeccompAction.of_u32(65536) == S.SeccompKillProcess{} : S.SeccompAction}

law install_path_limit:
  {S.seccomp_install(S.SeccompLimits{4096n, 19n}, [deny(39, 1), deny(39, 2)], I.bpf_encode(deny(110, 3))) == Fail{I.BpfErrPathTooLong{20n}} : Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>}

law install_pushes:
  {S.seccomp_install(S.seccomp_limits(), [deny(39, 1)], I.bpf_encode(deny(110, 3))) == Done{[deny(110, 3), deny(39, 1)]} : Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>}

law seccomp_rejects_mod:
  {S.seccomp_validate(V.bpf_maxinsns(), [I.BpfLdImm{7}, I.BpfAlu{I.BpfMod{}, I.BpfK{3}}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrSeccompInsn{1n}} : Result<&2, &2, I.BpfError, Unit>}

# the page's runs: ./a.out 1 0xC000003E 99 makes write (1) fail, and
# ./a.out 295 0xC000003E 99 leaves the calls whoami makes alone
law seccomp_example_write:
  {S.seccomp_run(S.seccomp_order(), seccomp_example(1, 99), sc_call(1, S.seccomp_arch_x86_64())) == Done{S.SeccompErrno{99}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

law seccomp_example_preadv:
  {S.seccomp_run(S.seccomp_order(), seccomp_example(295, 99), sc_call(1, S.seccomp_arch_x86_64())) == Done{S.SeccompAllow{}} : Result<&2, &2, I.BpfError, S.SeccompAction>}

# scratch memory read before it is written: refused by default, on every
# path (here the jump past the store), and allowed by the permissive options
law validate_mem_init:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdMem{3}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrMemInit{0n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_mem_init_path:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdImm{1}, I.BpfJmp{I.BpfJeq{}, I.BpfK{1}, 1, 0}, I.BpfSt{2}, I.BpfLdMem{2}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrMemInit{3n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_mem_init_written:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdImm{1}, I.BpfSt{2}, I.BpfJmp{I.BpfJeq{}, I.BpfK{1}, 1, 0}, I.BpfSt{3}, I.BpfLdMem{2}, I.BpfRet{I.BpfRetA{}}]) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}

# code after a jump is reached only by jumps to it; code after a return
# counts as reached from the return, as Linux counts it
law validate_mem_after_jump:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdImm{0}, I.BpfSt{0}, I.BpfJa{1}, I.BpfLdMem{1}, I.BpfRet{I.BpfRetA{}}]) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}

law validate_mem_after_return:
  {V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdImm{0}, I.BpfRet{I.BpfRetA{}}, I.BpfLdMem{1}, I.BpfRet{I.BpfRetA{}}]) == Fail{I.BpfErrMemInit{2n}} : Result<&2, &2, I.BpfError, Unit>}

law validate_permissive:
  {V.bpf_validate_with(V.BpfValidateOptions.permissive(), [I.BpfLdMem{3}, I.BpfRet{I.BpfRetA{}}]) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}

# Witnesses: each hypothesis of a law above holds for some input (the
# validation hypotheses: validate_accepts, validate_permissive and
# seccomp_example_valid; octets_over_limit: witness_octets_over)

law witness_skip_length:
  {List.length(&2, I.BpfOp, [I.BpfTax{}, I.BpfTxa{}, I.BpfNeg{}]) == U32.to_nat(3) : Nat}

law witness_octets_over:
  {B.Octets.at(B.Octets.zeros(9n), 8n) == Some{0} : Maybe<&2, U32>}

law witness_rank_le:
  {Nat.is_le(S.SeccompAction.rank(S.SeccompErrno{1}), S.SeccompAction.rank(S.SeccompErrno{2})) == True{} : Bool}

law witness_rank_lt:
  {Nat.is_lt(S.SeccompAction.rank(S.SeccompKillProcess{}), S.SeccompAction.rank(S.SeccompAllow{})) == True{} : Bool}
