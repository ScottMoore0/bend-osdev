import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./insn.bend as I
import ./validate.bend as V
import ./bpf.bend as R
import ./seccomp.bend as S

def show_run(r: Result<&2, &2, I.BpfError, U32>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{v}:
      U32.show(v)

def show_ok(r: Result<&2, &2, I.BpfError, Unit>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{u}:
      "ok"

def show_act(r: Result<&2, &2, I.BpfError, S.SeccompAction>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{a}:
      S.SeccompAction.show(a)

# bpf(4), EXAMPLES: accept only Reverse ARP requests, as BPF_STMT and
# BPF_JUMP lines (0x8035 = 32821, ETHERTYPE_REVARP; 3, REVARP_REQUEST)
def rarp() -> List<&2, I.BpfRaw>:
  [I.bpf_stmt(40, 12), I.bpf_jump(21, 32821, 0, 3), I.bpf_stmt(40, 20), I.bpf_jump(21, 3, 0, 1), I.bpf_stmt(6, 42), I.bpf_stmt(6, 0)]

def run_raw.go(o: B.Octets, p: Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>) -> Result<&2, &2, I.BpfError, U32>:
  match p:
    case Fail{e}:
      Fail{e}
    case Done{ops}:
      R.bpf_run(R.bpf_packet(o), ops)

def run_raw(o: B.Octets, rs: List<&2, I.BpfRaw>) -> Result<&2, &2, I.BpfError, U32>:
  run_raw.go(o, V.bpf_prepare(V.bpf_maxinsns(), rs))

# bpf(4): accept IP packets between 128.3.112.15 and 128.3.112.35
def hosts() -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfH{}, 12}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2048}, 0, 8}, I.BpfLdAbs{I.BpfW{}, 26}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708943}, 0, 2}, I.BpfLdAbs{I.BpfW{}, 30}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708963}, 3, 4}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708963}, 0, 3}, I.BpfLdAbs{I.BpfW{}, 30}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2147708943}, 0, 1}, I.BpfRet{I.BpfRetK{4294967295}}, I.BpfRet{I.BpfRetK{0}}]

# bpf(4): accept TCP finger packets (port 79), skipping IP fragments
def finger() -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfH{}, 12}, I.BpfJmp{I.BpfJeq{}, I.BpfK{2048}, 0, 10}, I.BpfLdAbs{I.BpfB{}, 23}, I.BpfJmp{I.BpfJeq{}, I.BpfK{6}, 0, 8}, I.BpfLdAbs{I.BpfH{}, 20}, I.BpfJmp{I.BpfJset{}, I.BpfK{8191}, 6, 0}, I.BpfLdxMsh{14}, I.BpfLdInd{I.BpfH{}, 14}, I.BpfJmp{I.BpfJeq{}, I.BpfK{79}, 2, 0}, I.BpfLdInd{I.BpfH{}, 16}, I.BpfJmp{I.BpfJeq{}, I.BpfK{79}, 0, 1}, I.BpfRet{I.BpfRetK{4294967295}}, I.BpfRet{I.BpfRetK{0}}]

def pkt_rarp() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 128, 53, 0, 1, 8, 0, 6, 4, 0, 3, 2, 0, 0, 0, 0, 1, 10, 0, 0, 1, 0, 0, 0, 0, 0, 0, 10, 0, 0, 2])

def pkt_arp() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 6, 0, 1, 8, 0, 6, 4, 0, 1, 2, 0, 0, 0, 0, 1, 10, 0, 0, 1, 0, 0, 0, 0, 0, 0, 10, 0, 0, 2])

def pkt_ip(src: List<&2, U32>, dst: List<&2, U32>) -> B.Octets:
  B.Octets.concat([B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0]), B.Octets.of_list(src), B.Octets.of_list(dst), B.Octets.of_list([3, 232, 0, 80]), B.Octets.zeros(16n)])

def pkt_finger() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 3, 255, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_web() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 3, 255, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_frag() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 69, 0, 0, 40, 0, 0, 32, 1, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 3, 255, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_finger_opts() -> B.Octets:
  B.Octets.of_list([255, 255, 255, 255, 255, 255, 2, 0, 0, 0, 0, 1, 8, 0, 70, 0, 0, 40, 0, 0, 64, 0, 64, 6, 0, 0, 10, 0, 0, 1, 128, 3, 112, 15, 1, 2, 3, 4, 0, 79, 3, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pkt_run(o: B.Octets, prog: List<&2, I.BpfOp>) -> String:
  show_run(R.bpf_run(R.bpf_packet(o), prog))

# seccomp(2), EXAMPLES: install_filter(59, AUDIT_ARCH_X86_64, 99): execve
# (59) fails with errno 99, other calls are allowed, and another
# architecture or an x32 call kills the process
def example() -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfW{}, 4}, I.BpfJmp{I.BpfJeq{}, I.BpfK{S.seccomp_arch_x86_64()}, 0, 5}, I.BpfLdAbs{I.BpfW{}, 0}, I.BpfJmp{I.BpfJgt{}, I.BpfK{U32.sub(S.seccomp_x32_syscall_bit(), 1)}, 3, 0}, I.BpfJmp{I.BpfJeq{}, I.BpfK{59}, 0, 1}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompErrno{99})}}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompAllow{})}}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompKillProcess{})}}]

def sc_call(nr: U32, arch: U32) -> S.SeccompData:
  S.SeccompData{nr, arch, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero()}

def sc(prog: List<&2, I.BpfOp>, d: S.SeccompData) -> String:
  show_act(S.seccomp_run(S.seccomp_order(), prog, d))

def ret_only(a: S.SeccompAction) -> List<&2, I.BpfOp>:
  [I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(a)}}]

# a filter that answers ERRNO(e) for system call nr and ALLOW otherwise
def deny(nr: U32, e: U32) -> List<&2, I.BpfOp>:
  [I.BpfLdAbs{I.BpfW{}, 0}, I.BpfJmp{I.BpfJeq{}, I.BpfK{nr}, 0, 1}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompErrno{e})}}, I.BpfRet{I.BpfRetK{S.SeccompAction.to_u32(S.SeccompAllow{})}}]

# A full-size program, as a regression test for long inputs: 4096
# instructions (BPF_MAXINSNS), stored as Octets, read back, prepared and run
# on 64 KB of pseudo-random bytes (a linear congruential generator). Block j
# of eight: ld [4j mod 65532]; add #j; st M[j mod 16]; ldx M[j mod 16];
# ldx #(7j mod 65000); ldb [x + 3]; jeq #j, 0, 0; ja 0 (ret a in the last).
def big.last(last: Bool) -> I.BpfRaw:
  match last:
    case True{}:
      I.bpf_stmt(22, 0)
    case False{}:
      I.bpf_stmt(5, 0)

def big.block(+j: U32, last: Bool, acc: List<&2, I.BpfRaw>) -> List<&2, I.BpfRaw>:
  +m = U32.mod(j, 16)
  Con{I.bpf_stmt(32, U32.mod(U32.mul(4, j), 65532)), Con{I.bpf_stmt(4, j), Con{I.bpf_stmt(2, m), Con{I.bpf_stmt(97, m), Con{I.bpf_stmt(1, U32.mod(U32.mul(j, 7), 65000)), Con{I.bpf_stmt(80, 3), Con{I.bpf_jump(21, j, 0, 0), Con{big.last(last), acc}}}}}}}}

def big.prog(n: Nat, +j: U32, acc: List<&2, I.BpfRaw>) -> List<&2, I.BpfRaw>:
  match n:
    case 0n:
      acc
    case 1n+p:
      big.prog(p, U32.sub(j, 1), big.block(j, U32.is_eq(j, 511), acc))

def big.packet(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      big.packet(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def big.run(r: Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>, pk: B.Octets) -> String:
  match r:
    case Done{ops}:
      show_run(R.bpf_run(R.bpf_packet(pk), ops))
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)

def big.read(r: Result<&2, &2, I.BpfError, List<&2, I.BpfRaw>>, pk: B.Octets) -> String:
  match r:
    case Done{raws}:
      big.run(V.bpf_prepare(V.bpf_maxinsns(), raws), pk)
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)

def main() -> IO(Unit):
  +big = I.bpf_to_octets(I.BpfBig{}, big.prog(512n, 511, Nil{}))
  do IO<Unit>:
    IO.print("rarp " ++ show_run(run_raw(pkt_rarp(), rarp())) ++ " " ++ show_run(run_raw(pkt_arp(), rarp())))
    IO.print("hosts " ++ pkt_run(pkt_ip([128, 3, 112, 15], [128, 3, 112, 35]), hosts()) ++ " " ++ pkt_run(pkt_ip([128, 3, 112, 35], [128, 3, 112, 15]), hosts()) ++ " " ++ pkt_run(pkt_ip([128, 3, 112, 15], [10, 0, 0, 1]), hosts()) ++ " " ++ pkt_run(pkt_arp(), hosts()))
    IO.print("finger " ++ pkt_run(pkt_finger(), finger()) ++ " " ++ pkt_run(pkt_web(), finger()) ++ " " ++ pkt_run(pkt_frag(), finger()) ++ " " ++ pkt_run(pkt_finger_opts(), finger()))
    IO.print("short " ++ pkt_run(B.Octets.of_list([1, 2, 3]), finger()))
    IO.print("len " ++ pkt_run(pkt_rarp(), [I.BpfLdLen{}, I.BpfRet{I.BpfRetA{}}]))
    IO.print("div0 " ++ pkt_run(pkt_rarp(), [I.BpfLdImm{7}, I.BpfAlu{I.BpfDiv{}, I.BpfX{}}, I.BpfRet{I.BpfRetK{1}}]))
    IO.print("mem " ++ pkt_run(pkt_rarp(), [I.BpfLdImm{5}, I.BpfSt{15}, I.BpfLdxImm{3}, I.BpfLdMem{15}, I.BpfAlu{I.BpfMul{}, I.BpfX{}}, I.BpfStx{0}, I.BpfLdxMem{15}, I.BpfAlu{I.BpfSub{}, I.BpfX{}}, I.BpfNeg{}, I.BpfRet{I.BpfRetA{}}]))
    IO.print("bytes " ++ B.Octets.hex(I.bpf_to_octets(I.BpfLittle{}, rarp())))
    IO.print("validate " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), finger())) ++ ", " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), [])) ++ ", " ++ show_ok(V.bpf_validate(1n, finger())) ++ ", " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), [I.BpfJa{1}, I.BpfRet{I.BpfRetA{}}])) ++ ", " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdImm{1}])) ++ ", " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), [I.BpfSt{16}, I.BpfRet{I.BpfRetA{}}])) ++ ", " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), [I.BpfAlu{I.BpfMod{}, I.BpfK{0}}, I.BpfRet{I.BpfRetA{}}])))
    IO.print("mem init " ++ show_ok(V.bpf_validate(V.bpf_maxinsns(), [I.BpfLdMem{3}, I.BpfRet{I.BpfRetA{}}])) ++ ", " ++ show_ok(V.bpf_validate_with(V.BpfValidateOptions.permissive(), [I.BpfLdMem{3}, I.BpfRet{I.BpfRetA{}}])))
    IO.print("decode " ++ show_run(run_raw(pkt_rarp(), [I.bpf_stmt(14, 0)])))
    IO.print("seccomp " ++ sc(example(), sc_call(59, S.seccomp_arch_x86_64())) ++ " " ++ sc(example(), sc_call(1, S.seccomp_arch_x86_64())) ++ " " ++ sc(example(), sc_call(59, S.seccomp_arch_i386())) ++ " " ++ sc(example(), sc_call(1073741883, S.seccomp_arch_x86_64())))
    IO.print("seccomp validate " ++ show_ok(S.seccomp_validate(V.bpf_maxinsns(), example())) ++ ", " ++ show_ok(S.seccomp_validate(V.bpf_maxinsns(), finger())) ++ ", " ++ show_ok(S.seccomp_validate(V.bpf_maxinsns(), [I.BpfLdAbs{I.BpfW{}, 6}, I.BpfRet{I.BpfRetA{}}])))
    IO.print("stack " ++ show_act(S.seccomp_eval([deny(39, 1), deny(39, 2), deny(110, 3)], S.seccomp_order(), sc_call(39, S.seccomp_arch_x86_64()))) ++ " " ++ show_act(S.seccomp_eval([deny(39, 1), ret_only(S.SeccompTrap{5}), deny(110, 3)], S.seccomp_order(), sc_call(39, S.seccomp_arch_x86_64()))) ++ " " ++ show_act(S.seccomp_eval([deny(39, 1), deny(110, 3)], S.seccomp_order(), sc_call(110, S.seccomp_arch_x86_64()))) ++ " " ++ show_act(S.seccomp_eval([], S.seccomp_order(), sc_call(110, S.seccomp_arch_x86_64()))))
    IO.print("action " ++ S.SeccompAction.show(S.SeccompAction.of_u32(196613)) ++ " " ++ S.SeccompAction.show(S.SeccompAction.of_u32(65536)) ++ " " ++ S.SeccompAction.show(S.SeccompAction.of_u32(0)) ++ " " ++ U32.show(S.SeccompAction.to_u32(S.SeccompErrno{65549})))
    IO.print("big " ++ Nat.show(B.Octets.len(big)) ++ " bytes, answer " ++ big.read(I.bpf_of_octets(I.BpfBig{}, big), B.Octets.of_list(big.packet(65536n, 7, Nil{}))))

#|rarp 42 0
#|hosts 4294967295 4294967295 0 0
#|finger 4294967295 0 0 4294967295
#|short 0
#|len 42
#|div0 0
#|mem 4294967286
#|bytes 280000000c000000150000033580000028000000140000001500000103000000060000002a0000000600000000000000
#|validate ok, error: empty program, error: program too long: 13, error: jump out of range at 0, error: no return after 0, error: scratch index out of range at 0, error: division by constant zero at 0
#|mem init error: scratch read before write at 0, ok
#|decode error: bad opcode 14 at 0
#|seccomp ERRNO(99) ALLOW KILL_PROCESS KILL_PROCESS
#|seccomp validate ok, error: load not allowed in seccomp at 0, error: load not allowed in seccomp at 0
#|stack ERRNO(1) TRAP(5) ERRNO(3) ALLOW
#|action TRAP(5) KILL_PROCESS KILL_THREAD 327693
#|big 32768 bytes, answer 180
