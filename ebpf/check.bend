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

def outp(o: R.EbpfOutcome) -> String:
  match o:
    case R.EbpfOk{v}:
      "ok " ++ W.W64.show_hex(v)
    case R.EbpfErr{e}:
      "err"

def accepts(r: Result<&2, &2, I.EbpfError, Unit>) -> String:
  match r:
    case Done{u}:
      "accept"
    case Fail{e}:
      "reject"

def empty_mem() -> M.EbpfMem:
  M.EbpfMem.new(C.BpfLittle{}, B.Octets.empty(), B.Octets.empty(), Nil{})

# a context of eight bytes 1..8, little-endian
def ctx_mem() -> M.EbpfMem:
  M.EbpfMem.new(C.BpfLittle{}, B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8]), B.Octets.empty(), Nil{})

# sum the first two 32-bit words of the context: r0 = ctx[0] + ctx[4]
def prog_ctx() -> List<&2, I.EbpfInsn>:
  [ I.EbpfLdx{I.EbpfSizeW{}, I.EbpfR2{}, I.EbpfR1{}, 0}
  , I.EbpfLdx{I.EbpfSizeW{}, I.EbpfR0{}, I.EbpfR1{}, 4}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfAdd{}, I.EbpfR0{}, I.EbpfX{I.EbpfR2{}}}
  , I.EbpfExit{}
  ]

# a map lookup and dereference: key 0, then read the 4-byte value
def prog_map() -> List<&2, I.EbpfInsn>:
  [ I.EbpfLddw{I.EbpfLdMapFd{}, I.EbpfR1{}, 77, 0}
  , I.EbpfSt{I.EbpfSizeW{}, I.EbpfR10{}, 65532, 0}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR2{}, I.EbpfX{I.EbpfR10{}}}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfSub{}, I.EbpfR2{}, I.EbpfK{4}}
  , I.EbpfCall{I.EbpfCallHelper{}, 1}
  , I.EbpfLdx{I.EbpfSizeW{}, I.EbpfR0{}, I.EbpfR0{}, 0}
  , I.EbpfExit{}
  ]

def map_mem() -> M.EbpfMem:
  M.EbpfMem.new(C.BpfLittle{}, B.Octets.empty(), B.Octets.empty(), [M.EbpfMap.of_values(77, 4, [B.Octets.of_list([222, 173, 190, 239])])])

# a BPF-to-BPF call: r1 = 20 ; r0 = double(r1) ; exit ;
# double: r0 = r1 ; r0 += r1 ; exit   => 40
def prog_call() -> List<&2, I.EbpfInsn>:
  [ I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR1{}, I.EbpfK{20}}
  , I.EbpfCall{I.EbpfCallLocal{}, 1}
  , I.EbpfExit{}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfMov{}, I.EbpfR0{}, I.EbpfX{I.EbpfR1{}}}
  , I.EbpfAlu{I.EbpfBits64{}, I.EbpfAdd{}, I.EbpfR0{}, I.EbpfX{I.EbpfR1{}}}
  , I.EbpfExit{}
  ]

# the round trip through stored bytes, as a Bool (decoded length matches)
def rt_dec(r: Result<&2, &2, I.EbpfError, List<&2, I.EbpfInsn>>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{p}:
      Nat.show(List.length(&2, I.EbpfInsn, p))

def rt_show(r: Result<&2, &2, I.EbpfError, List<&2, I.EbpfRaw>>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{raws}:
      rt_dec(I.ebpf_decode(raws))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(outp(R.ebpf_run(prog_ctx(), ctx_mem())))
    IO.print(outp(R.ebpf_run(prog_map(), map_mem())))
    IO.print(outp(R.ebpf_run(prog_call(), empty_mem())))
    IO.print(accepts(V.ebpf_verify(prog_call())))
    IO.print(accepts(V.ebpf_verify(prog_ctx())))
    IO.print(accepts(V.ebpf_verify_with(~H.ebpf_helper_sigs.std, V.EbpfVerifyOptions.xdp(1500), prog_ctx())))
    IO.print(rt_show(I.ebpf_of_octets(C.BpfLittle{}, I.ebpf_to_octets(C.BpfLittle{}, I.ebpf_encode(prog_call())))))

#|ok 000000000c0a0806
#|ok 00000000efbeadde
#|ok 0000000000000028
#|reject
#|reject
#|accept
#|6
