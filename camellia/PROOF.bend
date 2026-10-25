import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../cipher-core/cipher-core.bend as L
import ../cipher-core/LAWS.bend as CoreL
import ../cipher-core/PROOF.bend as CoreP
import ./camellia.bend as C
import ./LAWS.bend as Laws

def block_xx(s: M.CmBlock, k: M.CmBlock) -> {s == M.CmBlock.xor(M.CmBlock.xor(s, k), k) : M.CmBlock}:
  match s k:
    case M.CmBlock{+a0, +a1, +a2, +a3} M.CmBlock{+b0, +b1, +b2, +b3}:
      %CoreL.u32_xor_cancel(a0, b0) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{_, U32.xor(U32.xor(a1, b1), b1), U32.xor(U32.xor(a2, b2), b2), U32.xor(U32.xor(a3, b3), b3)} : M.CmBlock}
      %CoreL.u32_xor_cancel(a1, b1) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{a0, _, U32.xor(U32.xor(a2, b2), b2), U32.xor(U32.xor(a3, b3), b3)} : M.CmBlock}
      %CoreL.u32_xor_cancel(a2, b2) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{a0, a1, _, U32.xor(U32.xor(a3, b3), b3)} : M.CmBlock}
      %CoreL.u32_xor_cancel(a3, b3) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{a0, a1, a2, _} : M.CmBlock}
      {==}

# Camellia: each step of the cipher is undone (FL by FL^-1 and back, the
# rounds and whitening by XOR, whatever F is), so the list of steps is

def cam_fl_inv(x: L.LcBlock64, k: L.LcBlock64) -> {x == C.cam.flinv(C.cam.fl(x, k), k) : L.LcBlock64}:
  match x k:
    case L.LcBlock64{+x1, +x2} L.LcBlock64{+k1, +k2}:
      %CoreL.u32_xor_cancel(x1, U32.or(U32.xor(x2, L.lc.rotl(U32.and(x1, k1), 1n)), k2)) : {L.LcBlock64{x1, x2} == L.LcBlock64{_, U32.xor(U32.xor(x2, L.lc.rotl(U32.and(x1, k1), 1n)), L.lc.rotl(U32.and(_, k1), 1n))} : L.LcBlock64}
      %CoreL.u32_xor_cancel(x2, L.lc.rotl(U32.and(x1, k1), 1n)) : {L.LcBlock64{x1, x2} == L.LcBlock64{x1, _} : L.LcBlock64}
      {==}

def cam_flinv_inv(y: L.LcBlock64, k: L.LcBlock64) -> {y == C.cam.fl(C.cam.flinv(y, k), k) : L.LcBlock64}:
  match y k:
    case L.LcBlock64{+y1, +y2} L.LcBlock64{+k1, +k2}:
      %CoreL.u32_xor_cancel(y2, L.lc.rotl(U32.and(U32.xor(y1, U32.or(y2, k2)), k1), 1n)) : {L.LcBlock64{y1, y2} == L.LcBlock64{U32.xor(U32.xor(y1, U32.or(y2, k2)), U32.or(_, k2)), _} : L.LcBlock64}
      %CoreL.u32_xor_cancel(y1, U32.or(y2, k2)) : {L.LcBlock64{y1, y2} == L.LcBlock64{_, y2} : L.LcBlock64}
      {==}

def cam_white(a: L.LcBlock64, b: L.LcBlock64, +s: M.CmBlock) -> {s == C.cam.white(a, b, C.cam.white(a, b, s)) : M.CmBlock}:
  match a b:
    case L.LcBlock64{+a0, +a1} L.LcBlock64{+b0, +b1}:
      block_xx(s, M.CmBlock{a0, a1, b0, b1})

def cam_f1(+t: C.LcCamTabs, +k: L.LcBlock64, s: M.CmBlock) -> {s == C.cam.unop(C.LcCamF1{t, k}, C.cam.op(C.LcCamF1{t, k}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+s0, +s1, +s2, +s3}:
      %CoreL.u32_xor_cancel(s2, C.cam.hi(C.cam.f(t, L.LcBlock64{s0, s1}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, s1, _, U32.xor(U32.xor(s3, C.cam.lo(C.cam.f(t, L.LcBlock64{s0, s1}, k))), C.cam.lo(C.cam.f(t, L.LcBlock64{s0, s1}, k)))} : M.CmBlock}
      %CoreL.u32_xor_cancel(s3, C.cam.lo(C.cam.f(t, L.LcBlock64{s0, s1}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, s1, s2, _} : M.CmBlock}
      {==}

def cam_f1d(+t: C.LcCamTabs, +k: L.LcBlock64, s: M.CmBlock) -> {s == C.cam.op(C.LcCamF1{t, k}, C.cam.unop(C.LcCamF1{t, k}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+s0, +s1, +s2, +s3}:
      %CoreL.u32_xor_cancel(s2, C.cam.hi(C.cam.f(t, L.LcBlock64{s0, s1}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, s1, _, U32.xor(U32.xor(s3, C.cam.lo(C.cam.f(t, L.LcBlock64{s0, s1}, k))), C.cam.lo(C.cam.f(t, L.LcBlock64{s0, s1}, k)))} : M.CmBlock}
      %CoreL.u32_xor_cancel(s3, C.cam.lo(C.cam.f(t, L.LcBlock64{s0, s1}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, s1, s2, _} : M.CmBlock}
      {==}

def cam_f2(+t: C.LcCamTabs, +k: L.LcBlock64, s: M.CmBlock) -> {s == C.cam.unop(C.LcCamF2{t, k}, C.cam.op(C.LcCamF2{t, k}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+s0, +s1, +s2, +s3}:
      %CoreL.u32_xor_cancel(s0, C.cam.hi(C.cam.f(t, L.LcBlock64{s2, s3}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{_, U32.xor(U32.xor(s1, C.cam.lo(C.cam.f(t, L.LcBlock64{s2, s3}, k))), C.cam.lo(C.cam.f(t, L.LcBlock64{s2, s3}, k))), s2, s3} : M.CmBlock}
      %CoreL.u32_xor_cancel(s1, C.cam.lo(C.cam.f(t, L.LcBlock64{s2, s3}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, _, s2, s3} : M.CmBlock}
      {==}

def cam_f2d(+t: C.LcCamTabs, +k: L.LcBlock64, s: M.CmBlock) -> {s == C.cam.op(C.LcCamF2{t, k}, C.cam.unop(C.LcCamF2{t, k}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+s0, +s1, +s2, +s3}:
      %CoreL.u32_xor_cancel(s0, C.cam.hi(C.cam.f(t, L.LcBlock64{s2, s3}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{_, U32.xor(U32.xor(s1, C.cam.lo(C.cam.f(t, L.LcBlock64{s2, s3}, k))), C.cam.lo(C.cam.f(t, L.LcBlock64{s2, s3}, k))), s2, s3} : M.CmBlock}
      %CoreL.u32_xor_cancel(s1, C.cam.lo(C.cam.f(t, L.LcBlock64{s2, s3}, k))) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, _, s2, s3} : M.CmBlock}
      {==}

def cam_fl_step(a: L.LcBlock64, b: L.LcBlock64, s: M.CmBlock) -> {s == C.cam.unop(C.LcCamFl{a, b}, C.cam.op(C.LcCamFl{a, b}, s)) : M.CmBlock}:
  match a b s:
    case L.LcBlock64{+a0, +a1} L.LcBlock64{+b0, +b1} M.CmBlock{+s0, +s1, +s2, +s3}:
      %cam_fl_inv(L.LcBlock64{s0, s1}, L.LcBlock64{a0, a1}) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{C.cam.hi(_), C.cam.lo(_), C.cam.hi(C.cam.fl(C.cam.flinv(L.LcBlock64{s2, s3}, L.LcBlock64{b0, b1}), L.LcBlock64{b0, b1})), C.cam.lo(C.cam.fl(C.cam.flinv(L.LcBlock64{s2, s3}, L.LcBlock64{b0, b1}), L.LcBlock64{b0, b1}))} : M.CmBlock}
      %cam_flinv_inv(L.LcBlock64{s2, s3}, L.LcBlock64{b0, b1}) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, s1, C.cam.hi(_), C.cam.lo(_)} : M.CmBlock}
      {==}

def cam_fl_step_dual(a: L.LcBlock64, b: L.LcBlock64, s: M.CmBlock) -> {s == C.cam.op(C.LcCamFl{a, b}, C.cam.unop(C.LcCamFl{a, b}, s)) : M.CmBlock}:
  match a b s:
    case L.LcBlock64{+a0, +a1} L.LcBlock64{+b0, +b1} M.CmBlock{+s0, +s1, +s2, +s3}:
      %cam_flinv_inv(L.LcBlock64{s0, s1}, L.LcBlock64{a0, a1}) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{C.cam.hi(_), C.cam.lo(_), C.cam.hi(C.cam.flinv(C.cam.fl(L.LcBlock64{s2, s3}, L.LcBlock64{b0, b1}), L.LcBlock64{b0, b1})), C.cam.lo(C.cam.flinv(C.cam.fl(L.LcBlock64{s2, s3}, L.LcBlock64{b0, b1}), L.LcBlock64{b0, b1}))} : M.CmBlock}
      %cam_fl_inv(L.LcBlock64{s2, s3}, L.LcBlock64{b0, b1}) : {M.CmBlock{s0, s1, s2, s3} == M.CmBlock{s0, s1, C.cam.hi(_), C.cam.lo(_)} : M.CmBlock}
      {==}

def cam_unop_op(o: C.LcCamOp, +s: M.CmBlock) -> {s == C.cam.unop(o, C.cam.op(o, s)) : M.CmBlock}:
  match o:
    case C.LcCamWhite{a, b}:
      cam_white(a, b, s)
    case C.LcCamF1{t, k}:
      cam_f1(t, k, s)
    case C.LcCamF2{t, k}:
      cam_f2(t, k, s)
    case C.LcCamFl{a, b}:
      cam_fl_step(a, b, s)
    case C.LcCamSwap{}:
      match s:
        case M.CmBlock{s0, s1, s2, s3}:
          {==}

def cam_op_unop(o: C.LcCamOp, +s: M.CmBlock) -> {s == C.cam.op(o, C.cam.unop(o, s)) : M.CmBlock}:
  match o:
    case C.LcCamWhite{a, b}:
      cam_white(a, b, s)
    case C.LcCamF1{t, k}:
      cam_f1d(t, k, s)
    case C.LcCamF2{t, k}:
      cam_f2d(t, k, s)
    case C.LcCamFl{a, b}:
      cam_fl_step_dual(a, b, s)
    case C.LcCamSwap{}:
      match s:
        case M.CmBlock{s0, s1, s2, s3}:
          {==}

def cam_unrun_run(os: List<&2, C.LcCamOp>, +s: M.CmBlock) -> {s == C.cam.unrun(os, C.cam.run(os, s)) : M.CmBlock}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      %cam_unrun_run(t, C.cam.op(o, s)) : {s == C.cam.unop(o, _) : M.CmBlock}
      cam_unop_op(o, s)

def cam_run_unrun(os: List<&2, C.LcCamOp>, +s: M.CmBlock) -> {s == C.cam.run(os, C.cam.unrun(os, s)) : M.CmBlock}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      %cam_op_unop(o, C.cam.unrun(t, s)) : {s == C.cam.run(t, _) : M.CmBlock}
      cam_run_unrun(t, s)

def Laws.camellia_round_trip(k, b):
  match k:
    case C.LcCamelliaKey{ops}:
      Equal.sym(M.CmBlock, b, C.cam.unrun(ops, C.cam.run(ops, b)), cam_unrun_run(ops, b))

def Laws.camellia_round_trip_dual(k, b):
  match k:
    case C.LcCamelliaKey{ops}:
      Equal.sym(M.CmBlock, b, C.cam.run(ops, C.cam.unrun(ops, b)), cam_run_unrun(ops, b))

# BEGIN GENERATED by gen/vectors.py: vectors

def Laws.camellia_rfc3713():
  {==}

def Laws.camellia_bad_key_length():
  {==}
# END GENERATED: vectors
