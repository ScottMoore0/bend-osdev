import Base
import ../mode-core/mode-core.bend as M
import ../cipher-core/cipher-core.bend as L
import ../cipher-core/LAWS.bend as CoreL
import ../cipher-core/PROOF.bend as CoreP
import ./twofish.bend as F
import ./LAWS.bend as Laws

def block_xx(s: M.CmBlock, k: M.CmBlock) -> {s == M.CmBlock.xor(M.CmBlock.xor(s, k), k) : M.CmBlock}:
  match s k:
    case M.CmBlock{+a0, +a1, +a2, +a3} M.CmBlock{+b0, +b1, +b2, +b3}:
      %CoreL.u32_xor_cancel(a0, b0) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{_, U32.xor(U32.xor(a1, b1), b1), U32.xor(U32.xor(a2, b2), b2), U32.xor(U32.xor(a3, b3), b3)} : M.CmBlock}
      %CoreL.u32_xor_cancel(a1, b1) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{a0, _, U32.xor(U32.xor(a2, b2), b2), U32.xor(U32.xor(a3, b3), b3)} : M.CmBlock}
      %CoreL.u32_xor_cancel(a2, b2) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{a0, a1, _, U32.xor(U32.xor(a3, b3), b3)} : M.CmBlock}
      %CoreL.u32_xor_cancel(a3, b3) : {M.CmBlock{a0, a1, a2, a3} == M.CmBlock{a0, a1, a2, _} : M.CmBlock}
      {==}

# Twofish: each step of the cipher is undone (a round whatever F is, by the
# XORs and the 1-bit rotations undone), so the list of steps is

def tf_bswap(s: M.CmBlock) -> {s == F.tf.unop(F.LcTfBswap{}, F.tf.op(F.LcTfBswap{}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+a, +b, +c, +d}:
      %CoreL.bswap_bswap(a) : {M.CmBlock{a, b, c, d} == M.CmBlock{_, L.lc.bswap.bits(L.lc.bswap.bits(b)), L.lc.bswap.bits(L.lc.bswap.bits(c)), L.lc.bswap.bits(L.lc.bswap.bits(d))} : M.CmBlock}
      %CoreL.bswap_bswap(b) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, _, L.lc.bswap.bits(L.lc.bswap.bits(c)), L.lc.bswap.bits(L.lc.bswap.bits(d))} : M.CmBlock}
      %CoreL.bswap_bswap(c) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, b, _, L.lc.bswap.bits(L.lc.bswap.bits(d))} : M.CmBlock}
      %CoreL.bswap_bswap(d) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, b, c, _} : M.CmBlock}
      {==}

def tf_bswapd(s: M.CmBlock) -> {s == F.tf.op(F.LcTfBswap{}, F.tf.unop(F.LcTfBswap{}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+a, +b, +c, +d}:
      %CoreL.bswap_bswap(a) : {M.CmBlock{a, b, c, d} == M.CmBlock{_, L.lc.bswap.bits(L.lc.bswap.bits(b)), L.lc.bswap.bits(L.lc.bswap.bits(c)), L.lc.bswap.bits(L.lc.bswap.bits(d))} : M.CmBlock}
      %CoreL.bswap_bswap(b) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, _, L.lc.bswap.bits(L.lc.bswap.bits(c)), L.lc.bswap.bits(L.lc.bswap.bits(d))} : M.CmBlock}
      %CoreL.bswap_bswap(c) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, b, _, L.lc.bswap.bits(L.lc.bswap.bits(d))} : M.CmBlock}
      %CoreL.bswap_bswap(d) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, b, c, _} : M.CmBlock}
      {==}

def tf_round(+tb: F.LcTfTabs, +sk: List<&2, U32>, +ka: U32, +kb: U32, s: M.CmBlock) -> {s == F.tf.unop(F.LcTfRound{tb, sk, ka, kb}, F.tf.op(F.LcTfRound{tb, sk, ka, kb}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+r0, +r1, +r2, +r3}:
      %CoreL.rotl1_rotl31(U32.xor(r2, F.tf.f0(F.tf.f(tb, sk, r0, r1, ka, kb)))) : {M.CmBlock{r0, r1, r2, r3} == M.CmBlock{r0, r1, U32.xor(_, F.tf.f0(F.tf.f(tb, sk, r0, r1, ka, kb))), L.lc.rotl31.bits(U32.xor(U32.xor(L.lc.rotl1.bits(r3), F.tf.f1(F.tf.f(tb, sk, r0, r1, ka, kb))), F.tf.f1(F.tf.f(tb, sk, r0, r1, ka, kb))))} : M.CmBlock}
      %CoreL.u32_xor_cancel(r2, F.tf.f0(F.tf.f(tb, sk, r0, r1, ka, kb))) : {M.CmBlock{r0, r1, r2, r3} == M.CmBlock{r0, r1, _, L.lc.rotl31.bits(U32.xor(U32.xor(L.lc.rotl1.bits(r3), F.tf.f1(F.tf.f(tb, sk, r0, r1, ka, kb))), F.tf.f1(F.tf.f(tb, sk, r0, r1, ka, kb))))} : M.CmBlock}
      %CoreL.u32_xor_cancel(L.lc.rotl1.bits(r3), F.tf.f1(F.tf.f(tb, sk, r0, r1, ka, kb))) : {M.CmBlock{r0, r1, r2, r3} == M.CmBlock{r0, r1, r2, L.lc.rotl31.bits(_)} : M.CmBlock}
      %CoreL.rotl31_rotl1(r3) : {M.CmBlock{r0, r1, r2, r3} == M.CmBlock{r0, r1, r2, _} : M.CmBlock}
      {==}

def tf_roundd(+tb: F.LcTfTabs, +sk: List<&2, U32>, +ka: U32, +kb: U32, s: M.CmBlock) -> {s == F.tf.op(F.LcTfRound{tb, sk, ka, kb}, F.tf.unop(F.LcTfRound{tb, sk, ka, kb}, s)) : M.CmBlock}:
  match s:
    case M.CmBlock{+a, +b, +c, +d}:
      %CoreL.u32_xor_cancel(L.lc.rotl1.bits(a), F.tf.f0(F.tf.f(tb, sk, c, d, ka, kb))) : {M.CmBlock{a, b, c, d} == M.CmBlock{L.lc.rotl31.bits(_), U32.xor(L.lc.rotl1.bits(L.lc.rotl31.bits(U32.xor(b, F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb))))), F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb))), c, d} : M.CmBlock}
      %CoreL.rotl31_rotl1(a) : {M.CmBlock{a, b, c, d} == M.CmBlock{_, U32.xor(L.lc.rotl1.bits(L.lc.rotl31.bits(U32.xor(b, F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb))))), F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb))), c, d} : M.CmBlock}
      %CoreL.rotl1_rotl31(U32.xor(b, F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb)))) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, U32.xor(_, F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb))), c, d} : M.CmBlock}
      %CoreL.u32_xor_cancel(b, F.tf.f1(F.tf.f(tb, sk, c, d, ka, kb))) : {M.CmBlock{a, b, c, d} == M.CmBlock{a, _, c, d} : M.CmBlock}
      {==}

def tf_unop_op(o: F.LcTfOp, +s: M.CmBlock) -> {s == F.tf.unop(o, F.tf.op(o, s)) : M.CmBlock}:
  match o:
    case F.LcTfBswap{}:
      tf_bswap(s)
    case F.LcTfWhite{k}:
      block_xx(s, k)
    case F.LcTfRound{tb, sk, ka, kb}:
      tf_round(tb, sk, ka, kb, s)
    case F.LcTfSwap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          {==}

def tf_op_unop(o: F.LcTfOp, +s: M.CmBlock) -> {s == F.tf.op(o, F.tf.unop(o, s)) : M.CmBlock}:
  match o:
    case F.LcTfBswap{}:
      tf_bswapd(s)
    case F.LcTfWhite{k}:
      block_xx(s, k)
    case F.LcTfRound{tb, sk, ka, kb}:
      tf_roundd(tb, sk, ka, kb, s)
    case F.LcTfSwap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          {==}

def tf_unrun_run(os: List<&2, F.LcTfOp>, +s: M.CmBlock) -> {s == F.tf.unrun(os, F.tf.run(os, s)) : M.CmBlock}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      %tf_unrun_run(t, F.tf.op(o, s)) : {s == F.tf.unop(o, _) : M.CmBlock}
      tf_unop_op(o, s)

def tf_run_unrun(os: List<&2, F.LcTfOp>, +s: M.CmBlock) -> {s == F.tf.run(os, F.tf.unrun(os, s)) : M.CmBlock}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      %tf_op_unop(o, F.tf.unrun(t, s)) : {s == F.tf.run(t, _) : M.CmBlock}
      tf_run_unrun(t, s)

def Laws.twofish_round_trip(k, b):
  match k:
    case F.LcTwofishKey{ops}:
      Equal.sym(M.CmBlock, b, F.tf.unrun(ops, F.tf.run(ops, b)), tf_unrun_run(ops, b))

def Laws.twofish_round_trip_dual(k, b):
  match k:
    case F.LcTwofishKey{ops}:
      Equal.sym(M.CmBlock, b, F.tf.run(ops, F.tf.unrun(ops, b)), tf_run_unrun(ops, b))
