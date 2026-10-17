import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./insn.bend as I
import ./validate.bend as V
import ./bpf.bend as R
import ./seccomp.bend as S
import ./LAWS.bend as Laws

# Contradictions

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

def absurd.res(r: Result<&2, &2, I.BpfError, Unit>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{u}:
      Empty

def absurd.fd(-e: I.BpfError, h: {Fail{e} == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> Empty:
  %h : absurd.res(_)
  Unit{}

def nat.lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# What validation's success says

def need_ok(b: Bool, -e: I.BpfError, h: {V.bpf_chk(b, e) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.fd(e, h))

def both_l(r: Result<&2, &2, I.BpfError, Unit>, -s: Result<&2, &2, I.BpfError, Unit>, h: {V.bpf_both(r, s) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {r == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}:
  match r:
    case Fail{e}:
      Empty.absurd({Fail{e} == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}, absurd.fd(e, h))
    case Done{u}:
      match u:
        case Unit{}:
          {==}

def both_r(r: Result<&2, &2, I.BpfError, Unit>, -s: Result<&2, &2, I.BpfError, Unit>, h: {V.bpf_both(r, s) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {s == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}:
  match r:
    case Fail{e}:
      Empty.absurd({s == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}, absurd.fd(e, h))
    case Done{u}:
      h

def nxt(-pc: Nat, r: Nat, h: {V.bpf_check.next(pc, r) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {Nat.is_lt(0n, r) == True{} : Bool}:
  need_ok(Nat.is_lt(0n, r), I.BpfErrNoReturn{pc}, h)

# The interpreter's steps: a step is fine if it answers, or goes on to an
# instruction that exists

def step_ok(cur: R.BpfStep, r: Nat) -> Bool:
  match cur:
    case R.BpfNext{+skip, +st}:
      Nat.is_lt(skip, r)
    case R.BpfStop{v}:
      True{}
    case R.BpfFault{e}:
      False{}

def step_of_ok(m: Maybe<&2, R.BpfState>, -r: Nat, e: {Nat.is_lt(0n, r) == True{} : Bool}) -> {step_ok(R.bpf_step.of(m), r) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{st}:
      e

def scratch_ok(ok: Bool, -k: U32, -st: R.BpfState, -r: Nat, e1: {ok == True{} : Bool}, e2: {Nat.is_lt(0n, r) == True{} : Bool}) -> {step_ok(R.bpf_scratch(ok, k, st), r) == True{} : Bool}:
  match ok:
    case True{}:
      e2
    case False{}:
      Empty.absurd({step_ok(R.bpf_scratch(False{}, k, st), r) == True{} : Bool}, absurd.ft(e1))

def mem_ok(+k: U32, -st: R.BpfState, +pc: Nat, +r: Nat, +h: {V.bpf_check.mem(k, pc, r) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {step_ok(R.bpf_scratch(U32.is_lt(k, I.bpf_memwords()), k, st), r) == True{} : Bool}:
  scratch_ok(U32.is_lt(k, I.bpf_memwords()), k, st, r, need_ok(U32.is_lt(k, I.bpf_memwords()), I.BpfErrScratch{pc}, both_l(V.bpf_chk(U32.is_lt(k, I.bpf_memwords()), I.BpfErrScratch{pc}), V.bpf_check.next(pc, r), h)), nxt(pc, r, both_r(V.bpf_chk(U32.is_lt(k, I.bpf_memwords()), I.BpfErrScratch{pc}), V.bpf_check.next(pc, r), h)))

def jsel_ok(hit: Bool, -jt: U32, -jf: U32, -r: Nat, e1: {Nat.is_lt(U32.to_nat(jt), r) == True{} : Bool}, e2: {Nat.is_lt(U32.to_nat(jf), r) == True{} : Bool}) -> {Nat.is_lt(R.bpf_jsel(hit, jt, jf), r) == True{} : Bool}:
  match hit:
    case True{}:
      e1
    case False{}:
      e2

# the two range checks inside bpf_check.jmp
def jmp_ranges(+jt: U32, +jf: U32, +pc: Nat, +r: Nat, +h: {V.bpf_check.jmp(jt, jf, pc, r) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {V.bpf_both(V.bpf_chk(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}), V.bpf_chk(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc})) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}:
  both_r(V.bpf_chk(U32.is_lt(jf, 256), I.BpfErrJumpField{pc}), V.bpf_both(V.bpf_chk(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}), V.bpf_chk(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc})), both_r(V.bpf_chk(U32.is_lt(jt, 256), I.BpfErrJumpField{pc}), V.bpf_both(V.bpf_chk(U32.is_lt(jf, 256), I.BpfErrJumpField{pc}), V.bpf_both(V.bpf_chk(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}), V.bpf_chk(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc}))), h))

def jmp_ok(+jt: U32, +jf: U32, +pc: Nat, +r: Nat, hit: Bool, h: {V.bpf_check.jmp(jt, jf, pc, r) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {Nat.is_lt(R.bpf_jsel(hit, jt, jf), r) == True{} : Bool}:
  +g = jmp_ranges(jt, jf, pc, r, h)
  jsel_ok(hit, jt, jf, r, need_ok(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}, both_l(V.bpf_chk(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}), V.bpf_chk(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc}), g)), need_ok(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc}, both_r(V.bpf_chk(Nat.is_lt(U32.to_nat(jt), r), I.BpfErrJump{pc}), V.bpf_chk(Nat.is_lt(U32.to_nat(jf), r), I.BpfErrJump{pc}), g)))

# every instruction that passed its checks steps to an instruction that exists
def exec_ok(op: I.BpfOp, st: R.BpfState, +inp: R.BpfInput, +pc: Nat, +r: Nat, h: {V.bpf_check.op(op, pc, r) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {step_ok(R.bpf_exec(op, st, inp), r) == True{} : Bool}:
  match op:
    case I.BpfLdAbs{+size, +k}:
      step_of_ok(R.bpf_set_a.m(R.bpf_load(inp, size, k), st), r, nxt(pc, r, h))
    case I.BpfLdInd{+size, +k}:
      match st:
        case R.BpfState{+a, +x, +mem}:
          step_of_ok(R.bpf_set_a.m(R.bpf_load.ind(inp, size, x, k), R.BpfState{a, x, mem}), r, nxt(pc, r, h))
    case I.BpfLdImm{+k}:
      nxt(pc, r, h)
    case I.BpfLdLen{}:
      nxt(pc, r, h)
    case I.BpfLdMem{+k}:
      mem_ok(k, R.bpf_mem.lda(st, k), pc, r, h)
    case I.BpfLdxImm{+k}:
      nxt(pc, r, h)
    case I.BpfLdxMem{+k}:
      mem_ok(k, R.bpf_mem.ldx(st, k), pc, r, h)
    case I.BpfLdxLen{}:
      nxt(pc, r, h)
    case I.BpfLdxMsh{+k}:
      step_of_ok(R.bpf_set_x.m(R.bpf_load.msh(inp, k), st), r, nxt(pc, r, h))
    case I.BpfSt{+k}:
      mem_ok(k, R.bpf_mem.st(st, k), pc, r, h)
    case I.BpfStx{+k}:
      mem_ok(k, R.bpf_mem.stx(st, k), pc, r, h)
    case I.BpfAlu{+o, +src}:
      match st:
        case R.BpfState{+a, +x, +mem}:
          step_of_ok(R.bpf_set_a.m(R.bpf_alu(o, a, R.bpf_src(src, x)), R.BpfState{a, x, mem}), r, nxt(pc, r, both_r(V.bpf_check.div(o, src, pc), V.bpf_check.next(pc, r), h)))
    case I.BpfNeg{}:
      nxt(pc, r, h)
    case I.BpfJa{+k}:
      need_ok(Nat.is_lt(U32.to_nat(k), r), I.BpfErrJump{pc}, h)
    case I.BpfJmp{+c, +src, +jt, +jf}:
      match st:
        case R.BpfState{+a, +x, +mem}:
          jmp_ok(jt, jf, pc, r, R.bpf_test(c, a, R.bpf_src(src, x)), h)
    case I.BpfRet{+v}:
      match v:
        case I.BpfRetK{+k}:
          {==}
        case I.BpfRetA{}:
          {==}
    case I.BpfTax{}:
      nxt(pc, r, h)
    case I.BpfTxa{}:
      nxt(pc, r, h)

# A run from a fine step, over instructions that passed their checks,
# answers Done: induction on the instructions
def go_ok(xs: List<&2, I.BpfOp>, cur: R.BpfStep, +inp: R.BpfInput, +pc: Nat, +v: {V.bpf_check.all(xs, pc) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}, p: {step_ok(cur, List.length(&2, I.BpfOp, xs)) == True{} : Bool}) -> {Result.is_done(&2, &2, I.BpfError, U32, R.bpf_run.go(xs, cur, inp)) == True{} : Bool}:
  match xs:
    case Nil{}:
      match cur:
        case R.BpfNext{+skip, +st}:
          Empty.absurd({Result.is_done(&2, &2, I.BpfError, U32, R.bpf_run.go(Nil{}, R.BpfNext{skip, st}, inp)) == True{} : Bool}, absurd.ft(Equal.trans(Bool, False{}, Nat.is_lt(skip, 0n), True{}, Equal.sym(Bool, Nat.is_lt(skip, 0n), False{}, nat.lt_zero(skip)), p)))
        case R.BpfStop{w}:
          {==}
        case R.BpfFault{e}:
          Empty.absurd({Result.is_done(&2, &2, I.BpfError, U32, R.bpf_run.go(Nil{}, R.BpfFault{e}, inp)) == True{} : Bool}, absurd.ft(p))
    case Con{+op, +t}:
      match cur:
        case R.BpfNext{+skip, +st}:
          match skip:
            case 0n:
              go_ok(t, R.bpf_exec(op, st, inp), inp, 1n+pc, both_r(V.bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), V.bpf_check.all(t, 1n+pc), v), exec_ok(op, st, inp, pc, List.length(&2, I.BpfOp, t), both_l(V.bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), V.bpf_check.all(t, 1n+pc), v)))
            case 1n+s:
              go_ok(t, R.BpfNext{s, st}, inp, 1n+pc, both_r(V.bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), V.bpf_check.all(t, 1n+pc), v), p)
        case R.BpfStop{w}:
          {==}
        case R.BpfFault{e}:
          Empty.absurd({Result.is_done(&2, &2, I.BpfError, U32, R.bpf_run.go(Con{op, t}, R.BpfFault{e}, inp)) == True{} : Bool}, absurd.ft(p))

# what bpf_validate's success gives a run: the checks of every instruction,
# and at least one instruction
def valid_all(opts: V.BpfValidateOptions, +prog: List<&2, I.BpfOp>, ok: {V.bpf_validate_with(opts, prog) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {V.bpf_check.all(prog, 0n) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}:
  match opts:
    case V.BpfValidateOptions{+max, +need}:
      both_l(V.bpf_check.all(prog, 0n), V.bpf_check.mem_init(need, prog), both_r(V.bpf_check.len(List.length(&2, I.BpfOp, prog), max), V.bpf_both(V.bpf_check.all(prog, 0n), V.bpf_check.mem_init(need, prog)), ok))

def valid_nonempty(opts: V.BpfValidateOptions, +prog: List<&2, I.BpfOp>, ok: {V.bpf_validate_with(opts, prog) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}) -> {Nat.is_lt(0n, List.length(&2, I.BpfOp, prog)) == True{} : Bool}:
  match opts:
    case V.BpfValidateOptions{+max, +need}:
      +n = List.length(&2, I.BpfOp, prog)
      need_ok(Nat.is_lt(0n, n), I.BpfErrEmpty{}, both_l(V.bpf_chk(Nat.is_lt(0n, n), I.BpfErrEmpty{}), V.bpf_chk(Nat.is_le(n, max), I.BpfErrTooLong{n}), both_l(V.bpf_check.len(n, max), V.bpf_both(V.bpf_check.all(prog, 0n), V.bpf_check.mem_init(need, prog)), ok)))

def Laws.validated_returns(opts, prog, inp, ok):
  go_ok(prog, R.BpfNext{0n, R.bpf_init()}, inp, 0n, valid_all(opts, prog, ok), valid_nonempty(opts, prog, ok))

# Appending instructions after a validated program changes nothing: the run
# never reaches them

def go_stop(q: List<&2, I.BpfOp>, -w: U32, +inp: R.BpfInput) -> {R.bpf_run.go(q, R.BpfStop{w}, inp) == Done{w} : Result<&2, &2, I.BpfError, U32>}:
  match q:
    case Nil{}:
      {==}
    case Con{op, t}:
      {==}

def go_app(xs: List<&2, I.BpfOp>, +q: List<&2, I.BpfOp>, cur: R.BpfStep, +inp: R.BpfInput, +pc: Nat, +v: {V.bpf_check.all(xs, pc) == Done{Unit{}} : Result<&2, &2, I.BpfError, Unit>}, p: {step_ok(cur, List.length(&2, I.BpfOp, xs)) == True{} : Bool}) -> {R.bpf_run.go(List.append(&2, I.BpfOp, xs, q), cur, inp) == R.bpf_run.go(xs, cur, inp) : Result<&2, &2, I.BpfError, U32>}:
  match xs:
    case Nil{}:
      match cur:
        case R.BpfNext{+skip, +st}:
          Empty.absurd({R.bpf_run.go(q, R.BpfNext{skip, st}, inp) == R.bpf_run.go(Nil{}, R.BpfNext{skip, st}, inp) : Result<&2, &2, I.BpfError, U32>}, absurd.ft(Equal.trans(Bool, False{}, Nat.is_lt(skip, 0n), True{}, Equal.sym(Bool, Nat.is_lt(skip, 0n), False{}, nat.lt_zero(skip)), p)))
        case R.BpfStop{w}:
          go_stop(q, w, inp)
        case R.BpfFault{e}:
          Empty.absurd({R.bpf_run.go(q, R.BpfFault{e}, inp) == R.bpf_run.go(Nil{}, R.BpfFault{e}, inp) : Result<&2, &2, I.BpfError, U32>}, absurd.ft(p))
    case Con{+op, +t}:
      match cur:
        case R.BpfNext{+skip, +st}:
          match skip:
            case 0n:
              go_app(t, q, R.bpf_exec(op, st, inp), inp, 1n+pc, both_r(V.bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), V.bpf_check.all(t, 1n+pc), v), exec_ok(op, st, inp, pc, List.length(&2, I.BpfOp, t), both_l(V.bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), V.bpf_check.all(t, 1n+pc), v)))
            case 1n+s:
              go_app(t, q, R.BpfNext{s, st}, inp, 1n+pc, both_r(V.bpf_check.op(op, pc, List.length(&2, I.BpfOp, t)), V.bpf_check.all(t, 1n+pc), v), p)
        case R.BpfStop{w}:
          {==}
        case R.BpfFault{e}:
          Empty.absurd({R.bpf_run.go(Con{op, List.append(&2, I.BpfOp, t, q)}, R.BpfFault{e}, inp) == R.bpf_run.go(Con{op, t}, R.BpfFault{e}, inp) : Result<&2, &2, I.BpfError, U32>}, absurd.ft(p))

def Laws.validated_ignores_tail(opts, prog, rest, inp, ok):
  go_app(prog, rest, R.BpfNext{0n, R.bpf_init()}, inp, 0n, valid_all(opts, prog, ok), valid_nonempty(opts, prog, ok))

def Laws.ret_k(k, inp):
  {==}

# Jumps move forward over exactly the instructions they skip: induction on
# the skipped instructions

def skip_app(skipped: List<&2, I.BpfOp>, +rest: List<&2, I.BpfOp>, +st: R.BpfState, +inp: R.BpfInput) -> {R.bpf_run.go(List.append(&2, I.BpfOp, skipped, rest), R.BpfNext{List.length(&2, I.BpfOp, skipped), st}, inp) == R.bpf_run.go(rest, R.BpfNext{0n, st}, inp) : Result<&2, &2, I.BpfError, U32>}:
  match skipped:
    case Nil{}:
      {==}
    case Con{h, t}:
      skip_app(t, rest, st, inp)

def Laws.ja_skips(k, skipped, rest, inp, e):
  %e : {R.bpf_run.go(List.append(&2, I.BpfOp, skipped, rest), R.BpfNext{_, R.bpf_init()}, inp) == R.bpf_run(inp, rest) : Result<&2, &2, I.BpfError, U32>}
  skip_app(skipped, rest, R.bpf_init(), inp)

def Laws.jeq_taken_skips(jt, jf, skipped, rest, inp, e):
  %e : {R.bpf_run.go(List.append(&2, I.BpfOp, skipped, rest), R.BpfNext{_, R.bpf_init()}, inp) == R.bpf_run(inp, rest) : Result<&2, &2, I.BpfError, U32>}
  skip_app(skipped, rest, R.bpf_init(), inp)

def Laws.jeq_not_taken_skips(jt, jf, skipped, rest, inp, e):
  %e : {R.bpf_run.go(List.append(&2, I.BpfOp, skipped, rest), R.BpfNext{_, R.bpf_init()}, inp) == R.bpf_run(inp, rest) : Result<&2, &2, I.BpfError, U32>}
  skip_app(skipped, rest, R.bpf_init(), inp)

# Decoding what encoding wrote gives the instructions back

def Laws.insn_round_trip(op):
  match op:
    case I.BpfLdAbs{size, k}:
      match size:
        case I.BpfW{}:
          {==}
        case I.BpfH{}:
          {==}
        case I.BpfB{}:
          {==}
    case I.BpfLdInd{size, k}:
      match size:
        case I.BpfW{}:
          {==}
        case I.BpfH{}:
          {==}
        case I.BpfB{}:
          {==}
    case I.BpfLdImm{k}:
      {==}
    case I.BpfLdLen{}:
      {==}
    case I.BpfLdMem{k}:
      {==}
    case I.BpfLdxImm{k}:
      {==}
    case I.BpfLdxMem{k}:
      {==}
    case I.BpfLdxLen{}:
      {==}
    case I.BpfLdxMsh{k}:
      {==}
    case I.BpfSt{k}:
      {==}
    case I.BpfStx{k}:
      {==}
    case I.BpfNeg{}:
      {==}
    case I.BpfJa{k}:
      {==}
    case I.BpfTax{}:
      {==}
    case I.BpfTxa{}:
      {==}
    case I.BpfAlu{a, src}:
      match a:
        case I.BpfAdd{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfSub{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfMul{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfDiv{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfOr{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfAnd{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfLsh{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfRsh{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfMod{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfXor{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
    case I.BpfJmp{c, src, jt, jf}:
      match c:
        case I.BpfJeq{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfJgt{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfJge{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
        case I.BpfJset{}:
          match src:
            case I.BpfK{k}:
              {==}
            case I.BpfX{}:
              {==}
    case I.BpfRet{v}:
      match v:
        case I.BpfRetK{k}:
          {==}
        case I.BpfRetA{}:
          {==}

def decode_go(prog: List<&2, I.BpfOp>, +pc: Nat) -> {I.bpf_decode.go(I.bpf_encode(prog), pc) == Done{prog} : Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>}:
  match prog:
    case Nil{}:
      {==}
    case Con{+op, +t}:
      %Equal.sym(Maybe<&2, I.BpfOp>, I.BpfRaw.decode(I.BpfOp.encode(op)), Some{op}, Laws.insn_round_trip(op)) : {I.bpf_decode.cons(_, I.BpfErrBadCode{pc, I.BpfRaw.code(I.BpfOp.encode(op))}, I.bpf_decode.go(I.bpf_encode(t), 1n+pc)) == Done{Con{op, t}} : Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>}
      %Equal.sym(Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>, I.bpf_decode.go(I.bpf_encode(t), 1n+pc), Done{t}, decode_go(t, 1n+pc)) : {I.bpf_decode.cons(Some{op}, I.BpfErrBadCode{pc, I.BpfRaw.code(I.BpfOp.encode(op))}, _) == Done{Con{op, t}} : Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>}
      {==}

def Laws.program_round_trip(prog):
  decode_go(prog, 0n)


# Seccomp actions, by cases

def Laws.most_restrictive(a, b):
  match a:
    case S.SeccompKillProcess{}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompKillThread{}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompTrap{da}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompErrno{da}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompUserNotif{}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompTrace{da}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompLog{}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}
    case S.SeccompAllow{}:
      match b:
        case S.SeccompKillProcess{}:
          {==}
        case S.SeccompKillThread{}:
          {==}
        case S.SeccompTrap{db}:
          {==}
        case S.SeccompErrno{db}:
          {==}
        case S.SeccompUserNotif{}:
          {==}
        case S.SeccompTrace{db}:
          {==}
        case S.SeccompLog{}:
          {==}
        case S.SeccompAllow{}:
          {==}

def Laws.combine_assoc(a, b, c):
  match a:
    case S.SeccompKillProcess{}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompKillThread{}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompTrap{da}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompErrno{da}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompUserNotif{}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompTrace{da}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompLog{}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
    case S.SeccompAllow{}:
      match b:
        case S.SeccompKillProcess{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompKillThread{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrap{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompErrno{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompUserNotif{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompTrace{db}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompLog{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}
        case S.SeccompAllow{}:
          match c:
            case S.SeccompKillProcess{}:
              {==}
            case S.SeccompKillThread{}:
              {==}
            case S.SeccompTrap{dc}:
              {==}
            case S.SeccompErrno{dc}:
              {==}
            case S.SeccompUserNotif{}:
              {==}
            case S.SeccompTrace{dc}:
              {==}
            case S.SeccompLog{}:
              {==}
            case S.SeccompAllow{}:
              {==}

def Laws.action_round_trip(a):
  match a:
    case S.SeccompKillProcess{}:
      {==}
    case S.SeccompKillThread{}:
      {==}
    case S.SeccompTrap{d}:
      match d:
        case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          {==}
    case S.SeccompErrno{d}:
      match d:
        case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          {==}
    case S.SeccompUserNotif{}:
      {==}
    case S.SeccompTrace{d}:
      match d:
        case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          {==}
    case S.SeccompLog{}:
      {==}
    case S.SeccompAllow{}:
      {==}
def nat.lt_not_le(x: Nat, y: Nat, e: {Nat.is_lt(y, x) == True{} : Bool}) -> {Nat.is_le(x, y) == False{} : Bool}:
  match x y:
    case 0n _:
      Empty.absurd({Nat.is_le(0n, y) == False{} : Bool}, absurd.ft(Equal.trans(Bool, False{}, Nat.is_lt(y, 0n), True{}, Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, nat.lt_zero(y)), e)))
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      nat.lt_not_le(xp, yp, e)

def Laws.combine_newer(a, b, e):
  %Equal.sym(Bool, Nat.is_le(S.SeccompAction.rank(a), S.SeccompAction.rank(b)), True{}, e) : {S.seccomp_combine.pick(_, a, b) == a : S.SeccompAction}
  {==}

def Laws.combine_older(a, b, e):
  %Equal.sym(Bool, Nat.is_le(S.SeccompAction.rank(a), S.SeccompAction.rank(b)), False{}, nat.lt_not_le(S.SeccompAction.rank(a), S.SeccompAction.rank(b), e)) : {S.seccomp_combine.pick(_, a, b) == b : S.SeccompAction}
  {==}

def fin_done(r: Result<&2, &2, I.BpfError, U32>, e: {Result.is_done(&2, &2, I.BpfError, U32, r) == True{} : Bool}) -> {Result.is_done(&2, &2, I.BpfError, S.SeccompAction, S.seccomp_run.fin(r)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({Result.is_done(&2, &2, I.BpfError, S.SeccompAction, S.seccomp_run.fin(Fail{f})) == True{} : Bool}, absurd.ft(e))
    case Done{v}:
      {==}

def Laws.seccomp_validated_acts(opts, order, prog, d, ok):
  fin_done(R.bpf_run(S.SeccompData.input(order, d), prog), Laws.validated_returns(opts, prog, S.SeccompData.input(order, d), both_l(V.bpf_validate_with(opts, prog), S.seccomp_check.all(prog, 0n), ok)))

# Vectors, by computation

def Laws.rarp_prepares():
  {==}

def Laws.rarp_accepts():
  {==}

def Laws.rarp_rejects_arp():
  {==}

def Laws.hosts_accepts():
  {==}

def Laws.hosts_rejects():
  {==}

def Laws.finger_accepts():
  {==}

def Laws.finger_accepts_options():
  {==}

def Laws.finger_rejects_port():
  {==}

def Laws.finger_rejects_fragment():
  {==}

def Laws.short_packet():
  {==}

def Laws.divide_by_zero_x():
  {==}

def Laws.length_load():
  {==}

def Laws.scratch_and_alu():
  {==}

def Laws.validate_accepts():
  {==}

def Laws.validate_empty():
  {==}

def Laws.validate_too_long():
  {==}

def Laws.validate_jump_out():
  {==}

def Laws.validate_no_return():
  {==}

def Laws.validate_scratch():
  {==}

def Laws.validate_div_zero():
  {==}

def Laws.decode_bad_opcode():
  {==}

def Laws.program_bytes():
  {==}

def Laws.program_bytes_back():
  {==}

def Laws.seccomp_example_valid():
  {==}

def Laws.seccomp_example_errno():
  {==}

def Laws.seccomp_example_allow():
  {==}

def Laws.seccomp_example_other_arch():
  {==}

def Laws.seccomp_example_x32():
  {==}

def Laws.seccomp_rejects_byte_load():
  {==}

def Laws.seccomp_rejects_unaligned():
  {==}

def Laws.stack_newest_on_tie():
  {==}

def Laws.stack_most_restrictive():
  {==}

def Laws.stack_empty_allows():
  {==}

def Laws.unknown_action_kills():
  {==}

def Laws.install_path_limit():
  {==}

def Laws.install_pushes():
  {==}

def Laws.seccomp_rejects_mod():
  {==}

def Laws.seccomp_example_write():
  {==}

def Laws.seccomp_example_preadv():
  {==}

def Laws.validate_mem_init():
  {==}

def Laws.validate_mem_init_path():
  {==}

def Laws.validate_mem_init_written():
  {==}

def Laws.validate_permissive():
  {==}

def Laws.witness_skip_length():
  {==}

def Laws.witness_rank_le():
  {==}

def Laws.witness_rank_lt():
  {==}

def Laws.validate_mem_after_jump():
  {==}

def Laws.validate_mem_after_return():
  {==}

