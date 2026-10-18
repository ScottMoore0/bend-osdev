import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./container.bend as C
import ./lzma.bend as L
import ./lzma2.bend as L2
import ./xz.bend as X
import ./alone.bend as A
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# The bound: xz_decode ends with a guard that answers XzOutputTooLarge for any
# output longer than the maximum. e says which way the guard went.
def xz_bound_pick(+max: U32, +o: B.Octets, b: Bool, +e: {b == Nat.is_le(B.Octets.len(o), U32.to_nat(max)) : Bool}) -> {Laws.xz_within(max, X.Xz.bound.pick(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)) == True{} : Bool}:
  match b:
    case True{}:
      %e : {Laws.xz_within(max, X.Xz.bound.pick(_, o)) == True{} : Bool}
      %e : {_ == True{} : Bool}
      {==}
    case False{}:
      %e : {Laws.xz_within(max, X.Xz.bound.pick(_, o)) == True{} : Bool}
      {==}

def xz_bound_ok(+max: U32, r: Result<&2, &2, E.XzError, B.Octets>) -> {Laws.xz_within(max, X.Xz.bound(max, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+o}:
      xz_bound_pick(max, o, Nat.is_le(B.Octets.len(o), U32.to_nat(max)), {==})

def Laws.output_bounded(p, i):
  xz_bound_ok(X.XzParams.max_out(p), X.xz_decode.fin(X.XzDecoder.feed(X.XzDecoder.start(p), i)))

def Laws.empty_input(p):
  {==}

# A first chunk that does not reset the dictionary: the input is read through
# bytes' law octets_to_of (as in bad_magic below), the loop's bound through
# len_fast (the feed counts its buffer with B.len.fast), then the rest
# computes.
def Laws.lzma2_needs_reset(d, m, xs):
  +k = L2.XzLzma2.start.depth(d, m)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{2, xs})), B.mask(Con{2, xs}), BL.octets_to_of(Con{2, xs})) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(L2.XzLzma2.loop(1n+B.len.fast(B.append.fast(Nil{}, _)), L2.XzL2Go{L2.XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), L2.XzL2Ctl{True{}, True{}, False{}, m, 0n, Nat.min(k, 12n), k}, B.append.fast(Nil{}, _)}, Nil{}}))) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  %BL.len_fast(B.mask(Con{2, xs})) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(L2.XzLzma2.loop(1n+_, L2.XzL2Go{L2.XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), L2.XzL2Ctl{True{}, True{}, False{}, m, 0n, Nat.min(k, 12n), k}, B.mask(Con{2, xs})}, Nil{}}))) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

def Laws.lzma2_end_only(d, m):
  {==}

def Laws.empty_file():
  {==}

def Laws.one_byte():
  {==}

def Laws.one_byte_bad_check():
  {==}

def Laws.bad_header_crc():
  {==}

def Laws.lzma2_uncompressed():
  {==}

def Laws.lzma2_too_large():
  {==}

def Laws.lzma2_dict_sizes():
  {==}

# Bad magic: the first comparison of the magic bytes fails, so the header
# parser fails, so the decoder's first step stops, whatever follows.

def xz_magic_first(+h: U32, +t: List<&2, U32>, +e: {False{} == U32.is_eq(h, 253) : Bool}) -> {Fail{E.XzBadMagic{}} == C.XzC.magic.go([55, 122, 88, 90, 0], U32.is_eq(h, 253), t, E.XzBadMagic{}) : Result<&2, &2, E.XzError, List<&2, U32>>}:
  %e : {Fail{E.XzBadMagic{}} == C.XzC.magic.go([55, 122, 88, 90, 0], _, t, E.XzBadMagic{}) : Result<&2, &2, E.XzError, List<&2, U32>>}
  {==}

def xz_header_bad(+h: U32, +t: List<&2, U32>, +e: {False{} == U32.is_eq(h, 253) : Bool}) -> {Fail{E.XzBadMagic{}} == C.XzC.header(Con{h, t}) : Result<&2, &2, E.XzError, C.XzGot<U32>>}:
  %xz_magic_first(h, t, e) : {Fail{E.XzBadMagic{}} == C.XzC.header.after(_) : Result<&2, &2, E.XzError, C.XzGot<U32>>}
  {==}

def xz_loop_bad(n: Nat, +run: X.XzRun, +h: U32, +t: List<&2, U32>, +acc: List<&2, B.Octets>, +e: {False{} == U32.is_eq(h, 253) : Bool}) -> {X.XzStop{E.XzBadMagic{}} == X.XzDecoder.loop(1n+n, X.XzGo{X.XzDecoder{X.XzPhHeader{}, run, Con{h, t}}, acc}) : X.XzStep}:
  match n:
    case 0n:
      %xz_header_bad(h, t, e) : {X.XzStop{E.XzBadMagic{}} == X.XzDecoder.loop(0n, X.Xz.header(_, run, Con{h, t}, acc)) : X.XzStep}
      {==}
    case 1n+p:
      %xz_header_bad(h, t, e) : {X.XzStop{E.XzBadMagic{}} == X.XzDecoder.loop(1n+p, X.Xz.header(_, run, Con{h, t}, acc)) : X.XzStep}
      {==}

# The decoder reads its input through bytes' law octets_to_of (a list made
# into Octets and back is the list masked), so the first byte it sees is
# B.byte(b), whatever Octets stores.
def Laws.bad_magic(p, b, xs, e):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{b, xs})), B.mask(Con{b, xs}), BL.octets_to_of(Con{b, xs})) : {X.Xz.bound(X.XzParams.max_out(p), X.xz_decode.fin(X.XzDecoder.feed.fin(X.XzDecoder.loop(1n+Nat.add(Nat.mul(2n, B.len.fast(B.append.fast(Nil{}, _))), 3n), X.XzGo{X.XzDecoder{X.XzPhHeader{}, X.XzRun{0, Nil{}, X.XzParams.max_out(p)}, B.append.fast(Nil{}, _)}, Nil{}})))) == Fail{E.XzBadMagic{}} : Result<&2, &2, E.XzError, B.Octets>}
  %xz_loop_bad(Nat.add(Nat.mul(2n, B.len.fast(Con{B.byte(b), B.mask(xs)})), 3n), X.XzRun{0, Nil{}, X.XzParams.max_out(p)}, B.byte(b), B.mask(xs), Nil{}, Equal.sym(Bool, U32.is_eq(B.byte(b), 253), False{}, e)) : {X.Xz.bound(X.XzParams.max_out(p), X.xz_decode.fin(X.XzDecoder.feed.fin(_))) == Fail{E.XzBadMagic{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

# Reserved control bytes: the control byte is at least 3, so not a stream end
# or an uncompressed chunk, and below 128, so not an LZMA chunk.

def xz_control_bad(+c: U32, +rest: List<&2, U32>, +buf: List<&2, U32>, -probs: Array<U32>, -dict: Array<U32>, +regs: L.XzLzRegs, +ctl: L2.XzL2Ctl, +acc: List<&2, U32>, +e1: {False{} == U32.is_lt(c, 3) : Bool}, +e2: {True{} == U32.is_lt(c, 128) : Bool}) -> {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.control(U32.is_lt(c, 3), c, rest, buf, probs, dict, regs, ctl, acc) : L2.XzL2Step}:
  %e1 : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.control(_, c, rest, buf, probs, dict, regs, ctl, acc) : L2.XzL2Step}
  %e2 : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.control.high(_, c, rest, buf, probs, dict, regs, ctl, acc) : L2.XzL2Step}
  {==}

def xz_loop_control_bad(n: Nat, -probs: Array<U32>, -dict: Array<U32>, +regs: L.XzLzRegs, +nr: Bool, +np: Bool, +room: U32, +cons: Nat, +dd: Nat, +md: Nat, +c: U32, +rest: List<&2, U32>, +acc: List<&2, U32>, +e1: {False{} == U32.is_lt(c, 3) : Bool}, +e2: {True{} == U32.is_lt(c, 128) : Bool}) -> {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.loop(1n+n, L2.XzL2Go{L2.XzLzma2{probs, dict, regs, L2.XzL2Ctl{nr, np, False{}, room, cons, dd, md}, Con{c, rest}}, acc}) : L2.XzL2Step}:
  match n:
    case 0n:
      %xz_control_bad(c, rest, Con{c, rest}, probs, dict, regs, L2.XzL2Ctl{nr, np, False{}, room, cons, dd, md}, acc, e1, e2) : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.loop(0n, _) : L2.XzL2Step}
      {==}
    case 1n+p:
      %xz_control_bad(c, rest, Con{c, rest}, probs, dict, regs, L2.XzL2Ctl{nr, np, False{}, room, cons, dd, md}, acc, e1, e2) : {L2.XzL2Fail{E.XzCorruptLzma{}} == L2.XzLzma2.loop(1n+p, _) : L2.XzL2Step}
      {==}

def Laws.lzma2_reserved_control(d, m, c, xs, e1, e2):
  +k = L2.XzLzma2.start.depth(d, m)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{c, xs})), B.mask(Con{c, xs}), BL.octets_to_of(Con{c, xs})) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(L2.XzLzma2.loop(1n+B.len.fast(B.append.fast(Nil{}, _)), L2.XzL2Go{L2.XzLzma2{Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), L2.XzL2Ctl{True{}, True{}, False{}, m, 0n, Nat.min(k, 12n), k}, B.append.fast(Nil{}, _)}, Nil{}}))) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  %xz_loop_control_bad(B.len.fast(Con{B.byte(c), B.mask(xs)}), Array.new(U32, 0n, 1024), Array.new(U32, Nat.min(k, 12n), 0), L2.XzLzma2.start.regs(d, k), True{}, True{}, m, 0n, Nat.min(k, 12n), k, B.byte(c), B.mask(xs), Nil{}, Equal.sym(Bool, U32.is_lt(B.byte(c), 3), False{}, e1), Equal.sym(Bool, U32.is_lt(B.byte(c), 128), True{}, e2)) : {L2.XzLzma2.decode.fin(L2.XzLzma2.feed.fin(_)) == Fail{E.XzCorruptLzma{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

# .lzma files

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_not_true(h: {False{} == True{} : Bool}) -> Empty:
  %h : bool_disc(_)
  Unit{}

def absurd(-P: Type, e: Empty) -> P:
  match e:

def and_l(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, false_not_true(h))

def and_r(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case True{}:
      h
    case False{}:
      absurd({q == True{} : Bool}, false_not_true(h))

def not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      absurd({False{} == True{} : Bool}, false_not_true(h))
    case False{}:
      {==}

# BEGIN generated by gen/proofs.py: do not edit by hand

def al_props(+lc: Nat, +lp: Nat, +pb: Nat, +ys: List<&2, U32>, e1: {Nat.is_le(Nat.add(lc, lp), 4n) == True{} : Bool}, e2: {Nat.is_le(pb, 4n) == True{} : Bool}) -> {A.XzAl.parse.fields(lc, lp, pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(lc, lp, pb))), B.byte(A.XzAlone.props(lc, lp, pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}:
  match lc:
    case 0n:
      match lp:
        case 0n:
          match pb:
            case 0n:
              {==}
            case 1n+pb0:
              match pb0:
                case 0n:
                  {==}
                case 1n+pb1:
                  match pb1:
                    case 0n:
                      {==}
                    case 1n+pb2:
                      match pb2:
                        case 0n:
                          {==}
                        case 1n+pb3:
                          match pb3:
                            case 0n:
                              {==}
                            case 1n+pb4:
                              absurd({A.XzAl.parse.fields(0n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(0n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(0n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
        case 1n+lp0:
          match lp0:
            case 0n:
              match pb:
                case 0n:
                  {==}
                case 1n+pb0:
                  match pb0:
                    case 0n:
                      {==}
                    case 1n+pb1:
                      match pb1:
                        case 0n:
                          {==}
                        case 1n+pb2:
                          match pb2:
                            case 0n:
                              {==}
                            case 1n+pb3:
                              match pb3:
                                case 0n:
                                  {==}
                                case 1n+pb4:
                                  absurd({A.XzAl.parse.fields(0n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(0n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(0n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
            case 1n+lp1:
              match lp1:
                case 0n:
                  match pb:
                    case 0n:
                      {==}
                    case 1n+pb0:
                      match pb0:
                        case 0n:
                          {==}
                        case 1n+pb1:
                          match pb1:
                            case 0n:
                              {==}
                            case 1n+pb2:
                              match pb2:
                                case 0n:
                                  {==}
                                case 1n+pb3:
                                  match pb3:
                                    case 0n:
                                      {==}
                                    case 1n+pb4:
                                      absurd({A.XzAl.parse.fields(0n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(0n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(0n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                case 1n+lp2:
                  match lp2:
                    case 0n:
                      match pb:
                        case 0n:
                          {==}
                        case 1n+pb0:
                          match pb0:
                            case 0n:
                              {==}
                            case 1n+pb1:
                              match pb1:
                                case 0n:
                                  {==}
                                case 1n+pb2:
                                  match pb2:
                                    case 0n:
                                      {==}
                                    case 1n+pb3:
                                      match pb3:
                                        case 0n:
                                          {==}
                                        case 1n+pb4:
                                          absurd({A.XzAl.parse.fields(0n, 3n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(0n, 3n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(0n, 3n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                    case 1n+lp3:
                      match lp3:
                        case 0n:
                          match pb:
                            case 0n:
                              {==}
                            case 1n+pb0:
                              match pb0:
                                case 0n:
                                  {==}
                                case 1n+pb1:
                                  match pb1:
                                    case 0n:
                                      {==}
                                    case 1n+pb2:
                                      match pb2:
                                        case 0n:
                                          {==}
                                        case 1n+pb3:
                                          match pb3:
                                            case 0n:
                                              {==}
                                            case 1n+pb4:
                                              absurd({A.XzAl.parse.fields(0n, 4n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(0n, 4n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(0n, 4n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                        case 1n+lp4:
                          absurd({A.XzAl.parse.fields(0n, 1n+(1n+(1n+(1n+(1n+(lp4))))), pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(0n, 1n+(1n+(1n+(1n+(1n+(lp4))))), pb))), B.byte(A.XzAlone.props(0n, 1n+(1n+(1n+(1n+(1n+(lp4))))), pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e1))
    case 1n+lc0:
      match lc0:
        case 0n:
          match lp:
            case 0n:
              match pb:
                case 0n:
                  {==}
                case 1n+pb0:
                  match pb0:
                    case 0n:
                      {==}
                    case 1n+pb1:
                      match pb1:
                        case 0n:
                          {==}
                        case 1n+pb2:
                          match pb2:
                            case 0n:
                              {==}
                            case 1n+pb3:
                              match pb3:
                                case 0n:
                                  {==}
                                case 1n+pb4:
                                  absurd({A.XzAl.parse.fields(1n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(1n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(1n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
            case 1n+lp0:
              match lp0:
                case 0n:
                  match pb:
                    case 0n:
                      {==}
                    case 1n+pb0:
                      match pb0:
                        case 0n:
                          {==}
                        case 1n+pb1:
                          match pb1:
                            case 0n:
                              {==}
                            case 1n+pb2:
                              match pb2:
                                case 0n:
                                  {==}
                                case 1n+pb3:
                                  match pb3:
                                    case 0n:
                                      {==}
                                    case 1n+pb4:
                                      absurd({A.XzAl.parse.fields(1n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(1n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(1n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                case 1n+lp1:
                  match lp1:
                    case 0n:
                      match pb:
                        case 0n:
                          {==}
                        case 1n+pb0:
                          match pb0:
                            case 0n:
                              {==}
                            case 1n+pb1:
                              match pb1:
                                case 0n:
                                  {==}
                                case 1n+pb2:
                                  match pb2:
                                    case 0n:
                                      {==}
                                    case 1n+pb3:
                                      match pb3:
                                        case 0n:
                                          {==}
                                        case 1n+pb4:
                                          absurd({A.XzAl.parse.fields(1n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(1n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(1n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                    case 1n+lp2:
                      match lp2:
                        case 0n:
                          match pb:
                            case 0n:
                              {==}
                            case 1n+pb0:
                              match pb0:
                                case 0n:
                                  {==}
                                case 1n+pb1:
                                  match pb1:
                                    case 0n:
                                      {==}
                                    case 1n+pb2:
                                      match pb2:
                                        case 0n:
                                          {==}
                                        case 1n+pb3:
                                          match pb3:
                                            case 0n:
                                              {==}
                                            case 1n+pb4:
                                              absurd({A.XzAl.parse.fields(1n, 3n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(1n, 3n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(1n, 3n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                        case 1n+lp3:
                          absurd({A.XzAl.parse.fields(1n, 1n+(1n+(1n+(1n+(lp3)))), pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(1n, 1n+(1n+(1n+(1n+(lp3)))), pb))), B.byte(A.XzAlone.props(1n, 1n+(1n+(1n+(1n+(lp3)))), pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e1))
        case 1n+lc1:
          match lc1:
            case 0n:
              match lp:
                case 0n:
                  match pb:
                    case 0n:
                      {==}
                    case 1n+pb0:
                      match pb0:
                        case 0n:
                          {==}
                        case 1n+pb1:
                          match pb1:
                            case 0n:
                              {==}
                            case 1n+pb2:
                              match pb2:
                                case 0n:
                                  {==}
                                case 1n+pb3:
                                  match pb3:
                                    case 0n:
                                      {==}
                                    case 1n+pb4:
                                      absurd({A.XzAl.parse.fields(2n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(2n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(2n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                case 1n+lp0:
                  match lp0:
                    case 0n:
                      match pb:
                        case 0n:
                          {==}
                        case 1n+pb0:
                          match pb0:
                            case 0n:
                              {==}
                            case 1n+pb1:
                              match pb1:
                                case 0n:
                                  {==}
                                case 1n+pb2:
                                  match pb2:
                                    case 0n:
                                      {==}
                                    case 1n+pb3:
                                      match pb3:
                                        case 0n:
                                          {==}
                                        case 1n+pb4:
                                          absurd({A.XzAl.parse.fields(2n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(2n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(2n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                    case 1n+lp1:
                      match lp1:
                        case 0n:
                          match pb:
                            case 0n:
                              {==}
                            case 1n+pb0:
                              match pb0:
                                case 0n:
                                  {==}
                                case 1n+pb1:
                                  match pb1:
                                    case 0n:
                                      {==}
                                    case 1n+pb2:
                                      match pb2:
                                        case 0n:
                                          {==}
                                        case 1n+pb3:
                                          match pb3:
                                            case 0n:
                                              {==}
                                            case 1n+pb4:
                                              absurd({A.XzAl.parse.fields(2n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(2n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(2n, 2n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                        case 1n+lp2:
                          absurd({A.XzAl.parse.fields(2n, 1n+(1n+(1n+(lp2))), pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(2n, 1n+(1n+(1n+(lp2))), pb))), B.byte(A.XzAlone.props(2n, 1n+(1n+(1n+(lp2))), pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e1))
            case 1n+lc2:
              match lc2:
                case 0n:
                  match lp:
                    case 0n:
                      match pb:
                        case 0n:
                          {==}
                        case 1n+pb0:
                          match pb0:
                            case 0n:
                              {==}
                            case 1n+pb1:
                              match pb1:
                                case 0n:
                                  {==}
                                case 1n+pb2:
                                  match pb2:
                                    case 0n:
                                      {==}
                                    case 1n+pb3:
                                      match pb3:
                                        case 0n:
                                          {==}
                                        case 1n+pb4:
                                          absurd({A.XzAl.parse.fields(3n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(3n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(3n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                    case 1n+lp0:
                      match lp0:
                        case 0n:
                          match pb:
                            case 0n:
                              {==}
                            case 1n+pb0:
                              match pb0:
                                case 0n:
                                  {==}
                                case 1n+pb1:
                                  match pb1:
                                    case 0n:
                                      {==}
                                    case 1n+pb2:
                                      match pb2:
                                        case 0n:
                                          {==}
                                        case 1n+pb3:
                                          match pb3:
                                            case 0n:
                                              {==}
                                            case 1n+pb4:
                                              absurd({A.XzAl.parse.fields(3n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(3n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(3n, 1n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                        case 1n+lp1:
                          absurd({A.XzAl.parse.fields(3n, 1n+(1n+(lp1)), pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(3n, 1n+(1n+(lp1)), pb))), B.byte(A.XzAlone.props(3n, 1n+(1n+(lp1)), pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e1))
                case 1n+lc3:
                  match lc3:
                    case 0n:
                      match lp:
                        case 0n:
                          match pb:
                            case 0n:
                              {==}
                            case 1n+pb0:
                              match pb0:
                                case 0n:
                                  {==}
                                case 1n+pb1:
                                  match pb1:
                                    case 0n:
                                      {==}
                                    case 1n+pb2:
                                      match pb2:
                                        case 0n:
                                          {==}
                                        case 1n+pb3:
                                          match pb3:
                                            case 0n:
                                              {==}
                                            case 1n+pb4:
                                              absurd({A.XzAl.parse.fields(4n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))), ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(4n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4)))))))), B.byte(A.XzAlone.props(4n, 0n, 1n+(1n+(1n+(1n+(1n+(pb4))))))), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e2))
                        case 1n+lp0:
                          absurd({A.XzAl.parse.fields(4n, 1n+(lp0), pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(4n, 1n+(lp0), pb))), B.byte(A.XzAlone.props(4n, 1n+(lp0), pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e1))
                    case 1n+lc4:
                      absurd({A.XzAl.parse.fields(1n+(1n+(1n+(1n+(1n+(lc4))))), lp, pb, ys) == A.XzAl.parse.props(A.XzAlone.props_valid(B.byte(A.XzAlone.props(1n+(1n+(1n+(1n+(1n+(lc4))))), lp, pb))), B.byte(A.XzAlone.props(1n+(1n+(1n+(1n+(1n+(lc4))))), lp, pb)), ys) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e1))

def al_fields(+lc: Nat, +lp: Nat, +pb: Nat, +d: U32, +x: U32, +y: U32, +r: List<&2, U32>) -> {A.XzAl.parse.got(lc, lp, pb, Some{d}, Some{W.W64.from_parts(y, x)}) == A.XzAl.parse.fields(lc, lp, pb, B.append(B.mask(B.append(B.le32(d), B.append(B.le32(x), B.le32(y)))), r)) : Result<&2, &2, E.XzError, A.XzAloneHeader>}:
  match d x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def al_drop(+q: U32, +d: U32, +x: U32, +y: U32, +r: List<&2, U32>) -> {r == B.drop(13n, B.append(B.mask(Con{q, B.append(B.le32(d), B.append(B.le32(x), B.le32(y)))}), r)) : List<&2, U32>}:
  match d x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def al_short(+lc: Nat, +lp: Nat, +pb: Nat, xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), 12n) == True{} : Bool}) -> {Fail{E.XzTruncated{}} == A.XzAl.parse.fields(lc, lp, pb, B.mask(xs)) : Result<&2, &2, E.XzError, A.XzAloneHeader>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x0, t0}:
      match t0:
        case Nil{}:
          {==}
        case Con{x1, t1}:
          match t1:
            case Nil{}:
              {==}
            case Con{x2, t2}:
              match t2:
                case Nil{}:
                  {==}
                case Con{x3, t3}:
                  match t3:
                    case Nil{}:
                      {==}
                    case Con{x4, t4}:
                      match t4:
                        case Nil{}:
                          {==}
                        case Con{x5, t5}:
                          match t5:
                            case Nil{}:
                              {==}
                            case Con{x6, t6}:
                              match t6:
                                case Nil{}:
                                  {==}
                                case Con{x7, t7}:
                                  match t7:
                                    case Nil{}:
                                      {==}
                                    case Con{x8, t8}:
                                      match t8:
                                        case Nil{}:
                                          {==}
                                        case Con{x9, t9}:
                                          match t9:
                                            case Nil{}:
                                              {==}
                                            case Con{x10, t10}:
                                              match t10:
                                                case Nil{}:
                                                  {==}
                                                case Con{x11, t11}:
                                                  match t11:
                                                    case Nil{}:
                                                      absurd({Fail{E.XzTruncated{}} == A.XzAl.parse.fields(lc, lp, pb, B.mask(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}})) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e))
                                                    case Con{y, z}:
                                                      absurd({Fail{E.XzTruncated{}} == A.XzAl.parse.fields(lc, lp, pb, B.mask(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{y, z}}}}}}}}}}}}})) : Result<&2, &2, E.XzError, A.XzAloneHeader>}, false_not_true(e))

def al_has5(xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), 5n) == True{} : Bool}) -> {False{} == A.XzAl.has(5n, B.mask(xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x0, t0}:
      match t0:
        case Nil{}:
          {==}
        case Con{x1, t1}:
          match t1:
            case Nil{}:
              {==}
            case Con{x2, t2}:
              match t2:
                case Nil{}:
                  {==}
                case Con{x3, t3}:
                  match t3:
                    case Nil{}:
                      {==}
                    case Con{x4, t4}:
                      match t4:
                        case Nil{}:
                          absurd({False{} == A.XzAl.has(5n, B.mask(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}})) : Bool}, false_not_true(e))
                        case Con{y, z}:
                          absurd({False{} == A.XzAl.has(5n, B.mask(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{y, z}}}}}})) : Bool}, false_not_true(e))

# END generated by gen/proofs.py

# a size written and read back is itself (all ones being unknown)
def al_size(s: Maybe<&2, W.W64>, e: {A.XzAl.size_ok(s) == True{} : Bool}) -> {s == A.XzAl.size_of(A.XzAl.size_field(s)) : Maybe<&2, W.W64>}:
  match s:
    case None{}:
      {==}
    case Some{+w}:
      %not_true(W.W64.is_eq(w, W.W64.max()), e) : {Some{w} == A.XzAl.size_of.pick(_, w) : Maybe<&2, W.W64>}
      {==}

# The header round trip: through bytes' interface laws to the parser's list,
# then the properties byte (al_props), the fields (al_fields, on the size's
# halves, which word64's parts_of joins), and the size (al_size)
def al_rt(+lc: Nat, +lp: Nat, +pb: Nat, +d: U32, +s: Maybe<&2, W.W64>, +rest: B.Octets, +e: {A.XzAloneHeader.valid(A.XzAloneHeader{lc, lp, pb, d, s}) == True{} : Bool}) -> {A.XzAlone.header(B.Octets.append(A.XzAlone.header_bytes(A.XzAloneHeader{lc, lp, pb, d, s}), rest)) == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}:
  +t = {Con{A.XzAlone.props(lc, lp, pb), B.append(B.le32(d), B.le64(A.XzAl.size_field(s)))} : List<&2, U32>}
  +ys = {B.append(B.mask(B.append(B.le32(d), B.le64(A.XzAl.size_field(s)))), B.Octets.to_list(rest)) : List<&2, U32>}
  +e23 = and_r(Nat.is_le(Nat.add(lc, lp), 4n), Bool.and(Nat.is_le(pb, 4n), A.XzAl.size_ok(s)), e)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(t), rest)), B.append(B.Octets.to_list(B.Octets.of_list(t)), B.Octets.to_list(rest)), BL.octets_append_list(B.Octets.of_list(t), rest)) : {A.XzAl.parse(_) == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(t)), B.mask(t), BL.octets_to_of(t)) : {A.XzAl.parse(B.append(_, B.Octets.to_list(rest))) == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}
  %al_props(lc, lp, pb, ys, and_l(Nat.is_le(Nat.add(lc, lp), 4n), Bool.and(Nat.is_le(pb, 4n), A.XzAl.size_ok(s)), e), and_l(Nat.is_le(pb, 4n), A.XzAl.size_ok(s), e23)) : {_ == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}
  %al_fields(lc, lp, pb, d, W.W64.lo(A.XzAl.size_field(s)), W.W64.hi(A.XzAl.size_field(s)), B.Octets.to_list(rest)) : {_ == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}
  %Equal.sym(W.W64, W.W64.from_parts(W.W64.hi(A.XzAl.size_field(s)), W.W64.lo(A.XzAl.size_field(s))), A.XzAl.size_field(s), WL.parts_of(A.XzAl.size_field(s))) : {A.XzAl.parse.got(lc, lp, pb, Some{d}, Some{_}) == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}
  %al_size(s, and_r(Nat.is_le(pb, 4n), A.XzAl.size_ok(s), e23)) : {Done{A.XzAloneHeader{lc, lp, pb, d, _}} == Done{A.XzAloneHeader{lc, lp, pb, d, s}} : Result<&2, &2, E.XzError, A.XzAloneHeader>}
  {==}

def Laws.alone_header_round_trip(h, rest, e):
  match h:
    case A.XzAloneHeader{+lc, +lp, +pb, +d, +s}:
      al_rt(lc, lp, pb, d, s, rest, e)

# A bad properties byte: the parser's first test fails
def Laws.alone_bad_props(p, b, xs, e):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{b, xs})), B.mask(Con{b, xs}), BL.octets_to_of(Con{b, xs})) : {A.XzAl.decode.hdr(A.XzAl.parse(_), p, _) == Fail{E.XzBadFilterProps{}} : Result<&2, &2, E.XzError, B.Octets>}
  %Equal.sym(Bool, A.XzAlone.props_valid(B.byte(b)), False{}, e) : {A.XzAl.decode.hdr(A.XzAl.parse.props(_, B.byte(b), B.mask(xs)), p, B.mask(Con{b, xs})) == Fail{E.XzBadFilterProps{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

def Laws.alone_empty(p):
  {==}

# A header cut short: the fields cannot be read (al_short, case by case)
def Laws.alone_short_header(p, b, xs, e1, e2):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{b, xs})), B.mask(Con{b, xs}), BL.octets_to_of(Con{b, xs})) : {A.XzAl.decode.hdr(A.XzAl.parse(_), p, _) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %Equal.sym(Bool, A.XzAlone.props_valid(B.byte(b)), True{}, e1) : {A.XzAl.decode.hdr(A.XzAl.parse.props(_, B.byte(b), B.mask(xs)), p, B.mask(Con{b, xs})) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %al_short(U32.to_nat(U32.mod(B.byte(b), 9)), U32.to_nat(U32.mod(U32.div(B.byte(b), 9), 5)), U32.to_nat(U32.div(B.byte(b), 45)), xs, e2) : {A.XzAl.decode.hdr(_, p, B.mask(Con{b, xs})) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

# A stream of fewer than 5 bytes after a valid header: the header reads back
# (al_rt), its 13 bytes are skipped (al_drop), and fewer than 5 remain
# (al_has5)
def al_ss(+p: A.XzAloneParams, +lc: Nat, +lp: Nat, +pb: Nat, +d: U32, +s: Maybe<&2, W.W64>, +xs: List<&2, U32>, e1: {A.XzAloneHeader.valid(A.XzAloneHeader{lc, lp, pb, d, s}) == True{} : Bool}, e2: {Nat.is_lt(List.length(&2, U32, xs), 5n) == True{} : Bool}) -> {A.XzAlone.decode(p, B.Octets.append(A.XzAlone.header_bytes(A.XzAloneHeader{lc, lp, pb, d, s}), B.Octets.of_list(xs))) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}:
  +t = {Con{A.XzAlone.props(lc, lp, pb), B.append(B.le32(d), B.le64(A.XzAl.size_field(s)))} : List<&2, U32>}
  +i = {B.Octets.append(B.Octets.of_list(t), B.Octets.of_list(xs)) : B.Octets}
  %Equal.sym(Result<&2, &2, E.XzError, A.XzAloneHeader>, A.XzAlone.header(i), Done{A.XzAloneHeader{lc, lp, pb, d, s}}, al_rt(lc, lp, pb, d, s, B.Octets.of_list(xs), e1)) : {A.XzAl.decode.hdr(_, p, B.Octets.to_list(i)) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(i), B.append(B.Octets.to_list(B.Octets.of_list(t)), B.Octets.to_list(B.Octets.of_list(xs))), BL.octets_append_list(B.Octets.of_list(t), B.Octets.of_list(xs))) : {A.XzAl.guard(A.XzAloneHeader{lc, lp, pb, d, s}, A.XzAl.body(A.XzAloneHeader{lc, lp, pb, d, s}, p, B.drop(13n, _))) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(t)), B.mask(t), BL.octets_to_of(t)) : {A.XzAl.guard(A.XzAloneHeader{lc, lp, pb, d, s}, A.XzAl.body(A.XzAloneHeader{lc, lp, pb, d, s}, p, B.drop(13n, B.append(_, B.Octets.to_list(B.Octets.of_list(xs)))))) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {A.XzAl.guard(A.XzAloneHeader{lc, lp, pb, d, s}, A.XzAl.body(A.XzAloneHeader{lc, lp, pb, d, s}, p, B.drop(13n, B.append(B.mask(t), _)))) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %al_drop(A.XzAlone.props(lc, lp, pb), d, W.W64.lo(A.XzAl.size_field(s)), W.W64.hi(A.XzAl.size_field(s)), B.mask(xs)) : {A.XzAl.guard(A.XzAloneHeader{lc, lp, pb, d, s}, A.XzAl.body(A.XzAloneHeader{lc, lp, pb, d, s}, p, _)) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  %al_has5(xs, e2) : {A.XzAl.guard(A.XzAloneHeader{lc, lp, pb, d, s}, A.XzAl.body.go(_, A.XzAloneHeader{lc, lp, pb, d, s}, p, B.mask(xs))) == Fail{E.XzTruncated{}} : Result<&2, &2, E.XzError, B.Octets>}
  {==}

def Laws.alone_short_stream(p, h, xs, e1, e2):
  match h:
    case A.XzAloneHeader{+lc, +lp, +pb, +d, +s}:
      al_ss(p, lc, lp, pb, d, s, xs, e1, e2)

# The declared size: the decoder's last guard answers XzCorruptLzma unless
# the output has the size. e says which way the guard went.
def al_guard_pick(+h: A.XzAloneHeader, +o: B.Octets, b: Bool, +e: {b == A.XzAlone.has_size(o, A.XzAloneHeader.size(h)) : Bool}) -> {Laws.alone_size_holds(Done{h}, A.XzAl.guard.pick(A.XzAlone.has_size(o, A.XzAloneHeader.size(h)), o)) == True{} : Bool}:
  match b:
    case True{}:
      %e : {Laws.alone_size_holds(Done{h}, A.XzAl.guard.pick(_, o)) == True{} : Bool}
      %e : {_ == True{} : Bool}
      {==}
    case False{}:
      %e : {Laws.alone_size_holds(Done{h}, A.XzAl.guard.pick(_, o)) == True{} : Bool}
      {==}

def al_guard_ok(+h: A.XzAloneHeader, r: Result<&2, &2, E.XzError, B.Octets>) -> {Laws.alone_size_holds(Done{h}, A.XzAl.guard(h, r)) == True{} : Bool}:
  match r:
    case Fail{x}:
      {==}
    case Done{+o}:
      al_guard_pick(h, o, A.XzAlone.has_size(o, A.XzAloneHeader.size(h)), {==})

def al_size_ok(r: Result<&2, &2, E.XzError, A.XzAloneHeader>, +p: A.XzAloneParams, +xs: List<&2, U32>) -> {Laws.alone_size_holds(r, A.XzAl.decode.hdr(r, p, xs)) == True{} : Bool}:
  match r:
    case Fail{x}:
      {==}
    case Done{+h}:
      al_guard_ok(h, A.XzAl.body(h, p, B.drop(13n, xs)))

def Laws.alone_declared_size(p, i):
  al_size_ok(A.XzAlone.header(i), p, B.Octets.to_list(i))

def Laws.alone_props_table():
  {==}

def Laws.alone_header_python():
  {==}

def Laws.alone_header_bytes():
  {==}

def Laws.alone_unknown_size():
  {==}

def Laws.alone_known_size():
  {==}

def Laws.alone_known_empty():
  {==}

def Laws.alone_wrong_size():
  {==}

def Laws.alone_trailing():
  {==}

def Laws.alone_too_large():
  {==}
