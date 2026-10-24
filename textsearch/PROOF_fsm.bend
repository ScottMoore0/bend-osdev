# Proofs of LAWS_fsm.bend: the token automaton finds exactly what the
# backtracking reference finds. The method is apparmor's (glob_run):
#
# * fs.full, the reference's matcher without its fuel (fs.fuel_ok: the
#   fuel ts.fsm.naive gives is always enough), on the tokens with TsPlus
#   written as TsOne then TsStar as the automaton keeps them (fs.exp_ok);
# * fs.sem(E, a, s): what a set of positions accepts, some active
#   position whose remaining tokens match s exactly;
# * each pass of the step takes one meaning to the next: closing over
#   optional tokens adds nothing (fs.CL), reading a byte moves the closed
#   set's meaning on by one byte (fs.AL, fs.CA), and starting a match adds
#   the whole pattern (fs.ST); so after a byte c the set accepts w exactly
#   when the set before accepted c then w, or the pattern matches c then w
#   (fs.STEP), and it accepts the empty run exactly when its last position
#   is active (fs.HIT), which is the automaton's report;
# * the reference reports at the end of each prefix whether some
#   non-empty run ending there matches; from a set a, the automaton's
#   reports on the rest of the text are those, or a match begun before and
#   accepted by a (fs.run); from the start no position is active.
import Base
import ./textsearch.bend as T
import ./auto.bend as A
import ./fsm.bend as F
import ./proof_lib.bend as L
import ./LAWS_fsm.bend as Laws

# Sets of positions

def fs.hd(s: List<&2, Bool>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{b, t}:
      b

def fs.tl(s: List<&2, Bool>) -> List<&2, Bool>:
  match s:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      t

def fs.is_con(s: List<&2, Bool>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{b, t}:
      True{}

def fs.pick(c: Bool, x: Bool, y: Bool) -> Bool:
  match c:
    case True{}:
      x
    case False{}:
      y

# a has an entry for every position of E (one per token, and the end)
def fs.shaped(E: List<&2, F.TsToken>, a: List<&2, Bool>) -> Bool:
  match E a:
    case Nil{} Nil{}:
      False{}
    case Nil{} Con{x, r}:
      True{}
    case Con{tk, tt} Nil{}:
      False{}
    case Con{tk, tt} Con{x, r}:
      fs.shaped(tt, r)

# no TsPlus (the automaton's tokens)
def fs.noplus(E: List<&2, F.TsToken>) -> Bool:
  match E:
    case Nil{}:
      True{}
    case Con{F.TsToken{cl, r}, tt}:
      match r:
        case F.TsPlus{}:
          False{}
        case F.TsOne{}:
          fs.noplus(tt)
        case F.TsPerhaps{}:
          fs.noplus(tt)
        case F.TsStar{}:
          fs.noplus(tt)

# The reference's matcher without fuel

# whether the tokens match no bytes
def fs.full_nil(tks: List<&2, F.TsToken>) -> Bool:
  match tks:
    case Nil{}:
      True{}
    case Con{F.TsToken{cl, r}, tt}:
      match r:
        case F.TsOne{}:
          False{}
        case F.TsPerhaps{}:
          fs.full_nil(tt)
        case F.TsStar{}:
          fs.full_nil(tt)
        case F.TsPlus{}:
          False{}

# whether the tokens match exactly the bytes xs
def fs.full(xs: List<&2, U32>, tks: List<&2, F.TsToken>) -> Bool:
  match xs:
    case Nil{}:
      fs.full_nil(tks)
    case Con{+c, +t}:
      match tks:
        case Nil{}:
          False{}
        case Con{F.TsToken{+cl, r}, +tt}:
          match r:
            case F.TsOne{}:
              Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt))
            case F.TsPerhaps{}:
              Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt)))
            case F.TsStar{}:
              Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt})))
            case F.TsPlus{}:
              Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}))

# what a set of positions accepts: some active position's tokens match s
def fs.sem(E: List<&2, F.TsToken>, +a: List<&2, Bool>, +s: List<&2, U32>) -> Bool:
  match E:
    case Nil{}:
      Bool.and(fs.hd(a), fs.full(s, Nil{}))
    case Con{+tk, +tt}:
      Bool.or(Bool.and(fs.hd(a), fs.full(s, Con{tk, tt})), fs.sem(tt, fs.tl(a), s))

# what a set accepts after one byte c: an active position whose token
# takes c, then the rest w from where the token leaves it
def fs.adv(E: List<&2, F.TsToken>, +a: List<&2, Bool>, +c: U32, +w: List<&2, U32>) -> Bool:
  match E:
    case Nil{}:
      False{}
    case Con{+tk, +tt}:
      Bool.or(Bool.and(Bool.and(fs.hd(a), F.ts.fsm.matches(tk, c)), fs.pick(F.ts.fsm.stays(tk), fs.full(w, Con{tk, tt}), fs.full(w, tt))), fs.adv(tt, fs.tl(a), c, w))

# the automaton's step on the positions
def fs.a2(+E: List<&2, F.TsToken>, +act: List<&2, Bool>, +c: U32) -> List<&2, Bool>:
  F.ts.fsm.close(E, F.ts.fsm.advance(E, F.ts.fsm.close(E, F.ts.fsm.start_here(act), False{}), c, False{}), False{})

# Bool identities, by cases

def fs.t_cl_nil3(+x: Bool, +cr: Bool, +F: Bool) -> {Bool.and(Bool.or(x, cr), F) == Bool.or(Bool.and(cr, F), Bool.and(x, F)) : Bool}:
  match x:
    case True{}:
      match cr:
        case True{}:
          match F:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match F:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match cr:
        case True{}:
          match F:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match F:
            case True{}:
              {==}
            case False{}:
              {==}

def fs.t_cl_no(+x: Bool, +cr: Bool, +FE: Bool, +Ftt: Bool, +S: Bool) -> {Bool.or(Bool.and(Bool.or(x, cr), FE), Bool.or(Bool.and(Bool.and(Bool.or(x, cr), False{}), Ftt), S)) == Bool.or(Bool.and(cr, FE), Bool.or(Bool.and(x, FE), S)) : Bool}:
  match x:
    case True{}:
      match cr:
        case True{}:
          match FE:
            case True{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match FE:
            case True{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
    case False{}:
      match cr:
        case True{}:
          match FE:
            case True{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match FE:
            case True{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Ftt:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

def fs.t_cl_nilopt(+x: Bool, +cr: Bool, +F: Bool, +S: Bool) -> {Bool.or(Bool.and(Bool.or(x, cr), F), Bool.or(Bool.and(Bool.and(Bool.or(x, cr), True{}), F), S)) == Bool.or(Bool.and(cr, F), Bool.or(Bool.and(x, F), S)) : Bool}:
  match x:
    case True{}:
      match cr:
        case True{}:
          match F:
            case True{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match F:
            case True{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match cr:
        case True{}:
          match F:
            case True{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match F:
            case True{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match S:
                case True{}:
                  {==}
                case False{}:
                  {==}

def fs.t_cl_con(+x: Bool, +cr: Bool, +G: Bool, +Y: Bool, +S: Bool) -> {Bool.or(Bool.and(Bool.or(x, cr), Bool.or(G, Y)), Bool.or(Bool.and(Bool.and(Bool.or(x, cr), True{}), G), S)) == Bool.or(Bool.and(cr, Bool.or(G, Y)), Bool.or(Bool.and(x, Bool.or(G, Y)), S)) : Bool}:
  match x:
    case True{}:
      match cr:
        case True{}:
          match G:
            case True{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match G:
            case True{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
    case False{}:
      match cr:
        case True{}:
          match G:
            case True{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match G:
            case True{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Y:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

def fs.t_al(+inc: Bool, +mt: Bool, +st: Bool, +FE: Bool, +Ftt: Bool, +A: Bool) -> {Bool.or(Bool.and(Bool.or(inc, Bool.and(mt, st)), FE), Bool.or(Bool.and(Bool.and(mt, Bool.not(st)), Ftt), A)) == Bool.or(Bool.and(inc, FE), Bool.or(Bool.and(mt, fs.pick(st, FE, Ftt)), A)) : Bool}:
  match inc:
    case True{}:
      match mt:
        case True{}:
          match st:
            case True{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
            case False{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
        case False{}:
          match st:
            case True{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
            case False{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
    case False{}:
      match mt:
        case True{}:
          match st:
            case True{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
            case False{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
        case False{}:
          match st:
            case True{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
            case False{}:
              match FE:
                case True{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match Ftt:
                    case True{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match A:
                        case True{}:
                          {==}
                        case False{}:
                          {==}

def fs.t_ca_one(+o: Bool, +m: Bool, +F: Bool, +Z: Bool) -> {Bool.or(Bool.and(Bool.and(o, m), F), Z) == Bool.or(Bool.and(o, Bool.and(m, F)), Z) : Bool}:
  match o:
    case True{}:
      match m:
        case True{}:
          match F:
            case True{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match F:
            case True{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match m:
        case True{}:
          match F:
            case True{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match F:
            case True{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match Z:
                case True{}:
                  {==}
                case False{}:
                  {==}

def fs.t_ca_opt(+o: Bool, +m: Bool, +Fw: Bool, +Fcw: Bool, +S: Bool) -> {Bool.or(Bool.and(Bool.and(o, m), Fw), Bool.or(Bool.and(Bool.and(o, True{}), Fcw), S)) == Bool.or(Bool.and(o, Bool.or(Fcw, Bool.and(m, Fw))), Bool.or(Bool.and(Bool.and(o, True{}), Fcw), S)) : Bool}:
  match o:
    case True{}:
      match m:
        case True{}:
          match Fw:
            case True{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match Fw:
            case True{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
    case False{}:
      match m:
        case True{}:
          match Fw:
            case True{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match Fw:
            case True{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match Fcw:
                case True{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match S:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

def fs.t_st_nil(+F: Bool, +x: Bool) -> {F == Bool.or(F, Bool.and(x, F)) : Bool}:
  match F:
    case True{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}

def fs.t_st_con(+FE: Bool, +x: Bool, +S: Bool) -> {Bool.or(FE, S) == Bool.or(FE, Bool.or(Bool.and(x, FE), S)) : Bool}:
  match FE:
    case True{}:
      match x:
        case True{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match x:
        case True{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}

def fs.t_hit_no(+o: Bool, +Fn: Bool, +S: Bool) -> {Bool.or(Bool.and(o, False{}), Bool.or(Bool.and(Bool.and(o, False{}), Fn), S)) == Bool.or(Bool.and(Bool.and(o, False{}), Fn), S) : Bool}:
  match o:
    case True{}:
      match Fn:
        case True{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match Fn:
        case True{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}

def fs.t_hit_opt(+o: Bool, +Fn: Bool, +S: Bool) -> {Bool.or(Bool.and(o, Fn), Bool.or(Bool.and(Bool.and(o, True{}), Fn), S)) == Bool.or(Bool.and(Bool.and(o, True{}), Fn), S) : Bool}:
  match o:
    case True{}:
      match Fn:
        case True{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match Fn:
        case True{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match S:
            case True{}:
              {==}
            case False{}:
              {==}

def fs.t_r(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(b, a), c) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

def fs.t_r1(+a: Bool, +b: Bool) -> {Bool.or(a, Bool.or(b, False{})) == Bool.or(b, a) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}


# Shapes

def fs.sh_close(E: List<&2, F.TsToken>, x: List<&2, Bool>, +cr: Bool) -> {fs.shaped(E, F.ts.fsm.close(E, x, cr)) == fs.shaped(E, x) : Bool}:
  match E:
    case Nil{}:
      match x:
        case Nil{}:
          {==}
        case Con{+x0, +r}:
          {==}
    case Con{+tk, +tt}:
      match x:
        case Nil{}:
          {==}
        case Con{+x0, +xt}:
          fs.sh_close(tt, xt, Bool.and(Bool.or(x0, cr), F.ts.fsm.optional(tk)))

def fs.sh_adv(E: List<&2, F.TsToken>, x: List<&2, Bool>, +c: U32, +inc: Bool) -> {fs.shaped(E, F.ts.fsm.advance(E, x, c, inc)) == fs.shaped(E, x) : Bool}:
  match E:
    case Nil{}:
      match x:
        case Nil{}:
          {==}
        case Con{+x0, +r}:
          {==}
    case Con{+tk, +tt}:
      match x:
        case Nil{}:
          {==}
        case Con{+x0, +xt}:
          fs.sh_adv(tt, xt, c, Bool.and(Bool.and(x0, F.ts.fsm.matches(tk, c)), Bool.not(F.ts.fsm.stays(tk))))

def fs.sh_start(E: List<&2, F.TsToken>, x: List<&2, Bool>) -> {fs.shaped(E, F.ts.fsm.start_here(x)) == fs.shaped(E, x) : Bool}:
  match E:
    case Nil{}:
      match x:
        case Nil{}:
          {==}
        case Con{+x0, +r}:
          {==}
    case Con{+tk, +tt}:
      match x:
        case Nil{}:
          {==}
        case Con{+x0, +xt}:
          {==}

def fs.sh_falses(E: List<&2, F.TsToken>) -> {fs.shaped(E, F.ts.fsm.falses(E)) == True{} : Bool}:
  match E:
    case Nil{}:
      {==}
    case Con{+tk, +tt}:
      fs.sh_falses(tt)

# the step keeps the shape
def fs.sh_a2(+E: List<&2, F.TsToken>, +act: List<&2, Bool>, +c: U32, +h: {fs.shaped(E, act) == True{} : Bool}) -> {fs.shaped(E, fs.a2(E, act, c)) == True{} : Bool}:
  +sh = F.ts.fsm.start_here(act)
  +a0 = F.ts.fsm.close(E, sh, False{})
  +ad = F.ts.fsm.advance(E, a0, c, False{})
  Equal.trans(Bool, fs.shaped(E, F.ts.fsm.close(E, ad, False{})), fs.shaped(E, ad), True{}, fs.sh_close(E, ad, False{}), Equal.trans(Bool, fs.shaped(E, ad), fs.shaped(E, a0), True{}, fs.sh_adv(E, a0, c, False{}), Equal.trans(Bool, fs.shaped(E, a0), fs.shaped(E, sh), True{}, fs.sh_close(E, sh, False{}), Equal.trans(Bool, fs.shaped(E, sh), fs.shaped(E, act), True{}, fs.sh_start(E, act), h))))

def fs.sh_con(E: List<&2, F.TsToken>, a: List<&2, Bool>, +h: {fs.shaped(E, a) == True{} : Bool}) -> {fs.is_con(a) == True{} : Bool}:
  match E:
    case Nil{}:
      match a:
        case Nil{}:
          L.tsl.absurd(Bool, False{}, True{}, h)
        case Con{+x, +r}:
          {==}
    case Con{+tk, +tt}:
      match a:
        case Nil{}:
          L.tsl.absurd(Bool, False{}, True{}, h)
        case Con{+x, +r}:
          {==}

def fs.last_cons(+o: Bool, y: List<&2, Bool>, +h: {fs.is_con(y) == True{} : Bool}) -> {F.ts.fsm.last(Con{o, y}) == F.ts.fsm.last(y) : Bool}:
  match y:
    case Nil{}:
      L.tsl.absurd(Bool, o, False{}, h)
    case Con{+b, +t}:
      {==}

def fs.np_tl(tk: F.TsToken, +tt: List<&2, F.TsToken>, +h: {fs.noplus(Con{tk, tt}) == True{} : Bool}) -> {fs.noplus(tt) == True{} : Bool}:
  match tk:
    case F.TsToken{+cl, r}:
      match r:
        case F.TsOne{}:
          h
        case F.TsPerhaps{}:
          h
        case F.TsStar{}:
          h
        case F.TsPlus{}:
          L.tsl.absurd(Bool, fs.noplus(tt), True{}, h)

def fs.np_expand(tks: List<&2, F.TsToken>) -> {fs.noplus(F.ts.fsm.expand(tks)) == True{} : Bool}:
  match tks:
    case Nil{}:
      {==}
    case Con{tk, +t}:
      match tk:
        case F.TsToken{+cl, r}:
          match r:
            case F.TsOne{}:
              fs.np_expand(t)
            case F.TsPerhaps{}:
              fs.np_expand(t)
            case F.TsStar{}:
              fs.np_expand(t)
            case F.TsPlus{}:
              fs.np_expand(t)

# Closing over optional tokens adds nothing

def fs.CL_tok(s: List<&2, U32>, tk: F.TsToken, +tt: List<&2, F.TsToken>, +x: Bool, +cr: Bool, +S: Bool) -> {Bool.or(Bool.and(Bool.or(x, cr), fs.full(s, Con{tk, tt})), Bool.or(Bool.and(Bool.and(Bool.or(x, cr), F.ts.fsm.optional(tk)), fs.full(s, tt)), S)) == Bool.or(Bool.and(cr, fs.full(s, Con{tk, tt})), Bool.or(Bool.and(x, fs.full(s, Con{tk, tt})), S)) : Bool}:
  match s:
    case Nil{}:
      match tk:
        case F.TsToken{+cl, r}:
          match r:
            case F.TsOne{}:
              fs.t_cl_no(x, cr, False{}, fs.full(Nil{}, tt), S)
            case F.TsPerhaps{}:
              fs.t_cl_nilopt(x, cr, fs.full(Nil{}, tt), S)
            case F.TsStar{}:
              fs.t_cl_nilopt(x, cr, fs.full(Nil{}, tt), S)
            case F.TsPlus{}:
              fs.t_cl_no(x, cr, False{}, fs.full(Nil{}, tt), S)
    case Con{+c, +t}:
      match tk:
        case F.TsToken{+cl, r}:
          match r:
            case F.TsOne{}:
              fs.t_cl_no(x, cr, fs.full(Con{c, t}, Con{F.TsToken{cl, F.TsOne{}}, tt}), fs.full(Con{c, t}, tt), S)
            case F.TsPerhaps{}:
              fs.t_cl_con(x, cr, fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt)), S)
            case F.TsStar{}:
              fs.t_cl_con(x, cr, fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt})), S)
            case F.TsPlus{}:
              fs.t_cl_no(x, cr, fs.full(Con{c, t}, Con{F.TsToken{cl, F.TsPlus{}}, tt}), fs.full(Con{c, t}, tt), S)

# a closed set accepts what the set accepted, and the whole tokens if the
# carry came in
def fs.CL(E: List<&2, F.TsToken>, a: List<&2, Bool>, +cr: Bool, +s: List<&2, U32>, +h: {fs.shaped(E, a) == True{} : Bool}) -> {fs.sem(E, F.ts.fsm.close(E, a, cr), s) == Bool.or(Bool.and(cr, fs.full(s, E)), fs.sem(E, a, s)) : Bool}:
  match E:
    case Nil{}:
      match a:
        case Nil{}:
          L.tsl.absurd(Bool, fs.sem(Nil{}, Nil{}, s), Bool.or(Bool.and(cr, fs.full(s, Nil{})), False{}), h)
        case Con{+x, +r}:
          fs.t_cl_nil3(x, cr, fs.full(s, Nil{}))
    case Con{+tk, +tt}:
      match a:
        case Nil{}:
          L.tsl.absurd(Bool, fs.sem(Con{tk, tt}, Nil{}, s), Bool.or(Bool.and(cr, fs.full(s, Con{tk, tt})), fs.sem(Con{tk, tt}, Nil{}, s)), h)
        case Con{+x, +at}:
          +o = Bool.or(x, cr)
          +op = Bool.and(o, F.ts.fsm.optional(tk))
          %Equal.sym(Bool, fs.sem(tt, F.ts.fsm.close(tt, at, op), s), Bool.or(Bool.and(op, fs.full(s, tt)), fs.sem(tt, at, s)), fs.CL(tt, at, op, s, h)) : {Bool.or(Bool.and(o, fs.full(s, Con{tk, tt})), _) == Bool.or(Bool.and(cr, fs.full(s, Con{tk, tt})), Bool.or(Bool.and(x, fs.full(s, Con{tk, tt})), fs.sem(tt, at, s))) : Bool}
          fs.CL_tok(s, tk, tt, x, cr, fs.sem(tt, at, s))

# Reading a byte

# the positions after byte c accept w: the carry's tokens, or an active
# position's token takes c and the rest accept w
def fs.AL(E: List<&2, F.TsToken>, a: List<&2, Bool>, +c: U32, +inc: Bool, +w: List<&2, U32>, +h: {fs.shaped(E, a) == True{} : Bool}) -> {fs.sem(E, F.ts.fsm.advance(E, a, c, inc), w) == Bool.or(Bool.and(inc, fs.full(w, E)), fs.adv(E, a, c, w)) : Bool}:
  match E:
    case Nil{}:
      match a:
        case Nil{}:
          L.tsl.absurd(Bool, fs.sem(Nil{}, Nil{}, w), Bool.or(Bool.and(inc, fs.full(w, Nil{})), False{}), h)
        case Con{+x, +r}:
          Equal.sym(Bool, Bool.or(Bool.and(inc, fs.full(w, Nil{})), False{}), Bool.and(inc, fs.full(w, Nil{})), L.tsl.or_false_r(Bool.and(inc, fs.full(w, Nil{}))))
    case Con{+tk, +tt}:
      match a:
        case Nil{}:
          L.tsl.absurd(Bool, fs.sem(Con{tk, tt}, Nil{}, w), Bool.or(Bool.and(inc, fs.full(w, Con{tk, tt})), fs.adv(Con{tk, tt}, Nil{}, c, w)), h)
        case Con{+x, +at}:
          +mt = Bool.and(x, F.ts.fsm.matches(tk, c))
          +st = F.ts.fsm.stays(tk)
          %Equal.sym(Bool, fs.sem(tt, F.ts.fsm.advance(tt, at, c, Bool.and(mt, Bool.not(st))), w), Bool.or(Bool.and(Bool.and(mt, Bool.not(st)), fs.full(w, tt)), fs.adv(tt, at, c, w)), fs.AL(tt, at, c, Bool.and(mt, Bool.not(st)), w, h)) : {Bool.or(Bool.and(Bool.or(inc, Bool.and(mt, st)), fs.full(w, Con{tk, tt})), _) == Bool.or(Bool.and(inc, fs.full(w, Con{tk, tt})), Bool.or(Bool.and(mt, fs.pick(st, fs.full(w, Con{tk, tt}), fs.full(w, tt))), fs.adv(tt, at, c, w))) : Bool}
          fs.t_al(inc, mt, st, fs.full(w, Con{tk, tt}), fs.full(w, tt), fs.adv(tt, at, c, w))

def fs.CA_tok(tk: F.TsToken, +tt: List<&2, F.TsToken>, +o: Bool, +c: U32, +w: List<&2, U32>, +S: Bool, +h: {fs.noplus(Con{tk, tt}) == True{} : Bool}) -> {Bool.or(Bool.and(Bool.and(o, F.ts.fsm.matches(tk, c)), fs.pick(F.ts.fsm.stays(tk), fs.full(w, Con{tk, tt}), fs.full(w, tt))), Bool.or(Bool.and(Bool.and(o, F.ts.fsm.optional(tk)), fs.full(Con{c, w}, tt)), S)) == Bool.or(Bool.and(o, fs.full(Con{c, w}, Con{tk, tt})), Bool.or(Bool.and(Bool.and(o, F.ts.fsm.optional(tk)), fs.full(Con{c, w}, tt)), S)) : Bool}:
  match tk:
    case F.TsToken{+cl, r}:
      match r:
        case F.TsOne{}:
          fs.t_ca_one(o, F.ts.fsm.member(cl, c), fs.full(w, tt), Bool.or(Bool.and(Bool.and(o, False{}), fs.full(Con{c, w}, tt)), S))
        case F.TsPerhaps{}:
          fs.t_ca_opt(o, F.ts.fsm.member(cl, c), fs.full(w, tt), fs.full(Con{c, w}, tt), S)
        case F.TsStar{}:
          fs.t_ca_opt(o, F.ts.fsm.member(cl, c), fs.full(w, Con{F.TsToken{cl, F.TsStar{}}, tt}), fs.full(Con{c, w}, tt), S)
        case F.TsPlus{}:
          L.tsl.absurd(Bool, Bool.or(Bool.and(Bool.and(o, F.ts.fsm.member(cl, c)), fs.full(w, tt)), Bool.or(Bool.and(Bool.and(o, False{}), fs.full(Con{c, w}, tt)), S)), Bool.or(Bool.and(o, fs.full(Con{c, w}, Con{F.TsToken{cl, F.TsPlus{}}, tt})), Bool.or(Bool.and(Bool.and(o, False{}), fs.full(Con{c, w}, tt)), S)), h)

# a closed set: reading c moves its meaning on by c
def fs.CA(E: List<&2, F.TsToken>, x: List<&2, Bool>, +cr: Bool, +c: U32, +w: List<&2, U32>, +h: {fs.shaped(E, x) == True{} : Bool}, +hp: {fs.noplus(E) == True{} : Bool}) -> {fs.adv(E, F.ts.fsm.close(E, x, cr), c, w) == fs.sem(E, F.ts.fsm.close(E, x, cr), Con{c, w}) : Bool}:
  match E:
    case Nil{}:
      match x:
        case Nil{}:
          L.tsl.absurd(Bool, False{}, False{}, h)
        case Con{+x0, +r}:
          Equal.sym(Bool, Bool.and(Bool.or(x0, cr), False{}), False{}, L.tsl.and_false_r(Bool.or(x0, cr)))
    case Con{+tk, +tt}:
      match x:
        case Nil{}:
          L.tsl.absurd(Bool, fs.adv(tt, Nil{}, c, w), fs.sem(tt, Nil{}, Con{c, w}), h)
        case Con{+x0, +xt}:
          +o = Bool.or(x0, cr)
          +op = Bool.and(o, F.ts.fsm.optional(tk))
          +C1 = F.ts.fsm.close(tt, xt, op)
          %Equal.sym(Bool, fs.adv(tt, C1, c, w), fs.sem(tt, C1, Con{c, w}), fs.CA(tt, xt, op, c, w, h, fs.np_tl(tk, tt, hp))) : {Bool.or(Bool.and(Bool.and(o, F.ts.fsm.matches(tk, c)), fs.pick(F.ts.fsm.stays(tk), fs.full(w, Con{tk, tt}), fs.full(w, tt))), _) == Bool.or(Bool.and(o, fs.full(Con{c, w}, Con{tk, tt})), fs.sem(tt, C1, Con{c, w})) : Bool}
          %Equal.sym(Bool, fs.sem(tt, C1, Con{c, w}), Bool.or(Bool.and(op, fs.full(Con{c, w}, tt)), fs.sem(tt, xt, Con{c, w})), fs.CL(tt, xt, op, Con{c, w}, h)) : {Bool.or(Bool.and(Bool.and(o, F.ts.fsm.matches(tk, c)), fs.pick(F.ts.fsm.stays(tk), fs.full(w, Con{tk, tt}), fs.full(w, tt))), _) == Bool.or(Bool.and(o, fs.full(Con{c, w}, Con{tk, tt})), _) : Bool}
          fs.CA_tok(tk, tt, o, c, w, fs.sem(tt, xt, Con{c, w}), hp)

# Starting a match at the byte

def fs.ST(E: List<&2, F.TsToken>, act: List<&2, Bool>, +s: List<&2, U32>, +h: {fs.shaped(E, act) == True{} : Bool}) -> {fs.sem(E, F.ts.fsm.start_here(act), s) == Bool.or(fs.full(s, E), fs.sem(E, act, s)) : Bool}:
  match E:
    case Nil{}:
      match act:
        case Nil{}:
          L.tsl.absurd(Bool, False{}, Bool.or(fs.full(s, Nil{}), False{}), h)
        case Con{+x, +r}:
          fs.t_st_nil(fs.full(s, Nil{}), x)
    case Con{+tk, +tt}:
      match act:
        case Nil{}:
          L.tsl.absurd(Bool, fs.sem(Con{tk, tt}, Nil{}, s), Bool.or(fs.full(s, Con{tk, tt}), fs.sem(Con{tk, tt}, Nil{}, s)), h)
        case Con{+x, +r}:
          fs.t_st_con(fs.full(s, Con{tk, tt}), x, fs.sem(tt, r, s))

# The report: a closed set accepts no bytes exactly when its last position
# is active

def fs.HIT_tok(tk: F.TsToken, +tt: List<&2, F.TsToken>, +o: Bool, +S: Bool) -> {Bool.or(Bool.and(o, fs.full(Nil{}, Con{tk, tt})), Bool.or(Bool.and(Bool.and(o, F.ts.fsm.optional(tk)), fs.full(Nil{}, tt)), S)) == Bool.or(Bool.and(Bool.and(o, F.ts.fsm.optional(tk)), fs.full(Nil{}, tt)), S) : Bool}:
  match tk:
    case F.TsToken{+cl, r}:
      match r:
        case F.TsOne{}:
          fs.t_hit_no(o, fs.full(Nil{}, tt), S)
        case F.TsPerhaps{}:
          fs.t_hit_opt(o, fs.full(Nil{}, tt), S)
        case F.TsStar{}:
          fs.t_hit_opt(o, fs.full(Nil{}, tt), S)
        case F.TsPlus{}:
          fs.t_hit_no(o, fs.full(Nil{}, tt), S)

def fs.HIT(E: List<&2, F.TsToken>, x: List<&2, Bool>, +cr: Bool, +h: {fs.shaped(E, x) == True{} : Bool}) -> {fs.sem(E, F.ts.fsm.close(E, x, cr), Nil{}) == F.ts.fsm.last(F.ts.fsm.close(E, x, cr)) : Bool}:
  match E:
    case Nil{}:
      match x:
        case Nil{}:
          L.tsl.absurd(Bool, False{}, False{}, h)
        case Con{+x0, +r}:
          L.tsl.and_true_r(Bool.or(x0, cr))
    case Con{+tk, +tt}:
      match x:
        case Nil{}:
          L.tsl.absurd(Bool, fs.sem(tt, Nil{}, Nil{}), False{}, h)
        case Con{+x0, +xt}:
          +o = Bool.or(x0, cr)
          +op = Bool.and(o, F.ts.fsm.optional(tk))
          +C1 = F.ts.fsm.close(tt, xt, op)
          +h1 = Equal.trans(Bool, fs.shaped(tt, C1), fs.shaped(tt, xt), True{}, fs.sh_close(tt, xt, op), h)
          %Equal.sym(Bool, F.ts.fsm.last(Con{o, C1}), F.ts.fsm.last(C1), fs.last_cons(o, C1, fs.sh_con(tt, C1, h1))) : {Bool.or(Bool.and(o, fs.full(Nil{}, Con{tk, tt})), fs.sem(tt, C1, Nil{})) == _ : Bool}
          %fs.HIT(tt, xt, op, h) : {Bool.or(Bool.and(o, fs.full(Nil{}, Con{tk, tt})), fs.sem(tt, C1, Nil{})) == _ : Bool}
          %Equal.sym(Bool, fs.sem(tt, C1, Nil{}), Bool.or(Bool.and(op, fs.full(Nil{}, tt)), fs.sem(tt, xt, Nil{})), fs.CL(tt, xt, op, Nil{}, h)) : {Bool.or(Bool.and(o, fs.full(Nil{}, Con{tk, tt})), _) == _ : Bool}
          fs.HIT_tok(tk, tt, o, fs.sem(tt, xt, Nil{}))

# One byte

# after byte c the positions accept w exactly when, before it, they
# accepted c then w, or the whole pattern matches c then w
def fs.STEP(+E: List<&2, F.TsToken>, +act: List<&2, Bool>, +c: U32, +w: List<&2, U32>, +h: {fs.shaped(E, act) == True{} : Bool}, +hp: {fs.noplus(E) == True{} : Bool}) -> {fs.sem(E, fs.a2(E, act, c), w) == Bool.or(fs.full(Con{c, w}, E), fs.sem(E, act, Con{c, w})) : Bool}:
  +sh = F.ts.fsm.start_here(act)
  +a0 = F.ts.fsm.close(E, sh, False{})
  +ad = F.ts.fsm.advance(E, a0, c, False{})
  +h_sh = Equal.trans(Bool, fs.shaped(E, sh), fs.shaped(E, act), True{}, fs.sh_start(E, act), h)
  +h_a0 = Equal.trans(Bool, fs.shaped(E, a0), fs.shaped(E, sh), True{}, fs.sh_close(E, sh, False{}), h_sh)
  +h_ad = Equal.trans(Bool, fs.shaped(E, ad), fs.shaped(E, a0), True{}, fs.sh_adv(E, a0, c, False{}), h_a0)
  Equal.trans(Bool, fs.sem(E, F.ts.fsm.close(E, ad, False{}), w), fs.sem(E, ad, w), Bool.or(fs.full(Con{c, w}, E), fs.sem(E, act, Con{c, w})), fs.CL(E, ad, False{}, w, h_ad), Equal.trans(Bool, fs.sem(E, ad, w), fs.adv(E, a0, c, w), Bool.or(fs.full(Con{c, w}, E), fs.sem(E, act, Con{c, w})), fs.AL(E, a0, c, False{}, w, h_a0), Equal.trans(Bool, fs.adv(E, a0, c, w), fs.sem(E, a0, Con{c, w}), Bool.or(fs.full(Con{c, w}, E), fs.sem(E, act, Con{c, w})), fs.CA(E, sh, False{}, c, w, h_sh, hp), Equal.trans(Bool, fs.sem(E, a0, Con{c, w}), fs.sem(E, sh, Con{c, w}), Bool.or(fs.full(Con{c, w}, E), fs.sem(E, act, Con{c, w})), fs.CL(E, sh, False{}, Con{c, w}, h_sh), fs.ST(E, act, Con{c, w}, h)))))

# The reference's matcher

def fs.exp_nil(tks: List<&2, F.TsToken>) -> {fs.full_nil(F.ts.fsm.expand(tks)) == fs.full_nil(tks) : Bool}:
  match tks:
    case Nil{}:
      {==}
    case Con{tk, +t}:
      match tk:
        case F.TsToken{+cl, r}:
          match r:
            case F.TsOne{}:
              {==}
            case F.TsPerhaps{}:
              fs.exp_nil(t)
            case F.TsStar{}:
              fs.exp_nil(t)
            case F.TsPlus{}:
              {==}

# TsPlus as TsOne then TsStar matches the same
def fs.exp_ok(xs: List<&2, U32>, tks: List<&2, F.TsToken>) -> {fs.full(xs, F.ts.fsm.expand(tks)) == fs.full(xs, tks) : Bool}:
  match xs:
    case Nil{}:
      fs.exp_nil(tks)
    case Con{+c, +t}:
      match tks:
        case Nil{}:
          {==}
        case Con{tk, +tt}:
          match tk:
            case F.TsToken{+cl, r}:
              match r:
                case F.TsOne{}:
                  %Equal.sym(Bool, fs.full(t, F.ts.fsm.expand(tt)), fs.full(t, tt), fs.exp_ok(t, tt)) : {Bool.and(F.ts.fsm.member(cl, c), _) == Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt)) : Bool}
                  {==}
                case F.TsPerhaps{}:
                  %Equal.sym(Bool, fs.full(Con{c, t}, F.ts.fsm.expand(tt)), fs.full(Con{c, t}, tt), fs.exp_ok(Con{c, t}, tt)) : {Bool.or(_, Bool.and(F.ts.fsm.member(cl, c), fs.full(t, F.ts.fsm.expand(tt)))) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt))) : Bool}
                  %Equal.sym(Bool, fs.full(t, F.ts.fsm.expand(tt)), fs.full(t, tt), fs.exp_ok(t, tt)) : {Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), _)) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt))) : Bool}
                  {==}
                case F.TsStar{}:
                  %Equal.sym(Bool, fs.full(Con{c, t}, F.ts.fsm.expand(tt)), fs.full(Con{c, t}, tt), fs.exp_ok(Con{c, t}, tt)) : {Bool.or(_, Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, F.ts.fsm.expand(tt)}))) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}))) : Bool}
                  %Equal.sym(Bool, fs.full(t, F.ts.fsm.expand(Con{F.TsToken{cl, F.TsStar{}}, tt})), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}), fs.exp_ok(t, Con{F.TsToken{cl, F.TsStar{}}, tt})) : {Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), _)) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}))) : Bool}
                  {==}
                case F.TsPlus{}:
                  %Equal.sym(Bool, fs.full(t, F.ts.fsm.expand(Con{F.TsToken{cl, F.TsStar{}}, tt})), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}), fs.exp_ok(t, Con{F.TsToken{cl, F.TsStar{}}, tt})) : {Bool.and(F.ts.fsm.member(cl, c), _) == Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt})) : Bool}
                  {==}

# the fuel: two per token and one per byte is enough

def fs.mu(tks: List<&2, F.TsToken>, +xs: List<&2, U32>) -> Nat:
  match tks:
    case Nil{}:
      List.length(&2, U32, xs)
    case Con{tk, tt}:
      2n+fs.mu(tt, xs)

def fs.mu_con(tks: List<&2, F.TsToken>, +c: U32, +t: List<&2, U32>) -> {fs.mu(tks, Con{c, t}) == 1n+fs.mu(tks, t) : Nat}:
  match tks:
    case Nil{}:
      {==}
    case Con{+tk, +tt}:
      %fs.mu_con(tt, c, t) : {2n+fs.mu(tt, Con{c, t}) == 2n+_ : Nat}
      {==}

def fs.mul2(+n: Nat) -> {Nat.mul(2n, 1n+n) == 2n+Nat.mul(2n, n) : Nat}:
  Equal.cong(Nat, Nat, k => 1n+k, Nat.add(n, 1n+Nat.add(n, 0n)), 1n+Nat.add(n, Nat.add(n, 0n)), L.tsl.add_succ(n, Nat.add(n, 0n)))

def fs.mu_eq(tks: List<&2, F.TsToken>, +xs: List<&2, U32>) -> {Nat.add(Nat.mul(2n, List.length(&2, F.TsToken, tks)), List.length(&2, U32, xs)) == fs.mu(tks, xs) : Nat}:
  match tks:
    case Nil{}:
      {==}
    case Con{+tk, +tt}:
      %Equal.sym(Nat, Nat.mul(2n, 1n+List.length(&2, F.TsToken, tt)), 2n+Nat.mul(2n, List.length(&2, F.TsToken, tt)), fs.mul2(List.length(&2, F.TsToken, tt))) : {Nat.add(_, List.length(&2, U32, xs)) == 2n+fs.mu(tt, xs) : Nat}
      %fs.mu_eq(tt, xs) : {2n+Nat.add(Nat.mul(2n, List.length(&2, F.TsToken, tt)), List.length(&2, U32, xs)) == 2n+_ : Nat}
      {==}

def fs.lt_dec(+a: Nat, +f: Nat, +h: {Nat.is_lt(1n+a, f) == True{} : Bool}) -> {Nat.is_lt(a, f) == True{} : Bool}:
  match f:
    case 0n:
      L.tsl.absurd(Bool, Nat.is_lt(a, 0n), True{}, h)
    case 1n+g:
      L.tsl.lt_weak(a, g, h)

# is_lt(2 + mu(tt, c t), 1 + g): is_lt(2 + mu(tt, t), g)
def fs.lt_con(+tt: List<&2, F.TsToken>, +c: U32, +t: List<&2, U32>, +g: Nat, +h: {Nat.is_lt(1n+fs.mu(tt, Con{c, t}), g) == True{} : Bool}) -> {Nat.is_lt(2n+fs.mu(tt, t), g) == True{} : Bool}:
  %fs.mu_con(tt, c, t) : {Nat.is_lt(1n+_, g) == True{} : Bool}
  h

def fs.fuel_ok(f: Nat, tks: List<&2, F.TsToken>, xs: List<&2, U32>, +h: {Nat.is_lt(fs.mu(tks, xs), f) == True{} : Bool}) -> {F.ts.fsm.full(f, tks, xs) == fs.full(xs, tks) : Bool}:
  match f:
    case 0n:
      L.tsl.lt_zero_abs(Bool, F.ts.fsm.full(0n, tks, xs), fs.full(xs, tks), fs.mu(tks, xs), h)
    case 1n+ +g:
      match tks:
        case Nil{}:
          match xs:
            case Nil{}:
              {==}
            case Con{+c, +t}:
              {==}
        case Con{tk, +tt}:
          match tk:
            case F.TsToken{+cl, r}:
              match r:
                case F.TsOne{}:
                  match xs:
                    case Nil{}:
                      {==}
                    case Con{+c, +t}:
                      +h2 = fs.lt_con(tt, c, t, g, h)
                      +h1 = fs.lt_dec(1n+fs.mu(tt, t), g, h2)
                      +h0 = fs.lt_dec(fs.mu(tt, t), g, h1)
                      %Equal.sym(Bool, F.ts.fsm.full(g, tt, t), fs.full(t, tt), fs.fuel_ok(g, tt, t, h0)) : {Bool.and(F.ts.fsm.member(cl, c), _) == Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt)) : Bool}
                      {==}
                case F.TsPerhaps{}:
                  match xs:
                    case Nil{}:
                      fs.fuel_ok(g, tt, Nil{}, fs.lt_dec(fs.mu(tt, Nil{}), g, h))
                    case Con{+c, +t}:
                      +h2 = fs.lt_con(tt, c, t, g, h)
                      +h1 = fs.lt_dec(1n+fs.mu(tt, t), g, h2)
                      +h0 = fs.lt_dec(fs.mu(tt, t), g, h1)
                      +hc = fs.lt_dec(fs.mu(tt, Con{c, t}), g, h)
                      %Equal.sym(Bool, F.ts.fsm.full(g, tt, Con{c, t}), fs.full(Con{c, t}, tt), fs.fuel_ok(g, tt, Con{c, t}, hc)) : {Bool.or(_, Bool.and(F.ts.fsm.member(cl, c), F.ts.fsm.full(g, tt, t))) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt))) : Bool}
                      %Equal.sym(Bool, F.ts.fsm.full(g, tt, t), fs.full(t, tt), fs.fuel_ok(g, tt, t, h0)) : {Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), _)) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, tt))) : Bool}
                      {==}
                case F.TsStar{}:
                  match xs:
                    case Nil{}:
                      fs.fuel_ok(g, tt, Nil{}, fs.lt_dec(fs.mu(tt, Nil{}), g, h))
                    case Con{+c, +t}:
                      +h2 = fs.lt_con(tt, c, t, g, h)
                      +hc = fs.lt_dec(fs.mu(tt, Con{c, t}), g, h)
                      %Equal.sym(Bool, F.ts.fsm.full(g, tt, Con{c, t}), fs.full(Con{c, t}, tt), fs.fuel_ok(g, tt, Con{c, t}, hc)) : {Bool.or(_, Bool.and(F.ts.fsm.member(cl, c), F.ts.fsm.full(g, Con{F.TsToken{cl, F.TsStar{}}, tt}, t))) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}))) : Bool}
                      %Equal.sym(Bool, F.ts.fsm.full(g, Con{F.TsToken{cl, F.TsStar{}}, tt}, t), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}), fs.fuel_ok(g, Con{F.TsToken{cl, F.TsStar{}}, tt}, t, h2)) : {Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), _)) == Bool.or(fs.full(Con{c, t}, tt), Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}))) : Bool}
                      {==}
                case F.TsPlus{}:
                  match xs:
                    case Nil{}:
                      {==}
                    case Con{+c, +t}:
                      +h2 = fs.lt_con(tt, c, t, g, h)
                      %Equal.sym(Bool, F.ts.fsm.full(g, Con{F.TsToken{cl, F.TsStar{}}, tt}, t), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt}), fs.fuel_ok(g, Con{F.TsToken{cl, F.TsStar{}}, tt}, t, h2)) : {Bool.and(F.ts.fsm.member(cl, c), _) == Bool.and(F.ts.fsm.member(cl, c), fs.full(t, Con{F.TsToken{cl, F.TsStar{}}, tt})) : Bool}
                      {==}

# the reference's matcher, with the fuel it is given, on the expanded tokens
def fs.full_any(+tks: List<&2, F.TsToken>, +xs: List<&2, U32>) -> {F.ts.fsm.full(F.ts.fsm.fuel(tks, xs), tks, xs) == fs.full(xs, F.ts.fsm.expand(tks)) : Bool}:
  +hlt = Equal.trans(Bool, Nat.is_lt(fs.mu(tks, xs), F.ts.fsm.fuel(tks, xs)), Nat.is_lt(fs.mu(tks, xs), 1n+fs.mu(tks, xs)), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(fs.mu(tks, xs), 1n+n), Nat.add(Nat.mul(2n, List.length(&2, F.TsToken, tks)), List.length(&2, U32, xs)), fs.mu(tks, xs), fs.mu_eq(tks, xs)), L.tsl.lt_succ(fs.mu(tks, xs)))
  Equal.trans(Bool, F.ts.fsm.full(F.ts.fsm.fuel(tks, xs), tks, xs), fs.full(xs, tks), fs.full(xs, F.ts.fsm.expand(tks)), fs.fuel_ok(F.ts.fsm.fuel(tks, xs), tks, xs, hlt), Equal.sym(Bool, fs.full(xs, F.ts.fsm.expand(tks)), fs.full(xs, tks), fs.exp_ok(xs, tks)))

# The automaton against the reference

def fs.hits(+h: Bool, +e: Nat, +xs: List<&2, Nat>) -> {F.ts.fsm.hit(h, e, xs) == A.ts.auto.hit(h, e, xs) : List<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the reference's reports from the end of prefix i of xs on, k of them,
# with the matches begun before xs that the set act accepts
def fs.R(k: Nat, +tks: List<&2, F.TsToken>, +act: List<&2, Bool>, +xs: List<&2, U32>, +i: Nat, +pos: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      F.ts.fsm.hit(Bool.or(fs.sem(F.ts.fsm.expand(tks), act, List.take(&2, U32, xs, i)), F.ts.fsm.any_suffix(tks, List.take(&2, U32, xs, i))), Nat.add(pos, i), fs.R(r, tks, act, xs, 1n+i, pos))

def fs.bit(+tks: List<&2, F.TsToken>, +act: List<&2, Bool>, +c: U32, +w: List<&2, U32>, +h: {fs.shaped(F.ts.fsm.expand(tks), act) == True{} : Bool}) -> {Bool.or(fs.sem(F.ts.fsm.expand(tks), act, Con{c, w}), F.ts.fsm.any_suffix(tks, Con{c, w})) == Bool.or(fs.sem(F.ts.fsm.expand(tks), fs.a2(F.ts.fsm.expand(tks), act, c), w), F.ts.fsm.any_suffix(tks, w)) : Bool}:
  +E = F.ts.fsm.expand(tks)
  %Equal.sym(Bool, F.ts.fsm.full(F.ts.fsm.fuel(tks, Con{c, w}), tks, Con{c, w}), fs.full(Con{c, w}, E), fs.full_any(tks, Con{c, w})) : {Bool.or(fs.sem(E, act, Con{c, w}), Bool.or(_, F.ts.fsm.any_suffix(tks, w))) == Bool.or(fs.sem(E, fs.a2(E, act, c), w), F.ts.fsm.any_suffix(tks, w)) : Bool}
  %Equal.sym(Bool, fs.sem(E, fs.a2(E, act, c), w), Bool.or(fs.full(Con{c, w}, E), fs.sem(E, act, Con{c, w})), fs.STEP(E, act, c, w, h, fs.np_expand(tks))) : {Bool.or(fs.sem(E, act, Con{c, w}), Bool.or(fs.full(Con{c, w}, E), F.ts.fsm.any_suffix(tks, w))) == Bool.or(_, F.ts.fsm.any_suffix(tks, w)) : Bool}
  fs.t_r(fs.sem(E, act, Con{c, w}), fs.full(Con{c, w}, E), F.ts.fsm.any_suffix(tks, w))

# the reports from prefix 1 + i of c then t: those from prefix i of t,
# after the step on c
def fs.R_shift(k: Nat, +tks: List<&2, F.TsToken>, +act: List<&2, Bool>, +c: U32, +t: List<&2, U32>, +i: Nat, +pos: Nat, +h: {fs.shaped(F.ts.fsm.expand(tks), act) == True{} : Bool}) -> {fs.R(k, tks, act, Con{c, t}, 1n+i, pos) == fs.R(k, tks, fs.a2(F.ts.fsm.expand(tks), act, c), t, i, 1n+pos) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+ +r:
      +E = F.ts.fsm.expand(tks)
      +a2 = fs.a2(E, act, c)
      +w = List.take(&2, U32, t, i)
      %Equal.sym(List<&2, Nat>, fs.R(r, tks, act, Con{c, t}, 2n+i, pos), fs.R(r, tks, a2, t, 1n+i, 1n+pos), fs.R_shift(r, tks, act, c, t, 1n+i, pos, h)) : {F.ts.fsm.hit(Bool.or(fs.sem(E, act, Con{c, w}), F.ts.fsm.any_suffix(tks, Con{c, w})), Nat.add(pos, 1n+i), _) == fs.R(1n+r, tks, a2, t, i, 1n+pos) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(pos, 1n+i), 1n+Nat.add(pos, i), L.tsl.add_succ(pos, i)) : {F.ts.fsm.hit(Bool.or(fs.sem(E, act, Con{c, w}), F.ts.fsm.any_suffix(tks, Con{c, w})), _, fs.R(r, tks, a2, t, 1n+i, 1n+pos)) == fs.R(1n+r, tks, a2, t, i, 1n+pos) : List<&2, Nat>}
      %Equal.sym(Bool, Bool.or(fs.sem(E, act, Con{c, w}), F.ts.fsm.any_suffix(tks, Con{c, w})), Bool.or(fs.sem(E, a2, w), F.ts.fsm.any_suffix(tks, w)), fs.bit(tks, act, c, w, h)) : {F.ts.fsm.hit(_, Nat.add(1n+pos, i), fs.R(r, tks, a2, t, 1n+i, 1n+pos)) == fs.R(1n+r, tks, a2, t, i, 1n+pos) : List<&2, Nat>}
      {==}

# the automaton from a set act reports what fs.R reports
def fs.run(ys: List<&2, U32>, +tks: List<&2, F.TsToken>, +act: List<&2, Bool>, +pos: Nat, +h: {fs.shaped(F.ts.fsm.expand(tks), act) == True{} : Bool}) -> {A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{F.ts.fsm.expand(tks), act}, pos, ys)) == fs.R(List.length(&2, U32, ys), tks, act, ys, 1n, pos) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      +E = F.ts.fsm.expand(tks)
      +ad = F.ts.fsm.advance(E, F.ts.fsm.close(E, F.ts.fsm.start_here(act), False{}), c, False{})
      +a2 = fs.a2(E, act, c)
      +h2 = fs.sh_a2(E, act, c, h)
      +h_ad = Equal.trans(Bool, fs.shaped(E, ad), fs.shaped(E, F.ts.fsm.close(E, F.ts.fsm.start_here(act), False{})), True{}, fs.sh_adv(E, F.ts.fsm.close(E, F.ts.fsm.start_here(act), False{}), c, False{}), Equal.trans(Bool, fs.shaped(E, F.ts.fsm.close(E, F.ts.fsm.start_here(act), False{})), fs.shaped(E, F.ts.fsm.start_here(act)), True{}, fs.sh_close(E, F.ts.fsm.start_here(act), False{}), Equal.trans(Bool, fs.shaped(E, F.ts.fsm.start_here(act)), fs.shaped(E, act), True{}, fs.sh_start(E, act), h)))
      +e_last = Equal.trans(Bool, F.ts.fsm.last(a2), fs.sem(E, a2, Nil{}), Bool.or(fs.full(Con{c, Nil{}}, E), fs.sem(E, act, Con{c, Nil{}})), Equal.sym(Bool, fs.sem(E, a2, Nil{}), F.ts.fsm.last(a2), fs.HIT(E, ad, False{}, h_ad)), fs.STEP(E, act, c, Nil{}, h, fs.np_expand(tks)))
      +e_bit = Equal.trans(Bool, Bool.or(fs.sem(E, act, Con{c, Nil{}}), F.ts.fsm.any_suffix(tks, Con{c, Nil{}})), Bool.or(fs.sem(E, act, Con{c, Nil{}}), Bool.or(fs.full(Con{c, Nil{}}, E), False{})), F.ts.fsm.last(a2), Equal.cong(Bool, Bool, b => Bool.or(fs.sem(E, act, Con{c, Nil{}}), Bool.or(b, False{})), F.ts.fsm.full(F.ts.fsm.fuel(tks, Con{c, Nil{}}), tks, Con{c, Nil{}}), fs.full(Con{c, Nil{}}, E), fs.full_any(tks, Con{c, Nil{}})), Equal.trans(Bool, Bool.or(fs.sem(E, act, Con{c, Nil{}}), Bool.or(fs.full(Con{c, Nil{}}, E), False{})), Bool.or(fs.full(Con{c, Nil{}}, E), fs.sem(E, act, Con{c, Nil{}})), F.ts.fsm.last(a2), fs.t_r1(fs.sem(E, act, Con{c, Nil{}}), fs.full(Con{c, Nil{}}, E)), Equal.sym(Bool, F.ts.fsm.last(a2), Bool.or(fs.full(Con{c, Nil{}}, E), fs.sem(E, act, Con{c, Nil{}})), e_last)))
      +RT = fs.R(List.length(&2, U32, t), tks, a2, t, 1n, 1n+pos)
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, 0n), Nil{}, L.tsl.take0(t)) : {A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, act}, pos, Con{c, t})) == F.ts.fsm.hit(Bool.or(fs.sem(E, act, Con{c, _}), F.ts.fsm.any_suffix(tks, Con{c, _})), Nat.add(pos, 1n), fs.R(List.length(&2, U32, t), tks, act, Con{c, t}, 2n, pos)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, fs.R(List.length(&2, U32, t), tks, act, Con{c, t}, 2n, pos), RT, fs.R_shift(List.length(&2, U32, t), tks, act, c, t, 1n, pos, h)) : {A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, act}, pos, Con{c, t})) == F.ts.fsm.hit(Bool.or(fs.sem(E, act, Con{c, Nil{}}), F.ts.fsm.any_suffix(tks, Con{c, Nil{}})), Nat.add(pos, 1n), _) : List<&2, Nat>}
      %Equal.sym(Bool, Bool.or(fs.sem(E, act, Con{c, Nil{}}), F.ts.fsm.any_suffix(tks, Con{c, Nil{}})), F.ts.fsm.last(a2), e_bit) : {A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, act}, pos, Con{c, t})) == F.ts.fsm.hit(_, Nat.add(pos, 1n), RT) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(pos, 1n), 1n+pos, L.tsl.add_one(pos)) : {A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, act}, pos, Con{c, t})) == F.ts.fsm.hit(F.ts.fsm.last(a2), _, RT) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, F.ts.fsm.hit(F.ts.fsm.last(a2), 1n+pos, RT), A.ts.auto.hit(F.ts.fsm.last(a2), 1n+pos, RT), fs.hits(F.ts.fsm.last(a2), 1n+pos, RT)) : {A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, act}, pos, Con{c, t})) == _ : List<&2, Nat>}
      Equal.trans(List<&2, Nat>, A.ts.auto.snd(~F.TsFsm, A.ts.auto.go(~F.TsFsm, ~F.ts.fsm.step, t, 1n+pos, (F.TsFsm{E, a2}, F.ts.fsm.last(a2)))), A.ts.auto.hit(F.ts.fsm.last(a2), 1n+pos, A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, a2}, 1n+pos, t))), A.ts.auto.hit(F.ts.fsm.last(a2), 1n+pos, RT), L.tsl.go_snd(~F.TsFsm, ~F.ts.fsm.step, t, 1n+pos, F.TsFsm{E, a2}, F.ts.fsm.last(a2)), Equal.cong(List<&2, Nat>, List<&2, Nat>, x => A.ts.auto.hit(F.ts.fsm.last(a2), 1n+pos, x), A.ts.auto.snd(~F.TsFsm, A.ts.auto.feed(~F.TsFsm, ~F.ts.fsm.step, F.TsFsm{E, a2}, 1n+pos, t)), RT, fs.run(t, tks, a2, 1n+pos, h2)))

def fs.sem_falses(E: List<&2, F.TsToken>, +s: List<&2, U32>) -> {fs.sem(E, F.ts.fsm.falses(E), s) == False{} : Bool}:
  match E:
    case Nil{}:
      {==}
    case Con{+tk, +tt}:
      fs.sem_falses(tt, s)

# from the start no match is under way: fs.R is the reference
def fs.R_init(k: Nat, +tks: List<&2, F.TsToken>, +xs: List<&2, U32>, +i: Nat) -> {fs.R(k, tks, F.ts.fsm.falses(F.ts.fsm.expand(tks)), xs, i, 0n) == F.ts.fsm.naive.go(k, tks, xs, i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+ +r:
      %Equal.sym(Bool, fs.sem(F.ts.fsm.expand(tks), F.ts.fsm.falses(F.ts.fsm.expand(tks)), List.take(&2, U32, xs, i)), False{}, fs.sem_falses(F.ts.fsm.expand(tks), List.take(&2, U32, xs, i))) : {F.ts.fsm.hit(Bool.or(_, F.ts.fsm.any_suffix(tks, List.take(&2, U32, xs, i))), i, fs.R(r, tks, F.ts.fsm.falses(F.ts.fsm.expand(tks)), xs, 1n+i, 0n)) == F.ts.fsm.naive.go(1n+r, tks, xs, i) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, fs.R(r, tks, F.ts.fsm.falses(F.ts.fsm.expand(tks)), xs, 1n+i, 0n), F.ts.fsm.naive.go(r, tks, xs, 1n+i), fs.R_init(r, tks, xs, 1n+i)) : {F.ts.fsm.hit(F.ts.fsm.any_suffix(tks, List.take(&2, U32, xs, i)), i, _) == F.ts.fsm.naive.go(1n+r, tks, xs, i) : List<&2, Nat>}
      {==}

# The laws

def fs.ref(+tks: List<&2, F.TsToken>, +xs: List<&2, U32>) -> {F.ts.fsm.ends(tks, xs) == F.ts.fsm.naive(tks, xs) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, F.ts.fsm.ends(tks, xs), fs.R(List.length(&2, U32, xs), tks, F.ts.fsm.falses(F.ts.fsm.expand(tks)), xs, 1n, 0n), F.ts.fsm.naive(tks, xs), fs.run(xs, tks, F.ts.fsm.falses(F.ts.fsm.expand(tks)), 0n, fs.sh_falses(F.ts.fsm.expand(tks))), fs.R_init(List.length(&2, U32, xs), tks, xs, 1n))

def Laws.fsm_ref(tks, xs):
  fs.ref(tks, xs)

def Laws.fsm_search_ref(tks, cs):
  Equal.trans(List<&2, Nat>, F.ts.fsm.search(tks, cs), F.ts.fsm.ends(tks, T.ts.concat(cs)), F.ts.fsm.naive(tks, T.ts.concat(cs)), L.tsl.split(~F.TsFsm, ~F.ts.fsm.step, cs, 0n, F.ts.fsm.start(tks), Nil{}), fs.ref(tks, T.ts.concat(cs)))
