# bend-osdev-apparmor: file rules (apparmor.d(5), "FILE RULE", "Access
# Modes"): a pattern, the access modes r w a l k m, and at most one exec
# transition (ix ux Ux px Px cx Cx pix Pix cix Cix pux PUx cux CUx), or a
# bare x in a deny rule; leading or trailing permissions; owner; an exec
# target after ->.
#
# Permission bits: r 0, w 1, a 2, l 3, k 4, m 5, x 6. Write implies append
# (apparmor_parser compiles w to the write and append bits; see the README,
# "Experiments"), so w sets bit 2 too.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

type AaXFallback is Data:
  AaFbNone{}
  AaFbIx{}
  AaFbUx{}

# an exec transition: inherit, unconfined, a profile, a child profile; scrub:
# the upper-case forms, which scrub the environment
type AaXMode is Data:
  AaXIx{}
  AaXUx{scrub: Bool}
  AaXPx{scrub: Bool, fb: AaXFallback}
  AaXCx{scrub: Bool, fb: AaXFallback}

# text: the pattern as written (after variable expansion), for aliases and
# for comparing literal paths
type AaFileRule is Data:
  AaFileRule{qual: P.AaQual, text: List<&2, U32>, path: G.AaGlob, perms: P.AaPerms, exec: Maybe<&2, AaXMode>, target: Maybe<&2, List<&2, U32>>}

# a request: the path, whether the task owns the file (fsuid matches), the
# permissions asked for
type AaFileQuery is Data:
  AaFileQuery{path: List<&2, U32>, owner: Bool, req: P.AaPerms}

def AaFile.r() -> Nat:
  0n

def AaFile.w() -> Nat:
  1n

def AaFile.a() -> Nat:
  2n

def AaFile.l() -> Nat:
  3n

def AaFile.k() -> Nat:
  4n

def AaFile.m() -> Nat:
  5n

def AaFile.x() -> Nat:
  6n

def AaFile.letters() -> List<&2, String>:
  ["r", "w", "a", "l", "k", "m", "x"]

# Exec modes

def AaXFallback.eq(a: AaXFallback, b: AaXFallback) -> Bool:
  match a b:
    case AaFbNone{} AaFbNone{}:
      True{}
    case AaFbIx{} AaFbIx{}:
      True{}
    case AaFbUx{} AaFbUx{}:
      True{}
    case _ _:
      False{}

def AaXMode.eq(a: AaXMode, b: AaXMode) -> Bool:
  match a b:
    case AaXIx{} AaXIx{}:
      True{}
    case AaXUx{s} AaXUx{t}:
      Bool.not(Bool.xor(s, t))
    case AaXPx{s, f} AaXPx{t, g}:
      Bool.and(Bool.not(Bool.xor(s, t)), AaXFallback.eq(f, g))
    case AaXCx{s, f} AaXCx{t, g}:
      Bool.and(Bool.not(Bool.xor(s, t)), AaXFallback.eq(f, g))
    case _ _:
      False{}

def AaXMode.show.fb(f: AaXFallback, up: Bool) -> String:
  match f:
    case AaFbNone{}:
      ""
    case AaFbIx{}:
      "i"
    case AaFbUx{}:
      Bool.pick(String, up, "U", "u")

def AaXMode.show(m: AaXMode) -> String:
  match m:
    case AaXIx{}:
      "ix"
    case AaXUx{s}:
      Bool.pick(String, s, "Ux", "ux")
    case AaXPx{+s, f}:
      Bool.pick(String, s, "P", "p") ++ AaXMode.show.fb(f, s) ++ "x"
    case AaXCx{+s, f}:
      Bool.pick(String, s, "C", "c") ++ AaXMode.show.fb(f, s) ++ "x"

# Reading a permission string

# the letters read so far of an exec mode
type AaFpSt is Data:
  AaFpBase{}
  AaFpI{}
  AaFpLp{}
  AaFpLpi{}
  AaFpLpu{}
  AaFpUp{}
  AaFpUpi{}
  AaFpUpU{}
  AaFpLc{}
  AaFpLci{}
  AaFpLcu{}
  AaFpUc{}
  AaFpUci{}
  AaFpUcU{}
  AaFpLu{}
  AaFpUu{}

type AaFp is Data:
  AaFp{st: AaFpSt, r: Bool, w: Bool, a: Bool, l: Bool, k: Bool, m: Bool, exec: Maybe<&2, AaXMode>, bare: Bool, ok: Bool}

def AaFp.fail(f: AaFp) -> AaFp:
  match f:
    case AaFp{st, r, w, a, l, k, m, e, b, ok}:
      AaFp{AaFpBase{}, r, w, a, l, k, m, e, b, False{}}

def AaFp.go(f: AaFp, s: AaFpSt) -> AaFp:
  match f:
    case AaFp{st, r, w, a, l, k, m, e, b, ok}:
      AaFp{s, r, w, a, l, k, m, e, b, ok}

def AaFp.exec.go(e: Maybe<&2, AaXMode>, x: AaXMode, r: Bool, w: Bool, a: Bool, l: Bool, k: Bool, m: Bool, b: Bool, ok: Bool) -> AaFp:
  match e:
    case None{}:
      AaFp{AaFpBase{}, r, w, a, l, k, m, Some{x}, b, ok}
    case Some{y}:
      AaFp{AaFpBase{}, r, w, a, l, k, m, Some{y}, b, False{}}

def AaFp.exec(f: AaFp, x: AaXMode) -> AaFp:
  match f:
    case AaFp{st, r, w, a, l, k, m, e, b, ok}:
      AaFp.exec.go(e, x, r, w, a, l, k, m, b, ok)

# one of the access letters r w a l k m (n: its bit), or a bare x (n = 6)
def AaFp.bit(f: AaFp, n: Nat) -> AaFp:
  match f:
    case AaFp{st, r, w, a, l, k, m, e, b, ok}:
      match n:
        case 0n:
          AaFp{AaFpBase{}, True{}, w, a, l, k, m, e, b, ok}
        case 1n+n1:
          match n1:
            case 0n:
              AaFp{AaFpBase{}, r, True{}, a, l, k, m, e, b, ok}
            case 1n+n2:
              match n2:
                case 0n:
                  AaFp{AaFpBase{}, r, w, True{}, l, k, m, e, b, ok}
                case 1n+n3:
                  match n3:
                    case 0n:
                      AaFp{AaFpBase{}, r, w, a, True{}, k, m, e, b, ok}
                    case 1n+n4:
                      match n4:
                        case 0n:
                          AaFp{AaFpBase{}, r, w, a, l, True{}, m, e, b, ok}
                        case 1n+n5:
                          match n5:
                            case 0n:
                              AaFp{AaFpBase{}, r, w, a, l, k, True{}, e, b, ok}
                            case 1n+n6:
                              AaFp{AaFpBase{}, r, w, a, l, k, m, e, True{}, ok}

def AaFp.base(+f: AaFp, +h: U32) -> AaFp:
  Bool.pick(AaFp, U32.is_eq(h, 114), AaFp.bit(f, 0n), Bool.pick(AaFp, U32.is_eq(h, 119), AaFp.bit(f, 1n), Bool.pick(AaFp, U32.is_eq(h, 97), AaFp.bit(f, 2n), Bool.pick(AaFp, U32.is_eq(h, 108), AaFp.bit(f, 3n), Bool.pick(AaFp, U32.is_eq(h, 107), AaFp.bit(f, 4n), Bool.pick(AaFp, U32.is_eq(h, 109), AaFp.bit(f, 5n), Bool.pick(AaFp, U32.is_eq(h, 120), AaFp.bit(f, 6n), Bool.pick(AaFp, U32.is_eq(h, 105), AaFp.go(f, AaFpI{}), Bool.pick(AaFp, U32.is_eq(h, 112), AaFp.go(f, AaFpLp{}), Bool.pick(AaFp, U32.is_eq(h, 80), AaFp.go(f, AaFpUp{}), Bool.pick(AaFp, U32.is_eq(h, 99), AaFp.go(f, AaFpLc{}), Bool.pick(AaFp, U32.is_eq(h, 67), AaFp.go(f, AaFpUc{}), Bool.pick(AaFp, U32.is_eq(h, 117), AaFp.go(f, AaFpLu{}), Bool.pick(AaFp, U32.is_eq(h, 85), AaFp.go(f, AaFpUu{}), AaFp.fail(f)))))))))))))))

# the letter after a prefix: x ends the mode, i or u/U (when allowed) extend it
def AaFp.x(+f: AaFp, +h: U32, x: AaXMode) -> AaFp:
  Bool.pick(AaFp, U32.is_eq(h, 120), AaFp.exec(f, x), AaFp.fail(f))

def AaFp.ext(+f: AaFp, +h: U32, x: AaXMode, +ci: U32, si: AaFpSt, +cu: U32, su: AaFpSt) -> AaFp:
  Bool.pick(AaFp, U32.is_eq(h, 120), AaFp.exec(f, x), Bool.pick(AaFp, U32.is_eq(h, ci), AaFp.go(f, si), Bool.pick(AaFp, U32.is_eq(h, cu), AaFp.go(f, su), AaFp.fail(f))))

def AaFp.step.st(s: AaFpSt, +f: AaFp, +h: U32) -> AaFp:
  match s:
    case AaFpBase{}:
      AaFp.base(f, h)
    case AaFpI{}:
      AaFp.x(f, h, AaXIx{})
    case AaFpLp{}:
      AaFp.ext(f, h, AaXPx{False{}, AaFbNone{}}, 105, AaFpLpi{}, 117, AaFpLpu{})
    case AaFpLpi{}:
      AaFp.x(f, h, AaXPx{False{}, AaFbIx{}})
    case AaFpLpu{}:
      AaFp.x(f, h, AaXPx{False{}, AaFbUx{}})
    case AaFpUp{}:
      AaFp.ext(f, h, AaXPx{True{}, AaFbNone{}}, 105, AaFpUpi{}, 85, AaFpUpU{})
    case AaFpUpi{}:
      AaFp.x(f, h, AaXPx{True{}, AaFbIx{}})
    case AaFpUpU{}:
      AaFp.x(f, h, AaXPx{True{}, AaFbUx{}})
    case AaFpLc{}:
      AaFp.ext(f, h, AaXCx{False{}, AaFbNone{}}, 105, AaFpLci{}, 117, AaFpLcu{})
    case AaFpLci{}:
      AaFp.x(f, h, AaXCx{False{}, AaFbIx{}})
    case AaFpLcu{}:
      AaFp.x(f, h, AaXCx{False{}, AaFbUx{}})
    case AaFpUc{}:
      AaFp.ext(f, h, AaXCx{True{}, AaFbNone{}}, 105, AaFpUci{}, 85, AaFpUcU{})
    case AaFpUci{}:
      AaFp.x(f, h, AaXCx{True{}, AaFbIx{}})
    case AaFpUcU{}:
      AaFp.x(f, h, AaXCx{True{}, AaFbUx{}})
    case AaFpLu{}:
      AaFp.x(f, h, AaXUx{False{}})
    case AaFpUu{}:
      AaFp.x(f, h, AaXUx{True{}})

def AaFp.step(f: AaFp, +h: U32) -> AaFp:
  match f:
    case AaFp{st, r, w, a, l, k, m, e, b, ok}:
      AaFp.step.st(st, AaFp{AaFpBase{}, r, w, a, l, k, m, e, b, ok}, h)

def AaFp.run(xs: List<&2, U32>, f: AaFp) -> AaFp:
  match xs:
    case Nil{}:
      f
    case Con{+h, t}:
      AaFp.run(t, AaFp.step(f, h))

# what a permission string reads as: the bits and the exec mode
type AaFPerms is Data:
  AaFPerms{perms: P.AaPerms, exec: Maybe<&2, AaXMode>}

def AaFp.is_some(m: Maybe<&2, AaXMode>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def AaFp.base_st(s: AaFpSt) -> Bool:
  match s:
    case AaFpBase{}:
      True{}
    case _:
      False{}

# valid: whole letters, not w with a, an exec mode only without deny, a bare
# x only with deny, something granted
def AaFp.result(f: AaFp, +deny: Bool, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFPerms>:
  match f:
    case AaFp{st, +r, +w, +a, +l, +k, +m, +e, +b, ok}:
      +ex = AaFp.is_some(e)
      +good = Bool.and(ok, Bool.and(AaFp.base_st(st), Bool.and(Bool.not(Bool.and(w, a)), Bool.and(Bool.not(Bool.and(deny, ex)), Bool.and(Bool.not(Bool.and(Bool.not(deny), b)), Bool.and(Bool.not(Bool.and(ex, b)), Bool.or(r, Bool.or(w, Bool.or(a, Bool.or(l, Bool.or(k, Bool.or(m, Bool.or(ex, b)))))))))))))
      Bool.pick(Result<&2, &2, E.AaError, AaFPerms>, good, Done{AaFPerms{P.AaPerms.of_bits([r, w, Bool.or(w, a), l, k, m, Bool.or(ex, b)]), e}}, Fail{E.AaSrc.perms(src)})

# the permission string xs, in a rule that is (or is not) a deny rule
def AaFile.parse_perms(xs: List<&2, U32>, +deny: Bool, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFPerms>:
  AaFp.result(AaFp.run(xs, AaFp{AaFpBase{}, False{}, False{}, False{}, False{}, False{}, False{}, None{}, False{}, True{}}), deny, src)

# a set of file permissions from letters (r w a l k m x), for queries: None
# if a letter is not one of them
def AaFile.letter(+h: U32) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 114), Some{0n}, Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 119), Some{1n}, Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 97), Some{2n}, Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 108), Some{3n}, Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 107), Some{4n}, Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 109), Some{5n}, Bool.pick(Maybe<&2, Nat>, U32.is_eq(h, 120), Some{6n}, None{})))))))

def AaFile.perms.add(m: Maybe<&2, P.AaPerms>, l: Maybe<&2, Nat>) -> Maybe<&2, P.AaPerms>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match l:
        case None{}:
          None{}
        case Some{i}:
          Some{P.AaPerms.add(p, i)}

def AaFile.perms.go(xs: List<&2, U32>, acc: Maybe<&2, P.AaPerms>) -> Maybe<&2, P.AaPerms>:
  match xs:
    case Nil{}:
      acc
    case Con{+h, t}:
      AaFile.perms.go(t, AaFile.perms.add(acc, AaFile.letter(h)))

def AaFile.perms(s: String) -> P.AaPerms:
  Maybe.default(&2, P.AaPerms, AaFile.perms.go(X.AaText.of_string(s), Some{P.AaPerms.none()}), P.AaPerms.none())

# Reading a rule

# a term that is a pattern: a quoted string, or a word starting with '/' or
# '{' (after variable expansion)
def AaFile.is_path(t: T.AaTerm) -> Bool:
  match t:
    case T.AaTmWord{+w}:
      Bool.or(U32.is_eq(X.AaText.head(w), 47), U32.is_eq(X.AaText.head(w), 123))
    case T.AaTmQuoted{q}:
      True{}
    case T.AaTmList{xs}:
      False{}
    case T.AaTmCond{k, v}:
      False{}
    case T.AaTmArrow{}:
      False{}

def AaFile.word(t: T.AaTerm, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  match t:
    case T.AaTmWord{w}:
      Done{w}
    case T.AaTmQuoted{q}:
      Fail{E.AaSrc.perms(src)}
    case T.AaTmList{xs}:
      Fail{E.AaSrc.syntax(src)}
    case T.AaTmCond{k, v}:
      Fail{E.AaSrc.syntax(src)}
    case T.AaTmArrow{}:
      Fail{E.AaSrc.syntax(src)}

def AaFile.path_text(t: T.AaTerm, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  match t:
    case T.AaTmWord{w}:
      Done{w}
    case T.AaTmQuoted{q}:
      Done{q}
    case T.AaTmList{xs}:
      Fail{E.AaSrc.syntax(src)}
    case T.AaTmCond{k, v}:
      Fail{E.AaSrc.syntax(src)}
    case T.AaTmArrow{}:
      Fail{E.AaSrc.syntax(src)}

# every alternative of a rule's pattern starts with '/'
def AaFile.rooted.go(alts: List<&2, List<&2, G.AaGTok>>) -> Bool:
  match alts:
    case Nil{}:
      True{}
    case Con{a, t}:
      match a:
        case Nil{}:
          False{}
        case Con{tok, r}:
          match tok:
            case G.AaGChar{c}:
              Bool.and(U32.is_eq(c, 47), AaFile.rooted.go(t))
            case _:
              False{}

def AaFile.rooted(g: G.AaGlob) -> Bool:
  match g:
    case G.AaGlob{alts, lit}:
      AaFile.rooted.go(alts)

def AaFile.check_rooted(+g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, G.AaGlob>:
  Bool.pick(Result<&2, &2, E.AaError, G.AaGlob>, AaFile.rooted(g), Done{g}, Fail{E.AaSrc.syntax(src)})

# a target needs an exec mode; with the permissions leading, l and a target
# make a link rule, outside the model (apparmor_parser: "link and exec
# perms conflict on a file rule using ->")
def AaFile.target.check(t: Maybe<&2, List<&2, U32>>, +lead: Bool, fp: AaFPerms, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFPerms>:
  match t:
    case None{}:
      Done{fp}
    case Some{x}:
      match fp:
        case AaFPerms{+p, +e}:
          Bool.pick(Result<&2, &2, E.AaError, AaFPerms>, Bool.and(AaFp.is_some(e), Bool.not(Bool.and(lead, P.AaPerms.has(p, 3n)))), Done{AaFPerms{p, e}}, Fail{E.AaSrc.perms(src)})

def AaFile.build.go(fp: AaFPerms, q: P.AaQual, ptext: List<&2, U32>, g: G.AaGlob, target: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, E.AaError, AaFileRule>:
  match fp:
    case AaFPerms{p, e}:
      Done{AaFileRule{q, ptext, g, p, e, target}}

def AaFile.build(+q: P.AaQual, +ptext: List<&2, U32>, pw: List<&2, U32>, +target: Maybe<&2, List<&2, U32>>, +lead: Bool, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFileRule>:
  do Result<&2, &2, E.AaError, AaFileRule>:
    g0 : G.AaGlob <- R.AaRule.glob_text(ptext, src)
    g : G.AaGlob <- AaFile.check_rooted(g0, src)
    fp0 : AaFPerms <- AaFile.parse_perms(pw, P.AaQual.deny(q), src)
    fp : AaFPerms <- AaFile.target.check(target, lead, fp0, src)
    AaFile.build.go(fp, q, ptext, g, target)

def AaFile.pair.go(q: P.AaQual, pt: T.AaTerm, wt: T.AaTerm, target: Maybe<&2, List<&2, U32>>, lead: Bool, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFileRule>:
  do Result<&2, &2, E.AaError, AaFileRule>:
    ptext : List<&2, U32> <- AaFile.path_text(pt, src)
    pw : List<&2, U32> <- AaFile.word(wt, src)
    AaFile.build(q, ptext, pw, target, lead, src)

# the two terms in either order: pattern and permissions
def AaFile.pair(+q: P.AaQual, +a: T.AaTerm, +b: T.AaTerm, +target: Maybe<&2, List<&2, U32>>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFileRule>:
  Bool.pick(Result<&2, &2, E.AaError, AaFileRule>, AaFile.is_path(a), AaFile.pair.go(q, a, b, target, False{}, src), AaFile.pair.go(q, b, a, target, True{}, src))

# `file,` alone: every path, every permission (an allow rule grants
# r w a l k m and ix; a deny rule denies all of them and x)
def AaFile.all(q: P.AaQual) -> AaFileRule:
  match q:
    case P.AaQual{a, +d, o}:
      AaFileRule{P.AaQual{a, d, o}, Nil{}, G.AaGlob.all(), P.AaPerms.of_bits([True{}, True{}, True{}, True{}, True{}, True{}, True{}]), Bool.pick(Maybe<&2, AaXMode>, d, None{}, Some{AaXIx{}}), None{}}

def AaFile.target(t: T.AaTerm, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, U32>>:
  AaFile.path_text(t, src)

def AaFile.parse.arrow(ok: Bool, +q: P.AaQual, +a: T.AaTerm, +b: T.AaTerm, tgt: T.AaTerm, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFileRule>:
  match ok:
    case False{}:
      Fail{E.AaSrc.syntax(src)}
    case True{}:
      do Result<&2, &2, E.AaError, AaFileRule>:
        t : List<&2, U32> <- AaFile.target(tgt, src)
        AaFile.pair(q, a, b, Some{t}, src)

# the terms after the qualifiers (and after `file`, if present)
def AaFile.parse(ts: List<&2, T.AaTerm>, +q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaFileRule>:
  match ts:
    case Nil{}:
      Done{AaFile.all(q)}
    case Con{a, r1}:
      match r1:
        case Nil{}:
          Fail{E.AaSrc.syntax(src)}
        case Con{b, r2}:
          match r2:
            case Nil{}:
              AaFile.pair(q, a, b, None{}, src)
            case Con{arrow, r3}:
              match r3:
                case Nil{}:
                  Fail{E.AaSrc.syntax(src)}
                case Con{tgt, r4}:
                  match r4:
                    case Nil{}:
                      AaFile.parse.arrow(T.AaTerm.is_arrow(arrow), q, a, b, tgt, src)
                    case Con{x, r5}:
                      Fail{E.AaSrc.syntax(src)}

# Matching

def AaFileRule.qual(r: AaFileRule) -> P.AaQual:
  match r:
    case AaFileRule{q, t, g, p, e, tg}:
      q

def AaFileRule.matches(r: AaFileRule, q: AaFileQuery) -> Bool:
  match r:
    case AaFileRule{qu, t, g, p, e, tg}:
      match q:
        case AaFileQuery{path, owner, req}:
          Bool.and(Bool.or(Bool.not(P.AaQual.owner(qu)), owner), G.AaGlob.matches(g, path))

def AaFileRule.matching.go(hit: Bool, r: AaFileRule, rest: List<&2, AaFileRule>) -> List<&2, AaFileRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

# the rules that match a request
def AaFileRule.matching(rs: List<&2, AaFileRule>, +q: AaFileQuery) -> List<&2, AaFileRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaFileRule.matching.go(AaFileRule.matches(r, q), r, AaFileRule.matching(t, q))

def AaFileRule.grant(r: AaFileRule) -> P.AaGrant:
  match r:
    case AaFileRule{q, t, g, p, e, tg}:
      P.AaGrant.of(q, p)

def AaFileRule.grants.of(rs: List<&2, AaFileRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{AaFileRule.grant(r), AaFileRule.grants.of(t)}

# what the matching rules grant and deny
def AaFileRule.grants(rs: List<&2, AaFileRule>, +q: AaFileQuery) -> List<&2, P.AaGrant>:
  AaFileRule.grants.of(AaFileRule.matching(rs, q))

def AaFileRule.append(xs: List<&2, AaFileRule>, ys: List<&2, AaFileRule>) -> List<&2, AaFileRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaFileRule.append(t, ys)}

def AaFileQuery.req(q: AaFileQuery) -> P.AaPerms:
  match q:
    case AaFileQuery{p, o, r}:
      r

def AaFileQuery.path(q: AaFileQuery) -> List<&2, U32>:
  match q:
    case AaFileQuery{p, o, r}:
      p
