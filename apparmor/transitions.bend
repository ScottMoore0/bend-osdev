# bend-osdev-apparmor: exec transitions (apparmor.d(5), "Access Modes",
# "Directed profile transitions", "Attachment Conditionals").
#
# When a confined task executes a path, the profile must grant x on it; the
# exec mode of the matching allow rules then says where the task goes: ix
# stays in the profile, ux and Ux leave confinement, px and Px move to the
# profile named after -> or else to the profile whose attachment best
# matches the path, cx and Cx do the same among the profile's children; the
# i and u forms fall back to ix and ux (Ux for PUx and CUx) when no profile
# is found, and the plain forms fail. Upper case scrubs the environment.
#
# Where several allow rules with exec modes match, a rule whose pattern is
# literal (no wildcard, no braces) decides over pattern rules, and the rules
# that decide must agree (apparmor_parser 4.0.1 rejects a profile otherwise
# when it can tell; see the README, "Experiments"); disagreement is a
# failure here. Among attachments, a literal one wins, then the longest
# literal prefix; a tie fails ("If the heuristic can not determine a winner
# between multiple matches the exec will be denied").
#
# A task in complain mode whose profile grants no x, or whose x comes from
# no exec rule (default_allow), stays in its profile. A profile in
# unconfined mode executes as an unconfined task: the profile whose
# attachment matches, else unconfined.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./options.bend as O
import ./profile.bend as PR
import ./rule_file.bend as F
import ./eval.bend as V

type AaTarget is Data:
  # the same profile
  AaTStay{}
  # the profile with this full name
  AaTProfile{name: List<&2, U32>}
  # no profile
  AaTUnconfined{}

type AaExecWhy is Data:
  # the profile does not grant x on the path (the decision says how it refused)
  AaExecDenied{decision: V.AaDecision}
  # px or cx found no profile, and there is no fallback
  AaExecNoProfile{}
  # the matching rules give different exec modes or targets
  AaExecConflict{}
  # two attachments match equally well
  AaExecAmbiguous{}
  # the executing profile is not in the policy
  AaExecUnknown{}

type AaExecResult is Data:
  AaExecOk{target: AaTarget, scrub: Bool, decision: V.AaDecision}
  AaExecErr{why: AaExecWhy}

def AaExecResult.ok(r: AaExecResult) -> Bool:
  match r:
    case AaExecOk{t, s, d}:
      True{}
    case AaExecErr{w}:
      False{}

def AaTarget.show(t: AaTarget) -> String:
  match t:
    case AaTStay{}:
      "stay"
    case AaTProfile{n}:
      "profile " ++ X.AaText.to_string(n)
    case AaTUnconfined{}:
      "unconfined"

def AaExecResult.show(r: AaExecResult) -> String:
  match r:
    case AaExecOk{t, s, d}:
      AaTarget.show(t) ++ Bool.pick(String, s, " scrub", "")
    case AaExecErr{w}:
      match w:
        case AaExecDenied{d}:
          "denied (" ++ V.AaDecision.show(d) ++ ")"
        case AaExecNoProfile{}:
          "no profile"
        case AaExecConflict{}:
          "conflict"
        case AaExecAmbiguous{}:
          "ambiguous"
        case AaExecUnknown{}:
          "unknown profile"

# Attachments

type AaAttach is Data:
  AaAttachNone{}
  AaAttachOne{name: List<&2, U32>, rank: U32}
  AaAttachTie{rank: U32}

def AaAttach.rank(a: AaAttach) -> U32:
  match a:
    case AaAttachNone{}:
      0
    case AaAttachOne{n, r}:
      r
    case AaAttachTie{r}:
      r

# the better of the best so far and a candidate of rank r
def AaAttach.better(+best: AaAttach, +r: U32, name: List<&2, U32>) -> AaAttach:
  +b = AaAttach.rank(best)
  Bool.pick(AaAttach, U32.is_eq(r, 0), best, Bool.pick(AaAttach, U32.is_gt(r, b), AaAttachOne{name, r}, Bool.pick(AaAttach, U32.is_eq(r, b), AaAttachTie{r}, best)))

def AaAttach.rank_of(m: Maybe<&2, G.AaGlob>, +path: List<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{g}:
      G.AaGlob.rank(g, path)

def AaAttach.join(+prefix: List<&2, U32>, name: List<&2, U32>) -> List<&2, U32>:
  match prefix:
    case Nil{}:
      name
    case Con{h, t}:
      X.AaText.append(Con{h, t}, X.AaText.append(X.AaText.of_string("//"), name))

# the profile of the list whose attachment best matches the path; prefix:
# the full name of the parent, for children
def AaAttach.best(ps: List<&2, PR.AaProfile>, +path: List<&2, U32>, +prefix: List<&2, U32>, +best: AaAttach) -> AaAttach:
  match ps:
    case Nil{}:
      best
    case Con{+p, t}:
      AaAttach.best(t, path, prefix, AaAttach.better(best, AaAttach.rank_of(PR.AaProfile.attach(p), path), AaAttach.join(prefix, PR.AaProfile.name(p))))

# The exec mode the matching rules give

type AaXSel is Data:
  AaXSel{mode: F.AaXMode, target: Maybe<&2, List<&2, U32>>}

def AaXSel.target_eq(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      X.AaText.eq(x, y)
    case _ _:
      False{}

def AaXSel.eq(a: AaXSel, b: AaXSel) -> Bool:
  match a b:
    case AaXSel{m1, t1} AaXSel{m2, t2}:
      Bool.and(F.AaXMode.eq(m1, m2), AaXSel.target_eq(t1, t2))

# the exec rules among the matching ones: literal ones and pattern ones
type AaXSels is Data:
  AaXSels{literal: List<&2, AaXSel>, pattern: List<&2, AaXSel>}

def AaXSels.add(s: AaXSels, lit: Bool, x: AaXSel) -> AaXSels:
  match s:
    case AaXSels{l, p}:
      match lit:
        case True{}:
          AaXSels{Con{x, l}, p}
        case False{}:
          AaXSels{l, Con{x, p}}

def AaXSels.rule.go(deny: Bool, s: AaXSels, lit: Bool, x: AaXSel) -> AaXSels:
  match deny:
    case True{}:
      s
    case False{}:
      AaXSels.add(s, lit, x)

def AaXSels.rule(s: AaXSels, r: F.AaFileRule) -> AaXSels:
  match r:
    case F.AaFileRule{q, txt, g, ps, e, tg}:
      match e:
        case None{}:
          s
        case Some{m}:
          AaXSels.rule.go(P.AaQual.deny(q), s, G.AaGlob.is_literal(g), AaXSel{m, tg})

def AaXSels.of(rs: List<&2, F.AaFileRule>, s: AaXSels) -> AaXSels:
  match rs:
    case Nil{}:
      s
    case Con{r, t}:
      AaXSels.of(t, AaXSels.rule(s, r))

# every selection agrees with x
def AaXSel.all_eq(xs: List<&2, AaXSel>, +x: AaXSel) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(AaXSel.eq(y, x), AaXSel.all_eq(t, x))

# the selection the list agrees on: None for an empty list, a conflict otherwise
type AaXPick is Data:
  AaXNone{}
  AaXOne{sel: AaXSel}
  AaXClash{}

def AaXPick.of(xs: List<&2, AaXSel>) -> AaXPick:
  match xs:
    case Nil{}:
      AaXNone{}
    case Con{+x, t}:
      Bool.pick(AaXPick, AaXSel.all_eq(t, x), AaXOne{x}, AaXClash{})

def AaXPick.choose(lit: AaXPick, pat: AaXPick) -> AaXPick:
  match lit:
    case AaXNone{}:
      pat
    case AaXOne{x}:
      AaXOne{x}
    case AaXClash{}:
      AaXClash{}

def AaXPick.sels(s: AaXSels) -> AaXPick:
  match s:
    case AaXSels{l, p}:
      AaXPick.choose(AaXPick.of(l), AaXPick.of(p))

# the exec mode the matching rules rs give
def AaXPick.rules(rs: List<&2, F.AaFileRule>) -> AaXPick:
  AaXPick.sels(AaXSels.of(rs, AaXSels{Nil{}, Nil{}}))

# Applying a mode

def AaTrans.fallback(fb: F.AaXFallback, scrub: Bool, d: V.AaDecision) -> AaExecResult:
  match fb:
    case F.AaFbNone{}:
      AaExecErr{AaExecNoProfile{}}
    case F.AaFbIx{}:
      AaExecOk{AaTStay{}, False{}, d}
    case F.AaFbUx{}:
      AaExecOk{AaTUnconfined{}, scrub, d}

def AaTrans.attached(a: AaAttach, fb: F.AaXFallback, scrub: Bool, d: V.AaDecision) -> AaExecResult:
  match a:
    case AaAttachNone{}:
      AaTrans.fallback(fb, scrub, d)
    case AaAttachOne{n, r}:
      AaExecOk{AaTProfile{n}, scrub, d}
    case AaAttachTie{r}:
      AaExecErr{AaExecAmbiguous{}}

def AaTrans.named(m: Maybe<&2, PR.AaProfile>, name: List<&2, U32>, fb: F.AaXFallback, scrub: Bool, d: V.AaDecision) -> AaExecResult:
  match m:
    case None{}:
      AaTrans.fallback(fb, scrub, d)
    case Some{p}:
      AaExecOk{AaTProfile{name}, scrub, d}

# px: the profile named, else the best attachment in the namespace
def AaTrans.px(tg: Maybe<&2, List<&2, U32>>, pol: PR.AaPolicy, +path: List<&2, U32>, scrub: Bool, fb: F.AaXFallback, d: V.AaDecision) -> AaExecResult:
  match tg:
    case Some{+t}:
      AaTrans.named(PR.AaPolicy.lookup(pol, t), t, fb, scrub, d)
    case None{}:
      AaTrans.attached(AaAttach.best(PR.AaPolicy.profiles(pol), path, Nil{}, AaAttachNone{}), fb, scrub, d)

# cx: the child named, else the child whose attachment matches best
def AaTrans.cx(tg: Maybe<&2, List<&2, U32>>, +p: PR.AaProfile, +pname: List<&2, U32>, +path: List<&2, U32>, scrub: Bool, fb: F.AaXFallback, d: V.AaDecision) -> AaExecResult:
  match tg:
    case Some{+t}:
      AaTrans.named(PR.AaProfile.find(PR.AaProfile.children(p), t), AaAttach.join(pname, t), fb, scrub, d)
    case None{}:
      AaTrans.attached(AaAttach.best(PR.AaProfile.children(p), path, pname, AaAttachNone{}), fb, scrub, d)

def AaTrans.apply(sel: AaXSel, pol: PR.AaPolicy, p: PR.AaProfile, pname: List<&2, U32>, path: List<&2, U32>, d: V.AaDecision) -> AaExecResult:
  match sel:
    case AaXSel{m, tg}:
      match m:
        case F.AaXIx{}:
          AaExecOk{AaTStay{}, False{}, d}
        case F.AaXUx{s}:
          AaExecOk{AaTUnconfined{}, s, d}
        case F.AaXPx{s, fb}:
          AaTrans.px(tg, pol, path, s, fb, d)
        case F.AaXCx{s, fb}:
          AaTrans.cx(tg, p, pname, path, s, fb, d)

# an unconfined task (or a profile in unconfined mode) executing path: the
# profile whose attachment matches, else unconfined
def AaTrans.exec_unconfined(pol: PR.AaPolicy, +path: List<&2, U32>) -> AaExecResult:
  AaTrans.attached(AaAttach.best(PR.AaPolicy.profiles(pol), path, Nil{}, AaAttachNone{}), F.AaFbUx{}, False{}, V.AaAllow{})

def AaTrans.exec.pick(k: AaXPick, pol: PR.AaPolicy, p: PR.AaProfile, pname: List<&2, U32>, path: List<&2, U32>, d: V.AaDecision) -> AaExecResult:
  match k:
    case AaXNone{}:
      AaExecOk{AaTStay{}, False{}, d}
    case AaXOne{sel}:
      AaTrans.apply(sel, pol, p, pname, path, d)
    case AaXClash{}:
      AaExecErr{AaExecConflict{}}

def AaTrans.exec.granted(ok: Bool, +q: F.AaFileQuery, pol: PR.AaPolicy, +p: PR.AaProfile, pname: List<&2, U32>, path: List<&2, U32>, +d: V.AaDecision) -> AaExecResult:
  match ok:
    case True{}:
      AaTrans.exec.pick(AaXPick.rules(F.AaFileRule.matching(PR.AaRules.files(PR.AaProfile.rules(p)), q)), pol, p, pname, path, d)
    case False{}:
      AaExecErr{AaExecDenied{d}}

def AaTrans.is_unconfined(m: PR.AaMode) -> Bool:
  match m:
    case PR.AaModeUnconfined{}:
      True{}
    case _:
      False{}

def AaTrans.exec.mode(unc: Bool, opts: O.AaOptions, +pol: PR.AaPolicy, +p: PR.AaProfile, +pname: List<&2, U32>, owner: Bool, +path: List<&2, U32>) -> AaExecResult:
  match unc:
    case True{}:
      AaTrans.exec_unconfined(pol, path)
    case False{}:
      +q = {F.AaFileQuery{path, owner, P.AaPerms.bit(6n)} : F.AaFileQuery}
      +d = {V.AaEval.file(opts, p, q) : V.AaDecision}
      AaTrans.exec.granted(V.AaDecision.allowed(d), q, pol, p, pname, path, d)

def AaTrans.exec.of(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, pol: PR.AaPolicy, pname: List<&2, U32>, owner: Bool, path: List<&2, U32>) -> AaExecResult:
  match m:
    case None{}:
      AaExecErr{AaExecUnknown{}}
    case Some{+p}:
      AaTrans.exec.mode(AaTrans.is_unconfined(PR.AaFlags.mode(PR.AaProfile.flags(p))), opts, pol, p, pname, owner, path)

# a task confined by the profile with full name pname executes path (owner:
# its fsuid owns the file): where it goes, or why it may not
def AaTrans.exec(opts: O.AaOptions, +pol: PR.AaPolicy, +pname: List<&2, U32>, owner: Bool, path: List<&2, U32>) -> AaExecResult:
  AaTrans.exec.of(PR.AaPolicy.lookup(pol, pname), opts, pol, pname, owner, path)
