# bend-osdev-apparmor: profiles (apparmor.d(5), "Profile Head", "Flags",
# and the rules of a profile body), their children and hats, and a loaded
# policy.
#
# A profile has a name, an optional exec attachment (a pattern; a name that
# is an absolute path is its own attachment), flags (a mode and the audit
# flag), its rules of each kind, and its child profiles and hats. A child's
# full name is parent//child.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./rule_file.bend as F
import ./rule_capability.bend as RC
import ./rule_network.bend as RN
import ./rule_signal.bend as RS
import ./rule_ptrace.bend as RP
import ./rule_mount.bend as RM
import ./rule_dbus.bend as RD
import ./rule_change_profile.bend as RX

# the profile modes of apparmor.d(5): enforce (the default), complain, kill,
# unconfined, default_allow, prompt
type AaMode is Data:
  AaModeEnforce{}
  AaModeComplain{}
  AaModeKill{}
  AaModeUnconfined{}
  AaModeDefaultAllow{}
  AaModePrompt{}

type AaFlags is Data:
  AaFlags{mode: AaMode, audit: Bool}

def AaFlags.default() -> AaFlags:
  AaFlags{AaModeEnforce{}, False{}}

def AaFlags.mode(f: AaFlags) -> AaMode:
  match f:
    case AaFlags{m, a}:
      m

def AaFlags.audit(f: AaFlags) -> Bool:
  match f:
    case AaFlags{m, a}:
      a

def AaMode.show(m: AaMode) -> String:
  match m:
    case AaModeEnforce{}:
      "enforce"
    case AaModeComplain{}:
      "complain"
    case AaModeKill{}:
      "kill"
    case AaModeUnconfined{}:
      "unconfined"
    case AaModeDefaultAllow{}:
      "default_allow"
    case AaModePrompt{}:
      "prompt"

# the modes in which an access no rule allows is refused
def AaMode.enforcing(m: AaMode) -> Bool:
  match m:
    case AaModeEnforce{}:
      True{}
    case AaModeKill{}:
      True{}
    case AaModePrompt{}:
      True{}
    case AaModeComplain{}:
      False{}
    case AaModeUnconfined{}:
      False{}
    case AaModeDefaultAllow{}:
      False{}

def AaMode.is_complain(m: AaMode) -> Bool:
  match m:
    case AaModeComplain{}:
      True{}
    case _:
      False{}

# The rules of a profile, by kind

type AaRules is Data:
  AaRules{files: List<&2, F.AaFileRule>, caps: List<&2, RC.AaCapRule>, nets: List<&2, RN.AaNetRule>, signals: List<&2, RS.AaSignalRule>, ptraces: List<&2, RP.AaPtraceRule>, mounts: List<&2, RM.AaMountRule>, dbus: List<&2, RD.AaDbusRule>, changes: List<&2, RX.AaChangeRule>}

def AaRules.empty() -> AaRules:
  AaRules{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

# the rules of a and of b
def AaRules.append(a: AaRules, b: AaRules) -> AaRules:
  match a b:
    case AaRules{f1, c1, n1, s1, p1, m1, d1, x1} AaRules{f2, c2, n2, s2, p2, m2, d2, x2}:
      AaRules{F.AaFileRule.append(f1, f2), RC.AaCapRule.append(c1, c2), RN.AaNetRule.append(n1, n2), RS.AaSignalRule.append(s1, s2), RP.AaPtraceRule.append(p1, p2), RM.AaMountRule.append(m1, m2), RD.AaDbusRule.append(d1, d2), RX.AaChangeRule.append(x1, x2)}

def AaRules.files(r: AaRules) -> List<&2, F.AaFileRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      f

def AaRules.caps(r: AaRules) -> List<&2, RC.AaCapRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      c

def AaRules.nets(r: AaRules) -> List<&2, RN.AaNetRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      n

def AaRules.signals(r: AaRules) -> List<&2, RS.AaSignalRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      s

def AaRules.ptraces(r: AaRules) -> List<&2, RP.AaPtraceRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      p

def AaRules.mounts(r: AaRules) -> List<&2, RM.AaMountRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      m

def AaRules.dbus(r: AaRules) -> List<&2, RD.AaDbusRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      d

def AaRules.changes(r: AaRules) -> List<&2, RX.AaChangeRule>:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      x

def AaRules.file(r: F.AaFileRule) -> AaRules:
  AaRules{[r], Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def AaRules.cap(r: RC.AaCapRule) -> AaRules:
  AaRules{Nil{}, [r], Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def AaRules.net(r: RN.AaNetRule) -> AaRules:
  AaRules{Nil{}, Nil{}, [r], Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def AaRules.signal(r: RS.AaSignalRule) -> AaRules:
  AaRules{Nil{}, Nil{}, Nil{}, [r], Nil{}, Nil{}, Nil{}, Nil{}}

def AaRules.ptrace(r: RP.AaPtraceRule) -> AaRules:
  AaRules{Nil{}, Nil{}, Nil{}, Nil{}, [r], Nil{}, Nil{}, Nil{}}

def AaRules.mount(r: RM.AaMountRule) -> AaRules:
  AaRules{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, [r], Nil{}, Nil{}}

def AaRules.dbus_rule(r: RD.AaDbusRule) -> AaRules:
  AaRules{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, [r], Nil{}}

def AaRules.change(r: RX.AaChangeRule) -> AaRules:
  AaRules{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, [r]}

def AaRules.with_files(r: AaRules, fs: List<&2, F.AaFileRule>) -> AaRules:
  match r:
    case AaRules{f, c, n, s, p, m, d, x}:
      AaRules{fs, c, n, s, p, m, d, x}

# Profiles

type AaProfile is Data:
  AaProfile{name: List<&2, U32>, attach: Maybe<&2, G.AaGlob>, flags: AaFlags, rules: AaRules, children: List<&2, AaProfile>, hats: List<&2, AaProfile>}

def AaProfile.name(p: AaProfile) -> List<&2, U32>:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      n

def AaProfile.attach(p: AaProfile) -> Maybe<&2, G.AaGlob>:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      a

def AaProfile.flags(p: AaProfile) -> AaFlags:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      f

def AaProfile.rules(p: AaProfile) -> AaRules:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      r

def AaProfile.children(p: AaProfile) -> List<&2, AaProfile>:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      c

def AaProfile.hats(p: AaProfile) -> List<&2, AaProfile>:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      h

# a profile with no rules, children or hats
def AaProfile.new(n: List<&2, U32>, a: Maybe<&2, G.AaGlob>, f: AaFlags) -> AaProfile:
  AaProfile{n, a, f, AaRules.empty(), Nil{}, Nil{}}

def AaProfile.with_flags(p: AaProfile, f: AaFlags) -> AaProfile:
  match p:
    case AaProfile{n, a, f0, r, c, h}:
      AaProfile{n, a, f, r, c, h}

# p with the rules r added: what an include of rules r into p does
def AaProfile.include(p: AaProfile, r: AaRules) -> AaProfile:
  match p:
    case AaProfile{n, a, f, r0, c, h}:
      AaProfile{n, a, f, AaRules.append(r0, r), c, h}

def AaProfile.list_append(xs: List<&2, AaProfile>, ys: List<&2, AaProfile>) -> List<&2, AaProfile>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaProfile.list_append(t, ys)}

# p with the rules r put first (the order of rules does not matter; this is
# what loading uses, in time proportional to r)
def AaProfile.prepend(p: AaProfile, r: AaRules) -> AaProfile:
  match p:
    case AaProfile{n, a, f, r0, c, h}:
      AaProfile{n, a, f, AaRules.append(r, r0), c, h}

def AaProfile.add_child(p: AaProfile, k: AaProfile) -> AaProfile:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      AaProfile{n, a, f, r, AaProfile.list_append(c, [k]), h}

def AaProfile.add_hat(p: AaProfile, k: AaProfile) -> AaProfile:
  match p:
    case AaProfile{n, a, f, r, c, h}:
      AaProfile{n, a, f, r, c, AaProfile.list_append(h, [k])}

def AaProfile.find.go(hit: Bool, p: AaProfile, rest: Maybe<&2, AaProfile>) -> Maybe<&2, AaProfile>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      rest

# the profile of the list named n
def AaProfile.find(ps: List<&2, AaProfile>, +n: List<&2, U32>) -> Maybe<&2, AaProfile>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, t}:
      AaProfile.find.go(X.AaText.eq(AaProfile.name(p), n), p, AaProfile.find(t, n))

# A policy: the top-level profiles of a namespace

type AaPolicy is Data:
  AaPolicy{profiles: List<&2, AaProfile>}

def AaPolicy.profiles(p: AaPolicy) -> List<&2, AaProfile>:
  match p:
    case AaPolicy{ps}:
      ps

# the child or hat named by the rest of a full name
def AaProfile.descend(fuel: Nat, m: Maybe<&2, AaProfile>, rest: Maybe<&2, X.AaSplit>) -> Maybe<&2, AaProfile>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match m:
        case None{}:
          None{}
        case Some{+p}:
          match rest:
            case None{}:
              Some{p}
            case Some{sp}:
              match sp:
                case X.AaSplit{first, more}:
                  AaProfile.descend(f, AaProfile.find(AaProfile.list_append(AaProfile.children(p), AaProfile.hats(p)), first), X.AaText.split2.opt(more))

def AaPolicy.lookup.go(s: X.AaSplit, ps: List<&2, AaProfile>, fuel: Nat) -> Maybe<&2, AaProfile>:
  match s:
    case X.AaSplit{first, more}:
      AaProfile.descend(fuel, AaProfile.find(ps, first), X.AaText.split2.opt(more))

# the profile with the full name n (a, a//b, a//b//c, ...)
def AaPolicy.lookup(pol: AaPolicy, +n: List<&2, U32>) -> Maybe<&2, AaProfile>:
  AaPolicy.lookup.go(X.AaText.split2(n), AaPolicy.profiles(pol), 1n+X.AaText.len(n))
