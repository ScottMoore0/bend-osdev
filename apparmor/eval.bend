# bend-osdev-apparmor: the access decision.
#
# The rules of one kind that match a request each contribute a grant
# (perm.bend). Allow grants accumulate into the allowed set, deny grants
# into the denied set (rules accumulate as a union: apparmor.d(5), "order
# ... does not matter"); what is granted is allowed minus denied, so a deny
# rule always wins. A request is granted when every permission it asks for
# is. Then the profile mode decides (apparmor.d(5), "Profile Mode";
# apparmor(7), "Complain mode"):
#   enforce, prompt: granted -> allowed, else denied;
#   kill: granted -> allowed, else denied and the task killed;
#   complain: granted -> allowed, else allowed and logged, except that a
#     request an explicit deny rule meets is denied (AaOptions.complain_deny);
#   default_allow: allowed unless a deny rule meets the request;
#   unconfined: allowed.
# Logging: an allowed request is audited when the profile has the audit
# flag or an audit rule grants a requested permission; a denial is logged
# unless every refused permission is quieted by a deny rule without audit.
import Base
import ./perm.bend as P
import ./options.bend as O
import ./profile.bend as PR
import ./rule_file.bend as F
import ./rule_capability.bend as RC
import ./rule_network.bend as RN
import ./rule_signal.bend as RS
import ./rule_ptrace.bend as RP
import ./rule_mount.bend as RM
import ./rule_dbus.bend as RD
import ./rule_change_profile.bend as RX

type AaDecision is Data:
  # allowed, not logged
  AaAllow{}
  # allowed, logged as AUDIT
  AaAudit{}
  # not granted, allowed in complain mode, logged as ALLOWED
  AaComplain{}
  # denied (EACCES or EPERM), logged as DENIED unless quieted
  AaDeny{logged: Bool}
  # denied, and the task is killed (kill mode)
  AaKill{}

def AaDecision.allowed(d: AaDecision) -> Bool:
  match d:
    case AaAllow{}:
      True{}
    case AaAudit{}:
      True{}
    case AaComplain{}:
      True{}
    case AaDeny{l}:
      False{}
    case AaKill{}:
      False{}

def AaDecision.show(d: AaDecision) -> String:
  match d:
    case AaAllow{}:
      "allow"
    case AaAudit{}:
      "audit"
    case AaComplain{}:
      "complain"
    case AaDeny{l}:
      Bool.pick(String, l, "deny", "deny-quiet")
    case AaKill{}:
      "kill"

# What the grants add up to

type AaAcc is Data:
  AaAcc{allow: P.AaPerms, deny: P.AaPerms, audit: P.AaPerms, quiet: P.AaPerms}

def AaAcc.empty() -> AaAcc:
  AaAcc{P.AaPerms.none(), P.AaPerms.none(), P.AaPerms.none(), P.AaPerms.none()}

# two accumulations together: each set the union
def AaAcc.join(a: AaAcc, b: AaAcc) -> AaAcc:
  match a b:
    case AaAcc{al, de, au, qu} AaAcc{al2, de2, au2, qu2}:
      AaAcc{P.AaPerms.union(al, al2), P.AaPerms.union(de, de2), P.AaPerms.union(au, au2), P.AaPerms.union(qu, qu2)}

# what one grant contributes: allowed or denied; audited, or (for a denial
# without audit) quieted
def AaAcc.single.go(audit: Bool, deny: Bool, +p: P.AaPerms) -> AaAcc:
  match audit:
    case True{}:
      match deny:
        case True{}:
          AaAcc{P.AaPerms.none(), p, p, P.AaPerms.none()}
        case False{}:
          AaAcc{p, P.AaPerms.none(), p, P.AaPerms.none()}
    case False{}:
      match deny:
        case True{}:
          AaAcc{P.AaPerms.none(), p, P.AaPerms.none(), p}
        case False{}:
          AaAcc{p, P.AaPerms.none(), P.AaPerms.none(), P.AaPerms.none()}

def AaAcc.single(g: P.AaGrant) -> AaAcc:
  match g:
    case P.AaGrant{audit, deny, p}:
      AaAcc.single.go(audit, deny, p)

def AaAcc.add(a: AaAcc, g: P.AaGrant) -> AaAcc:
  AaAcc.join(a, AaAcc.single(g))

def AaAcc.from(gs: List<&2, P.AaGrant>, a: AaAcc) -> AaAcc:
  match gs:
    case Nil{}:
      a
    case Con{g, t}:
      AaAcc.from(t, AaAcc.add(a, g))

def AaAcc.of(gs: List<&2, P.AaGrant>) -> AaAcc:
  AaAcc.from(gs, AaAcc.empty())

def AaAcc.allow(a: AaAcc) -> P.AaPerms:
  match a:
    case AaAcc{al, de, au, qu}:
      al

def AaAcc.deny(a: AaAcc) -> P.AaPerms:
  match a:
    case AaAcc{al, de, au, qu}:
      de

def AaAcc.audit(a: AaAcc) -> P.AaPerms:
  match a:
    case AaAcc{al, de, au, qu}:
      au

def AaAcc.quiet(a: AaAcc) -> P.AaPerms:
  match a:
    case AaAcc{al, de, au, qu}:
      qu

# what the grants allow and do not deny
def AaAcc.granted(a: AaAcc) -> P.AaPerms:
  match a:
    case AaAcc{al, de, au, qu}:
      P.AaPerms.minus(al, de)

def AaEval.granted(gs: List<&2, P.AaGrant>) -> P.AaPerms:
  AaAcc.granted(AaAcc.of(gs))

# what the grants deny
def AaEval.denied(gs: List<&2, P.AaGrant>) -> P.AaPerms:
  AaAcc.deny(AaAcc.of(gs))

# The decision

def AaEval.choose(c: Bool, a: AaDecision, b: AaDecision) -> AaDecision:
  match c:
    case True{}:
      a
    case False{}:
      b

# cov: the grants cover the request; hit: a deny rule meets it; cd:
# AaOptions.complain_deny; ok: the allowed outcome; no: the denied one
def AaEval.decide.mode(m: PR.AaMode, cov: Bool, hit: Bool, cd: Bool, ok: AaDecision, no: AaDecision) -> AaDecision:
  match m:
    case PR.AaModeEnforce{}:
      AaEval.choose(cov, ok, no)
    case PR.AaModePrompt{}:
      AaEval.choose(cov, ok, no)
    case PR.AaModeKill{}:
      AaEval.choose(cov, ok, AaKill{})
    case PR.AaModeComplain{}:
      AaEval.choose(cov, ok, AaEval.choose(Bool.and(cd, hit), no, AaComplain{}))
    case PR.AaModeDefaultAllow{}:
      AaEval.choose(hit, no, ok)
    case PR.AaModeUnconfined{}:
      AaAllow{}

def AaEval.decide.acc(opts: O.AaOptions, flags: PR.AaFlags, +req: P.AaPerms, a: AaAcc) -> AaDecision:
  match flags:
    case PR.AaFlags{m, +fa}:
      match a:
        case AaAcc{al, +de, +au, qu}:
          +granted = P.AaPerms.minus(al, de)
          AaEval.decide.mode(m, P.AaPerms.covers(granted, req), P.AaPerms.meets(req, de), O.AaOptions.complain_deny(opts), AaEval.choose(Bool.or(fa, P.AaPerms.meets(req, au)), AaAudit{}, AaAllow{}), AaDeny{Bool.or(fa, Bool.not(P.AaPerms.covers(P.AaPerms.minus(qu, au), P.AaPerms.minus(req, granted))))})

# the decision on a request for the permissions req, given the grants of
# the rules that match it, under a profile's flags
def AaEval.decide(opts: O.AaOptions, flags: PR.AaFlags, +req: P.AaPerms, gs: List<&2, P.AaGrant>) -> AaDecision:
  AaEval.decide.acc(opts, flags, req, AaAcc.of(gs))

# whether a deny rule decides under these options and mode: every mode but
# unconfined, and complain only with complain_deny
def AaEval.deny_applies(opts: O.AaOptions, m: PR.AaMode) -> Bool:
  match m:
    case PR.AaModeUnconfined{}:
      False{}
    case PR.AaModeComplain{}:
      O.AaOptions.complain_deny(opts)
    case PR.AaModeEnforce{}:
      True{}
    case PR.AaModeKill{}:
      True{}
    case PR.AaModePrompt{}:
      True{}
    case PR.AaModeDefaultAllow{}:
      True{}

# Each rule kind, on a profile

def AaEval.file(opts: O.AaOptions, +p: PR.AaProfile, +q: F.AaFileQuery) -> AaDecision:
  match q:
    case F.AaFileQuery{path, owner, req}:
      AaEval.decide(opts, PR.AaProfile.flags(p), req, F.AaFileRule.grants(PR.AaRules.files(PR.AaProfile.rules(p)), F.AaFileQuery{path, owner, req}))

def AaEval.capability(opts: O.AaOptions, +p: PR.AaProfile, +q: RC.AaCapQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RC.AaCapQuery.req(), RC.AaCapRule.grants(PR.AaRules.caps(PR.AaProfile.rules(p)), q))

def AaEval.network(opts: O.AaOptions, +p: PR.AaProfile, +q: RN.AaNetQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RN.AaNetQuery.req(), RN.AaNetRule.grants(PR.AaRules.nets(PR.AaProfile.rules(p)), q))

def AaEval.signal(opts: O.AaOptions, +p: PR.AaProfile, +q: RS.AaSignalQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RS.AaSignalQuery.req(q), RS.AaSignalRule.grants(PR.AaRules.signals(PR.AaProfile.rules(p)), q))

def AaEval.ptrace(opts: O.AaOptions, +p: PR.AaProfile, +q: RP.AaPtraceQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RP.AaPtraceQuery.req(q), RP.AaPtraceRule.grants(PR.AaRules.ptraces(PR.AaProfile.rules(p)), q))

def AaEval.mount(opts: O.AaOptions, +p: PR.AaProfile, +q: RM.AaMountQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RM.AaMountQuery.req(), RM.AaMountRule.grants(PR.AaRules.mounts(PR.AaProfile.rules(p)), q))

def AaEval.dbus(opts: O.AaOptions, +p: PR.AaProfile, +q: RD.AaDbusQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RD.AaDbusQuery.req(q), RD.AaDbusRule.grants(PR.AaRules.dbus(PR.AaProfile.rules(p)), q))

def AaEval.change_profile(opts: O.AaOptions, +p: PR.AaProfile, +q: RX.AaChangeQuery) -> AaDecision:
  AaEval.decide(opts, PR.AaProfile.flags(p), RX.AaChangeQuery.req(), RX.AaChangeRule.grants(PR.AaRules.changes(PR.AaProfile.rules(p)), q))
