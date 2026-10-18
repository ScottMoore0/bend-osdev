# Properties, for every input:
#   globs: the backtracking matcher agrees with the list model (a path
#     matches a pattern when it can be cut into one piece per pattern
#     element, each piece matching its element), and the fast matcher (a set
#     of active positions moved a byte at a time) with the backtracking one,
#     for every sequence, pattern and path;
#   the decision engine (eval.bend), for every set of matching rules (their
#     grants), every request, mode and option:
#     what is granted never includes what is denied;
#     a deny rule that meets the request wins, in every mode where deny
#       rules apply (all but unconfined, and complain only with
#       complain_deny);
#     a request no rule matches is denied in enforcing modes (enforce,
#       kill, prompt);
#     complain mode allows exactly what no applicable deny rule refuses, so
#       with complain_deny off it never denies;
#   the same for file rules on a profile: a deny rule meeting the request
#     wins, a path no rule matches is denied;
#   include is idempotent: adding a set of rules to a profile twice decides
#     every request of every kind as adding it once;
#   an exec the profile does not grant x for fails.
#
# Witnesses: each hypothesis above holds for some input (the *_sat laws).
# Vectors: globs as apparmor_parser compiles them (see the README,
# "Experiments"), and decisions on a small policy.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./options.bend as O
import ./profile.bend as PR
import ./eval.bend as V
import ./transitions.bend as TR
import ./rule_file.bend as F
import ./rule_capability.bend as RC
import ./rule_network.bend as RN
import ./rule_signal.bend as RS
import ./rule_ptrace.bend as RP
import ./rule_mount.bend as RM
import ./rule_dbus.bend as RD
import ./rule_change_profile.bend as RX
import ./example.bend as EX

# Globs

law glob_seq_model:
  for seq: List<&2, G.AaGTok>
  for s: List<&2, U32>
  {G.AaGSeq.matches(seq, s) == G.AaGSeq.model(seq, s) : Bool}

law glob_run:
  for seq: List<&2, G.AaGTok>
  for s: List<&2, U32>
  {G.AaGSeq.run(seq, s) == G.AaGSeq.matches(seq, s) : Bool}

law glob_model:
  for g: G.AaGlob
  for s: List<&2, U32>
  {G.AaGlob.matches(g, s) == G.AaGlob.model(g, s) : Bool}

law glob_ref_model:
  for g: G.AaGlob
  for s: List<&2, U32>
  {G.AaGlob.matches_ref(g, s) == G.AaGlob.model(g, s) : Bool}

# The decision engine

law granted_never_denied:
  for gs: List<&2, P.AaGrant>
  {P.AaPerms.meets(V.AaEval.granted(gs), V.AaEval.denied(gs)) == False{} : Bool}

law deny_wins:
  for opts: O.AaOptions
  for gs: List<&2, P.AaGrant>
  for flags: PR.AaFlags
  for req: P.AaPerms
  for h1: {V.AaEval.deny_applies(opts, PR.AaFlags.mode(flags)) == True{} : Bool}
  for h2: {P.AaPerms.meets(req, V.AaEval.denied(gs)) == True{} : Bool}
  {V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, gs)) == False{} : Bool}

law unmatched_denied:
  for opts: O.AaOptions
  for flags: PR.AaFlags
  for req: P.AaPerms
  for h1: {PR.AaMode.enforcing(PR.AaFlags.mode(flags)) == True{} : Bool}
  for h2: {P.AaPerms.any(req) == True{} : Bool}
  {V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, Nil{})) == False{} : Bool}

law complain_decided_by_deny:
  for opts: O.AaOptions
  for flags: PR.AaFlags
  for req: P.AaPerms
  for gs: List<&2, P.AaGrant>
  for h: {PR.AaMode.is_complain(PR.AaFlags.mode(flags)) == True{} : Bool}
  {V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, gs)) == Bool.not(Bool.and(O.AaOptions.complain_deny(opts), P.AaPerms.meets(req, V.AaEval.denied(gs)))) : Bool}

law complain_never_denies:
  for opts: O.AaOptions
  for flags: PR.AaFlags
  for req: P.AaPerms
  for gs: List<&2, P.AaGrant>
  for h1: {O.AaOptions.complain_deny(opts) == False{} : Bool}
  for h2: {PR.AaMode.is_complain(PR.AaFlags.mode(flags)) == True{} : Bool}
  {V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, gs)) == True{} : Bool}

# File rules on a profile

law file_deny_wins:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for q: F.AaFileQuery
  for h1: {V.AaEval.deny_applies(opts, PR.AaFlags.mode(PR.AaProfile.flags(p))) == True{} : Bool}
  for h2: {P.AaPerms.meets(F.AaFileQuery.req(q), V.AaEval.denied(F.AaFileRule.grants(PR.AaRules.files(PR.AaProfile.rules(p)), q))) == True{} : Bool}
  {V.AaDecision.allowed(V.AaEval.file(opts, p, q)) == False{} : Bool}

law file_unmatched_denied:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for q: F.AaFileQuery
  for h1: {PR.AaMode.enforcing(PR.AaFlags.mode(PR.AaProfile.flags(p))) == True{} : Bool}
  for h2: {F.AaFileRule.matching(PR.AaRules.files(PR.AaProfile.rules(p)), q) == Nil{} : List<&2, F.AaFileRule>}
  for h3: {P.AaPerms.any(F.AaFileQuery.req(q)) == True{} : Bool}
  {V.AaDecision.allowed(V.AaEval.file(opts, p, q)) == False{} : Bool}

# Include is idempotent, for every kind of rule

law include_idempotent_file:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: F.AaFileQuery
  {V.AaEval.file(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.file(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_capability:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RC.AaCapQuery
  {V.AaEval.capability(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.capability(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_network:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RN.AaNetQuery
  {V.AaEval.network(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.network(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_signal:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RS.AaSignalQuery
  {V.AaEval.signal(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.signal(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_ptrace:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RP.AaPtraceQuery
  {V.AaEval.ptrace(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.ptrace(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_mount:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RM.AaMountQuery
  {V.AaEval.mount(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.mount(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_dbus:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RD.AaDbusQuery
  {V.AaEval.dbus(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.dbus(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

law include_idempotent_change_profile:
  for opts: O.AaOptions
  for p: PR.AaProfile
  for r: PR.AaRules
  for q: RX.AaChangeQuery
  {V.AaEval.change_profile(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.change_profile(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}

# Exec

law exec_needs_x:
  for opts: O.AaOptions
  for pol: PR.AaPolicy
  for name: List<&2, U32>
  for owner: Bool
  for path: List<&2, U32>
  for p: PR.AaProfile
  for h1: {PR.AaPolicy.lookup(pol, name) == Some{p} : Maybe<&2, PR.AaProfile>}
  for h2: {TR.AaTrans.is_unconfined(PR.AaFlags.mode(PR.AaProfile.flags(p))) == False{} : Bool}
  for h3: {V.AaDecision.allowed(V.AaEval.file(opts, p, F.AaFileQuery{path, owner, P.AaPerms.bit(6n)})) == False{} : Bool}
  {TR.AaExecResult.ok(TR.AaTrans.exec(opts, pol, name, owner, path)) == False{} : Bool}

# Witnesses: the hypotheses of the laws above hold for some input (the
# example profile ex of example.bend: /etc/x rw, deny /etc/x w, audit
# /var/log/x w, /lib/** r, no exec rule)

law deny_wins_sat:
  {Bool.and(V.AaEval.deny_applies(O.AaOptions.default(), PR.AaFlags.mode(PR.AaProfile.flags(EX.AaExample.profile(PR.AaModeEnforce{})))), P.AaPerms.meets(F.AaFileQuery.req(EX.AaExample.query("/etc/x", "w")), V.AaEval.denied(F.AaFileRule.grants(PR.AaRules.files(PR.AaProfile.rules(EX.AaExample.profile(PR.AaModeEnforce{}))), EX.AaExample.query("/etc/x", "w"))))) == True{} : Bool}

law deny_wins_example:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeEnforce{}), EX.AaExample.query("/etc/x", "w")) == V.AaDeny{False{}} : V.AaDecision}

law allow_example:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeEnforce{}), EX.AaExample.query("/etc/x", "r")) == V.AaAllow{} : V.AaDecision}

law audit_example:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeEnforce{}), EX.AaExample.query("/var/log/x", "w")) == V.AaAudit{} : V.AaDecision}

law unmatched_sat:
  {Bool.and(PR.AaMode.enforcing(PR.AaFlags.mode(PR.AaProfile.flags(EX.AaExample.profile(PR.AaModeEnforce{})))), P.AaPerms.any(F.AaFileQuery.req(EX.AaExample.query("/etc/y", "r")))) == True{} : Bool}

law file_unmatched_sat:
  {F.AaFileRule.matching(PR.AaRules.files(PR.AaProfile.rules(EX.AaExample.profile(PR.AaModeEnforce{}))), EX.AaExample.query("/etc/y", "r")) == Nil{} : List<&2, F.AaFileRule>}

law unmatched_example:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeEnforce{}), EX.AaExample.query("/etc/y", "r")) == V.AaDeny{True{}} : V.AaDecision}

law complain_sat:
  {Bool.and(PR.AaMode.is_complain(PR.AaFlags.mode(PR.AaProfile.flags(EX.AaExample.profile(PR.AaModeComplain{})))), Bool.not(O.AaOptions.complain_deny(O.AaOptions.with_complain_deny(O.AaOptions.default(), False{})))) == True{} : Bool}

law complain_example_unmatched:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeComplain{}), EX.AaExample.query("/etc/y", "r")) == V.AaComplain{} : V.AaDecision}

law complain_example_deny_rule:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeComplain{}), EX.AaExample.query("/etc/x", "w")) == V.AaDeny{False{}} : V.AaDecision}

law complain_example_no_deny:
  {V.AaEval.file(O.AaOptions.with_complain_deny(O.AaOptions.default(), False{}), EX.AaExample.profile(PR.AaModeComplain{}), EX.AaExample.query("/etc/x", "w")) == V.AaComplain{} : V.AaDecision}

law kill_example:
  {V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeKill{}), EX.AaExample.query("/etc/y", "r")) == V.AaKill{} : V.AaDecision}

law exec_needs_x_sat:
  {PR.AaPolicy.lookup(EX.AaExample.policy(), X.AaText.of_string("ex")) == Some{EX.AaExample.profile(PR.AaModeEnforce{})} : Maybe<&2, PR.AaProfile>}

law exec_needs_x_sat2:
  {Bool.and(Bool.not(TR.AaTrans.is_unconfined(PR.AaFlags.mode(PR.AaProfile.flags(EX.AaExample.profile(PR.AaModeEnforce{}))))), Bool.not(V.AaDecision.allowed(V.AaEval.file(O.AaOptions.default(), EX.AaExample.profile(PR.AaModeEnforce{}), F.AaFileQuery{X.AaText.of_string("/bin/sh"), False{}, P.AaPerms.bit(6n)})))) == True{} : Bool}

# Vectors: globs, as apparmor_parser 4.0.1 compiles them

law glob_star_not_empty_segment:
  {G.AaGlob.match_text(X.AaText.of_string("/tmp/*"), X.AaText.of_string("/tmp/")) == False{} : Bool}

law glob_star_file:
  {G.AaGlob.match_text(X.AaText.of_string("/tmp/*"), X.AaText.of_string("/tmp/x")) == True{} : Bool}

law glob_star_no_slash:
  {G.AaGlob.match_text(X.AaText.of_string("/tmp/*"), X.AaText.of_string("/tmp/x/y")) == False{} : Bool}

law glob_star2_not_dir_itself:
  {G.AaGlob.match_text(X.AaText.of_string("/tmp/**"), X.AaText.of_string("/tmp/")) == False{} : Bool}

law glob_star2_deep:
  {G.AaGlob.match_text(X.AaText.of_string("/tmp/**"), X.AaText.of_string("/tmp/a/b/")) == True{} : Bool}

law glob_star_inside_segment:
  {G.AaGlob.match_text(X.AaText.of_string("/a/*b"), X.AaText.of_string("/a/b")) == True{} : Bool}

law glob_star_in_braces:
  {G.AaGlob.match_text(X.AaText.of_string("/a/{b,*}"), X.AaText.of_string("/a/")) == True{} : Bool}

law glob_negated_class_slash:
  {G.AaGlob.match_text(X.AaText.of_string("/a/[^b]c"), X.AaText.of_string("/a//c")) == True{} : Bool}

law glob_slashes_collapse:
  {G.AaGlob.match_text(X.AaText.of_string("/a//b"), X.AaText.of_string("/a/b")) == True{} : Bool}

law glob_class_range:
  {Bool.and(G.AaGlob.match_text(X.AaText.of_string("/a/[a-c]x"), X.AaText.of_string("/a/bx")), Bool.not(G.AaGlob.match_text(X.AaText.of_string("/a/[a-c]x"), X.AaText.of_string("/a/dx")))) == True{} : Bool}

law glob_nested_braces:
  {G.AaGlob.match_text(X.AaText.of_string("/a/{b,c{d,e}}"), X.AaText.of_string("/a/ce")) == True{} : Bool}

law glob_question:
  {Bool.and(G.AaGlob.match_text(X.AaText.of_string("/a/?b"), X.AaText.of_string("/a/xb")), Bool.not(G.AaGlob.match_text(X.AaText.of_string("/a/?b"), X.AaText.of_string("/a//b")))) == True{} : Bool}

law glob_one_alternative_rejected:
  {G.AaGlob.parse(X.AaText.of_string("/a/{b}")) == None{} : Maybe<&2, G.AaGlob>}

law glob_trailing_dash_rejected:
  {G.AaGlob.parse(X.AaText.of_string("/a/[a-]")) == None{} : Maybe<&2, G.AaGlob>}

law glob_empty_class_rejected:
  {G.AaGlob.parse(X.AaText.of_string("/a/[]]")) == None{} : Maybe<&2, G.AaGlob>}

# Vectors: a small policy text (AaExample.small_files: a tunable, an
# abstraction included twice, a deny rule, a variable, a px exec into a
# complain-mode profile), loaded and asked. (The larger example policy is
# in check.bend: the --verdict kernel runs out of fuel parsing it.)

law policy_file_vectors:
  {[EX.AaExample.small_file("/usr/bin/foo", "/lib/x/y.so", "mr"), EX.AaExample.small_file("/usr/bin/foo", "/etc/shadow", "r"), EX.AaExample.small_file("/usr/bin/foo", "/home/al/f", "rw"), EX.AaExample.small_file("/usr/bin/foo", "/root/f", "a"), EX.AaExample.small_file("/usr/bin/foo", "/etc/x", "r"), EX.AaExample.small_file("bar", "/etc/x", "r")] == [Some{V.AaAllow{}}, Some{V.AaDeny{False{}}}, Some{V.AaAllow{}}, Some{V.AaAllow{}}, Some{V.AaDeny{True{}}}, Some{V.AaComplain{}}] : List<&2, Maybe<&2, V.AaDecision>>}

law policy_exec_vectors:
  {[EX.AaExample.small_exec("/usr/bin/foo", "/bin/x"), EX.AaExample.small_exec("/usr/bin/foo", "/bin/y")] == ["profile bar", "denied (deny)"] : List<&2, String>}
