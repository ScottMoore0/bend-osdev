# bend-osdev-apparmor: examples, for the laws' witnesses, check.bend and
# users: a profile built directly from the types, and a small policy in
# the profile language (the example of apparmor.d(5), cut down, with an
# abstraction and a tunable in a file map).
import Base
import ../bytes/bytes.bend as B
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./options.bend as O
import ./profile.bend as PR
import ./rule_file.bend as F
import ./error.bend as E
import ./eval.bend as V
import ./transitions.bend as TR
import ./apparmor.bend as A

def AaExample.qual(audit: Bool, deny: Bool) -> P.AaQual:
  P.AaQual{audit, deny, False{}}

# a file rule on a literal path
def AaExample.rule(+path: String, q: P.AaQual, perms: String) -> F.AaFileRule:
  F.AaFileRule{q, X.AaText.of_string(path), G.AaGlob.literal(X.AaText.of_string(path)), F.AaFile.perms(perms), None{}, None{}}

# profile ex: /etc/x rw, deny /etc/x w, audit /var/log/x w, /lib/** (built
# as a literal-free pattern) r; no x rule anywhere
def AaExample.rules() -> PR.AaRules:
  PR.AaRules.with_files(PR.AaRules.empty(), [AaExample.rule("/etc/x", AaExample.qual(False{}, False{}), "rw"), AaExample.rule("/etc/x", AaExample.qual(False{}, True{}), "w"), AaExample.rule("/var/log/x", AaExample.qual(True{}, False{}), "w"), F.AaFileRule{AaExample.qual(False{}, False{}), X.AaText.of_string("/lib/**"), G.AaGlob{[[G.AaGChar{47}, G.AaGChar{108}, G.AaGChar{105}, G.AaGChar{98}, G.AaGChar{47}, G.AaGAny{}, G.AaGStar2{}]], False{}}, F.AaFile.perms("r"), None{}, None{}}])

def AaExample.profile(m: PR.AaMode) -> PR.AaProfile:
  PR.AaProfile.include(PR.AaProfile.new(X.AaText.of_string("ex"), None{}, PR.AaFlags{m, False{}}), AaExample.rules())

def AaExample.policy() -> PR.AaPolicy:
  PR.AaPolicy{[AaExample.profile(PR.AaModeEnforce{})]}

def AaExample.query(+path: String, perms: String) -> F.AaFileQuery:
  F.AaFileQuery{X.AaText.of_string(path), False{}, F.AaFile.perms(perms)}

# The policy text

def AaExample.source(n: String, t: String) -> A.AaSource:
  A.AaSource{B.Octets.of_string(n), B.Octets.of_string(t)}

def AaExample.files() -> List<&2, A.AaSource>:
  [AaExample.source("tunables/home", "@{HOMEDIRS} = /home/\n@{HOME} = @{HOMEDIRS}/*/ /root/\n"), AaExample.source("abstractions/base", "/etc/ld.so.cache r,\n/{usr/,}lib{,32,64}/** mr,\n"), AaExample.source("main", "include <tunables/home>\n# a cut-down version of the example in apparmor.d(5)\n/usr/bin/foo {\n  include <abstractions/base>\n  include <abstractions/base>\n  /bin/mount ux,\n  /dev/{,u}random r,\n  /etc/foo/* r,\n  /tmp/foo.* lrw,\n  @{HOME}/.foo_file rw,\n  deny /etc/shadow rw,\n  audit /var/log/foo w,\n  owner /proc/[0-9]*/stat r,\n  /usr/bin/baz Cx -> baz,\n  /usr/bin/bar px,\n  /usr/bin/** pix,\n  capability setuid,\n  network inet stream,\n  signal (send) set=(term, kill) peer=/usr/bin/bar,\n  ^hat {\n    /var/spool/* rwl,\n  }\n  profile baz {\n    /bin/bash ixr,\n  }\n}\nprofile bar /usr/bin/bar flags=(complain) {\n  /etc/bar r,\n  deny /etc/secret r,\n}\n")]

def AaExample.loaded() -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  A.Aa.load(O.AaOptions.default(), AaExample.files(), B.Octets.of_string("main"))

def AaExample.pol() -> PR.AaPolicy:
  Result.default(&2, &2, E.AaError, PR.AaPolicy, AaExample.loaded(), PR.AaPolicy{Nil{}})

def AaExample.file(prof: String, path: String, perms: String) -> Maybe<&2, V.AaDecision>:
  A.Aa.file(O.AaOptions.default(), AaExample.pol(), B.Octets.of_string(prof), B.Octets.of_string(path), False{}, F.AaFile.perms(perms))

def AaExample.exec(prof: String, path: String) -> String:
  TR.AaExecResult.show(A.Aa.exec(O.AaOptions.default(), AaExample.pol(), B.Octets.of_string(prof), B.Octets.of_string(path), False{}))

# A smaller policy, for the laws' vectors (the checker's kernel evaluates
# them, so they are kept short)
def AaExample.small_files() -> List<&2, A.AaSource>:
  [AaExample.source("t", "@{H} = /home/*/ /root/\n"), AaExample.source("a", "/lib/** mr,\n"), AaExample.source("m", "include <t>\n/usr/bin/foo {\n  include <a>\n  include <a>\n  deny /etc/shadow r,\n  @{H}/f rw,\n  /bin/x px,\n}\nprofile bar /bin/x flags=(complain) {\n}\n")]

def AaExample.small() -> PR.AaPolicy:
  Result.default(&2, &2, E.AaError, PR.AaPolicy, A.Aa.load(O.AaOptions.default(), AaExample.small_files(), B.Octets.of_string("m")), PR.AaPolicy{Nil{}})

def AaExample.small_file(prof: String, path: String, perms: String) -> Maybe<&2, V.AaDecision>:
  A.Aa.file(O.AaOptions.default(), AaExample.small(), B.Octets.of_string(prof), B.Octets.of_string(path), False{}, F.AaFile.perms(perms))

def AaExample.small_exec(prof: String, path: String) -> String:
  TR.AaExecResult.show(A.Aa.exec(O.AaOptions.default(), AaExample.small(), B.Octets.of_string(prof), B.Octets.of_string(path), False{}))
