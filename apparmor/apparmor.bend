# bend-osdev-apparmor: AppArmor policy, as a pure model: loading profiles
# from text (apparmor.d(5)) and answering what they allow.
#
# Aa.load reads a policy from a file map (each file a name and its text, as
# Octets) and the name of the file to start from. The queries name a
# profile by its full name (a, a//child, a//^hat is a//hat) and answer an
# AaDecision (eval.bend), or None when the policy has no such profile;
# Aa.exec answers where an exec goes (transitions.bend).
#
# The files below this one work on byte lists (List<&2, U32>, what
# Octets.to_list gives), which is what their laws are stated over.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./perm.bend as P
import ./options.bend as O
import ./profile.bend as PR
import ./parse.bend as S
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

# a file of the policy: its name as includes name it (abstractions/base
# for <abstractions/base>), and its text
type AaSource is Data:
  AaSource{name: B.Octets, text: B.Octets}

def Aa.files(xs: List<&2, AaSource>) -> List<&2, S.AaSrcFile>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match x:
        case AaSource{n, s}:
          Con{S.AaSrcFile{B.Octets.to_list(n), B.Octets.to_list(s)}, Aa.files(t)}

# the policy the file main defines, with its includes taken from sources
def Aa.load(opts: O.AaOptions, sources: List<&2, AaSource>, main: B.Octets) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  S.AaParse.load(opts, Aa.files(sources), B.Octets.to_list(main))

def Aa.load_default(sources: List<&2, AaSource>, main: B.Octets) -> Result<&2, &2, E.AaError, PR.AaPolicy>:
  Aa.load(O.AaOptions.default(), sources, main)

def Aa.profile(pol: PR.AaPolicy, name: B.Octets) -> Maybe<&2, PR.AaProfile>:
  PR.AaPolicy.lookup(pol, B.Octets.to_list(name))

def Aa.on.file(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: F.AaFileQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.file(opts, p, q)}

# may the profile access path with the permissions req (owner: the task owns the file)?
def Aa.file(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, path: B.Octets, owner: Bool, req: P.AaPerms) -> Maybe<&2, V.AaDecision>:
  Aa.on.file(Aa.profile(pol, profile), opts, F.AaFileQuery{B.Octets.to_list(path), owner, req})

def Aa.on.capability(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RC.AaCapQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.capability(opts, p, q)}

# may the profile use capability number cap?
def Aa.capability(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, cap: U32) -> Maybe<&2, V.AaDecision>:
  Aa.on.capability(Aa.profile(pol, profile), opts, RC.AaCapQuery{cap})

def Aa.on.network(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RN.AaNetQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.network(opts, p, q)}

# may the profile use a socket of this domain, type and protocol (names: inet, stream, tcp)?
def Aa.network(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, domain: B.Octets, stype: B.Octets, proto: B.Octets) -> Maybe<&2, V.AaDecision>:
  Aa.on.network(Aa.profile(pol, profile), opts, RN.AaNetQuery{B.Octets.to_list(domain), B.Octets.to_list(stype), B.Octets.to_list(proto)})

def Aa.on.signal(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RS.AaSignalQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.signal(opts, p, q)}

# may the profile send (receive) the signal named sig to (from) the peer profile?
def Aa.signal(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, req: P.AaPerms, sig: B.Octets, peer: B.Octets) -> Maybe<&2, V.AaDecision>:
  Aa.on.signal(Aa.profile(pol, profile), opts, RS.AaSignalQuery{req, B.Octets.to_list(sig), B.Octets.to_list(peer)})

def Aa.on.ptrace(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RP.AaPtraceQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.ptrace(opts, p, q)}

def Aa.ptrace(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, req: P.AaPerms, peer: B.Octets) -> Maybe<&2, V.AaDecision>:
  Aa.on.ptrace(Aa.profile(pol, profile), opts, RP.AaPtraceQuery{req, B.Octets.to_list(peer)})

def Aa.on.mount(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RM.AaMountQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.mount(opts, p, q)}

def Aa.mount(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, q: RM.AaMountQuery) -> Maybe<&2, V.AaDecision>:
  Aa.on.mount(Aa.profile(pol, profile), opts, q)

def Aa.on.dbus(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RD.AaDbusQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.dbus(opts, p, q)}

def Aa.dbus(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, q: RD.AaDbusQuery) -> Maybe<&2, V.AaDecision>:
  Aa.on.dbus(Aa.profile(pol, profile), opts, q)

def Aa.on.change(m: Maybe<&2, PR.AaProfile>, opts: O.AaOptions, q: RX.AaChangeQuery) -> Maybe<&2, V.AaDecision>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{V.AaEval.change_profile(opts, p, q)}

def Aa.opt_list(m: Maybe<&2, B.Octets>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{o}:
      Some{B.Octets.to_list(o)}

# may the profile change_profile to target (now: exec None; at the exec of a program: Some)?
def Aa.change_profile(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, exec: Maybe<&2, B.Octets>, target: B.Octets) -> Maybe<&2, V.AaDecision>:
  Aa.on.change(Aa.profile(pol, profile), opts, RX.AaChangeQuery{Aa.opt_list(exec), B.Octets.to_list(target)})

# where an exec of path by a task confined by profile goes
def Aa.exec(opts: O.AaOptions, pol: PR.AaPolicy, profile: B.Octets, path: B.Octets, owner: Bool) -> TR.AaExecResult:
  TR.AaTrans.exec(opts, pol, B.Octets.to_list(profile), owner, B.Octets.to_list(path))

# where an exec of path by an unconfined task goes
def Aa.exec_unconfined(pol: PR.AaPolicy, path: B.Octets) -> TR.AaExecResult:
  TR.AaTrans.exec_unconfined(pol, B.Octets.to_list(path))
