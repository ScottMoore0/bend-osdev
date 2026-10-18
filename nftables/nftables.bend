# bend-osdev-nftables: nftables rule evaluation as a pure model. The entry:
# one packet through one hook of a rule set.
#
# The other files: family.bend (families, hooks, priorities, NftError),
# verdict.bend (verdicts and policies), sets.bend (keys, sets, maps),
# expr.bend (packets, expressions, rules, counters and limits), chains.bend
# (chains, tables, rule sets, building them), eval.bend (chains and base
# chains, NftOptions).
import Base
import ../word64/word64.bend as W
import ./family.bend as F
import ./verdict.bend as V
import ./expr.bend as X
import ./chains.bend as C
import ./eval.bend as E

# What a hook did with a packet: the verdict, the packet after it (its marks
# changed by statements), the state (counters, limits), and the deepest
# level of chains that jumps and gotos entered
type NftResult is Data:
  NftResult{verdict: V.NftFinal, pkt: X.NftPacket, st: X.NftState, depth: Nat}

def NftResult.verdict_of(m: Maybe<&2, V.NftFinal>) -> V.NftFinal:
  match m:
    case Some{f}:
      f
    case None{}:
      V.NftFinalAccept{}

def NftResult.of(o: E.NftOut) -> NftResult:
  match o:
    case E.NftOut{f, env, d}:
      match env:
        case X.NftEnv{p, s, n}:
          NftResult{NftResult.verdict_of(f), p, s, d}

def NftResult.verdict(r: NftResult) -> V.NftFinal:
  match r:
    case NftResult{v, p, s, d}:
      v

def NftResult.pkt(r: NftResult) -> X.NftPacket:
  match r:
    case NftResult{v, p, s, d}:
      p

def NftResult.st(r: NftResult) -> X.NftState:
  match r:
    case NftResult{v, p, s, d}:
      s

def NftResult.depth(r: NftResult) -> Nat:
  match r:
    case NftResult{v, p, s, d}:
      d

# the packet pkt, of protocol family proto, through hook of the rule set rs,
# at time now (milliseconds), with state st
def Nft.eval(+opts: E.NftOptions, rs: C.NftRuleset, +proto: F.NftProto, +hook: F.NftHook, now: W.W64, pkt: X.NftPacket, st: X.NftState) -> NftResult:
  NftResult.of(E.Nft.run_hook(opts, C.NftRuleset.base_chains(rs, proto, hook), X.NftEnv{pkt, st, now}))

# the same with the default options
def Nft.eval_default(rs: C.NftRuleset, +proto: F.NftProto, +hook: F.NftHook, now: W.W64, pkt: X.NftPacket, st: X.NftState) -> NftResult:
  Nft.eval(E.NftOptions.default(), rs, proto, hook, now, pkt, st)

# Text

def NftCounters.show(cs: List<&2, X.NftCounterVal>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      match c:
        case X.NftCounterVal{id, pk, by}:
          " c" ++ U32.show(id) ++ "=" ++ W.W64.show(pk) ++ "/" ++ W.W64.show(by) ++ NftCounters.show(t)

# the verdict, the meta and ct marks, the depth, and the counters
def NftResult.show(r: NftResult) -> String:
  match r:
    case NftResult{v, +p, s, d}:
      match s:
        case X.NftState{cs, bs}:
          V.NftFinal.show(v) ++ " mark=" ++ U32.show(X.NftPacket.mark(p)) ++ " ctmark=" ++ U32.show(X.NftPacket.ct_mark(p)) ++ " depth=" ++ Nat.show(d) ++ NftCounters.show(cs)
