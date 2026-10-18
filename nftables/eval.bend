# bend-osdev-nftables: evaluating chains and base chains (nft(8), "VERDICT
# STATEMENT", "CHAINS").
#
# A chain runs its rules in order. A rule's verdict decides what happens:
#   * accept, drop, reject, queue: the base chain's evaluation ends, through
#     every chain on the call stack;
#   * continue (or no verdict): the next rule;
#   * return, or the chain's last rule done: back to the rule after the jump
#     that entered this chain (in a base chain: the policy applies);
#   * jump c: chain c runs, then the next rule here, unless c ends the
#     evaluation;
#   * goto c: chain c runs instead of the rest of this chain, so its return
#     goes back to where this chain was entered.
# Each jump or goto enters a chain one level deeper; a chain beyond the
# options' max_depth is not entered, and the evaluation ends with
# depth_final. A jump or goto to a chain the table does not have ends it
# with missing_final.
#
# At a hook the base chains run in order: drop, reject and queue end the
# hook; accept, or a policy of accept, passes the packet on to the next base
# chain; a packet that passes them all is accepted.
import Base
import ./verdict.bend as V
import ./sets.bend as S
import ./expr.bend as X
import ./chains.bend as C

# The evaluator's choices
type NftOptions is Data:
  # how deep jumps and gotos may nest
  NftOptions{max_depth: Nat, depth_final: V.NftFinal, missing_final: V.NftFinal}

# 16 levels (see README, Choices); a ruleset that goes deeper, or names a
# missing chain, drops the packet
def NftOptions.default() -> NftOptions:
  NftOptions{16n, V.NftFinalDrop{}, V.NftFinalDrop{}}

def NftOptions.max_depth(o: NftOptions) -> Nat:
  match o:
    case NftOptions{d, df, mf}:
      d

def NftOptions.depth_final(o: NftOptions) -> V.NftFinal:
  match o:
    case NftOptions{d, df, mf}:
      df

def NftOptions.missing_final(o: NftOptions) -> V.NftFinal:
  match o:
    case NftOptions{d, df, mf}:
      mf

# How a chain ended: back to its caller, or the evaluation stopped
type NftChainRes is Data:
  NftChainReturn{}
  NftChainStop{final: V.NftFinal}

# Where a chain's evaluation stands
type NftPend is Data:
  # run the next rule
  NftPendNext{}
  # the last rule jumped, or went, to a chain
  NftPendJump{chain: String}
  NftPendGoto{chain: String}
  # the chain has ended
  NftPendDone{res: NftChainRes}

# A chain's evaluation: where it stands, the packet and state, and the
# deepest level of chains it entered
type NftRun is Data:
  NftRun{pend: NftPend, env: X.NftEnv, depth: Nat}

def NftPend.result(p: NftPend) -> NftChainRes:
  match p:
    case NftPendDone{r}:
      r
    case _:
      NftChainReturn{}

# how the chain ended (a chain whose rules ran out returned)
def NftRun.result(r: NftRun) -> NftChainRes:
  match r:
    case NftRun{p, e, d}:
      NftPend.result(p)

def NftRun.env(r: NftRun) -> X.NftEnv:
  match r:
    case NftRun{p, e, d}:
      e

# the deepest level entered by jumps and gotos (0: none)
def NftRun.depth(r: NftRun) -> Nat:
  match r:
    case NftRun{p, e, d}:
      d

# what the chain does after a verdict
def NftPend.of_verdict(v: V.NftVerdict) -> NftPend:
  match v:
    case V.NftAccept{}:
      NftPendDone{NftChainStop{V.NftFinalAccept{}}}
    case V.NftDrop{}:
      NftPendDone{NftChainStop{V.NftFinalDrop{}}}
    case V.NftReject{h}:
      NftPendDone{NftChainStop{V.NftFinalReject{h}}}
    case V.NftContinue{}:
      NftPendNext{}
    case V.NftReturn{}:
      NftPendDone{NftChainReturn{}}
    case V.NftJump{c}:
      NftPendJump{c}
    case V.NftGoto{c}:
      NftPendGoto{c}
    case V.NftQueue{n, b}:
      NftPendDone{NftChainStop{V.NftFinalQueue{n, b}}}

def NftRun.of_rule(o: X.NftRuleOut, d: Nat) -> NftRun:
  match o:
    case X.NftRuleNext{env}:
      NftRun{NftPendNext{}, env, d}
    case X.NftRuleVerdict{v, env}:
      NftRun{NftPend.of_verdict(v), env, d}

# the rule r, if the chain goes on
def NftRun.step(r: X.NftRule, +sets: List<&2, S.NftNamedSet>, a: NftRun) -> NftRun:
  match a:
    case NftRun{p, env, d}:
      match p:
        case NftPendNext{}:
          NftRun.of_rule(X.NftRule.eval(r, sets, env), d)
        case NftPendJump{c}:
          NftRun{NftPendJump{c}, env, d}
        case NftPendGoto{c}:
          NftRun{NftPendGoto{c}, env, d}
        case NftPendDone{x}:
          NftRun{NftPendDone{x}, env, d}

# a chain whose rules ran out returns
def NftRun.fin(a: NftRun) -> NftRun:
  match a:
    case NftRun{p, env, d}:
      match p:
        case NftPendDone{x}:
          NftRun{NftPendDone{x}, env, d}
        case _:
          NftRun{NftPendDone{NftChainReturn{}}, env, d}

# at the depth limit: a jump or goto ends the evaluation with depth_final
def NftRun.cut(a: NftRun, +opts: NftOptions) -> NftRun:
  match a:
    case NftRun{p, env, d}:
      match p:
        case NftPendJump{c}:
          NftRun{NftPendDone{NftChainStop{NftOptions.depth_final(opts)}}, env, d}
        case NftPendGoto{c}:
          NftRun{NftPendDone{NftChainStop{NftOptions.depth_final(opts)}}, env, d}
        case NftPendNext{}:
          NftRun{NftPendNext{}, env, d}
        case NftPendDone{x}:
          NftRun{NftPendDone{x}, env, d}

def NftRun.join.go(r: NftChainRes, env: X.NftEnv, d: Nat) -> NftRun:
  match r:
    case NftChainReturn{}:
      NftRun{NftPendNext{}, env, d}
    case NftChainStop{f}:
      NftRun{NftPendDone{NftChainStop{f}}, env, d}

# after a jump: callee is the jumped-to chain's evaluation (found: whether
# the chain exists), d the caller's depth so far
def NftRun.join(found: Bool, +callee: NftRun, +d: Nat, +opts: NftOptions, env: X.NftEnv) -> NftRun:
  match found:
    case False{}:
      NftRun{NftPendDone{NftChainStop{NftOptions.missing_final(opts)}}, env, d}
    case True{}:
      NftRun.join.go(NftRun.result(callee), NftRun.env(callee), Nat.max(d, 1n+NftRun.depth(callee)))

# after a goto: the gone-to chain's end is this chain's end
def NftRun.goto(found: Bool, +callee: NftRun, +d: Nat, +opts: NftOptions, env: X.NftEnv) -> NftRun:
  match found:
    case False{}:
      NftRun{NftPendDone{NftChainStop{NftOptions.missing_final(opts)}}, env, d}
    case True{}:
      NftRun{NftPendDone{NftRun.result(callee)}, NftRun.env(callee), Nat.max(d, 1n+NftRun.depth(callee))}

# the rules of a chain of table tbl, from a, with fuel levels of jumps and
# gotos left
def NftRun.run(+fuel: Nat, rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: NftOptions, a: NftRun) -> NftRun:
  match fuel:
    case 0n:
      match rules:
        case Nil{}:
          NftRun.fin(NftRun.cut(a, opts))
        case Con{r, rest}:
          NftRun.run(fuel, rest, tbl, opts, NftRun.step(r, C.NftTable.sets(tbl), NftRun.cut(a, opts)))
    case 1n+q:
      match rules:
        case Nil{}:
          match a:
            case NftRun{p, +env, +d}:
              match p:
                case NftPendNext{}:
                  NftRun{NftPendDone{NftChainReturn{}}, env, d}
                case NftPendDone{x}:
                  NftRun{NftPendDone{x}, env, d}
                case NftPendJump{+c}:
                  NftRun.fin(NftRun.join(C.NftTable.has_chain(tbl, c), NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, NftRun{NftPendNext{}, env, 0n}), d, opts, env))
                case NftPendGoto{+c}:
                  NftRun.goto(C.NftTable.has_chain(tbl, c), NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, NftRun{NftPendNext{}, env, 0n}), d, opts, env)
        case Con{r, rest}:
          match a:
            case NftRun{p, +env, +d}:
              match p:
                case NftPendNext{}:
                  NftRun.run(fuel, rest, tbl, opts, NftRun.of_rule(X.NftRule.eval(r, C.NftTable.sets(tbl), env), d))
                case NftPendDone{x}:
                  NftRun{NftPendDone{x}, env, d}
                case NftPendJump{+c}:
                  NftRun.run(fuel, rest, tbl, opts, NftRun.step(r, C.NftTable.sets(tbl), NftRun.join(C.NftTable.has_chain(tbl, c), NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, NftRun{NftPendNext{}, env, 0n}), d, opts, env)))
                case NftPendGoto{+c}:
                  NftRun.goto(C.NftTable.has_chain(tbl, c), NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, NftRun{NftPendNext{}, env, 0n}), d, opts, env)

# the chain whose rules are rules, in table tbl, entered with fuel levels of
# jumps and gotos left
def Nft.run_chain(+opts: NftOptions, +fuel: Nat, +tbl: C.NftTable, rules: List<&2, X.NftRule>, env: X.NftEnv) -> NftRun:
  NftRun.run(fuel, rules, tbl, opts, NftRun{NftPendNext{}, env, 0n})

# What a base chain, or a hook, does with a packet: a final verdict (None:
# the packet goes on to the next base chain), the packet and state after
# it, and the deepest level of chains entered
type NftOut is Data:
  NftOut{final: Maybe<&2, V.NftFinal>, env: X.NftEnv, depth: Nat}

def NftOut.final(o: NftOut) -> Maybe<&2, V.NftFinal>:
  match o:
    case NftOut{f, e, d}:
      f

def NftOut.env(o: NftOut) -> X.NftEnv:
  match o:
    case NftOut{f, e, d}:
      e

def NftOut.depth(o: NftOut) -> Nat:
  match o:
    case NftOut{f, e, d}:
      d

def NftBase.stop(f: V.NftFinal, env: X.NftEnv, d: Nat) -> NftOut:
  match f:
    case V.NftFinalAccept{}:
      NftOut{None{}, env, d}
    case V.NftFinalDrop{}:
      NftOut{Some{V.NftFinalDrop{}}, env, d}
    case V.NftFinalReject{h}:
      NftOut{Some{V.NftFinalReject{h}}, env, d}
    case V.NftFinalQueue{n, b}:
      NftOut{Some{V.NftFinalQueue{n, b}}, env, d}

def NftBase.policy(pol: V.NftPolicy, env: X.NftEnv, d: Nat) -> NftOut:
  match pol:
    case V.NftPolicyAccept{}:
      NftOut{None{}, env, d}
    case V.NftPolicyDrop{}:
      NftOut{Some{V.NftFinalDrop{}}, env, d}

def NftBase.out(r: NftChainRes, pol: V.NftPolicy, env: X.NftEnv, d: Nat) -> NftOut:
  match r:
    case NftChainReturn{}:
      NftBase.policy(pol, env, d)
    case NftChainStop{f}:
      NftBase.stop(f, env, d)

def NftBase.of_run(+r: NftRun, pol: V.NftPolicy) -> NftOut:
  NftBase.out(NftRun.result(r), pol, NftRun.env(r), NftRun.depth(r))

# one base chain: its rules, then its policy if they return
def Nft.run_base(+opts: NftOptions, h: C.NftHooked, env: X.NftEnv) -> NftOut:
  match h:
    case C.NftHooked{+tbl, rules, prio, pol}:
      NftBase.of_run(Nft.run_chain(opts, NftOptions.max_depth(opts), tbl, rules, env), pol)

# a base chain's outcome after those before it, which reached depth d
def NftHookRun.combine(+o: NftOut, +d: Nat) -> NftOut:
  NftOut{NftOut.final(o), NftOut.env(o), Nat.max(d, NftOut.depth(o))}

def NftHookRun.go(hs: List<&2, C.NftHooked>, +opts: NftOptions, acc: NftOut) -> NftOut:
  match hs:
    case Nil{}:
      acc
    case Con{h, t}:
      match acc:
        case NftOut{f, env, +d}:
          match f:
            case None{}:
              NftHookRun.go(t, opts, NftHookRun.combine(Nft.run_base(opts, h, env), d))
            case Some{x}:
              NftOut{Some{x}, env, d}

# the base chains hs in order (None: every one passed the packet on)
def Nft.run_hook(+opts: NftOptions, hs: List<&2, C.NftHooked>, env: X.NftEnv) -> NftOut:
  NftHookRun.go(hs, opts, NftOut{None{}, env, 0n})
