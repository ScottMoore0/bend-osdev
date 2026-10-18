# bend-osdev-nftables: chains, tables and rule sets (nft(8), "TABLES",
# "CHAINS", "RULES", "SETS"), building them, and the base chains a packet
# meets at a hook.
#
# A table has a family, chains and named sets. A base chain is attached to
# a hook with a priority and a policy; a regular chain is reached only by a
# jump or a goto from a rule of the same table. At a hook, the base chains
# of every table whose family sees the packet run in priority order, lowest
# first; chains of equal priority run in the order they were added (nft(8)
# leaves that order unspecified; see the README, Choices).
import Base
import ./family.bend as F
import ./verdict.bend as V
import ./sets.bend as S
import ./expr.bend as X

# A base chain's hook, priority (a signed number held in a U32, see
# family.bend) and policy. Open type.
type NftBaseSpec is Data:
  NftBaseSpec{hook: F.NftHook, prio: U32, policy: V.NftPolicy}

# A chain: a base chain if base is Some. Open type.
type NftChain is Data:
  NftChain{name: String, base: Maybe<&2, NftBaseSpec>, rules: List<&2, X.NftRule>}

# Open type.
type NftTable is Data:
  NftTable{name: String, family: F.NftFamily, chains: List<&2, NftChain>, sets: List<&2, S.NftNamedSet>}

# Open type.
type NftRuleset is Data:
  NftRuleset{tables: List<&2, NftTable>}

def NftTable.family(t: NftTable) -> F.NftFamily:
  match t:
    case NftTable{n, f, cs, ss}:
      f

def NftTable.chains(t: NftTable) -> List<&2, NftChain>:
  match t:
    case NftTable{n, f, cs, ss}:
      cs

def NftTable.sets(t: NftTable) -> List<&2, S.NftNamedSet>:
  match t:
    case NftTable{n, f, cs, ss}:
      ss

def NftChain.name(c: NftChain) -> String:
  match c:
    case NftChain{n, b, rs}:
      n

def NftChain.rules(c: NftChain) -> List<&2, X.NftRule>:
  match c:
    case NftChain{n, b, rs}:
      rs

def NftChains.find.pick(hit: Bool, c: NftChain, rest: Maybe<&2, NftChain>) -> Maybe<&2, NftChain>:
  match hit:
    case True{}:
      Some{c}
    case False{}:
      rest

# the first chain named n
def NftChains.find(cs: List<&2, NftChain>, +n: String) -> Maybe<&2, NftChain>:
  match cs:
    case Nil{}:
      None{}
    case Con{+c, t}:
      NftChains.find.pick(String.eq(NftChain.name(c), n), c, NftChains.find(t, n))

def NftChains.rules_of(m: Maybe<&2, NftChain>) -> List<&2, X.NftRule>:
  match m:
    case Some{c}:
      NftChain.rules(c)
    case None{}:
      Nil{}

def NftChains.found(m: Maybe<&2, NftChain>) -> Bool:
  match m:
    case Some{c}:
      True{}
    case None{}:
      False{}

# the rules of the chain named n in table t (none if there is no such chain)
def NftTable.rules(t: NftTable, +n: String) -> List<&2, X.NftRule>:
  NftChains.rules_of(NftChains.find(NftTable.chains(t), n))

# whether table t has a chain named n
def NftTable.has_chain(t: NftTable, +n: String) -> Bool:
  NftChains.found(NftChains.find(NftTable.chains(t), n))

# The base chains at a hook

# a base chain as a hook runs it: its table (for jumps and named sets), its
# rules, priority and policy. Open type.
type NftHooked is Data:
  NftHooked{tbl: NftTable, rules: List<&2, X.NftRule>, prio: U32, policy: V.NftPolicy}

def NftHooked.prio(h: NftHooked) -> U32:
  match h:
    case NftHooked{t, rs, p, pol}:
      p

def NftHooked.ins.pick(before: Bool, x: NftHooked, h: NftHooked, t: List<&2, NftHooked>, r: List<&2, NftHooked>) -> List<&2, NftHooked>:
  match before:
    case True{}:
      Con{x, Con{h, t}}
    case False{}:
      Con{h, r}

# l, in priority order, with x after every entry of the same or a lower
# priority
def NftHooked.ins(l: List<&2, NftHooked>, +x: NftHooked) -> List<&2, NftHooked>:
  match l:
    case Nil{}:
      Con{x, Nil{}}
    case Con{+h, +t}:
      NftHooked.ins.pick(F.NftPrio.lt(NftHooked.prio(x), NftHooked.prio(h)), x, h, t, NftHooked.ins(t, x))

def NftChain.offer.go(at: Bool, t: NftTable, rules: List<&2, X.NftRule>, prio: U32, pol: V.NftPolicy, acc: List<&2, NftHooked>) -> List<&2, NftHooked>:
  match at:
    case True{}:
      NftHooked.ins(acc, NftHooked{t, rules, prio, pol})
    case False{}:
      acc

def NftChain.offer(c: NftChain, t: NftTable, +hook: F.NftHook, acc: List<&2, NftHooked>) -> List<&2, NftHooked>:
  match c:
    case NftChain{n, b, rules}:
      match b:
        case None{}:
          acc
        case Some{spec}:
          match spec:
            case NftBaseSpec{h, prio, pol}:
              NftChain.offer.go(F.NftHook.is_eq(h, hook), t, rules, prio, pol, acc)

def NftChains.collect(cs: List<&2, NftChain>, +t: NftTable, +hook: F.NftHook, acc: List<&2, NftHooked>) -> List<&2, NftHooked>:
  match cs:
    case Nil{}:
      acc
    case Con{c, rest}:
      NftChains.collect(rest, t, hook, NftChain.offer(c, t, hook, acc))

def NftTable.offer(sees: Bool, +t: NftTable, +hook: F.NftHook, acc: List<&2, NftHooked>) -> List<&2, NftHooked>:
  match sees:
    case True{}:
      NftChains.collect(NftTable.chains(t), t, hook, acc)
    case False{}:
      acc

def NftTables.collect(ts: List<&2, NftTable>, +proto: F.NftProto, +hook: F.NftHook, acc: List<&2, NftHooked>) -> List<&2, NftHooked>:
  match ts:
    case Nil{}:
      acc
    case Con{+t, rest}:
      NftTables.collect(rest, proto, hook, NftTable.offer(F.NftFamily.sees(NftTable.family(t), proto), t, hook, acc))

# the base chains a packet of protocol family proto meets at hook, in the
# order they run
def NftRuleset.base_chains(rs: NftRuleset, +proto: F.NftProto, +hook: F.NftHook) -> List<&2, NftHooked>:
  match rs:
    case NftRuleset{ts}:
      NftTables.collect(ts, proto, hook, Nil{})

# The rule set without its rules: every chain kept, empty

def NftChains.strip(cs: List<&2, NftChain>) -> List<&2, NftChain>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, rest}:
      match c:
        case NftChain{n, b, rs}:
          Con{NftChain{n, b, Nil{}}, NftChains.strip(rest)}

def NftTables.strip(ts: List<&2, NftTable>) -> List<&2, NftTable>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      match t:
        case NftTable{n, f, cs, ss}:
          Con{NftTable{n, f, NftChains.strip(cs), ss}, NftTables.strip(rest)}

def NftRuleset.without_rules(rs: NftRuleset) -> NftRuleset:
  match rs:
    case NftRuleset{ts}:
      NftRuleset{NftTables.strip(ts)}

# Building a rule set, as nft's add commands do

def NftRuleset.empty() -> NftRuleset:
  NftRuleset{Nil{}}

# a change to one table
type NftEdit is Data:
  NftEditChain{name: String, base: Maybe<&2, NftBaseSpec>}
  NftEditRule{chain: String, rule: X.NftRule}
  NftEditSet{name: String, set: S.NftSet}
  NftEditElem{set: String, elem: S.NftElem}

def NftSets.find_any(ss: List<&2, S.NftNamedSet>, +n: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{s, t}:
      match s:
        case S.NftNamedSet{name, x}:
          Bool.or(String.eq(name, n), NftSets.find_any(t, n))

def NftChains.cons(h: NftChain, r: Result<&2, &2, F.NftError, List<&2, NftChain>>) -> Result<&2, &2, F.NftError, List<&2, NftChain>>:
  match r:
    case Done{t}:
      Done{Con{h, t}}
    case Fail{e}:
      Fail{e}

def NftChains.add_rule.pick(hit: Bool, c: NftChain, t: List<&2, NftChain>, rule: X.NftRule, rec: Result<&2, &2, F.NftError, List<&2, NftChain>>) -> Result<&2, &2, F.NftError, List<&2, NftChain>>:
  match hit:
    case True{}:
      match c:
        case NftChain{n, b, rs}:
          Done{Con{NftChain{n, b, List.append(&2, X.NftRule, rs, [rule])}, t}}
    case False{}:
      NftChains.cons(c, rec)

# the chains with rule appended to the chain named n
def NftChains.add_rule(cs: List<&2, NftChain>, +n: String, +rule: X.NftRule) -> Result<&2, &2, F.NftError, List<&2, NftChain>>:
  match cs:
    case Nil{}:
      Fail{F.NftErrNoChain{}}
    case Con{+c, +t}:
      NftChains.add_rule.pick(String.eq(NftChain.name(c), n), c, t, rule, NftChains.add_rule(t, n, rule))

def NftSets.cons(h: S.NftNamedSet, r: Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>) -> Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>:
  match r:
    case Done{t}:
      Done{Con{h, t}}
    case Fail{e}:
      Fail{e}

def NftSets.put(n: String, r: Result<&2, &2, F.NftError, S.NftSet>, t: List<&2, S.NftNamedSet>) -> Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>:
  match r:
    case Done{s}:
      Done{Con{S.NftNamedSet{n, s}, t}}
    case Fail{e}:
      Fail{e}

def NftSets.add_elem.pick(hit: Bool, n: String, s: S.NftSet, t: List<&2, S.NftNamedSet>, e: S.NftElem, rec: Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>) -> Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>:
  match hit:
    case True{}:
      NftSets.put(n, S.NftSet.insert(s, e), t)
    case False{}:
      NftSets.cons(S.NftNamedSet{n, s}, rec)

# the sets with e inserted into the set named n
def NftSets.add_elem(ss: List<&2, S.NftNamedSet>, +n: String, +e: S.NftElem) -> Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>:
  match ss:
    case Nil{}:
      Fail{F.NftErrNoSet{}}
    case Con{x, +t}:
      match x:
        case S.NftNamedSet{+name, +s}:
          NftSets.add_elem.pick(String.eq(name, n), name, s, t, e, NftSets.add_elem(t, n, e))

def NftEdit.chain_go(exists: Bool, hook_ok: Bool, t: NftTable, c: NftChain) -> Result<&2, &2, F.NftError, NftTable>:
  match exists:
    case True{}:
      Fail{F.NftErrExists{}}
    case False{}:
      match hook_ok:
        case False{}:
          Fail{F.NftErrBadHook{}}
        case True{}:
          match t:
            case NftTable{n, f, cs, ss}:
              Done{NftTable{n, f, List.append(&2, NftChain, cs, [c]), ss}}

def NftEdit.hook_ok(f: F.NftFamily, b: Maybe<&2, NftBaseSpec>) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{spec}:
      match spec:
        case NftBaseSpec{h, p, pol}:
          F.NftFamily.has_hook(f, h)

def NftEdit.rules_go(r: Result<&2, &2, F.NftError, List<&2, NftChain>>, n: String, f: F.NftFamily, ss: List<&2, S.NftNamedSet>) -> Result<&2, &2, F.NftError, NftTable>:
  match r:
    case Done{cs}:
      Done{NftTable{n, f, cs, ss}}
    case Fail{e}:
      Fail{e}

def NftEdit.sets_go(r: Result<&2, &2, F.NftError, List<&2, S.NftNamedSet>>, n: String, f: F.NftFamily, cs: List<&2, NftChain>) -> Result<&2, &2, F.NftError, NftTable>:
  match r:
    case Done{ss}:
      Done{NftTable{n, f, cs, ss}}
    case Fail{e}:
      Fail{e}

def NftEdit.set_go(exists: Bool, n: String, f: F.NftFamily, cs: List<&2, NftChain>, ss: List<&2, S.NftNamedSet>, x: S.NftNamedSet) -> Result<&2, &2, F.NftError, NftTable>:
  match exists:
    case True{}:
      Fail{F.NftErrExists{}}
    case False{}:
      Done{NftTable{n, f, cs, List.append(&2, S.NftNamedSet, ss, [x])}}

# table t with the edit made
def NftEdit.apply(ed: NftEdit, t: NftTable) -> Result<&2, &2, F.NftError, NftTable>:
  match ed:
    case NftEditChain{+name, +base}:
      match t:
        case NftTable{+n, +f, +cs, ss}:
          NftEdit.chain_go(NftChains.found(NftChains.find(cs, name)), NftEdit.hook_ok(f, base), NftTable{n, f, cs, ss}, NftChain{name, base, Nil{}})
    case NftEditRule{c, rule}:
      match t:
        case NftTable{n, f, cs, ss}:
          NftEdit.rules_go(NftChains.add_rule(cs, c, rule), n, f, ss)
    case NftEditSet{+name, s}:
      match t:
        case NftTable{n, f, cs, +ss}:
          NftEdit.set_go(NftSets.find_any(ss, name), n, f, cs, ss, S.NftNamedSet{name, s})
    case NftEditElem{sn, e}:
      match t:
        case NftTable{n, f, cs, ss}:
          NftEdit.sets_go(NftSets.add_elem(ss, sn, e), n, f, cs)

def NftTables.cons(h: NftTable, r: Result<&2, &2, F.NftError, List<&2, NftTable>>) -> Result<&2, &2, F.NftError, List<&2, NftTable>>:
  match r:
    case Done{t}:
      Done{Con{h, t}}
    case Fail{e}:
      Fail{e}

def NftTables.put(r: Result<&2, &2, F.NftError, NftTable>, t: List<&2, NftTable>) -> Result<&2, &2, F.NftError, List<&2, NftTable>>:
  match r:
    case Done{x}:
      Done{Con{x, t}}
    case Fail{e}:
      Fail{e}

def NftTables.same(t: NftTable, +f: F.NftFamily, +n: String) -> Bool:
  match t:
    case NftTable{name, fam, cs, ss}:
      Bool.and(F.NftFamily.is_eq(fam, f), String.eq(name, n))

def NftTables.edit.pick(hit: Bool, +ed: NftEdit, t: NftTable, rest: List<&2, NftTable>, rec: Result<&2, &2, F.NftError, List<&2, NftTable>>) -> Result<&2, &2, F.NftError, List<&2, NftTable>>:
  match hit:
    case True{}:
      NftTables.put(NftEdit.apply(ed, t), rest)
    case False{}:
      NftTables.cons(t, rec)

def NftTables.edit(ts: List<&2, NftTable>, +f: F.NftFamily, +n: String, +ed: NftEdit) -> Result<&2, &2, F.NftError, List<&2, NftTable>>:
  match ts:
    case Nil{}:
      Fail{F.NftErrNoTable{}}
    case Con{+t, +rest}:
      NftTables.edit.pick(NftTables.same(t, f, n), ed, t, rest, NftTables.edit(rest, f, n, ed))

def NftRuleset.wrap(r: Result<&2, &2, F.NftError, List<&2, NftTable>>) -> Result<&2, &2, F.NftError, NftRuleset>:
  match r:
    case Done{ts}:
      Done{NftRuleset{ts}}
    case Fail{e}:
      Fail{e}

# rs with the edit made to the table of family f named n: NftErrNoTable if
# there is none
def NftRuleset.edit(rs: NftRuleset, +f: F.NftFamily, +n: String, +ed: NftEdit) -> Result<&2, &2, F.NftError, NftRuleset>:
  match rs:
    case NftRuleset{ts}:
      NftRuleset.wrap(NftTables.edit(ts, f, n, ed))

def NftTables.has(ts: List<&2, NftTable>, +f: F.NftFamily, +n: String) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{+t, rest}:
      Bool.or(NftTables.same(t, f, n), NftTables.has(rest, f, n))

def NftRuleset.add_table.go(exists: Bool, ts: List<&2, NftTable>, t: NftTable) -> Result<&2, &2, F.NftError, NftRuleset>:
  match exists:
    case True{}:
      Fail{F.NftErrExists{}}
    case False{}:
      Done{NftRuleset{List.append(&2, NftTable, ts, [t])}}

# add table: NftErrExists if rs has a table of that family and name
def NftRuleset.add_table(rs: NftRuleset, +f: F.NftFamily, +n: String) -> Result<&2, &2, F.NftError, NftRuleset>:
  match rs:
    case NftRuleset{+ts}:
      NftRuleset.add_table.go(NftTables.has(ts, f, n), ts, NftTable{n, f, Nil{}, Nil{}})

# add chain: NftErrExists if the table has a chain of that name,
# NftErrBadHook if the hook is not one of the table's family
def NftRuleset.add_chain(rs: NftRuleset, +f: F.NftFamily, +table: String, name: String, base: Maybe<&2, NftBaseSpec>) -> Result<&2, &2, F.NftError, NftRuleset>:
  NftRuleset.edit(rs, f, table, NftEditChain{name, base})

# add rule: appended to the chain; NftErrNoChain if there is none
def NftRuleset.add_rule(rs: NftRuleset, +f: F.NftFamily, +table: String, chain: String, rule: X.NftRule) -> Result<&2, &2, F.NftError, NftRuleset>:
  NftRuleset.edit(rs, f, table, NftEditRule{chain, rule})

# add set (or map): NftErrExists if the table has one of that name
def NftRuleset.add_set(rs: NftRuleset, +f: F.NftFamily, +table: String, name: String, s: S.NftSet) -> Result<&2, &2, F.NftError, NftRuleset>:
  NftRuleset.edit(rs, f, table, NftEditSet{name, s})

# add element: NftErrNoSet, or the set's insertion errors
def NftRuleset.add_element(rs: NftRuleset, +f: F.NftFamily, +table: String, set: String, e: S.NftElem) -> Result<&2, &2, F.NftError, NftRuleset>:
  NftRuleset.edit(rs, f, table, NftEditElem{set, e})

# the edits in a row, stopping at the first error
def NftRuleset.then(r: Result<&2, &2, F.NftError, NftRuleset>, +f: F.NftFamily, +table: String, +ed: NftEdit) -> Result<&2, &2, F.NftError, NftRuleset>:
  match r:
    case Done{rs}:
      NftRuleset.edit(rs, f, table, ed)
    case Fail{e}:
      Fail{e}
