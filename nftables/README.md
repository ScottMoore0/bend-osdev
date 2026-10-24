# bend-osdev-nftables

nftables rule evaluation as a pure model: tables, chains and rules, the
expressions a rule is made of, sets, maps and verdict maps, counters and
limits, and the evaluation of one packet through one hook, base chain by
base chain, with jumps, gotos and the jump-depth limit. Packets are the
parsed headers of bend-osdev-netheaders; byte strings are `Octets`
(bend-osdev-bytes); counters and times are `W64` (bend-osdev-word64).

This is a model of what a rule set *does* with a packet, not a parser of
nft's language and not a kernel interface: a rule set is built as Bend
values (or with the `add_*` functions, which check what `nft` checks when it
adds tables, chains, rules, sets and elements), and a packet goes in with
its meta data, conntrack state and the time.

## Specification

**Clean room.** The kernel's nf_tables and the nft and libnftnl programs are
GPL. None of their source was opened, read or searched, nor any quotation of
it. There was no network while this package was written, so it was written
from memory of the documentation below; every fact the package depends on is
listed with its source, and every point where the documentation is silent
or incomplete is listed with how the package resolves it.

Documents:

* the nft(8) manual page: ADDRESS FAMILIES, TABLES, CHAINS (base chains,
  hooks, the table of standard priority names), RULES, SETS, MAPS, the
  expressions (PAYLOAD, RAW PAYLOAD, META, CONNTRACK) and the statements
  (VERDICT, COUNTER, LIMIT, META, REJECT, QUEUE);
* the nftables wiki's documentation pages: "Configuring chains", "Netfilter
  hooks", "Verdict statements"/"Jumping to chain", "Sets", "Maps", "Verdict
  Maps (vmaps)", "Intervals", "Concatenations", "Rate limiting matchings",
  "Counters", "Matching packet headers", "Matching connection tracking
  stateful metainformation";
* the netfilter UAPI concepts as the man pages describe them (the NFPROTO_*
  family numbers, the conntrack state bits);
* for header offsets: RFC 791 (IPv4), RFC 8200 (IPv6), RFC 9293 (TCP),
  RFC 768 (UDP), RFC 792 (ICMP), RFC 4443 (ICMPv6), IEEE 802.3 (Ethernet).

### The facts used, and where they come from

| Fact | Source |
|---|---|
| Families ip, ip6, inet, arp, bridge, netdev; an ip table sees IPv4 packets, ip6 IPv6, inet both | nft(8) ADDRESS FAMILIES |
| Hooks: prerouting, input, forward, output, postrouting for ip, ip6, inet and bridge; ingress also for inet; input and output for arp; ingress and egress for netdev | nft(8) ADDRESS FAMILIES |
| A base chain has a hook, a priority and a policy (accept or drop); a regular chain is reached only by jump or goto | nft(8) CHAINS; wiki "Configuring chains" |
| Base chains at one hook run in order of priority, lowest number first | nft(8) CHAINS |
| Priority names: raw -300, mangle -150, dstnat -100, filter 0, security 50, srcnat 100; bridge: dstnat -300, filter -200, out 100, srcnat 300 | nft(8) CHAINS, the priority table |
| accept ends the evaluation of the base chain but a later base chain (or hook) may still drop the packet; drop ends everything at once | nft(8) VERDICT STATEMENT |
| continue goes on with the next rule, and is what a rule without a verdict does | nft(8) VERDICT STATEMENT |
| return goes back to the rule after the jump into the current chain; in a base chain it is the policy | nft(8) VERDICT STATEMENT |
| jump pushes the current position on a call stack, goto does not, so a gone-to chain's return goes back past the current chain | nft(8) VERDICT STATEMENT |
| queue ends the evaluation and passes the packet to a userspace queue, with an option to bypass it when no program listens | nft(8) QUEUE STATEMENT, VERDICT STATEMENT |
| reject ends the evaluation like drop, answering with an ICMP / ICMPv6 / icmpx code or a TCP reset | nft(8) REJECT STATEMENT |
| A rule's expressions run in order; a match that fails ends the rule | nft(8) RULES; wiki |
| Raw payload expressions `@base,offset,length` with bases ll, nh, th (and ih) | nft(8) RAW PAYLOAD EXPRESSION |
| A header field match carries a dependency on the protocol (`tcp dport` matches only TCP: an implicit `meta l4proto tcp`) | wiki "Matching packet headers"; nft(8) |
| meta iif, oif, mark, l4proto, length, nfproto; `meta mark set`; ct state (new, established, related, invalid, untracked), ct mark, `ct mark set` | nft(8) META EXPRESSIONS, META STATEMENT, CONNTRACK EXPRESSIONS |
| Comparisons ==, !=, <, <=, >, >=, ranges `a-b`, prefixes `a/n`, bitwise `&`, `^` | nft(8) relational expressions, bitwise |
| Anonymous sets `{ ... }` and named sets; interval sets hold ranges and prefixes; elements that overlap are refused (unless auto-merge) | nft(8) SETS; wiki "Sets", "Intervals" |
| Maps (`key : value`), verdict maps (`key : verdict`); a lookup that finds nothing does not match | nft(8) MAPS; wiki "Maps", "Verdict Maps (vmaps)" |
| Concatenations `a . b` as keys | wiki "Concatenations" |
| counter counts packets and bytes | nft(8) COUNTER STATEMENT |
| limit rate [over] N/second, minute, hour, day, week [burst N packets/bytes], a token bucket | nft(8) LIMIT STATEMENT; wiki "Rate limiting matchings" |
| NFPROTO numbers (`meta nfproto`): ipv4 2, arp 3, netdev 5, bridge 7, ipv6 10 | the netfilter UAPI, as remembered |
| ct state bits: invalid 1, established 2, related 4, new 8, untracked 64 | the conntrack UAPI, as remembered |
| Header offsets (IPv4 protocol 9, saddr 12, daddr 16; IPv6 next header 6, saddr 8, daddr 24; ports 0 and 2; TCP flags 13; ICMP type 0, code 1) | the RFCs above |

### Where the documentation is silent, and what the package does

These are stated choices; where the choice is a real one it is an option
(see Extension points).

* **Base chains of equal priority.** nft(8) does not say which runs first.
  The package runs them in the order they were added (tables in rule set
  order, chains in table order).
* **The jump-depth limit.** The documentation says jumps nest and loops are
  refused, not how deep nesting may go; nft refuses a looping rule set when
  it is loaded. The package evaluates any rule set: a jump or goto that would
  enter a chain more than `max_depth` levels down (16 by default, the
  kernel's jump stack size as remembered) is not taken, and the evaluation
  ends with `depth_final` (drop by default). A jump or goto to a chain the
  table does not have (nft refuses it when loading) ends with
  `missing_final` (drop by default).
* **goto and depth.** goto does not push a return address, but it does enter
  a chain one level deeper for the depth limit, as jump does: otherwise a
  goto loop would never end.
* **Byte order.** The kernel holds meta and ct values (mark, iif, length,
  ct state) in host byte order and nft converts constants to match. The
  model holds every value in network byte order and compares values as
  numbers spelled most significant byte first, which is what nft's
  comparisons mean for both orders.
* **Offsets in bytes.** nft's raw payload offsets and lengths are in bits.
  The model's are in bytes; a field narrower than a byte is a byte load and a
  bitwise mask (`NftSrcBitwise`), as nft itself compiles such a field. The
  inner header base (ih) is not modelled.
* **The token bucket.** nft(8) gives the syntax, not the arithmetic. The
  model: the bucket holds `burst` packets (bytes), or `rate` if burst is 0;
  it starts full; it refills at `rate` per unit, measured in milliseconds;
  a packet conforms if the bucket holds its cost (one packet, or its length
  in bytes), and a conforming packet takes its cost even under `over`, which
  only inverts the match; time going backwards refills nothing. When no
  burst is given, `NftLimitSpec.default_burst()` is 5 (iptables' documented
  default; nft's is not documented).
* **Missing names at evaluation.** A rule naming a set that does not exist
  (nft refuses this when loading) does not match, neither `in` nor `not in`.
* **meta l4proto.** In the kernel it is the transport protocol after any
  IPv6 extension headers; `NftPacket.of_ip` does not walk extension headers,
  so for IPv6 it is the fixed header's next header. A caller with a parsed
  extension chain can build the `NftPacket` itself (the type is open).
* **meta length** is the length of the bytes given to `NftPacket.of_ip` /
  `of_eth`.
* **Counters** are 64-bit (W64) and identified by an id the rule set gives
  each one, standing for nft's per-rule anonymous counters and its named
  counters alike; limits likewise.
* **Not modelled:** chain types (every chain is a filter chain; nat and
  route chains' extra behaviour is not modelled), the packets reject sends,
  what userspace does with a queued packet (the verdict is a value: resuming
  after an accept from userspace means calling `Nft.run_hook` on the base
  chains after the one that queued), set element timeouts, dynamic sets
  (`add @set`), auto-merge, flowtables, and the reject statement's
  restriction to some hooks.

## Files

| File | Holds |
|---|---|
| `nftables.bend` | the entry: `NftResult`, `Nft.eval` (one packet through one hook of a rule set), `Nft.eval_default`, `NftResult.show` |
| `family.bend` | `NftError` (shared by every file), families `NftFamily`, protocol families `NftProto`, hooks `NftHook`, priorities `NftPrio` |
| `verdict.bend` | `NftVerdict`, `NftRejectWith`, `NftFinal` (what a hook does with a packet), `NftPolicy` |
| `sets.bend` | keys `NftKey`, elements `NftElem`, `NftData`, sets and maps `NftSet`, `NftNamedSet` |
| `expr.bend` | packets (`NftPacket`, `NftMeta`, `NftCt`, the header layers), building packets from bytes, sources `NftSrc`, tests `NftTest`, expressions `NftExpr`, rules `NftRule`, state (counters, token buckets) `NftState`, `NftEnv`, header fields `NftField` |
| `chains.bend` | `NftChain`, `NftBaseSpec`, `NftTable`, `NftRuleset`, the base chains at a hook (`NftRuleset.base_chains`), building rule sets (`add_*`, `NftEdit`), `without_rules` |
| `eval.bend` | `NftOptions` and its default, a chain's evaluation (`Nft.run_chain`, `NftRun`), a base chain's (`Nft.run_base`), a hook's (`Nft.run_hook`, `NftOut`) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `LAWS_map.bend`, `PROOF_map.bend` | the key order and map lookup: laws and proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

Bend imports do not re-export: import the files whose types you use.

## Public interface

Everything not listed here is internal (the `NftRun.run` machine and its
`NftPend` states' handling, the `.go`/`.pick` helpers, `NftTail`,
`NftUpper`, `NftLayer`, `NftValue`, `NftBucket`, `NftCounters`,
`NftChains`, `NftSets`, `NftTables`, `NftHookRun`, `NftBase`). Types marked
open may be matched on and built; `NftSet` is opaque.

### nftables.bend

| Def or type | Meaning |
|---|---|
| `Nft.eval(opts, rs, proto, hook, now, pkt, st)` | packet `pkt` of protocol family `proto` through `hook` of rule set `rs` at time `now` (ms, `W64`) from state `st`: an `NftResult` |
| `Nft.eval_default(rs, proto, hook, now, pkt, st)` | the same with `NftOptions.default()` |
| `NftResult{verdict, pkt, st, depth}` (open) | the final verdict, the packet after it (marks set by statements), the state after it, the deepest level of chains entered; `NftResult.verdict`, `.pkt`, `.st`, `.depth`, `NftResult.show` |

A stream of packets is a fold: each `Nft.eval` takes the state the previous
one returned, so counters count and limits limit across packets.

### family.bend

| Def or type | Meaning |
|---|---|
| `NftError` | `NftErrSetOverlap`, `NftErrBadInterval`, `NftErrNoTable`, `NftErrNoChain`, `NftErrNoSet`, `NftErrExists`, `NftErrBadHook`, `NftErrBadPacket` |
| `NftFamily` | `NftIp`, `NftIp6`, `NftInet`, `NftArp`, `NftBridge`, `NftNetdev`; `NftFamily.sees(f, proto)`, `NftFamily.has_hook(f, hook)`, `NftFamily.is_eq` |
| `NftProto` | `NftProtoIpv4`, `NftProtoIpv6`, `NftProtoArp`, `NftProtoBridge`, `NftProtoNetdev`; `NftProto.nfproto(p)` |
| `NftHook` | `NftPrerouting`, `NftInput`, `NftForward`, `NftOutput`, `NftPostrouting`, `NftIngress`, `NftEgress`; `NftHook.is_eq` |
| `NftPrio.of(neg, n)`, `NftPrio.lt(a, b)` | a priority (a signed 32-bit number held in a `U32`), the signed order |
| `NftPrio.raw()`, `mangle()`, `dstnat()`, `filter()`, `security()`, `srcnat()`, `bridge_dstnat()`, `bridge_filter()`, `bridge_out()`, `bridge_srcnat()` | the standard priority names |

### verdict.bend

| Def or type | Meaning |
|---|---|
| `NftVerdict` (open) | `NftAccept`, `NftDrop`, `NftReject{how}`, `NftContinue`, `NftReturn`, `NftJump{chain}`, `NftGoto{chain}`, `NftQueue{num, bypass}` |
| `NftRejectWith` (open) | `NftRejectDefault`, `NftRejectIcmp{code}`, `NftRejectIcmpv6{code}`, `NftRejectIcmpx{code}`, `NftRejectTcpReset` |
| `NftFinal` (open) | `NftFinalAccept`, `NftFinalDrop`, `NftFinalReject{how}`, `NftFinalQueue{num, bypass}` |
| `NftPolicy` (open) | `NftPolicyAccept`, `NftPolicyDrop`; `NftPolicy.final`, `NftPolicy.accepts` |
| `NftVerdict.show`, `NftFinal.show`, `NftRejectWith.show` | as nft(8) writes them |

### sets.bend

| Def or type | Meaning |
|---|---|
| `NftKey.cmp`, `lt`, `le`, `eq` | the order of keys (`Octets`): byte by byte, most significant first |
| `NftKey.u8`, `u16`, `u32`, `ipv4(a, b, c, d)`, `concat(a, b)`, `prefix_lo(k, n)`, `prefix_hi(k, n)` | keys of the usual widths, in network byte order |
| `NftElem{lo, hi, data}` (open) | the closed interval of keys `[lo, hi]` and its data; `NftElem.single(k)`, `range(lo, hi)`, `prefix(k, n)`, `to(e, data)`, `valid(e)`, `contains(e, x)`, `lo`, `hi`, `data` |
| `NftData` (open) | `NftNoData` (a set), `NftDataValue{value}` (a map), `NftDataVerdict{verdict}` (a verdict map) |
| `NftSet` (opaque) | `NftSet.empty()`, `insert(s, e)` (`Result`: `NftErrBadInterval`, `NftErrSetOverlap`), `of_list(es)`, `mem(s, x)`, `lookup(s, x)` (`Maybe<&2, NftData>`), `elements(s)` (in key order), `wf(s)` (the invariant) |
| `NftNamedSet{name, set}` (open) | a table's set or map; `NftNamedSet.find(sets, name)` |

### expr.bend

| Def or type | Meaning |
|---|---|
| `NftPacket{meta, ct, l2, l3, l4, data}` (open) | a packet: `NftMeta{iif, oif, mark, l4proto, length, nfproto}`, `NftCt{state, mark}`, `NftL2` (`NftL2None`, `NftL2Eth{h}`), `NftL3` (`NftL3None`, `NftL3Ipv4{h}`, `NftL3Ipv6{h}`, `NftL3Arp{p}`), `NftL4` (`NftL4None`, `NftL4Tcp{h}`, `NftL4Udp{h}`, `NftL4Icmp{h}`), the bytes after the headers |
| `NftPacket.of_ip(iif, oif, mark, ct, o)` | the packet from its IPv4 or IPv6 bytes, parsed with netheaders (`NftErrBadPacket` if the network header does not parse) |
| `NftPacket.of_eth(iif, oif, mark, nfproto, ct, o)` | the same from an Ethernet frame, for bridge and netdev |
| `NftPacket.meta`, `ct`, `length`, `mark`, `ct_mark`, `set_mark`, `set_ct_mark`, `NftPacket.base(b, p)` | reading and changing a packet; the bytes from a payload base on |
| `NftCt.INVALID()`, `ESTABLISHED()`, `RELATED()`, `NEW()`, `UNTRACKED()` | the ct state bits |
| `NftSrc` (open) | `NftSrcPayload{base, offset, len}` (`NftBaseLl`, `NftBaseNh`, `NftBaseTh`), `NftSrcMeta{key}` (`NftMetaIif` … `NftMetaNfproto`), `NftSrcCt{key}` (`NftCtState`, `NftCtMark`), `NftSrcImm{value}`, `NftSrcBitwise{src, mask, xor}`, `NftSrcConcat{a, b}`, `NftSrcMap{key, map}`; `NftSrc.load(src, sets, p)` |
| `NftSetRef` (open) | `NftSetAnon{set}`, `NftSetNamed{name}` |
| `NftTest` (open) | `NftCmp{op, value}` (`NftOpEq` … `NftOpGe`), `NftRange{lo, hi}`, `NftNotRange{lo, hi}`, `NftIn{set}`, `NftNotIn{set}`; `NftTest.check` |
| `NftExpr` (open) | `NftMatch{src, test}`, `NftCount{id}`, `NftLimit{id, spec}`, `NftMarkSet{src}`, `NftCtMarkSet{src}`, `NftVmap{src, map}`, `NftVerdictStmt{verdict}`; `NftExpr.eval` |
| `NftRule{exprs}` (open) | a rule; `NftRule.eval(r, sets, env)` gives `NftRuleNext{env}` or `NftRuleVerdict{verdict, env}` |
| `NftLimitSpec{rate, unit_ms, burst, bytes, over}` (open) | a limit; `NftLimitSpec.second()` … `week()`, `default_burst()`, `packets(rate, unit)` |
| `NftState` (open), `NftCounterVal{id, packets, bytes}` | `NftState.empty()`, `NftState.counter(st, id)` |
| `NftEnv{pkt, st, now}` (open) | what evaluation carries |
| `NftExpr.eq`, `ne`, `cmp`, `range`, `in_set`, `not_in`, `verdict`, `ct_state(mask)`, `needs_l4proto(n)`, `needs_nfproto(n)` | building expressions; the payload dependencies nft adds |
| `NftField.ip_protocol()`, `ip_saddr()`, `ip_daddr()`, `ip_ttl()`, `ip6_nexthdr()`, `ip6_hoplimit()`, `ip6_saddr()`, `ip6_daddr()`, `th_sport()`, `th_dport()`, `tcp_flags()`, `icmp_type()`, `icmp_code()`, `ether_daddr()`, `ether_saddr()`, `ether_type()`, `meta(k)`, `ct(k)` | header fields as payload loads |

### chains.bend

| Def or type | Meaning |
|---|---|
| `NftChain{name, base, rules}`, `NftBaseSpec{hook, prio, policy}`, `NftTable{name, family, chains, sets}`, `NftRuleset{tables}` (open) | the structure |
| `NftTable.rules(t, name)`, `NftTable.has_chain(t, name)`, `NftTable.sets`, `NftTable.chains`, `NftTable.family`, `NftChain.name`, `NftChain.rules` | reading it |
| `NftHooked{tbl, rules, prio, policy}` (open), `NftRuleset.base_chains(rs, proto, hook)` | the base chains a packet meets at a hook, in the order they run |
| `NftRuleset.empty()`, `add_table`, `add_chain`, `add_rule`, `add_set`, `add_element`, `edit(rs, f, table, ed)`, `then(r, f, table, ed)`, `NftEdit` | building rule sets, with nft's checks (`NftErrExists`, `NftErrBadHook`, `NftErrNoTable`, `NftErrNoChain`, `NftErrNoSet`, the set errors) |
| `NftRuleset.without_rules(rs)` | every chain kept, empty |

### eval.bend

| Def or type | Meaning |
|---|---|
| `NftOptions{max_depth, depth_final, missing_final}`, `NftOptions.default()` | the evaluator's choices (16, drop, drop); `NftOptions.max_depth`, `depth_final`, `missing_final` |
| `Nft.run_chain(opts, fuel, tbl, rules, env)`, `NftRun`, `NftRun.result`, `NftRun.env`, `NftRun.depth`, `NftChainRes` (`NftChainReturn`, `NftChainStop{final}`) | a chain's evaluation with `fuel` levels left |
| `Nft.run_base(opts, h, env)`, `Nft.run_hook(opts, hs, env)`, `NftOut{final, env, depth}`, `NftOut.final`, `.env`, `.depth` | a base chain's and a hook's evaluation (`final` None: passed on) |

## Extension points

* **The evaluator's choices** are `NftOptions`: how deep jumps may nest,
  and what a too-deep or a dangling jump does (`depth_final`,
  `missing_final`: any `NftFinal`, so a test harness can make them visible
  as a queue verdict, say). `NftOptions.default()` is 16, drop, drop.
* **Limits:** `NftLimitSpec` is open, with the units and
  `default_burst()` as named defaults; a different bucket arithmetic is one
  function (`NftBucket.step`).
* **Packets** are open records of netheaders headers: `of_ip` and `of_eth`
  are conveniences, and a caller that walks IPv6 extension headers, or has
  another link layer, builds `NftPacket` directly.
* **Expressions:** a new key (another meta key, a header field) is a
  constructor of `NftMetaKey` or a payload load (`NftField`); a new
  statement is a constructor of `NftExpr` and a case of `NftExpr.eval`. The
  laws about chains and hooks hold whatever the expressions are: they are
  stated over `NftRule.eval`'s results.
* **Sets are opaque.** `NftSet` is a sorted list of disjoint intervals with
  a linear lookup, the simplest structure to prove things about. A faster
  structure (bend-osdev-itree's interval tree, a hash for single keys) can
  replace it behind the same defs; the set laws state what it must keep.
* **Priorities, families and hooks** are plain data with named defaults
  (`NftPrio.filter()` and the rest).

## Laws

`LAWS.bend`, on the public
interface only: 15 laws for every input, 8 vectors, and 12 witnesses.

For every input:

* **depth:** `chain_depth_bound`: a chain's evaluation never enters chains
  deeper than its fuel; `eval_depth_bound`: a hook's never deeper than
  `max_depth`, for every rule set, packet, state and options. (That every
  evaluation terminates is Bend's own guarantee: every def is total.)
* **drop is final:** `drop_rule_final` (a rule that drops ends its chain
  with drop, whatever follows), `drop_through_jump` and
  `drop_through_goto` (a jump or goto to a chain that drops ends the caller
  with drop), `drop_ends_hook` (a base chain that drops ends the hook with
  drop, whatever base chains follow, with the packet and state that chain
  left: nothing later runs);
* **the call stack:** `jump_returns` (after a jumped-to chain returns, the
  caller's evaluation is that of the rest of its rules from where the callee
  left the packet and state), `goto_returns` and `goto_result` (a goto's
  chain's result and packet are the current chain's: its rest is skipped);
* **no rules:** `no_rules_policy`: for every rule set `rs`,
  `Nft.eval(opts, without_rules(rs), …)` is `drop` if some base chain the
  packet meets at the hook has policy drop and `accept` otherwise, with the
  packet and state unchanged and depth 0 (the model, `policy_model`, scans
  the tables directly, without the priority sort);
* **sets:** `set_mem_insert` (after inserting `e`, a key is in the set iff
  `e` holds it or it was in before), `set_mem_of_list` (the set built from
  a list holds exactly the keys some element of the list holds: the list
  model `list_mem`), `map_lookup_mem` (a lookup finds data iff the key is a
  member), `set_wf_insert` and `set_wf_of_list` (interval sets never
  overlap: insertion keeps the invariant, and every built set has it).

Vectors: a chain that jumps to itself reaches depth 16 and drops; jump then
return, and goto then return (they differ in which chain continues);
accept in one base chain followed by drop in a later one; queue as a final
value; an overlapping and an inverted interval refused; the empty set's
invariant. Witnesses: each hypothesis of the laws above holds for a
concrete input (the drop, jump and goto rules, the chain existing, the
callee dropping or returning, a base chain dropping, a set built, a set with
the invariant, an insertion that succeeds).

The proofs (`PROOF.bend`) follow the evaluator's structure: the depth by
induction on the fuel and the rules; drop by "Done passes through every
later rule and base chain"; jump's return by a lemma that a chain's result
and packet do not depend on the depth it starts from; the policies by
showing that the priority-ordered insertion keeps "no chain has rules" and
"some policy drops"; the sets by induction on the sorted list, using only
the outcomes of the key comparisons the insertion makes, so no lemma about
the order of keys was needed. `PROOF.bend` uses bytes and netheaders only
through their public defs (no laws of theirs were needed).

`LAWS_map.bend`, on the public interface only: 9 laws for every input, 1
vector and 1 witness.

* **the key order:** `key_le_refl`, `key_le_trans`, `key_lt_trans`,
  `key_lt_le_trans`, `key_le_lt_trans` (`NftKey.le` is reflexive and
  transitive, `NftKey.lt` transitive, and the two chain either way), and
  `key_lt_not_le` (a key below another is not at or above it);
* **maps:** `map_lookup_unique` (on a set with the invariant, if
  `elements(s)` is `pre ++ [e] ++ post` and `e` holds `x`, then
  `lookup(s, x)` is `Some{data(e)}`: the element holding a key is the only
  one), `map_lookup_insert` (after inserting `e`, `lookup` gives `e`'s data
  for the keys `e` holds and what it gave before for the others; no
  hypothesis on the set is needed: insertion only puts `e` after elements
  it lies above), `map_lookup_of_list` (the map built from a list answers
  as the list does: the data of the first element of the list holding the
  key, the list model `list_lookup`).

The vector builds a map of two intervals and looks it up inside one and
between them; the witness is a one-element set with the invariant holding
the key it is looked up with.

The proofs (`PROOF_map.bend`) state the key order's transitivity as one
fact about three comparisons (`cm.ck`), prove it for `Nat.cmp` by
induction, carry it to `U32.cmp` by bend-osdev-u32's `u32_cmp_value` (the
only law of another package used), and through the lexicographic step by
induction on the byte lists; comparing the other way round flips the
result, the same way. Uniqueness: on a list with the invariant every
element before one lies below its low end and every element after it above
its high end. Insertion: the element goes in before the first it lies below
(so lookup reads it first) or after one it lies above (which holds none of
its keys, so the two lookups commute), and it succeeds only when no element
holds a key of the new one. The list model follows by induction over the
insertions, with the set's lookup the first answer of the elements inserted
so far.

Not proved: the expressions' semantics (payload loads, comparisons, limits)
are covered by the differential test and `check.bend`.

## Tests

`check.bend` runs a filter (established/related accept, ssh accept, web
ports to a counting chain), jump and goto with return, a jump loop, a
verdict map with accept, reject and queue, a map setting the mark, two base
chains at one hook from ip and inet tables, a limit over five packets in
time, and the `add_*` errors.

`ref/run.sh` compares the package with an independent model of nftables
evaluation in Python (`ref/gen.py`), **written by the same author from the
same documentation**, so it catches slips in the Bend code, not a shared
misreading of the documentation. The Python model is written differently on
purpose: chains run by plain recursion with an explicit level, packets are
bytes packed with `struct` (Bend parses them with netheaders), sets are
lists checked with Python's bytes comparison, the limit is
`min(cap, credit + elapsed * rate)`. gen.py builds random rule sets (ip, ip6
and inet tables; base chains at several hooks and priorities; jumps, gotos,
loops and dangling jumps; anonymous and named sets, some refused for
overlap; concatenations; maps setting marks; verdict maps; counters; limits
in packets and bytes, with and without `over`; every verdict) and random
IPv4 and IPv6 packets (TCP with and without options, UDP, ICMP, ICMPv6, an
unknown protocol, cut-short transport headers), and sends one to three
packets through each rule set at increasing (sometimes decreasing) times,
the state carried between them. The default run is 80 rule sets and 152
packets, about 40 s natively; seeds 1 to 8 at 120 rule sets (960 rule sets,
1,914 packets) and seed 7 at 400 rule sets all matched.

**nft.** `nft` is not installed here, and running packets through the
kernel's nf_tables needs root and a network namespace (veth pairs, packets
sent and counted), so the verdicts are not compared with the kernel. gen.py
also writes the rule sets that it can express in nft syntax (about a third
of the cases are generated within that subset: raw payload matches,
comparisons, ranges, anonymous sets, counters, limits per second, marks,
plain reject, jumps that do not loop) to `ref/nft/`, and when `nft` is
installed and may reach the kernel, `run.sh` gives each to
`nft --check -f`, which **validates their syntax only**. That printer could
not be tried here; if CI installs nft and it refuses a file, the printer (or
this README's reading of nft's syntax) is wrong. CI needs the apt package
**`nftables`** (and CAP_NET_ADMIN, e.g. `sudo`, for `nft --check`).

## Speed

Measured natively (Bend 2.0.37, WSL2):

| Run | Time | Peak RAM |
|---|---|---|
| one packet through a chain of 1,000 rules (counter, port compare) | 0.03 s | 3 MB |
| one packet through 10,000 rules | 0.31 s | 6 MB |
| 10,000 packets through 10 rules (state carried) | 6.0 s | 3 MB |
| building a set of 1,000 single keys | 1.0 s | 3 MB |
| building a set of 3,000 single keys | 9.4 s | 4 MB |
| that, then 1,000 packets looked up in it | 17 s in all | 4 MB |

A rule costs about 30 microseconds natively: every payload load rebuilds
the header's bytes from the parsed header (netheaders' builders work by bit
slicing, so that their round trips are proved). Building a set is quadratic
(each insertion walks the sorted list) and a lookup is linear; both are the
reference structure, chosen for the proofs (see Extension points).

## Sizes

A chain's rules and a rule's expressions are walked by tail calls, so a
chain may be as long as memory allows on both lanes. Set operations, the
counter and bucket lists and the base-chain insertion recurse structurally:
natively (a 2 GB stack) that is no limit; on the JavaScript lane, sets of
more than some thousands of elements would overflow its stack. `check.bend`
runs natively. The differential test's generated program is about 210 KB,
and checking and building it takes about 1 GB.

## Status

Bend 2.0.37: `PROOF.bend` and `PROOF_map.bend` ALL PROOFS CHECK, `--verdict`
ALL PROOFS CHECK (`PROOF_map.bend` peaks at 0.22 GB), `check.bend` passes
(native), `ref/run.sh` 80 cases (152 packets) match, and where nft was
installed, `nft --check` accepted all 32 rule sets written in nft syntax;
`scripts/deps.sh` ok.
