# bend-osdev-nftables: verdicts (nft(8), "VERDICT STATEMENT"), the final
# verdict a hook gives a packet, and base chain policies.
#
# accept, drop, reject and queue end the evaluation of a base chain; drop,
# reject and queue end the hook too, accept passes the packet on to the next
# base chain. continue goes on with the next rule; return leaves the current
# chain; jump and goto enter another chain, jump pushing the current
# position on the call stack, goto not.
import Base

# How a reject answers (nft(8), "REJECT STATEMENT")
type NftRejectWith is Data:
  # the family's default: an ICMP port unreachable, or a TCP reset for TCP
  NftRejectDefault{}
  # an ICMP destination unreachable with this code
  NftRejectIcmp{code: U32}
  # an ICMPv6 destination unreachable with this code
  NftRejectIcmpv6{code: U32}
  # the inet family's ICMP or ICMPv6 code (icmpx)
  NftRejectIcmpx{code: U32}
  # a TCP reset
  NftRejectTcpReset{}

type NftVerdict is Data:
  NftAccept{}
  NftDrop{}
  NftReject{how: NftRejectWith}
  NftContinue{}
  NftReturn{}
  NftJump{chain: String}
  NftGoto{chain: String}
  # queue to userspace queue num; bypass: accept if no program listens
  NftQueue{num: U32, bypass: Bool}

# What a hook does with a packet
type NftFinal is Data:
  NftFinalAccept{}
  NftFinalDrop{}
  NftFinalReject{how: NftRejectWith}
  NftFinalQueue{num: U32, bypass: Bool}

# A base chain's policy: what happens when its evaluation ends without a
# verdict that ends it
type NftPolicy is Data:
  NftPolicyAccept{}
  NftPolicyDrop{}

def NftPolicy.final(p: NftPolicy) -> NftFinal:
  match p:
    case NftPolicyAccept{}:
      NftFinalAccept{}
    case NftPolicyDrop{}:
      NftFinalDrop{}

def NftPolicy.accepts(p: NftPolicy) -> Bool:
  match p:
    case NftPolicyAccept{}:
      True{}
    case NftPolicyDrop{}:
      False{}

# Text, as nft(8) writes it

def NftRejectWith.show(r: NftRejectWith) -> String:
  match r:
    case NftRejectDefault{}:
      "reject"
    case NftRejectIcmp{c}:
      "reject with icmp " ++ U32.show(c)
    case NftRejectIcmpv6{c}:
      "reject with icmpv6 " ++ U32.show(c)
    case NftRejectIcmpx{c}:
      "reject with icmpx " ++ U32.show(c)
    case NftRejectTcpReset{}:
      "reject with tcp reset"

def NftQueue.show(n: U32, bypass: Bool) -> String:
  match bypass:
    case False{}:
      "queue num " ++ U32.show(n)
    case True{}:
      "queue num " ++ U32.show(n) ++ " bypass"

def NftVerdict.show(v: NftVerdict) -> String:
  match v:
    case NftAccept{}:
      "accept"
    case NftDrop{}:
      "drop"
    case NftReject{r}:
      NftRejectWith.show(r)
    case NftContinue{}:
      "continue"
    case NftReturn{}:
      "return"
    case NftJump{c}:
      "jump " ++ c
    case NftGoto{c}:
      "goto " ++ c
    case NftQueue{n, b}:
      NftQueue.show(n, b)

def NftFinal.show(f: NftFinal) -> String:
  match f:
    case NftFinalAccept{}:
      "accept"
    case NftFinalDrop{}:
      "drop"
    case NftFinalReject{r}:
      NftRejectWith.show(r)
    case NftFinalQueue{n, b}:
      NftQueue.show(n, b)
