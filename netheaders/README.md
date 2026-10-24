# bend-osdev-netheaders

Parse and build the binary headers of the common network protocols, and
compute and verify the Internet checksum, on `Octets` (bend-osdev-bytes).

## Specifications

* IEEE 802.3: Ethernet II framing (destination, source, EtherType);
* IEEE 802.1Q: the VLAN tag (TPID 0x8100, priority, drop eligible, VLAN id);
* RFC 826: ARP (here for IPv4 over Ethernet);
* RFC 791: IPv4;
* RFC 8200: IPv6, and in section 8.1 the IPv6 pseudo-header for
  upper-layer checksums, and that a zero UDP checksum is invalid over IPv6;
* RFC 792: ICMP; RFC 4443: ICMPv6 (its checksum covers the IPv6
  pseudo-header, next header 58);
* RFC 768: UDP, its IPv4 pseudo-header, and "a computed checksum of zero is
  sent as all ones";
* RFC 9293: TCP, and its IPv4 pseudo-header (section 3.1);
* RFC 1071: the Internet checksum.

## Files

| File | Holds |
|---|---|
| `netheaders.bend` | what the others share: the error type `NetError`, and `NetField`, the bit fields of a 32-bit word |
| `checksum.bend` | the Internet checksum, usable on its own: one shot and in pieces |
| `ethernet.bend` | `MacAddr`, `VlanTag`, `EthHeader` |
| `arp.bend` | `ArpPacket` (imports `ethernet.bend` for `MacAddr`) |
| `ipv4.bend` | `Ipv4Header`, its checksum, the IPv4 pseudo-header |
| `ipv6.bend` | `Ipv6Addr`, `Ipv6Header`, the IPv6 pseudo-header |
| `icmp.bend` | `IcmpHeader`, for ICMP and ICMPv6 |
| `udp.bend` | `UdpHeader`, its checksum over IPv4 or IPv6 |
| `tcp.bend` | `TcpHeader`, its checksum over IPv4 or IPv6 |
| `LAWS.bend`, `PROOF.bend` | the round trips, truncation, the checksum in pieces, and the vectors |
| `LAWS_sum.bend`, `PROOF_sum.bend` | the checksum's one's complement arithmetic, and that ICMP, ICMPv6, UDP and TCP built with their checksums verify |
| `LAWS_ipv4.bend`, `PROOF_ipv4.bend` | that an IPv4 header built with its checksum verifies |
| `proof_ones.bend` | the lemmas `PROOF_sum.bend` and `PROOF_ipv4.bend` rest on (no laws) |

Bend imports do not re-export: import `netheaders.bend` (for `NetError`)
and the files of the protocols you use.

## API

Every header has a record type `X` (all fields `U32` unless noted), and:

| Def | Meaning |
|---|---|
| `X.parse(o)` | the header at the start of `o`: `Done{h}`, or `Fail{e}` with a `NetError` |
| `X.build(h)` | the header's bytes, every field masked to its width (checksum written as given) |
| `X.norm(h)` | `h` with every field masked to its width: what `parse(build(h))` gives |
| `X.length(h)` | the header's length in bytes: the payload is `B.Octets.drop(X.length(h), o)` (UDP: `header_length`) |

`NetError`: `NetTruncated` (too few bytes), `NetBadVersion`, `NetBadIhl`
(IPv4 IHL below 5), `NetBadDataOffset` (TCP data offset below 5),
`NetBadArpFormat` (not IPv4 over Ethernet), `NetBadLength` (a length field
shorter than its header), `NetBadChecksum`.

| Header | Fields | Also |
|---|---|---|
| `EthHeader{dst, src, vlan, ethertype}` | `MacAddr{a0 .. a5}` bytes; `vlan: Maybe<VlanTag{pcp, dei, vid}>` | `parse_with(tpid, o)`, `build_with(tpid, h)`, `TPID_8021Q()`, `TYPE_IPV4/ARP/IPV6()`, `MacAddr.bytes`, `MacAddr.broadcast` |
| `ArpPacket{oper, sha, spa, tha, tpa}` | addresses `MacAddr` and `U32` | `REQUEST()`, `REPLY()` |
| `Ipv4Header{version, ihl, dscp, ecn, total_length, ident, flags, frag_offset, ttl, protocol, checksum, src, dst, options}` | `options: Octets`, raw | `build_checksum(h)`, `verify(o)`, `parse_verified(o)`, `payload(h, packet)`, `ipv4_pseudo(src, dst, proto, len)`, `PROTO_ICMP/TCP/UDP()` |
| `Ipv6Header{version, traffic_class, flow_label, payload_length, next_header, hop_limit, src, dst}` | `Ipv6Addr{w0, w1, w2, w3}`, most significant word first | `payload(h, packet)`, `ipv6_pseudo(src, dst, len, next)`, `Ipv6Addr.bytes` |
| `IcmpHeader{msg_type, code, checksum, rest_of_header}` | `rest_of_header`: the 4 bytes after the checksum | `build_checksum(h, data)`, `verify(msg)`, `build_ipv6(src, dst, h, data)`, `verify_ipv6(src, dst, msg)`, `ECHO_REQUEST()` … |
| `UdpHeader{src_port, dst_port, length, checksum}` | | `build_ipv4(src, dst, h, payload)`, `build_ipv6(…)`, `verify_ipv4(src, dst, dg)`, `verify_ipv4_with(zero_ok, …)`, `verify_ipv6(…)`, `payload(h, dg)` |
| `TcpHeader{src_port, dst_port, seq, ack, data_offset, reserved, flags, window, checksum, urgent, options}` | `options: Octets`, raw; `flags` the 8 control bits | `build_ipv4(src, dst, h, payload)`, `build_ipv6(…)`, `verify_ipv4(src, dst, seg)`, `verify_ipv6(…)`, `FIN()` … `CWR()` |

The checksum (`checksum.bend`): `inet_checksum(o)`, `inet_verify(o)` (the
sum of data that includes its checksum is all ones), `inet_sum(o)`; in
pieces `inet_start()`, `inet_update(acc, o)` (every piece but the last of
even length, `inet_even(o)`), `inet_finish(acc)`; `inet_add(a, b)`, the one's
complement sum of two 16-bit values (add, then fold the carry back in);
`inet_put16(o, off, v)`, `o` with the 16-bit big-endian field at `off`
replaced by `v`; and `inet_fill(pseudo, o, off)`, `o` with the checksum of
`pseudo ++ o` written at offset `off`.

`NetField.low(k, v)`, `NetField.get(v, p, k)` and `NetField.put(p, k, x, v)`
read and write the `k`-bit field from bit `p` of a word, by bit slicing.

What the parsers check: the bytes are there (`NetTruncated`), the version
(IPv4, IPv6), IHL and data offset at least 5 with all their bytes present,
and ARP's hardware and protocol types and lengths. They do not check the
checksum (except `Ipv4Header.parse_verified`) or the length fields against
the bytes that follow: the `payload` functions do that.

`build` writes every field as given, so it can build malformed headers too:
IHL and data offset must match the options' length (multiples of 4 bytes)
for the header to parse back, and the UDP length should match the datagram.
The pseudo-header's length is the number of bytes checksummed.

## Extension points

* **Another tag protocol:** `EthHeader.parse_with(tpid, o)` and
  `build_with(tpid, h)` take the tag protocol identifier (`TPID_8021Q()`,
  0x8100, is the default; pass 0x88a8 for an 802.1ad service tag). One tag is
  read; an inner tag is reported as the EtherType.
* **UDP without a checksum:** `UdpHeader.verify_ipv4_with(zero_ok, …)`
  chooses whether a zero checksum field (RFC 768's "none computed") is
  accepted over IPv4; `verify_ipv4` accepts it, as RFC 768 allows.
* **Options and extension headers** are left raw: IPv4 and TCP options are
  `Octets` for a caller to interpret, and IPv6 extension headers start at
  `Ipv6Header.length(h)`, named by `next_header`. A TCP option parser or an
  extension-header walker can be added in its own file on top of these.
* **Other protocols** can be written with `NetField` and the checksum
  functions (`inet_fill` with a pseudo-header), as the files here are.
* **A fast checksum** (native arithmetic, several bytes at a time) could be
  added beside `checksum.bend`'s bit-slicing one, with a law or the
  differential test holding the two together; the present one is the
  reference.

## Laws

Three pairs of law and proof files, each checked on its own, all on the
public interface. `LAWS.bend`:

* **for every input** (16 properties):
  * round trips, for every field value, followed by any bytes `rest`:
    `parse(build(h) ++ rest) == Done{norm(h)}` for UDP, ICMP, ARP, IPv6
    (version 6), Ethernet tagged, Ethernet untagged when the EtherType's low
    16 bits are not 0x8100, and IPv4 (version 4) and TCP for **every** IHL or
    data offset from 5 to 15 with options of the matching length, that is for
    every header the parser accepts;
  * truncation: every input shorter than a header's fixed part (14, 28, 20,
    40, 8, 8 and 20 bytes) fails with `NetTruncated`;
  * the checksum in pieces: `inet_update(acc, a ++ b) ==
    inet_update(inet_update(acc, a), b)` when `a` has an even length.
* **vectors** (28): RFC 1071's worked example (sum 0xddf2, checksum 0x220d)
  whole and in two pieces; odd lengths and the end-around carry; an IPv4
  header checksum (0xb861); headers built with their checksums verify, for
  IPv4, ICMP, ICMPv6, UDP and TCP over IPv4 and IPv6; a corrupted IPv4
  checksum fails with `NetBadChecksum`; UDP's zero checksum over IPv4 and
  IPv6; each `NetError` from a malformed header; the `payload` functions.

The proofs (`PROOF.bend`, generated by `ref/gen_proof.py`: run `python3
ref/gen_proof.py PROOF.bend` in this directory) split every field into the
bits its width keeps and compute; the IHL and data offset are split into
their 16 values, and the options list into its required length, the other
cases contradicting the law's hypotheses. `rest` is handled through bytes'
interface law `octets_append_list`.

`LAWS_sum.bend`, the one's complement arithmetic of RFC 1071 and what it
gives the headers (26 laws, for every input but the last two):

* on 16-bit values (a `U32` of at most 65535): `inet_add` is the plain sum
  when that fits 16 bits (`inet_add_no_carry`) and otherwise the sum less
  65535, the end-around carry (`inet_add_end_around`); it is commutative
  (`inet_add_comm`, for all words), associative (`inet_add_assoc`), has 0 as
  its identity (`inet_add_zero`), keeps values in 16 bits
  (`inet_add_bound`), and a value plus its checksum is 0xffff
  (`inet_add_complement`); `inet_finish` is always a 16-bit value
  (`inet_finish_bound`);
* order independence: `inet_update` keeps a 16-bit accumulator in 16 bits
  (`inet_update_bound`), and updates commute with each other
  (`inet_update_comm`, any data, odd lengths too) and with `inet_add`
  (`inet_update_add`); two pieces of even length sum the same in either
  order (`inet_sum_swap`); with `inet_update_split` (`LAWS.bend`) a sum may
  be split into pieces and summed in any order;
* the checksum written in: for a pseudo-header of even length and the field
  at an even offset `2k` with `2k <= len(o)`, `pseudo ++ inet_fill(pseudo,
  o, 2k)` verifies (`inet_fill_verifies`);
* headers built with their checksums verify, for every header and payload:
  ICMP (`icmp_build_verifies`), ICMPv6 over its pseudo-header
  (`icmp6_build_verifies`), UDP over IPv4 and IPv6
  (`udp_ipv4_build_verifies`, `udp_ipv6_build_verifies`: RFC 768's
  computed 0 is sent as 0xffff, which verifies too, and over IPv6 the field
  read back is never 0), TCP over IPv4 and IPv6 (`tcp_ipv4_build_verifies`,
  `tcp_ipv6_build_verifies`); the verifier's pseudo-header carries the
  length the builder used, since writing the field keeps the length;
* the checksum field written by `inet_put16` (as `inet_fill` and UDP write
  it): the length is kept (`inet_put16_len`) and so are the bytes past the
  field (`inet_put16_drop`); ICMP and UDP headers followed by any bytes,
  with the field written, parse back with it (`icmp_put_parse`,
  `udp_put_parse`); and with UDP's length field the datagram's length,
  `UdpHeader.payload` reads the payload back (`udp_put_payload`);
* a satisfiability law (`inet_sum_sat`) and a vector of the end-around carry
  and the complement (`inet_add_vector`).

`LAWS_ipv4.bend` (2 laws): an IPv4 header built with `build_checksum`
verifies, for every header the parser accepts (version 4, IHL 5 to 15 with
options of the matching length: the round trip's hypotheses), whatever its
checksum field held (`ipv4_build_verifies`); and its hypotheses hold
(`ipv4_build_verifies_sat`).

How the one's complement proofs go (`proof_ones.bend`, generated with the
two proof files by `ref/gen_sum.py`: run `python3 ref/gen_sum.py` in this
directory, `--check` to check they are up to date). The sum of t ones is
modelled on `Nat` by `rep(d, t)` with d = 2^16 - 1: counting up from 0, a
value below d steps to its successor and d steps to 1. Folding early
changes nothing (`rep(rep(x) + y) = rep(x + y)`) and d more ones go once
round the cycle, so every order of summing gives one value. `inet_add` on
two values of at most d computes `rep` of their sum: through bend-osdev-u32's
value laws, the 32-bit sum does not wrap and is `lo + 2^16 hi` with `hi`
0 or 1, which the mask and the shift by 16 read. A byte list then sums to
`rep` of the plain sum of its 16-bit words, and the checksum c of a sum S
has c + S = d, so data with c written in sums to `rep(S + c) = d`. d is never
computed: the lemmas take it as a variable with the facts 1 + d = 2^16 and
d = `U32.to_nat(65535)`, proved without expanding the number (a closed
2^16 is a unary `Nat` the checkers cannot hold). The IPv4 proof shows that
the bytes `build_checksum` writes are those of the header with its checksum
field set to the checksum (by computation on the bits of the fields that
share the checksum's word), so the round trip parses them back.

Not proved for every input: the reverse round trip (building a parsed
header gives back its bytes), covered by vectors and the differential test.

## Tests

`ref/run.sh` compares the package with an independent Python implementation
(`ref/gen.py`: `struct` packing and unpacking written from the header
layouts, `socket.inet_pton` for addresses, and the RFC 1071 checksum written
from the RFC) on random inputs, 696 cases for the default seed: Bend builds
from random fields (some with bits above a field's width) and Python packs
the same; Python packs random headers, some malformed or cut short, and Bend
parses them with the same result or error; IPv4, ICMP, ICMPv6, UDP and TCP
checksums over both pseudo-headers agree; packets with one flipped bit fail
to verify; and the checksum in pieces agrees with the whole.

## Speed

Fields are read and written by bit slicing, so that the round trips can be
proved; that is fine for headers. The checksum assembles each 16-bit word by
bit slicing too, so it is slower than native arithmetic on large payloads.

## Sizes

The checksum and every reader walk their bytes with tail calls, so packet
size has no limit beyond memory on either of Bend 2.0.37's lanes (no
conversion was needed for the JavaScript lane's stack limit). Measured on a
native build (Bend 2.0.37, `bend file.bend -o prog`, WSL2), in one run:
building and verifying a 65,515-byte UDP datagram over IPv4 inside a
65,535-byte IPv4 packet (header checksum, parse, payload, UDP checksum), a
65,515-byte TCP segment, a 65,515-byte ICMP message and a 65,535-byte UDP
datagram over IPv6, with every checksum checked against Python: 0.48 s,
33 MB peak (2.4 s and 550 MB on the JavaScript lane). `check.bend` builds
and verifies the 64 KB UDP datagram as a regression test (0.12 s and 10 MB
natively; 0.7 s and 280 MB on the JavaScript lane).

## Status

Bend 2.0.37: `PROOF.bend` (44 laws), `PROOF_sum.bend` (26 laws) and
`PROOF_ipv4.bend` (2 laws) ALL PROOFS CHECK, and `--verdict` ALL PROOFS
CHECK for each (peaks 0.62 GB, 0.30 GB and 0.58 GB);
`ref/gen_sum.py --check` up to date; `check.bend` passes, `ref/run.sh` 696
cases match, `scripts/deps.sh` ok.
