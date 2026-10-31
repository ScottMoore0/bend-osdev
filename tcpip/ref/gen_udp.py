#!/usr/bin/env python3
"""UDP receive vectors from Python's struct and RFC 768 Internet checksum.

Generate wire bytes independently of netheaders, including surplus area bytes
(RFC 9868 sections 7-9), corruption, absent checksums and invalid lengths.
"""
from pathlib import Path
import struct


def checksum(data):
    data += b"\0" * (len(data) % 2)
    total = sum(struct.unpack("!%dH" % (len(data) // 2), data))
    while total >> 16:
        total = (total & 65535) + (total >> 16)
    return (~total) & 65535


def datagram(payload, length=None, zero=False):
    length = 8 + len(payload) if length is None else length
    wire = struct.pack("!HHHH", 1234, 53, length, 0) + payload
    if not zero:
        pseudo = struct.pack("!IIBBH", 1, 2, 0, 17, len(wire))
        ck = checksum(pseudo + wire) or 65535
        wire = wire[:6] + struct.pack("!H", ck) + wire[8:]
    return wire


def octets(data):
    return "B.Octets.of_list([%s])" % ", ".join(map(str, data))


cases = []
for size in range(6):
    payload = bytes(range(65, 65 + size))
    for surplus in (b"", b"\1", b"\1\2", b"\0\0\xff"):
        for zero in (False, True):
            wire = datagram(payload, zero=zero) + surplus
            cases.append((wire, payload))
            if not zero:
                bad = bytearray(wire)
                bad[8 if payload else 0] ^= 1
                cases.append((bytes(bad), None))
# Invalid lengths must fail even with an absent checksum.
for length in (0, 1, 7, 12, 65535):
    cases.append((datagram(b"hi!", length, zero=True), None))
# A truncated header, and a checksum-bearing truncated datagram.
for size in range(8):
    cases.append((datagram(b"hi!")[:size], None))
cases.append((datagram(b"hi!")[:-1], None))

source = """import Base
import ../../bytes/bytes.bend as B
import ../udp.bend as U

def matches(actions: List<&2, U.UdpAction>, want: Maybe<&2, B.Octets>) -> Bool:
  match actions want:
    case Nil{} None{}:
      True{}
    case Con{U.UdpDeliver{tag, src, sport, dport, data}, Nil{}} Some{expected}:
      Bool.and(U32.is_eq(tag, 9), Bool.and(U32.is_eq(src, 1), Bool.and(U32.is_eq(sport, 1234), Bool.and(U32.is_eq(dport, 53), B.Octets.is_eq(data, expected)))))
    case _ _:
      False{}

def received(wire: B.Octets) -> List<&2, U.UdpAction>:
  st = Pair.fst(U.UdpState, List<&2, U.UdpAction>, U.Udp.bind(U.UdpState.new(2), 53, 9))
  Pair.snd(U.UdpState, List<&2, U.UdpAction>, U.Udp.recv(st, 1, 2, wire))

def main() -> IO(Unit):
  do IO<Unit>:
"""
for wire, payload in cases:
    want = "None{}" if payload is None else "Some{%s}" % octets(payload)
    source += "    IO.print(Bool.show(matches(received(%s), %s)))\n" % (octets(wire), want)
root = Path(__file__).resolve().parent
(root / "udp_cases.bend").write_text(source)
(root / "udp_expected.txt").write_text("True\n" * len(cases))
print(len(cases))
