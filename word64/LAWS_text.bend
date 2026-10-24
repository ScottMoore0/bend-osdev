# bend-osdev-word64's law of decimal text, for every input: W64.show reads
# back as the value. Proved in PROOF_text.bend.
import Base
import ../u32/u32.bend as U
import ./word64.bend as W

# Decimal text: the digits of W64.show(a), read back one by one (Base's
# Nat.read.go, the reader without Nat.read's 2^48 gate), are the value.
law show_reads:
  for +a: W.W64
  {Nat.read.go(W.W64.show(a), 0n) == Some{W.W64.to_nat(a)} : Maybe<&2, Nat>}
