# Laws of stream.bend's CrXor, for every keystream generator: the same
# statements as LAWS.bend's xor_involution, xor_streaming_data and
# xor_streaming_state, in a pair of their own so that a proof elsewhere can
# use them without importing PROOF.bend (and with it every generic proof);
# PROOF.bend proves its three from these.
import Base
import ../bytes/bytes.bend as B
import ./stream.bend as St

# the cipher is its own inverse: from one state, applied twice, the data
# comes back
law xor_involution:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +m: B.Octets
  {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, m)))) == m : B.Octets}

# data in pieces: the output of a ++ b is the output of a, then the output of
# b from the state after a
law xor_streaming_data:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == B.Octets.append(St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, a)), St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, a)), b))) : B.Octets}

law xor_streaming_state:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, a)), b)) : S}
