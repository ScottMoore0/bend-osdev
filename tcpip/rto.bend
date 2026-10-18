# The retransmission timeout (RFC 6298, "Computing TCP's Retransmission
# Timer"): a smoothed round-trip time and its variation, measured from
# acknowledged segments, give the time to wait before resending.
#
# Times are milliseconds. The state keeps 8 * SRTT and 4 * RTTVAR, so that
# the RFC's gains (alpha = 1/8, beta = 1/4) are exact in integers:
#   first sample R:   SRTT = R, RTTVAR = R / 2                   (2.2)
#   later samples R:  RTTVAR = 3/4 RTTVAR + 1/4 |SRTT - R|
#                     SRTT = 7/8 SRTT + 1/8 R                    (2.3)
#   RTO = SRTT + max(G, 4 * RTTVAR), then at least min, at most max (2.4, 2.5)
#   on a timeout:     RTO = 2 * RTO, at most max                 (5.5)
import Base

# initial: the RTO before any sample (2.1: 1 second); min, max: the bounds
# (2.4: 1 second; 2.5: at least 60 seconds); granularity: the clock's, G;
# after_syn_loss: the RTO data transmission starts with when the SYN had to be
# resent and no sample was taken (5.7: 3 seconds)
type RtoParams is Data:
  RtoParams{initial: U32, min: U32, max: U32, granularity: U32, after_syn_loss: U32}

# RFC 6298's values
def RtoParams.default() -> RtoParams:
  RtoParams{1000, 1000, 60000, 1, 3000}

def RtoParams.max(p: RtoParams) -> U32:
  match p:
    case RtoParams{i, lo, hi, g, s}:
      hi

# srtt8 = 8 * SRTT, rttvar4 = 4 * RTTVAR, the current RTO, and whether a
# sample has been taken
type Rto is Data:
  Rto{srtt8: U32, rttvar4: U32, rto: U32, sampled: Bool}

# x, at most hi
def Rto.at_most.pick(fits: Bool, x: U32, hi: U32) -> U32:
  match fits:
    case True{}:
      x
    case False{}:
      hi

def Rto.at_most(+x: U32, +hi: U32) -> U32:
  Rto.at_most.pick(U32.is_le(x, hi), x, hi)

def Rto.at_least.pick(below: Bool, x: U32, lo: U32) -> U32:
  match below:
    case True{}:
      lo
    case False{}:
      x

def Rto.at_least(+x: U32, +lo: U32) -> U32:
  Rto.at_least.pick(U32.is_lt(x, lo), x, lo)

# x within [min, max]; max wins if min > max
def Rto.clamp(p: RtoParams, x: U32) -> U32:
  match p:
    case RtoParams{i, lo, hi, g, s}:
      Rto.at_most(Rto.at_least(x, lo), hi)

# the estimator before any sample (2.1)
def Rto.start(p: RtoParams) -> Rto:
  match p:
    case RtoParams{+i, lo, +hi, g, s}:
      Rto{0, 0, Rto.at_most(i, hi), False{}}

# the current timeout, in milliseconds
def Rto.current(r: Rto) -> U32:
  match r:
    case Rto{s, v, rto, k}:
      rto

def Rto.sampled(r: Rto) -> Bool:
  match r:
    case Rto{s, v, rto, k}:
      k

# the smoothed round-trip time, in milliseconds (0 before a sample)
def Rto.srtt(r: Rto) -> U32:
  match r:
    case Rto{s, v, rto, k}:
      U32.shrn(s, 3n)

# |a - b|
def Rto.absdiff.pick(lt: Bool, +a: U32, +b: U32) -> U32:
  match lt:
    case True{}:
      U32.sub(b, a)
    case False{}:
      U32.sub(a, b)

def Rto.absdiff(+a: U32, +b: U32) -> U32:
  Rto.absdiff.pick(U32.is_lt(a, b), a, b)

def Rto.max32.pick(lt: Bool, a: U32, b: U32) -> U32:
  match lt:
    case True{}:
      b
    case False{}:
      a

def Rto.max32(+a: U32, +b: U32) -> U32:
  Rto.max32.pick(U32.is_lt(a, b), a, b)

# RTO from the (scaled) estimates: SRTT + max(G, 4 * RTTVAR), clamped
def Rto.of(+p: RtoParams, +srtt8: U32, +rttvar4: U32) -> Rto:
  match p:
    case RtoParams{i, lo, hi, +g, s}:
      Rto{srtt8, rttvar4, Rto.clamp(p, U32.add(U32.shrn(srtt8, 3n), Rto.max32(g, rttvar4))), True{}}

def Rto.sample.go(sampled: Bool, +p: RtoParams, +srtt8: U32, +rttvar4: U32, +r: U32) -> Rto:
  match sampled:
    case False{}:
      # 2.2: SRTT = R, RTTVAR = R / 2
      Rto.of(p, U32.shln(r, 3n), U32.shl(r))
    case True{}:
      # 2.3: RTTVAR first, from the old SRTT
      +v = U32.add(U32.sub(rttvar4, U32.shrn(rttvar4, 2n)), Rto.absdiff(U32.shrn(srtt8, 3n), r))
      +s = U32.add(U32.sub(srtt8, U32.shrn(srtt8, 3n)), r)
      Rto.of(p, s, v)

# the estimator after a round-trip time sample of rtt milliseconds (a sample
# taken only from a segment that was not retransmitted, Karn's algorithm,
# section 3)
def Rto.sample(+p: RtoParams, r: Rto, +rtt: U32) -> Rto:
  match r:
    case Rto{s, v, rto, k}:
      Rto.sample.go(k, p, s, v, rtt)

# twice x, at most hi (2^31 and more doubles past 32 bits: hi)
def Rto.double.pick(small: Bool, +x: U32, +hi: U32) -> U32:
  match small:
    case True{}:
      Rto.at_most(U32.add(x, x), hi)
    case False{}:
      hi

def Rto.double(+x: U32, +hi: U32) -> U32:
  Rto.double.pick(U32.is_lt(x, 2147483648), x, hi)

# the estimator after the retransmission timer expired (5.5): the timeout
# doubled, at most max
def Rto.backoff(p: RtoParams, r: Rto) -> Rto:
  match p r:
    case RtoParams{i, lo, hi, g, a} Rto{s, v, rto, k}:
      Rto{s, v, Rto.double(rto, hi), k}

# the estimator when data transmission starts after the SYN was resent (5.7):
# without a sample, the timeout is re-initialised to after_syn_loss
def Rto.syn_lost.go(sampled: Bool, +p: RtoParams, r: Rto) -> Rto:
  match sampled:
    case True{}:
      r
    case False{}:
      match p r:
        case RtoParams{i, lo, +hi, g, a} Rto{s, v, rto, k}:
          Rto{s, v, Rto.at_most(a, hi), k}

def Rto.syn_lost(+p: RtoParams, +r: Rto) -> Rto:
  Rto.syn_lost.go(Rto.sampled(r), p, r)
