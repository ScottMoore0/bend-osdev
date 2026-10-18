import Base
import ../word64/word64.bend as W
import ./dim.bend as D

def mode(m: D.DimMode) -> String:
  match m:
    case D.DimGoing{True{}, rs, ls}:
      "right"
    case D.DimGoing{False{}, rs, ls}:
      "left"
    case D.DimParkedTop{}:
      "top"
    case D.DimParkedTired{d, k}:
      "tired" ++ Nat.show(k)

def flag(c: Bool) -> String:
  match c:
    case True{}:
      "*"
    case False{}:
      ""

# the index and mode after each sample; * where the profile changed
def trace(ss: List<&2, D.DimSample>, +p: D.DimParams, st: D.Dim) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{s, rest}:
      +r = D.Dim.step(p, st, s)
      +st1 = D.DimStep.state(r)
      " " ++ Nat.show(D.Dim.index(st1)) ++ flag(D.DimStep.changed(r)) ++ ":" ++ mode(D.Dim.mode(st1)) ++ trace(rest, p, st1)

# an interval of 1 ms with b bytes, b / 1000 packets and 100 events
def ms(+b: U32) -> D.DimSample:
  D.DimSample{U32.div(b, 1000), b, 100, 0, 1000}

def usec(m: Maybe<&2, D.DimProfile>) -> String:
  match m:
    case None{}:
      "none"
    case Some{D.DimProfile{u, k}}:
      U32.show(u) ++ "us/" ++ U32.show(k)

def sample(s: D.DimSample) -> String:
  match s:
    case D.DimSample{p, b, e, c, t}:
      U32.show(p) ++ " " ++ U32.show(b) ++ " " ++ U32.show(e) ++ " " ++ U32.show(c) ++ " " ++ U32.show(t)

def main() -> IO(Unit):
  +p = D.DimParams.default()
  +p3 = {D.DimParams{D.DimParams.profiles_default(), 0n, 10, 2n, 10n, D.DimParams.chain_default()} : D.DimParams}
  +one = {D.DimParams{[D.DimProfile{50, 50}], 0n, 10, 2n, 10n, D.DimParams.chain_default()} : D.DimParams}
  do IO<Unit>:
    IO.print("start: " ++ Nat.show(D.Dim.index(D.Dim.new(p))) ++ " " ++ usec(D.Dim.profile(p, D.Dim.new(p))))
    IO.print("climb:" ++ trace([ms(1000000), ms(1200000), ms(1400000), ms(1300000), ms(1300000), ms(1000000), ms(1000000)], p, D.Dim.new(p)))
    IO.print("same: " ++ trace([ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000)], p3, D.Dim.new(p3)))
    IO.print("top:  " ++ trace([ms(100), ms(200), ms(400), ms(800), ms(1600), ms(3200), ms(3200), ms(3200), ms(3200), ms(3200), ms(3200), ms(3200)], p3, D.Dim.new(p3)))
    IO.print("one:  " ++ trace([ms(100), ms(200), ms(200), ms(200), ms(200), ms(200)], one, D.Dim.new(one)))
    IO.print("skip: " ++ trace([D.DimSample{1, 1, 1, 1, 0}, ms(100), D.DimSample{9, 9, 9, 9, 0}, ms(200)], p, D.Dim.new(p)))
    IO.print("interval: " ++ sample(D.Dim.interval(D.DimCounters{W.W64.from_u32(1000), 4294967290, 7, 3, 0}, D.DimCounters{W.W64.from_u32(2500), 10, 1007, 5, 9})))
    IO.print("parked: " ++ Bool.show(D.Dim.parked(D.Dim.run(p, D.Dim.new(p), [ms(1000), ms(1000)]))))
    IO.print("final profile: " ++ usec(D.Dim.profile(p, D.Dim.run(p, D.Dim.new(p), [ms(1000000), ms(1200000), ms(1400000)]))))

#|start: 0 2us/256
#|climb: 0:right 1*:right 2*:right 2:top 2:top 1*:left 1:top
#|same:  0:right 0:top 0:top 0:top 0:top 0:top 0:top 0:top
#|top:   0:right 1*:right 2*:right 3*:right 4*:right 4:tired0 4:tired1 4:tired2 3*:left 3:top 3:top 3:top
#|one:   0:right 0:tired0 0:tired1 0:tired2 0:tired0 0:tired1
#|skip:  0:right 0:right 0:right 1*:right
#|interval: 16 1000 2 9 1500
#|parked: True
#|final profile: 32us/64
