import Base
import ./dim.bend as D

def mode(m: D.DimMode) -> String:
  match m:
    case D.DimGoing{True{}, False{}}:
      "right"
    case D.DimGoing{False{}, False{}}:
      "left"
    case D.DimGoing{True{}, True{}}:
      "probe-right"
    case D.DimGoing{False{}, True{}}:
      "probe-left"
    case D.DimParked{t}:
      "parked" ++ Nat.show(t)
    case D.DimSettled{}:
      "settled"

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

def main() -> IO(Unit):
  +p = D.DimParams.default()
  +p3 = {D.DimParams{D.DimParams.profiles_default(), 0n, 10, 3n, D.DimParams.chain_default()} : D.DimParams}
  +one = {D.DimParams{[D.DimProfile{50, 50}], 0n, 10, 3n, D.DimParams.chain_default()} : D.DimParams}
  do IO<Unit>:
    IO.print("start: " ++ Nat.show(D.Dim.index(D.Dim.new(p))) ++ " " ++ usec(D.Dim.profile(p, D.Dim.new(p))))
    IO.print("climb:" ++ trace([ms(1000000), ms(1200000), ms(1400000), ms(1300000), ms(1300000), ms(1000000), ms(1000000)], p, D.Dim.new(p)))
    IO.print("edge: " ++ trace([ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000), ms(1000000)], p3, D.Dim.new(p3)))
    IO.print("top:  " ++ trace([ms(100), ms(200), ms(400), ms(800), ms(1600), ms(3200), ms(3200), ms(3200), ms(3200), ms(3200), ms(3200), ms(3200)], p3, D.Dim.new(p3)))
    IO.print("one:  " ++ trace([ms(100), ms(200), ms(200), ms(200), ms(200), ms(200)], one, D.Dim.new(one)))
    IO.print("skip: " ++ trace([D.DimSample{1, 1, 1, 1, 0}, ms(100), D.DimSample{9, 9, 9, 9, 0}, ms(200)], p, D.Dim.new(p)))
    IO.print("final profile: " ++ usec(D.Dim.profile(p, D.Dim.run(p, D.Dim.new(p), [ms(1000000), ms(1200000), ms(1400000)]))))

#|start: 0 2us/256
#|climb: 0:right 1*:right 2*:right 2:parked0 2:parked0 1*:left 1:parked0
#|edge:  0:right 0:parked0 0:parked1 0:parked2 1*:probe-right 1:settled 1:settled 1:settled
#|top:   0:right 1*:right 2*:right 3*:right 4*:right 4:parked0 4:parked1 4:parked2 3*:probe-left 3:settled 3:settled 3:settled
#|one:   0:right 0:parked0 0:parked0 0:parked0 0:parked0 0:parked0
#|skip:  0:right 0:right 0:right 1*:right
#|final profile: 32us/64
