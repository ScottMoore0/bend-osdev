# Text forms of TCP segments, actions and states, for logs and tests.
#
# A segment shows as "<flags> seq=<n> ack=<n> wnd=<n> len=<n>", the flags as
# letters (S SYN, A ACK, F FIN, R RST, P PSH), an MSS option as " mss=<n>".
import Base
import ../bytes/bytes.bend as B
import ./segment.bend as G
import ./tcp.bend as T

def TcpShow.if(c: Bool, s: String) -> String:
  match c:
    case True{}:
      s
    case False{}:
      ""

def TcpShow.flags(+f: U32) -> String:
  TcpShow.if(G.TcpSeg.has(f, 2), "S") ++ TcpShow.if(G.TcpSeg.has(f, 16), "A") ++ TcpShow.if(G.TcpSeg.has(f, 1), "F") ++ TcpShow.if(G.TcpSeg.has(f, 4), "R") ++ TcpShow.if(G.TcpSeg.has(f, 8), "P")

def TcpShow.mss(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      ""
    case Some{v}:
      " mss=" ++ U32.show(v)

def TcpShow.seg(s: G.TcpSeg) -> String:
  match s:
    case G.TcpSeg{q, a, +f, w, m, d}:
      TcpShow.flags(f) ++ " seq=" ++ U32.show(q) ++ " ack=" ++ U32.show(a) ++ " wnd=" ++ U32.show(w) ++ " len=" ++ Nat.show(B.Octets.len(d)) ++ TcpShow.mss(m)

def TcpShow.error(e: T.TcpError) -> String:
  match e:
    case T.TcpErrNoConnection{}:
      "no connection"
    case T.TcpErrExists{}:
      "exists"
    case T.TcpErrClosing{}:
      "closing"

def TcpShow.note(n: T.TcpNote) -> String:
  match n:
    case T.TcpNoteEstablished{}:
      "established"
    case T.TcpNotePeerClosed{}:
      "peer closed"
    case T.TcpNoteReset{}:
      "reset"
    case T.TcpNoteRefused{}:
      "refused"
    case T.TcpNoteTimedOut{}:
      "timed out"
    case T.TcpNoteQueued{k}:
      "queued " ++ U32.show(k)
    case T.TcpNoteError{e}:
      "error " ++ TcpShow.error(e)
    case T.TcpNoteClosed{}:
      "closed"

def TcpShow.timer(t: T.TcpTimer) -> String:
  match t:
    case T.TcpTimerRtx{}:
      "rtx"
    case T.TcpTimerTimeWait{}:
      "time-wait"

def TcpShow.action(a: T.TcpAction) -> String:
  match a:
    case T.TcpOut{s}:
      "send " ++ TcpShow.seg(s)
    case T.TcpDeliver{d}:
      "deliver " ++ B.Octets.to_string(d)
    case T.TcpNotify{n}:
      "note " ++ TcpShow.note(n)
    case T.TcpSetTimer{t, at}:
      "timer " ++ TcpShow.timer(t) ++ " " ++ U32.show(at)
    case T.TcpStopTimer{t}:
      "stop " ++ TcpShow.timer(t)

def TcpShow.actions(xs: List<&2, T.TcpAction>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      TcpShow.actions(t, acc ++ "; " ++ TcpShow.action(h))
