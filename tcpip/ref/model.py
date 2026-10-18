"""An independent model of bend-osdev-tcpip's TCP connection, written from
RFC 9293 (TCP), RFC 6298 (the retransmission timer) and RFC 5681 (Reno), and
from the choices the package's README states where those leave room. It
shares an author with the package; it is written as ordinary Python, not
translated from the Bend code.

It also models sim.bend's two-endpoint network, so that a script of events
gives the same trace in both.
"""

M32 = 0xFFFFFFFF
FIN, SYN, RST, PSH, ACK = 1, 2, 4, 8, 16

def u(x):
    return x & M32

def seq_lt(a, b):
    d = u(b - a)
    return 0 < d < 2 ** 31

def seq_le(a, b):
    return a == b or seq_lt(a, b)

def seq_max(a, b):
    return b if seq_lt(a, b) else a

def in_window(x, start, n):
    return seq_le(start, x) and seq_lt(x, u(start + n))

def reached(now, at):
    return seq_le(at, now)

# The states and their names
CLOSED, LISTEN, SYN_SENT, SYN_RCVD, ESTAB, FW1, FW2, CLOSE_WAIT, CLOSING, LAST_ACK, TIME_WAIT = range(11)
NAMES = ["CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED", "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING", "LAST-ACK", "TIME-WAIT"]

class Options:
    def __init__(self, mss=1460, rcv_buf=65535, snd_buf=65535, iw_bytes=4380, msl=120000, retries=8, syn_retries=7, nagle=True, app_reads=False, ooo_limit=64, rto=(1000, 1000, 60000, 1, 3000)):
        self.mss, self.rcv_buf, self.snd_buf, self.iw_bytes, self.msl = mss, rcv_buf, snd_buf, iw_bytes, msl
        self.retries, self.syn_retries, self.nagle, self.app_reads, self.ooo_limit = retries, syn_retries, nagle, app_reads, ooo_limit
        self.rto_initial, self.rto_min, self.rto_max, self.rto_g, self.rto_after_syn = rto

    def bend(self):
        b = lambda x: "True{}" if x else "False{}"
        return "T.TcpOptions{%d, %d, %d, %d, %d, %d, %d, %s, %s, %d, R.RtoParams{%d, %d, %d, %d, %d}}" % (
            self.mss, self.rcv_buf, self.snd_buf, self.iw_bytes, self.msl, self.retries, self.syn_retries,
            b(self.nagle), b(self.app_reads), self.ooo_limit, self.rto_initial, self.rto_min, self.rto_max, self.rto_g, self.rto_after_syn)

# RFC 6298, with 8 * SRTT and 4 * RTTVAR kept as integers
class Rto:
    def __init__(self, o):
        self.o = o
        self.srtt8 = self.rttvar4 = 0
        self.rto = min(o.rto_initial, o.rto_max)
        self.sampled = False

    def clamp(self, x):
        return min(max(x, self.o.rto_min), self.o.rto_max)

    def sample(self, r):
        r = u(r)
        if not self.sampled:
            s, v = u(r * 8), u(r * 2)
        else:
            v = u(u(self.rttvar4 - (self.rttvar4 >> 2)) + abs((self.srtt8 >> 3) - r))
            s = u(u(self.srtt8 - (self.srtt8 >> 3)) + r)
        self.srtt8, self.rttvar4, self.sampled = s, v, True
        self.rto = self.clamp(u((s >> 3) + max(self.o.rto_g, v)))

    def backoff(self):
        self.rto = min(self.rto * 2, self.o.rto_max) if self.rto < 2 ** 31 else self.o.rto_max

    def syn_lost(self):
        if not self.sampled:
            self.rto = min(self.o.rto_after_syn, self.o.rto_max)

# Reno (RFC 5681)
CAP = 1073741823

class Reno:
    def __init__(self, smss, iw):
        self.cwnd, self.ssthresh, self.dupacks, self.recovering = iw, 65535, 0, False

    def on_ack(self, acked, smss, flight):
        if self.recovering:
            self.cwnd = self.ssthresh
        elif self.cwnd < self.ssthresh:
            self.cwnd = min(self.cwnd + min(acked, smss), CAP)
        else:
            self.cwnd = min(self.cwnd + max(1, (smss * smss) // max(self.cwnd, 1)), CAP)
        self.dupacks, self.recovering = 0, False

    def halve(self, flight, smss):
        return max(flight >> 1, 2 * smss)

    def on_dupack(self, smss, flight):
        self.dupacks += 1
        if self.recovering:
            self.cwnd = min(self.cwnd + smss, CAP)
            return False
        if self.dupacks == 3:
            self.ssthresh = self.halve(flight, smss)
            self.cwnd = self.ssthresh + 3 * smss
            self.recovering = True
            return True
        return False

    def on_timeout(self, smss, flight):
        self.ssthresh = self.halve(flight, smss)
        self.cwnd, self.dupacks, self.recovering = smss, 0, False

class Seg:
    def __init__(self, seq, ack, flags, wnd, mss=None, data=b""):
        self.seq, self.ack, self.flags, self.wnd, self.mss, self.data = u(seq), u(ack), flags, wnd, mss, data

    def has(self, f):
        return bool(self.flags & f)

    def length(self):
        return len(self.data) + self.has(SYN) + self.has(FIN)

    def show(self):
        fl = "".join(c for f, c in ((SYN, "S"), (ACK, "A"), (FIN, "F"), (RST, "R"), (PSH, "P")) if self.flags & f)
        s = "%s seq=%d ack=%d wnd=%d len=%d" % (fl, self.seq, self.ack, self.wnd, len(self.data))
        return s + (" mss=%d" % self.mss if self.mss is not None else "")

# The receive queue: pieces held by stream offset, delivered in order
class RcvQ:
    def __init__(self):
        self.next, self.held = 0, []

    def insert(self, limit, rel, data):
        at = self.next + rel
        if data and (rel == 0 or len(self.held) < limit):
            for i, (a, d) in enumerate(self.held):
                if at < a:
                    self.held.insert(i, (at, data)); break
                if at == a:
                    if len(data) > len(d):
                        self.held[i] = (at, data)
                    break
            else:
                self.held.append((at, data))
        out = b""
        while self.held and self.held[0][0] <= self.next:
            a, d = self.held.pop(0)
            fresh = d[self.next - a:]
            out += fresh
            self.next += len(fresh)
        return out

class Conn:
    def __init__(self, o):
        self.o, self.state = o, CLOSED
        self.passive = False
        self.iss = self.una = self.nxt = self.max = self.wnd = self.wl1 = self.wl2 = 0
        self.smss, self.buf, self.bseq, self.fin = 536, b"", 0, False
        self.irs = self.rnxt = 0
        self.q, self.unread = RcvQ(), 0
        self.rto, self.rtx_at, self.tw_at, self.retx, self.rtt, self.syn_lost = Rto(o), None, None, 0, None, False
        self.cc = Reno(536, self.iw(536))

    # derived values
    def iw(self, smss):
        return smss if self.syn_lost else min(4 * smss, max(2 * smss, self.o.iw_bytes))

    def rwnd(self):
        return min(self.o.rcv_buf - min(self.unread, self.o.rcv_buf), 65535)

    def fin_seq(self):
        return u(self.bseq + len(self.buf))

    def syn_acked(self):
        return seq_lt(self.iss, self.una)

    def fin_acked(self):
        return self.fin and seq_lt(self.fin_seq(), self.una)

    def outstanding(self):
        return seq_lt(self.una, self.max)

    def off(self, x):
        return 0 if seq_lt(x, self.bseq) else u(x - self.bseq)

    def unsent(self):
        return max(len(self.buf) - self.off(self.nxt), 0)

    def usable(self):
        edge = u(self.una + min(self.wnd, self.cc.cwnd))
        return u(edge - self.nxt) if seq_lt(self.nxt, edge) else 0

    def needs_probe(self):
        return self.unsent() > 0 and self.usable() == 0 and not self.outstanding()

    # segments
    def ack_seg(self):
        return Seg(self.nxt, self.rnxt, ACK, self.rwnd())

    def syn_seg(self, has_peer):
        if has_peer:
            return Seg(self.iss, self.rnxt, SYN | ACK, self.rwnd(), self.o.mss)
        return Seg(self.iss, 0, SYN, self.rwnd(), self.o.mss)

    def resend_first(self, has_peer):
        if not self.syn_acked():
            return self.syn_seg(has_peer)
        off = self.off(self.una)
        n = min(self.smss, max(len(self.buf) - off, 0))
        fin_now = self.fin and seq_lt(self.fin_seq(), self.max) and off + n == len(self.buf)
        return Seg(self.una, self.rnxt, ACK | (FIN if fin_now else 0) | (PSH if n else 0), self.rwnd(), None, self.buf[off:off + n])

    def emit(self, n, fin_now, now, acts):
        off = self.off(self.nxt)
        acts.append(("send", Seg(self.nxt, self.rnxt, ACK | (FIN if fin_now else 0) | (PSH if n else 0), self.rwnd(), None, self.buf[off:off + n])))
        nxt2 = u(self.nxt + n + fin_now)
        fresh = seq_le(self.max, self.nxt)
        self.max = seq_max(self.max, nxt2)
        self.nxt = nxt2
        if fresh and self.rtt is None:
            self.rtt = (nxt2, now)

    def output(self, now, acts):
        sent = False
        for _ in range(self.unsent() + 1):
            off = self.off(self.nxt)
            n = min(self.smss, max(len(self.buf) - off, 0), self.usable())
            fin_now = self.fin and off + n == len(self.buf)
            hold = self.o.nagle and 0 < n < self.smss and seq_lt(self.una, self.nxt)
            if hold or not (n > 0 or fin_now):
                break
            self.emit(n, fin_now, now, acts)
            sent = True
        return sent

    def open_tcb(self, now, isn, passive, wnd, wl1, smss):
        self.passive = passive
        self.iss, self.una, self.nxt, self.max = isn, isn, u(isn + 1), u(isn + 1)
        self.wnd, self.wl1, self.wl2, self.smss = wnd, wl1, isn, smss
        self.buf, self.bseq, self.fin = b"", u(isn + 1), False
        self.rto, self.rtx_at, self.tw_at, self.retx, self.rtt, self.syn_lost = Rto(self.o), None, None, 0, (u(isn + 1), now), False

    def peer_smss(self, mss):
        return min(536 if mss is None else mss, self.o.mss)

    def new_rcv(self, sq):
        self.irs, self.rnxt, self.q, self.unread = sq, u(sq + 1), RcvQ(), 0

    # one event; answers the actions
    def step(self, ev, now, isn):
        st = self.state
        old = (self.rtx_at, self.tw_at)
        acts, go, k = [], False, ("none",)
        self.ack_now, self.acked_new = False, False
        kind = ev[0]
        if kind == "open":
            if st != CLOSED:
                acts.append(("note", "error exists"))
            elif ev[1]:
                self.open_tcb(now, isn, False, 0, 0, self.o.mss)
                self.irs = self.rnxt = 0
                self.q, self.unread = RcvQ(), 0
                acts.append(("send", self.syn_seg(False)))
                k = ("active",)
            else:
                self.passive = True
                k = ("passive",)
        elif kind == "send":
            if st in (CLOSED, LISTEN):
                acts.append(("note", "error no connection"))
            elif st in (SYN_SENT, SYN_RCVD, ESTAB, CLOSE_WAIT):
                take = ev[1][:max(self.o.snd_buf - len(self.buf), 0)]
                self.buf += take
                acts.append(("note", "queued %d" % len(take)))
            else:
                acts.append(("note", "error closing"))
        elif kind == "read":
            if st >= SYN_RCVD:
                w1 = self.rwnd()
                self.unread -= min(ev[1], self.unread)
                w2 = self.rwnd()
                step = min(self.o.rcv_buf >> 1, self.smss)
                self.ack_now = (w1 == 0 or step <= w2 - w1) and w1 != w2
        elif kind == "close":
            if st == CLOSED:
                acts.append(("note", "error no connection"))
            elif st in (LISTEN, SYN_SENT):
                k = ("close",)
            elif st in (SYN_RCVD, ESTAB, CLOSE_WAIT):
                self.fin = True
                k = ("close",)
            else:
                acts.append(("note", "error closing"))
        elif kind == "abort":
            if st == CLOSED:
                acts.append(("note", "error no connection"))
            else:
                if st in (SYN_RCVD, ESTAB, FW1, FW2, CLOSE_WAIT):
                    acts.append(("send", Seg(self.nxt, 0, RST, 0)))
                k = ("abort",)
        elif kind == "recv":
            k = self.arrive(ev[1], now, isn, acts)
        elif kind == "fire":
            k = self.fire(ev[1], now, acts)
        return self.finish(st, k, now, old, acts)

    def fire(self, timer, now, acts):
        if timer == "time-wait":
            return ("twend",) if self.tw_at is not None and reached(now, self.tw_at) else ("none",)
        if self.rtx_at is None or not reached(now, self.rtx_at):
            return ("none",)
        if not self.syn_acked():
            if self.retx >= self.o.syn_retries:
                return ("giveup",)
            acts.append(("send", self.resend_first(self.state != SYN_SENT)))
            self.backed_off(now, True)
            return ("none",)
        if self.outstanding():
            if self.retx >= self.o.retries:
                return ("giveup",)
            flight = u(self.max - self.una)
            self.nxt = self.una
            self.backed_off(now, False)
            self.cc.on_timeout(self.smss, flight)
            return ("none",)
        if self.unsent() > 0 and self.retx < self.o.retries:
            self.backed_off(now, False)
            self.rtt = None
            self.emit(1, False, now, acts)
        else:
            self.rtx_at = None
        return ("none",)

    def backed_off(self, now, syn):
        self.rto.backoff()
        self.rtx_at = u(now + self.rto.rto)
        self.retx += 1
        self.rtt = None
        self.syn_lost = self.syn_lost or syn

    def arrive(self, s, now, isn, acts):
        st = self.state
        if st == CLOSED:
            if not s.has(RST):
                acts.append(("send", Seg(s.ack, 0, RST, 0) if s.has(ACK) else Seg(0, u(s.seq + s.length()), RST | ACK, 0)))
            return ("none",)
        if st == LISTEN:
            if s.has(RST):
                return ("none",)
            if s.has(ACK):
                acts.append(("send", Seg(s.ack, 0, RST, 0)))
                return ("none",)
            if not s.has(SYN):
                return ("none",)
            self.open_tcb(now, isn, True, s.wnd, s.seq, self.peer_smss(s.mss))
            self.new_rcv(s.seq)
            acts.append(("send", self.syn_seg(True)))
            return ("syn",)
        if st == SYN_SENT:
            ackf = s.has(ACK)
            ack_ok = seq_lt(self.iss, s.ack) and seq_le(s.ack, self.max)
            if ackf and not ack_ok:
                if not s.has(RST):
                    acts.append(("send", Seg(s.ack, 0, RST, 0)))
                return ("none",)
            if s.has(RST):
                return ("reset", False) if ackf else ("none",)
            if not s.has(SYN):
                return ("none",)
            self.wnd, self.wl1, self.wl2, self.smss = s.wnd, s.seq, s.ack, self.peer_smss(s.mss)
            self.new_rcv(s.seq)
            if not ackf:
                acts.append(("send", self.syn_seg(True)))
                return ("syn",)
            self.ack_now = True
            if not self.on_ack(s, now, acts):
                return ("none",)
            return self.on_text(s, True, True, acts)
        # synchronized states
        slen, rn, w = s.length(), self.rnxt, self.rwnd()
        if slen == 0 and w == 0:
            acc = s.seq == rn
        elif slen == 0:
            acc = in_window(s.seq, rn, w)
        elif w == 0:
            acc = False
        else:
            acc = in_window(s.seq, rn, w) or in_window(u(s.seq + slen - 1), rn, w)
        acc = acc or s.seq == rn
        if not acc:
            if st == TIME_WAIT and s.has(FIN):
                self.tw_at = u(now + 2 * self.o.msl)
            if not s.has(RST):
                acts.append(("send", self.ack_seg()))
            return ("none",)
        if s.has(RST):
            if s.seq == rn:
                return ("reset", st == SYN_RCVD and self.passive)
            acts.append(("send", self.ack_seg()))
            return ("none",)
        if s.has(SYN):
            if st == SYN_RCVD and self.passive:
                return ("reset", True)
            acts.append(("send", self.ack_seg()))
            return ("none",)
        if not s.has(ACK):
            return ("none",)
        if st == SYN_RCVD and not (seq_lt(self.una, s.ack) and seq_le(s.ack, self.max)):
            acts.append(("send", Seg(s.ack, 0, RST, 0)))
            return ("none",)
        if not self.on_ack(s, now, acts):
            return ("none",)
        return self.on_text(s, st in (SYN_RCVD, ESTAB, FW1, FW2), False, acts)

    # the fifth step; False if the segment is dropped
    def on_ack(self, s, now, acts):
        if seq_lt(self.max, s.ack):
            acts.append(("send", self.ack_seg()))
            return False
        dup = (s.ack == self.una and not s.data and not (s.has(FIN) or s.has(SYN)) and s.wnd == self.wnd and self.outstanding())
        if dup and self.cc.on_dupack(self.smss, u(self.max - self.una)):
            acts.append(("send", self.resend_first(True)))
        new = seq_lt(self.una, s.ack) and seq_le(s.ack, self.max)
        inrange = seq_le(self.una, s.ack) and seq_le(s.ack, self.max)
        if new:
            acked, flight = u(s.ack - self.una), u(self.max - self.una)
            dacked = min(self.off(s.ack), len(self.buf))
            self.una, self.nxt = s.ack, seq_max(self.nxt, s.ack)
            self.buf, self.bseq = self.buf[dacked:], u(self.bseq + dacked)
            if self.rtt is not None and seq_le(self.rtt[0], s.ack):
                self.rto.sample(u(now - self.rtt[1]))
                self.rtt = None
            self.retx = 0
            self.cc.on_ack(acked, self.smss, flight)
        if inrange:
            self.retx = 0
            if seq_lt(self.wl1, s.seq) or (self.wl1 == s.seq and seq_le(self.wl2, s.ack)):
                self.wnd, self.wl1, self.wl2 = s.wnd, s.seq, s.ack
        self.acked_new = new
        return True

    # the seventh and eighth steps
    def on_text(self, s, takes, synsent, acts):
        af = self.fin_acked()
        if not takes:
            self.ack_now = self.ack_now or bool(s.data) or s.has(FIN)
            return ("seg", af, False)
        self.ack_now = self.ack_now or bool(s.data)
        rn = self.rnxt
        dseq0 = u(s.seq + s.has(SYN))
        skip = min(0 if seq_lt(rn, dseq0) else u(rn - dseq0), len(s.data))
        dseq, data = u(dseq0 + skip), s.data[skip:]
        fin_ok = False
        if seq_le(rn, dseq):
            rel = u(dseq - rn)
            kept = data[:max(self.rwnd() - rel, 0)]
            fin_kept = s.has(FIN) and len(kept) == len(data)
            got = self.q.insert(self.o.ooo_limit, rel, kept)
            rn2 = u(rn + len(got))
            fin_ok = fin_kept and rn2 == u(dseq + len(kept))
            if self.o.app_reads:
                self.unread = u(self.unread + len(got))
            self.rnxt = u(rn2 + fin_ok)
            if got:
                acts.append(("deliver", got))
        self.ack_now = self.ack_now or fin_ok
        return ("synack", fin_ok) if synsent else ("seg", af, fin_ok)

    def next_state(self, st, k):
        t = k[0]
        if t in ("reset", "abort", "giveup") and st not in (CLOSED, LISTEN):
            if t == "reset" and st == SYN_RCVD and k[1]:
                return LISTEN
            return CLOSED
        if st == CLOSED:
            return {"passive": LISTEN, "active": SYN_SENT}.get(t, CLOSED)
        if st == LISTEN:
            return {"syn": SYN_RCVD, "close": CLOSED, "abort": CLOSED}.get(t, LISTEN)
        if st == SYN_SENT:
            if t == "synack":
                return CLOSE_WAIT if k[1] else ESTAB
            return {"syn": SYN_RCVD, "close": CLOSED}.get(t, SYN_SENT)
        if t == "close":
            return {SYN_RCVD: FW1, ESTAB: FW1, CLOSE_WAIT: LAST_ACK}.get(st, st)
        if t == "twend":
            return CLOSED if st == TIME_WAIT else st
        if t == "seg":
            af, fin = k[1], k[2]
            if st in (SYN_RCVD, ESTAB):
                return CLOSE_WAIT if fin else ESTAB
            if st == FW1:
                return (TIME_WAIT if fin else FW2) if af else (CLOSING if fin else FW1)
            if st == FW2:
                return TIME_WAIT if fin else FW2
            if st == CLOSING:
                return TIME_WAIT if af else CLOSING
            if st == LAST_ACK:
                return CLOSED if af else LAST_ACK
        return st

    def finish(self, st, k, now, old, acts):
        st2 = self.next_state(st, k)
        entered = st in (SYN_SENT, SYN_RCVD) and st2 in (ESTAB, CLOSE_WAIT)
        if entered:
            if self.syn_lost:
                self.rto.syn_lost()
            self.cc = Reno(self.smss, self.iw(self.smss))
        if st2 == TIME_WAIT and (st != TIME_WAIT or k[0] == "seg"):
            self.tw_at, self.rtx_at = u(now + 2 * self.o.msl), None
        elif st2 in (CLOSED, LISTEN):
            self.tw_at = self.rtx_at = None
        sent = False
        if st2 in (ESTAB, FW1, CLOSE_WAIT, CLOSING, LAST_ACK) and self.syn_acked():
            sent = self.output(now, acts)
        if self.ack_now and not sent and st2 >= SYN_RCVD:
            acts.append(("send", self.ack_seg()))
        if SYN_SENT <= st2 <= LAST_ACK:
            if self.outstanding() or self.needs_probe():
                if self.rtx_at is None or self.acked_new:
                    self.rtx_at = u(now + self.rto.rto)
            else:
                self.rtx_at = None
        if entered:
            acts.append(("note", "established"))
        if (k[0] == "seg" and k[2]) or (k[0] == "synack" and k[1]):
            acts.append(("note", "peer closed"))
        if st2 == CLOSED and st != CLOSED:
            if k[0] == "reset":
                if st in (SYN_SENT, SYN_RCVD):
                    acts.append(("note", "refused"))
                elif ESTAB <= st <= CLOSE_WAIT:
                    acts.append(("note", "reset"))
            elif k[0] == "giveup":
                acts.append(("note", "timed out"))
            acts.append(("note", "closed"))
        for name, a, b in (("rtx", old[0], self.rtx_at), ("time-wait", old[1], self.tw_at)):
            if a is not None and b is None:
                acts.append(("stop", name))
            elif b is not None and a != b:
                acts.append(("timer", name, b))
        self.state = st2
        return acts

def show_action(a):
    if a[0] == "send":
        return "send " + a[1].show()
    if a[0] == "deliver":
        return "deliver " + a[1].decode("latin-1")
    if a[0] == "note":
        return "note " + a[1]
    if a[0] == "timer":
        return "timer %s %d" % (a[1], a[2])
    return "stop " + a[1]

def show_event(ev):
    if ev[0] == "open":
        return "open active" if ev[1] else "open passive"
    if ev[0] == "send":
        return "send " + ev[1].decode("latin-1")
    if ev[0] == "read":
        return "read %d" % ev[1]
    if ev[0] in ("close", "abort"):
        return ev[0]
    if ev[0] == "recv":
        return "recv " + ev[1].show()
    return "fire " + ev[1]

# sim.bend's network
class Side:
    def __init__(self, o, isn):
        self.conn, self.rtx, self.tw, self.isn = Conn(o), None, None, isn

class Sim:
    def __init__(self, oa, ia, ob, ib):
        self.sides = {True: Side(oa, ia), False: Side(ob, ib)}
        self.wire = {True: [], False: []}   # segments in flight to that side
        self.now, self.log = 0, []

    def step(self, side, ev):
        me = self.sides[side]
        acts = me.conn.step(ev, self.now, me.isn)
        for a in acts:
            if a[0] == "timer":
                if a[1] == "rtx":
                    me.rtx = a[2]
                else:
                    me.tw = a[2]
            elif a[0] == "stop":
                if a[1] == "rtx":
                    me.rtx = None
                else:
                    me.tw = None
            elif a[0] == "send":
                self.wire[not side].append(a[1])
        self.log.append("t=%d %s %s => %s%s" % (self.now, "A" if side else "B", show_event(ev), NAMES[me.conn.state], "".join("; " + show_action(a) for a in acts)))

    def deliver(self, side):
        if self.wire[side]:
            self.step(side, ("recv", self.wire[side].pop(0)))

    def drop(self, side):
        if self.wire[side]:
            s = self.wire[side].pop(0)
            self.log.append("t=%d lost to %s: %s" % (self.now, "A" if side else "B", s.show()))

    def fire(self, side):
        me = self.sides[side]
        r = me.rtx is not None and reached(self.now, me.rtx)
        w = me.tw is not None and reached(self.now, me.tw)
        if r:
            self.step(side, ("fire", "rtx"))
        if w:
            self.step(side, ("fire", "time-wait"))

    def cmd(self, c):
        if c[0] == "call":
            self.step(c[1], c[2])
        elif c[0] == "deliver":
            self.deliver(c[1])
        elif c[0] == "drop":
            self.drop(c[1])
        elif c[0] == "tick":
            self.now = u(self.now + c[1])
            self.fire(True)
            self.fire(False)
        elif c[0] == "flush":
            for _ in range(64):
                if not (self.wire[True] or self.wire[False]):
                    break
                self.deliver(False)
                self.deliver(True)

    def trace(self):
        return "\n".join(self.log)
