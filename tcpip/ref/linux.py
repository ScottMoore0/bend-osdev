#!/usr/bin/env python3
"""The Bend stack against Linux's own, on a TAP device.

Run inside a user and network namespace (`unshare -rn python3 linux.py
PEER`), so that no privilege is needed: there we may create tap0, give Linux
10.0.0.1/24 on it, and pass its frames to and from the Bend stack (PEER, a
build of ref/peer.bend, at 10.0.0.2) as UDP datagrams on the namespace's
loopback. Then Linux's own tools and sockets talk to the Bend stack:

  * ping, with small and with fragmented (4000-byte) messages;
  * UDP echo;
  * TCP echo of 200 KB, then a close from each side;
  * the Bend stack's active open to a Linux listener, with a half close;
  * the TCP and UDP echoes again with 10% of frames lost each way, so that
    the Bend stack retransmits (and Linux does).

Prints one line per check ("ok ..." or "FAIL ..."), then "<n> checks".
"""
import fcntl, os, random, select, socket, struct, subprocess, sys, threading, time

TUNSETIFF, IFF_TAP, IFF_NO_PI = 0x400454CA, 0x0002, 0x1000
BEND_IP = "10.0.0.2"

def sh(*args):
    subprocess.run(list(args), check=True)

def free_port():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p

class Bridge(threading.Thread):
    """Frames between tap0 and the Bend peer; loss is the chance a frame is dropped."""
    def __init__(self, tap, sock, peer_port, seed):
        super().__init__(daemon=True)
        self.tap, self.sock, self.peer = tap, sock, ("127.0.0.1", peer_port)
        self.loss, self.rng, self.stop = 0.0, random.Random(seed), False
        self.frames = [0, 0]
    def lose(self):
        return self.loss > 0 and self.rng.random() < self.loss
    def run(self):
        while not self.stop:
            r, _, _ = select.select([self.tap, self.sock], [], [], 0.1)
            if self.tap in r:
                f = os.read(self.tap, 65536)
                self.frames[0] += 1
                if not self.lose():
                    self.sock.sendto(f, self.peer)
            if self.sock in r:
                f, _ = self.sock.recvfrom(65536)
                self.frames[1] += 1
                if not self.lose():
                    os.write(self.tap, f)

results = []
def check(name, ok, detail=""):
    results.append(ok)
    print(("ok " if ok else "FAIL ") + name + ("" if ok else ": " + detail), flush=True)

def ping(size):
    r = subprocess.run(["ping", "-c", "3", "-i", "0.2", "-W", "3", "-s", str(size), BEND_IP], capture_output=True, text=True)
    return r.returncode == 0, r.stdout[-300:] + r.stderr[-300:]

def udp_echo(n, tries=1):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.settimeout(1.0)
    data = bytes(random.Random(n).randrange(256) for _ in range(n))
    for _ in range(tries):
        s.sendto(data, (BEND_IP, 7))
        try:
            got, addr = s.recvfrom(65536)
            s.close()
            return got == data and addr == (BEND_IP, 7), "got %d bytes from %s" % (len(got), addr)
        except socket.timeout:
            pass
    s.close()
    return False, "no answer"

def tcp_echo(n, timeout):
    data = bytes(random.Random(n).randrange(256) for _ in range(n))
    s = socket.create_connection((BEND_IP, 7), timeout=timeout)
    s.settimeout(timeout)
    got = bytearray()
    sent = 0
    while sent < len(data):
        sent += s.send(data[sent:sent + 4096])
        while True:
            r, _, _ = select.select([s], [], [], 0)
            if not r:
                break
            chunk = s.recv(65536)
            if not chunk:
                break
            got += chunk
    s.shutdown(socket.SHUT_WR)
    while True:
        chunk = s.recv(65536)
        if not chunk:
            break
        got += chunk
    s.close()
    return bytes(got) == data, "%d of %d bytes back, equal prefix %s" % (len(got), len(data), bytes(got) == data[:len(got)])

def main():
    peer = sys.argv[1]
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 2026
    tap = os.open("/dev/net/tun", os.O_RDWR)
    fcntl.ioctl(tap, TUNSETIFF, struct.pack("16sH", b"tap0", IFF_TAP | IFF_NO_PI))
    sh("ip", "link", "set", "lo", "up")
    sh("ip", "addr", "add", "10.0.0.1/24", "dev", "tap0")
    sh("ip", "link", "set", "tap0", "up")
    bsock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    bsock.bind(("127.0.0.1", 0))
    peer_port = free_port()
    # the listener the Bend stack's active open connects to
    lst = socket.socket()
    lst.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    lst.bind(("10.0.0.1", 9000))
    lst.listen(1)
    bridge = Bridge(tap, bsock, peer_port, seed)
    bridge.start()
    proc = subprocess.Popen([peer, str(bsock.getsockname()[1]), str(peer_port), "240"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    time.sleep(0.5)
    try:
        # the active open: greeting, then the Bend side closes; we answer on
        # the half-closed connection and close
        lst.settimeout(10)
        try:
            c, addr = lst.accept()
            c.settimeout(10)
            got = b""
            while True:
                chunk = c.recv(4096)
                if not chunk:
                    break
                got += chunk
            c.sendall(b"hi bend")
            c.close()
            check("bend active open, data, half close", got == b"hello from bend\n", repr(got))
        except socket.timeout:
            check("bend active open, data, half close", False, "timed out")
        check("ping 56 bytes", *ping(56))
        check("ping 4000 bytes (fragmented both ways)", *ping(4000))
        check("udp echo 100 bytes", *udp_echo(100))
        check("udp echo 1400 bytes", *udp_echo(1400))
        check("tcp echo 1 byte", *tcp_echo(1, 10))
        check("tcp echo 200000 bytes", *tcp_echo(200000, 30))
        bridge.loss = 0.10
        check("udp echo with 10% loss", *udp_echo(500, tries=10))
        check("tcp echo 50000 bytes with 10% loss", *tcp_echo(50000, 120))
        bridge.loss = 0.0
        check("tcp echo after loss", *tcp_echo(5000, 30))
    finally:
        bsock.sendto(b"quit", ("127.0.0.1", peer_port))
        try:
            out, _ = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            out, _ = proc.communicate()
        bridge.stop = True
    check("bend got the reply on its half-closed connection", "got hi bend" in out, out[-500:])
    check("bend peer ran to the end", out.rstrip().endswith("done"), out[-300:])
    print("%d checks, %d frames from linux, %d from bend" % (len(results), bridge.frames[0], bridge.frames[1]))
    if os.environ.get("PEER_LOG"):
        open(os.environ["PEER_LOG"], "w").write(out)
    sys.exit(0 if all(results) else 1)

main()
