#!/usr/bin/env python3
"""Differential test cases for bend-osdev-apparmor.

Writes ref/cases-NN.bend (Bend programs that load generated policies and
print the answer to each query) and ref/expected.txt (the answers of an
independent Python model of the same documents, apparmor.d(5) and
apparmor(7), written here; it shares an author with the package):
  * random policies: file rules with globs, variables, an alias, an
    include (sometimes twice), qualifiers, exec modes and targets; the
    capability, network, signal, ptrace, mount, dbus and change_profile
    rules; child profiles, hats, attached profiles, profile modes;
  * random queries of every kind on every profile, and execs;
  * edge texts, each loaded by the package and compared with what
    apparmor_parser says.
The model holds each policy as data and renders it to text: it evaluates
the data, the package parses the text. Globs are matched here by Python's
re, through a translation to regular expressions, not by the package's
backtracking matcher.

When apparmor_parser is installed, every generated policy (all of which the
package must load) is also checked with `apparmor_parser -Q -K` (compile,
skip the kernel): it must accept them too. The edge texts are run through
both, and each disagreement is printed as `disagree` with what each said;
the known ones are listed in KNOWN (and in the README).
"""
import os, random, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# Globs: the translation apparmor_parser 4.0.1 makes (README, Experiments)

class GlobError(Exception):
    pass

def glob_regex(text):
    out = []
    i, n = 0, len(text)
    depth = 0
    prev = ''
    slash = False      # the last thing emitted is a '/' a following '/' collapses into
    start = True
    items = [0]        # alternatives seen in each open group
    while i < n:
        c = text[i]
        if c == '\\':
            if i + 1 >= n:
                raise GlobError()
            out.append(re.escape(text[i + 1])); prev = text[i + 1]; slash = False; start = False; i += 2
            continue
        if c == '*':
            if i + 1 < n and text[i + 1] == '*':
                nxt = text[i + 2] if i + 2 < n else ''
                seg = prev == '/' and nxt in ('/', '*', '')
                out.append('[^/].*' if seg else '.*')
                i += 2
            else:
                nxt = text[i + 1] if i + 1 < n else ''
                seg = prev == '/' and nxt in ('/', '')
                out.append('[^/][^/]*' if seg else '[^/]*')
                i += 1
            prev = '*'; slash = False; start = False
            continue
        if c == '?':
            out.append('[^/]'); prev = '?'; slash = False; start = False; i += 1
            continue
        if c == '[':
            j = i + 1
            neg = False
            if j < n and text[j] == '^':
                neg = True; j += 1
            body = []
            first = True
            while True:
                if j >= n:
                    raise GlobError()
                d = text[j]
                if d == ']' and not first:
                    break
                if d == ']' or d == '\\':
                    raise GlobError()
                body.append(d); first = False; j += 1
            if body[-1] == '-':
                raise GlobError()
            cls = ''
            k = 0
            while k < len(body):
                if k + 2 < len(body) and body[k + 1] == '-':
                    cls += re.escape(body[k]) + '-' + re.escape(body[k + 2]); k += 3
                else:
                    cls += re.escape(body[k]); k += 1
            out.append('[' + ('^' if neg else '') + cls + ']')
            prev = ']'; slash = False; start = False; i = j + 1
            continue
        if c == '{':
            out.append('(?:'); depth += 1; items.append(1); prev = '{'; slash = False; start = False; i += 1
            continue
        if c == ',' and depth > 0:
            out.append('|'); items[-1] += 1; prev = ','; slash = False; start = False; i += 1
            continue
        if c == '}':
            if depth == 0 or items[-1] < 2:
                raise GlobError()
            out.append(')'); depth -= 1; items.pop(); prev = '}'; slash = False; start = False; i += 1
            continue
        if c == ']':
            raise GlobError()
        if c == '/':
            if not slash:
                out.append('/')
                slash = not start
            prev = '/'; start = False; i += 1
            continue
        out.append(re.escape(c)); prev = c; slash = False; start = False; i += 1
    if depth != 0:
        raise GlobError()
    return ''.join(out)

def glob_match(text, path):
    return re.fullmatch(glob_regex(text), path, re.S) is not None

def glob_literal(text):
    return not any(c in text for c in '*?[{')

def brace_alts(text):
    """the brace-free alternatives of a pattern's text"""
    # simple explicit stack version
    def expand(s):
        res = ['']
        i = 0
        while i < len(s):
            c = s[i]
            if c == '\\':
                res = [x + s[i:i + 2] for x in res]; i += 2; continue
            if c == '{':
                d, j = 1, i + 1
                parts, k = [], i + 1
                while d:
                    if s[j] == '\\':
                        j += 2; continue
                    if s[j] == '{':
                        d += 1
                    elif s[j] == '}':
                        d -= 1
                        if d == 0:
                            parts.append(s[k:j]); break
                    elif s[j] == ',' and d == 1:
                        parts.append(s[k:j]); k = j + 1
                    j += 1
                sub = [y for p in parts for y in expand(p)]
                res = [x + y for x in res for y in sub]
                i = j + 1
                continue
            res = [x + c for x in res]; i += 1
        return res
    return expand(text)

def alt_prefix(alt):
    """leading literal bytes of a brace-free alternative, after slash collapse and star treatment"""
    n = 0
    prev = ''
    slash = False
    start = True
    i = 0
    while i < len(alt):
        c = alt[i]
        if c in '*?[':
            return n
        if c == '\\':
            n += 1; prev = alt[i + 1]; slash = False; start = False; i += 2; continue
        if c == '/':
            if not slash:
                n += 1; slash = not start
            prev = '/'; start = False; i += 1; continue
        n += 1; prev = c; slash = False; start = False; i += 1
    return n

def glob_rank(text, path):
    if glob_literal(text):
        return 1000000 if glob_match(text, path) else 0
    best = 0
    for a in brace_alts(text):
        if glob_match(a, path):
            best = max(best, alt_prefix(a) + 1)
    return best

# ---------------------------------------------------------------------------
# Variables: one value as itself, several as {v1,v2}; a value's trailing
# '/' is dropped before a '/'

def expand_vars(text, env, pname):
    for _ in range(9):
        if '@{' not in text:
            return text
        out = []
        i = 0
        while i < len(text):
            if text.startswith('@{', i):
                j = text.index('}', i)
                name = text[i + 2:j]
                vals = [pname] if (name == 'profile_name' and pname is not None) else env[name]
                strip = j + 1 < len(text) and text[j + 1] == '/'
                vals = [v[:-1] if strip and v.endswith('/') else v for v in vals]
                out.append(vals[0] if len(vals) == 1 else '{' + ','.join(vals) + '}')
                i = j + 1
            else:
                out.append(text[i]); i += 1
        text = ''.join(out)
    raise KeyError('depth')

# ---------------------------------------------------------------------------
# The decision engine (apparmor.d(5) "Profile Mode", apparmor(7) "Complain mode")

def decide(mode, audit_flag, req, grants, complain_deny=True):
    allow = deny = audit = quiet = 0
    for g_audit, g_deny, p in grants:
        if g_deny:
            deny |= p
            if g_audit:
                audit |= p
            else:
                quiet |= p
        else:
            allow |= p
            if g_audit:
                audit |= p
    granted = allow & ~deny
    cov = req & ~granted == 0
    hit = req & deny != 0
    ok = 'audit' if (audit_flag or req & audit) else 'allow'
    missing = req & ~granted
    logged = audit_flag or (missing & ~(quiet & ~audit)) != 0
    no = 'deny' if logged else 'deny-quiet'
    if mode in ('enforce', 'prompt'):
        return ok if cov else no
    if mode == 'kill':
        return ok if cov else 'kill'
    if mode == 'complain':
        return ok if cov else (no if (complain_deny and hit) else 'complain')
    if mode == 'default_allow':
        return no if hit else ok
    return 'allow'

def allowed(d):
    return d in ('allow', 'audit', 'complain')

# ---------------------------------------------------------------------------
# Policies as data

PERM = {'r': 1, 'w': 2 | 4, 'a': 4, 'l': 8, 'k': 16, 'm': 32, 'x': 64}
QPERM = {'r': 1, 'w': 2, 'a': 4, 'l': 8, 'k': 16, 'm': 32, 'x': 64}

def perms_bits(s):
    b = 0
    for ch in s:
        b |= PERM[ch]
    return b

def qbits(s):
    b = 0
    for ch in s:
        b |= QPERM[ch]
    return b

CAPS = ["chown", "dac_override", "dac_read_search", "fowner", "fsetid", "kill", "setgid", "setuid", "setpcap",
        "linux_immutable", "net_bind_service", "net_broadcast", "net_admin", "net_raw", "ipc_lock", "ipc_owner",
        "sys_module", "sys_rawio", "sys_chroot", "sys_ptrace", "sys_pacct", "sys_admin", "sys_boot", "sys_nice",
        "sys_resource", "sys_time", "sys_tty_config", "mknod", "lease", "audit_write", "audit_control", "setfcap",
        "mac_override", "mac_admin", "syslog", "wake_alarm", "block_suspend", "audit_read", "perfmon", "bpf",
        "checkpoint_restore"]
DOMAINS = ["unix", "inet", "inet6", "netlink", "packet"]
TYPES = ["stream", "dgram", "raw", "seqpacket"]
PROTOS = ["tcp", "udp", "icmp"]
SIGNALS = ["hup", "int", "term", "kill", "usr1", "usr2", "chld", "rtmin+3"]
MOUNTFLAGS = ["ro", "rw", "nodev", "nosuid", "noexec", "atime", "noatime", "bind"]
# options apparmor_parser refuses together in an exact options= set
OPPOSED = [("ro", "rw"), ("suid", "nosuid"), ("dev", "nodev"), ("exec", "noexec"), ("atime", "noatime")]
FSTYPES = ["ext4", "xfs", "tmpfs", "proc"]
WORDS = ["a", "b", "c", "lib", "foo", "x1", "etc"]
XMODES = ["ix", "ux", "Ux", "px", "Px", "cx", "Cx", "pix", "Pix", "cix", "Cix", "pux", "PUx", "cux", "CUx"]

class Rng(random.Random):
    def pick(self, xs):
        return xs[self.randrange(len(xs))]

def gen_segment(r):
    k = r.randrange(12)
    w = r.pick(WORDS)
    if k == 0:
        return '*'
    if k == 1:
        return '**'
    if k == 2:
        return w + '*'
    if k == 3:
        return '*' + w[-1]
    if k == 4:
        return '?' + w[1:]
    if k == 5:
        return '[ab]' + w
    if k == 6:
        return '[^a]*'
    if k == 7:
        return '{' + w + ',' + r.pick(WORDS) + '}'
    if k == 8:
        return '{,' + w + '}'
    return w

def gen_glob(r, use_var):
    segs = [gen_segment(r) for _ in range(r.randrange(1, 4))]
    text = '/' + '/'.join(segs)
    if r.random() < 0.2:
        text += '/'
    if use_var and r.random() < 0.25:
        text = '@{V1}' + text[1:] if r.random() < 0.5 else '@{V1}/' + text[1:]
    return text

def gen_path(r):
    segs = [r.pick(WORDS + ['ab', 'ba', 'zz', 'aa']) for _ in range(r.randrange(1, 4))]
    p = '/' + '/'.join(segs)
    if r.random() < 0.15:
        p = r.pick(['/v1/', '/v2/x/']) + '/'.join(segs)
    if r.random() < 0.15:
        p += '/'
    return p

class Rule:
    pass

def alias_texts(text, aliases):
    out = [text]
    for a, b in aliases:
        if text.startswith(a):
            out.append(b + text[len(a):])
    return out

def gen_file_rule(r, use_var, exec_state, allow_exec=True):
    q = {'audit': r.random() < 0.2, 'deny': r.random() < 0.25, 'owner': r.random() < 0.15}
    text = gen_glob(r, use_var)
    letters = ''
    for ch in 'rwlkm':
        if r.random() < 0.35:
            letters += ch
    if 'w' not in letters and r.random() < 0.2:
        letters += 'a'
    xmode = None
    target = None
    if q['deny']:
        if r.random() < 0.3:
            letters += 'x'
    elif allow_exec and r.random() < 0.25:
        lit = glob_literal(text) and '@' not in text
        if lit or not exec_state['pattern']:
            xmode = r.pick(XMODES)
            if not lit:
                exec_state['pattern'] = True
            elif any(t in exec_state['literals'] for t in alias_texts(text, exec_state['aliases'])):
                xmode = None
            else:
                exec_state['literals'].update(alias_texts(text, exec_state['aliases']))
            if xmode and xmode[0] in 'pPcC' and r.random() < 0.5:
                target = r.pick(['c1', 'h1', 'other', 'nosuch', 'top2'])
    if not letters and not xmode:
        letters = 'r'
    rule = Rule()
    rule.kind = 'file'
    rule.q = q
    rule.text = text
    rule.letters = letters
    rule.xmode = xmode
    rule.target = target
    perm = (' ' if letters and xmode else '').join([letters, xmode or '']) if False else letters + (xmode or '')
    quals = ('audit ' if q['audit'] else '') + ('deny ' if q['deny'] else '') + ('owner ' if q['owner'] else '')
    lead = r.random() < 0.2 and not (target and 'l' in letters)
    body = (perm + ' ' + text) if lead else (text + ' ' + perm)
    rule.src = quals + ('file ' if r.random() < 0.1 else '') + body + ((' -> ' + target) if target else '') + ','
    return rule

def gen_other_rule(r):
    rule = Rule()
    q = {'audit': r.random() < 0.2, 'deny': r.random() < 0.25, 'owner': False}
    quals = ('audit ' if q['audit'] else '') + ('deny ' if q['deny'] else '')
    rule.q = q
    k = r.randrange(7)
    if k == 0:
        rule.kind = 'cap'
        if r.random() < 0.15:
            rule.caps = None
            rule.src = quals + 'capability,'
        else:
            rule.caps = sorted(set(r.pick(range(len(CAPS))) for _ in range(r.randrange(1, 4))))
            rule.src = quals + 'capability ' + ' '.join(CAPS[c] for c in rule.caps) + ','
    elif k == 1:
        rule.kind = 'net'
        rule.domain = r.pick(DOMAINS) if r.random() < 0.7 else None
        rule.stype = rule.proto = None
        x = r.random()
        if x < 0.4:
            rule.stype = r.pick(TYPES)
        elif x < 0.6 and rule.domain in (None, 'inet', 'inet6'):
            rule.proto = r.pick(PROTOS)
            if rule.domain == 'inet6' and rule.proto == 'icmp':
                rule.proto = 'tcp'
        rule.src = quals + ' '.join(['network'] + [w for w in (rule.domain, rule.stype, rule.proto) if w]) + ','
    elif k == 2:
        rule.kind = 'signal'
        acc = r.randrange(4)
        rule.perms = {0: 3, 1: 1, 2: 2, 3: 3}[acc]
        words = {0: '', 1: r.pick(['send', 'w', 'write']), 2: r.pick(['receive', 'r', 'read']), 3: r.pick(['(send, receive)', 'rw', '(send receive)'])}[acc]
        rule.sigs = sorted(set(r.pick(SIGNALS) for _ in range(r.randrange(1, 3)))) if r.random() < 0.6 else None
        rule.peer = r.pick(['p1', 'p*', '/usr/bin/*', '{p1,p2}']) if r.random() < 0.6 else None
        parts = ['signal'] + ([words] if words else [])
        if rule.sigs:
            parts.append('set=(' + ', '.join(rule.sigs) + ')')
        if rule.peer:
            parts.append('peer=' + rule.peer)
        rule.src = quals + ' '.join(parts) + ','
    elif k == 3:
        rule.kind = 'ptrace'
        names = ['read', 'trace', 'readby', 'tracedby']
        if r.random() < 0.3:
            rule.perms = 15
            words = ''
        else:
            chosen = sorted(set(r.randrange(4) for _ in range(r.randrange(1, 3))))
            rule.perms = sum(1 << c for c in chosen)
            words = '(' + ', '.join(names[c] for c in chosen) + ')'
        rule.peer = r.pick(['p1', 'p*', 'unconfined']) if r.random() < 0.6 else None
        rule.src = quals + ' '.join(['ptrace'] + ([words] if words else []) + (['peer=' + rule.peer] if rule.peer else [])) + ','
    elif k == 4:
        rule.kind = 'mount'
        rule.op = r.pick(['mount', 'mount', 'remount', 'umount'])
        rule.fstypes = sorted(set(r.pick(FSTYPES) for _ in range(r.randrange(1, 3)))) if r.random() < 0.5 else None
        rule.opts = []
        parts = [rule.op]
        if rule.fstypes:
            parts.append('fstype=(' + ','.join(rule.fstypes) + ')')
        if r.random() < 0.5:
            exact = r.random() < 0.5
            fl = sorted(set(r.pick(MOUNTFLAGS) for _ in range(r.randrange(1, 3))))
            if exact:
                for a, b in OPPOSED:
                    if a in fl and b in fl:
                        fl.remove(b)
            rule.opts.append((exact, fl))
            parts.append(('options=' if exact else 'options in ') + '(' + ','.join(fl) + ')')
        rule.source = rule.target = None
        if rule.op == 'mount':
            if r.random() < 0.5:
                rule.source = r.pick(['/dev/sda1', '/dev/sd*'])
                parts.append(rule.source)
            if r.random() < 0.5:
                rule.target = r.pick(['/mnt/', '/mnt/**'])
                parts += ['->', rule.target]
        else:
            rule.target = r.pick(['/mnt/', '/mnt/**', '/srv/*/'])
            parts.append(rule.target)
        rule.src = quals + ' '.join(parts) + ','
    elif k == 5:
        rule.kind = 'dbus'
        form = r.randrange(3)
        rule.bus = r.pick(['session', 'system']) if r.random() < 0.6 else None
        rule.path = rule.iface = rule.member = rule.name = rule.pname = rule.plabel = None
        parts = ['dbus']
        if form == 0:
            acc = r.pick([('', 3), ('send', 1), ('receive', 2), ('(send, receive)', 3), ('r', 2), ('w', 1)])
            if r.random() < 0.6:
                rule.path = r.pick(['/org/a', '/org/*'])
            if r.random() < 0.4:
                rule.iface = r.pick(['org.a', 'org.*'])
            if r.random() < 0.3:
                rule.member = r.pick(['Get', 'Set*'])
            if r.random() < 0.3:
                rule.plabel = r.pick(['p1', 'unconfined'])
            if not (rule.path or rule.iface or rule.member or rule.plabel):
                rule.path = '/org/a'
            rule.perms = acc[1]
            if acc[0]:
                parts.append(acc[0])
            if rule.bus:
                parts.append('bus=' + rule.bus)
            if rule.path:
                parts.append('path=' + rule.path)
            if rule.iface:
                parts.append('interface=' + rule.iface)
            if rule.member:
                parts.append('member=' + rule.member)
            if rule.plabel:
                parts.append('peer=(label=' + rule.plabel + ')')
        elif form == 1:
            rule.name = r.pick(['org.a', 'org.*'])
            rule.perms = 4
            if r.random() < 0.5:
                parts.append('bind')
            if rule.bus:
                parts.append('bus=' + rule.bus)
            parts.append('name=' + rule.name)
        else:
            if r.random() < 0.5:
                rule.perms = 8
                parts.append('eavesdrop')
            else:
                rule.perms = 15
            if rule.bus:
                parts.append('bus=' + rule.bus)
        rule.src = quals + ' '.join(parts) + ','
    else:
        rule.kind = 'change'
        rule.exec = r.pick(['/bin/a', '/bin/*']) if r.random() < 0.4 else None
        rule.target = r.pick(['p1', 'p*', '{p1,p2}', '**']) if r.random() < 0.7 else None
        parts = ['change_profile']
        if rule.exec:
            if r.random() < 0.3:
                parts.append('safe')
            parts.append(rule.exec)
        if rule.target:
            parts += ['->', rule.target]
        rule.src = quals + ' '.join(parts) + ','
    return rule

class Profile:
    def __init__(self, name, attach, mode, audit, hat=False):
        self.name, self.attach, self.mode, self.audit, self.hat = name, attach, mode, audit, hat
        self.rules = []
        self.children = []
        self.include_rules = []
        self.include_count = 0

def flags_text(p):
    fl = []
    if p.mode != 'enforce' or random.random() < 0.0:
        fl.append(p.mode)
    if p.audit:
        fl.append('audit')
    return (' flags=(' + ','.join(fl) + ')') if fl else ''

def gen_policy(r, idx):
    use_var = r.random() < 0.6
    pol = {'vars': {}, 'aliases': [], 'profiles': [], 'abs': [], 'idx': idx}
    if use_var:
        pol['vars']['V1'] = r.pick([['/v1/', '/v2/x/'], ['/v1/'], ['/v1', '/v2/x']])
    if r.random() < 0.3:
        pol['aliases'].append(('/a/', '/b/'))
    abs_state = {'pattern': True, 'literals': set(), 'aliases': pol['aliases']}
    pol['abs'] = [gen_file_rule(r, use_var, abs_state, False) for _ in range(r.randrange(1, 4))]
    mode = r.pick(['enforce'] * 5 + ['complain', 'kill', 'default_allow', 'unconfined'])
    main = Profile('main', '/usr/bin/main' if r.random() < 0.5 else None, mode, r.random() < 0.1)
    def fill(p, n):
        st = {'pattern': False, 'literals': set(), 'aliases': pol['aliases']}
        for _ in range(n):
            if r.random() < 0.6:
                p.rules.append(gen_file_rule(r, use_var, st))
            else:
                p.rules.append(gen_other_rule(r))
    fill(main, r.randrange(4, 12))
    if r.random() < 0.7:
        main.include_count = r.pick([1, 1, 2])
    c1 = Profile('c1', r.pick([None, '/usr/bin/c*', '/usr/bin/c1']), r.pick(['enforce', 'enforce', 'complain']), False)
    fill(c1, r.randrange(1, 5))
    main.children.append(c1)
    if r.random() < 0.5:
        h1 = Profile('h1', None, 'enforce', False, hat=True)
        fill(h1, r.randrange(1, 4))
        main.children.append(h1)
    pol['profiles'].append(main)
    other = Profile('other', r.pick(['/usr/bin/o*', '/usr/bin/other', '/usr/bin/{other,top2}']), 'enforce', False)
    fill(other, r.randrange(1, 4))
    pol['profiles'].append(other)
    if r.random() < 0.5:
        top2 = Profile('top2', r.pick(['/usr/bin/t*', '/usr/bin/**']), 'enforce', False)
        fill(top2, 1)
        pol['profiles'].append(top2)
    return pol

def render_profile(p, depth):
    ind = '  ' * depth
    if p.hat:
        head = '^' + p.name + flags_text(p)
    elif depth == 0 and p.attach and p.name.startswith('/'):
        head = p.name + flags_text(p)
    else:
        head = 'profile ' + p.name + ((' ' + p.attach) if p.attach else '') + flags_text(p)
    lines = [ind + head + ' {']
    for _ in range(p.include_count):
        lines.append(ind + '  include <zzaa/abs%d>' % p.idx)
    for x in p.rules:
        lines.append(ind + '  ' + x.src)
    for c in p.children:
        c.idx = p.idx
        lines += render_profile(c, depth + 1)
    lines.append(ind + '}')
    return lines

def render(pol):
    files = {}
    files['zzaa/abs%d' % pol['idx']] = '\n'.join(x.src for x in pol['abs']) + '\n'
    lines = []
    if pol['vars']:
        lines.append('include <zzaa/vars%d>' % pol['idx'])
        files['zzaa/vars%d' % pol['idx']] = ''.join('@{%s} = %s\n' % (k, ' '.join(v)) for k, v in pol['vars'].items())
    for a, b in pol['aliases']:
        lines.append('alias %s -> %s,' % (a, b))
    lines.append('# policy %d' % pol['idx'])
    for p in pol['profiles']:
        p.idx = pol['idx']
        lines += render_profile(p, 0)
    files['main%d' % pol['idx']] = '\n'.join(lines) + '\n'
    return files

# ---------------------------------------------------------------------------
# The model's evaluation

def full_name(path):
    return '//'.join(path)

def file_rules(pol, p):
    rules = list(p.rules)
    if p.include_count:
        rules += pol['abs']
    out = []
    for x in rules:
        if x.kind != 'file':
            continue
        text = expand_vars(x.text, pol['vars'], None)
        out.append((x, text))
        for a, b in pol['aliases']:
            if text.startswith(a):
                out.append((x, b + text[len(a):]))
    return out

def other_rules(p, kind):
    return [x for x in p.rules if x.kind == kind]

def grants_file(pol, p, path, owner):
    gs = []
    for x, text in file_rules(pol, p):
        if x.q['owner'] and not owner:
            continue
        if glob_match(text, path):
            bits = perms_bits(x.letters) | (64 if x.xmode else 0)
            gs.append((x.q['audit'], x.q['deny'], bits))
    return gs

def q_file(pol, p, path, perms, owner):
    return decide(p.mode, p.audit, qbits(perms), grants_file(pol, p, path, owner))

def peer_ok(pat, peer, pname):
    return pat is None or glob_match(expand_vars(pat, {}, pname), peer)

def q_cap(p, cap):
    gs = [(x.q['audit'], x.q['deny'], 1) for x in other_rules(p, 'cap') if x.caps is None or cap in x.caps]
    return decide(p.mode, p.audit, 1, gs)

def q_net(p, d, t, pr):
    gs = [(x.q['audit'], x.q['deny'], 1) for x in other_rules(p, 'net')
          if (x.domain is None or x.domain == d) and (x.stype is None or x.stype == t) and (x.proto is None or x.proto == pr)]
    return decide(p.mode, p.audit, 1, gs)

def q_signal(p, req, sig, peer, pname):
    gs = [(x.q['audit'], x.q['deny'], x.perms) for x in other_rules(p, 'signal')
          if (x.sigs is None or sig in x.sigs) and peer_ok(x.peer, peer, pname)]
    return decide(p.mode, p.audit, req, gs)

def q_ptrace(p, req, peer, pname):
    gs = [(x.q['audit'], x.q['deny'], x.perms) for x in other_rules(p, 'ptrace') if peer_ok(x.peer, peer, pname)]
    return decide(p.mode, p.audit, req, gs)

def mount_opts_ok(opts, qo):
    if not opts:
        return True
    for exact, fl in opts:
        if set(qo) <= set(fl) and (not exact or set(fl) <= set(qo)):
            return True
    return False

def q_mount(p, op, fs, opts, src, tgt):
    gs = []
    for x in other_rules(p, 'mount'):
        if x.op != op:
            continue
        if x.fstypes is not None and not any(glob_match(f, fs) for f in x.fstypes):
            continue
        if not mount_opts_ok(x.opts, opts):
            continue
        if x.source is not None and not glob_match(x.source, src):
            continue
        if x.target is not None and not glob_match(x.target, tgt):
            continue
        gs.append((x.q['audit'], x.q['deny'], 1))
    return decide(p.mode, p.audit, 1, gs)

def q_dbus(p, req, bus, path, iface, member, name, plabel):
    gs = []
    for x in other_rules(p, 'dbus'):
        conds = [(x.bus, bus), (x.path, path), (x.iface, iface), (x.member, member), (x.name, name), (x.plabel, plabel)]
        if all(c is None or glob_match(c, v) for c, v in conds):
            gs.append((x.q['audit'], x.q['deny'], x.perms))
    return decide(p.mode, p.audit, req, gs)

def q_change(p, exe, target):
    gs = []
    for x in other_rules(p, 'change'):
        if x.exec is not None and (exe is None or not glob_match(x.exec, exe)):
            continue
        if x.target is not None and not glob_match(x.target, target):
            continue
        gs.append((x.q['audit'], x.q['deny'], 1))
    return decide(p.mode, p.audit, 1, gs)

def lookup(pol, name):
    parts = name.split('//')
    ps = pol['profiles']
    cur = None
    for part in parts:
        cur = next((q for q in ps if q.name == part), None)
        if cur is None:
            return None
        ps = cur.children
    return cur

def attach_best(profiles, path, prefix):
    best, name, tie = 0, None, False
    for q in profiles:
        a = q.attach if q.attach else (q.name if q.name.startswith('/') else None)
        if not a or q.hat:
            continue
        rk = glob_rank(a, path)
        if rk == 0:
            continue
        nm = (prefix + '//' + q.name) if prefix else q.name
        if rk > best:
            best, name, tie = rk, nm, False
        elif rk == best:
            tie = True
    if best == 0:
        return ('none', None)
    return ('tie', None) if tie else ('one', name)

def fallback(fb, scrub):
    if fb == '':
        return 'no profile'
    if fb == 'i':
        return 'stay'
    return 'unconfined' + (' scrub' if scrub else '')

def exec_unconfined(pol, path):
    k, n = attach_best(pol['profiles'], path, '')
    if k == 'one':
        return 'profile ' + n
    if k == 'tie':
        return 'ambiguous'
    return 'unconfined'

def parse_xmode(m):
    scrub = m[0].isupper()
    kind = m[0].lower()
    fb = ''
    if len(m) == 3:
        fb = 'i' if m[1] == 'i' else 'u'
    return kind, scrub, fb

def q_exec(pol, pname, path, owner):
    p = lookup(pol, pname)
    if p is None:
        return 'unknown profile'
    if p.mode == 'unconfined':
        return exec_unconfined(pol, path)
    d = decide(p.mode, p.audit, 64, grants_file(pol, p, path, owner))
    if not allowed(d):
        return 'denied (%s)' % d
    lit, pat = [], []
    for x, text in file_rules(pol, p):
        if x.q['deny'] or not x.xmode:
            continue
        if x.q['owner'] and not owner:
            continue
        if glob_match(text, path):
            (lit if glob_literal(text) else pat).append((x.xmode, x.target))
    sel = lit if lit else pat
    if not sel:
        return 'stay'
    if any(s != sel[0] for s in sel):
        return 'conflict'
    m, tg = sel[0]
    if m == 'ix':
        return 'stay'
    kind, scrub, fb = parse_xmode(m)
    sc = ' scrub' if scrub else ''
    if kind == 'u':
        return 'unconfined' + sc
    if kind == 'p':
        if tg is not None:
            return ('profile ' + tg + sc) if lookup(pol, tg) is not None else fallback(fb, scrub)
        k, n = attach_best(pol['profiles'], path, '')
    else:
        if tg is not None:
            ok = any(c.name == tg for c in p.children if not c.hat)
            return ('profile ' + pname + '//' + tg + sc) if ok else fallback(fb, scrub)
        k, n = attach_best([c for c in p.children if not c.hat], path, pname)
    if k == 'one':
        return 'profile ' + n + sc
    if k == 'tie':
        return 'ambiguous'
    return fallback(fb, scrub)

# ---------------------------------------------------------------------------
# Writing the cases

def bstr(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../text.bend as X
import ../error.bend as E
import ../perm.bend as P
import ../options.bend as O
import ../profile.bend as PR
import ../eval.bend as V
import ../transitions.bend as TR
import ../rule_file.bend as F
import ../rule_mount.bend as RM
import ../rule_dbus.bend as RD
import ../apparmor.bend as A

def src(n: String, t: String) -> A.AaSource:
  A.AaSource{B.Octets.of_string(n), B.Octets.of_string(t)}

def o(s: String) -> B.Octets:
  B.Octets.of_string(s)

def l(s: String) -> List<&2, U32>:
  X.AaText.of_string(s)

def opts() -> O.AaOptions:
  O.AaOptions.default()

def show.load(r: Result<&2, &2, E.AaError, PR.AaPolicy>) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.AaError.name(e)
    case Done{p}:
      "ok"

def show.ok(r: Result<&2, &2, E.AaError, PR.AaPolicy>) -> String:
  match r:
    case Fail{e}:
      "error"
    case Done{p}:
      "ok"

def pol.of(r: Result<&2, &2, E.AaError, PR.AaPolicy>) -> PR.AaPolicy:
  Result.default(&2, &2, E.AaError, PR.AaPolicy, r, PR.AaPolicy{Nil{}})

def show.d(m: Maybe<&2, V.AaDecision>) -> String:
  match m:
    case None{}:
      "no profile"
    case Some{d}:
      V.AaDecision.show(d)

def bits(n: Nat) -> P.AaPerms:
  P.AaPerms.bit(n)

def mop(n: Nat) -> RM.AaMountOp:
  match n:
    case 0n:
      RM.AaMountOpMount{}
    case 1n+k:
      match k:
        case 0n:
          RM.AaMountOpRemount{}
        case 1n+j:
          RM.AaMountOpUmount{}
'''

def cap_index(name):
    return CAPS.index(name)

def perms_of(bitsv, n):
    return 'P.AaPerms.of_bits([%s])' % ', '.join('True{}' if bitsv >> i & 1 else 'False{}' for i in range(n))

def gen_queries(r, pol, pnames):
    """(bend expression, expected) pairs; the policy variable is p"""
    out = []
    for _ in range(26):
        pname = r.pick(pnames)
        prof = lookup(pol, pname)
        k = r.randrange(10)
        if k <= 3:
            path = gen_path(r)
            perms = ''.join(ch for ch in 'rwalkmx' if r.random() < 0.25) or r.pick('rwm')
            owner = r.random() < 0.5
            exp = q_file(pol, prof, path, perms, owner)
            out.append(('show.d(A.Aa.file(opts(), p, o(%s), o(%s), %s, F.AaFile.perms(%s)))' % (bstr(pname), bstr(path), 'True{}' if owner else 'False{}', bstr(perms)), 'f %s %s %s %s' % (pname, path, perms, 'o' if owner else '-'), exp))
        elif k == 4:
            c = r.randrange(len(CAPS))
            exp = q_cap(prof, c)
            out.append(('show.d(A.Aa.capability(opts(), p, o(%s), %d))' % (bstr(pname), c), 'cap %s %d' % (pname, c), exp))
        elif k == 5:
            d, t, pr = r.pick(DOMAINS), r.pick(TYPES), r.pick(PROTOS + [''])
            exp = q_net(prof, d, t, pr)
            out.append(('show.d(A.Aa.network(opts(), p, o(%s), o(%s), o(%s), o(%s)))' % (bstr(pname), bstr(d), bstr(t), bstr(pr)), 'net %s %s %s %s' % (pname, d, t, pr), exp))
        elif k == 6:
            if r.random() < 0.5:
                req = r.pick([1, 2, 3])
                sig, peer = r.pick(SIGNALS), r.pick(['p1', 'p2', 'px', '/usr/bin/o', 'q'])
                exp = q_signal(prof, req, sig, peer, pname)
                out.append(('show.d(A.Aa.signal(opts(), p, o(%s), %s, o(%s), o(%s)))' % (bstr(pname), perms_of(req, 2), bstr(sig), bstr(peer)), 'sig %s %d %s %s' % (pname, req, sig, peer), exp))
            else:
                req = r.pick([1, 2, 4, 8, 3])
                peer = r.pick(['p1', 'p2', 'unconfined', 'q'])
                exp = q_ptrace(prof, req, peer, pname)
                out.append(('show.d(A.Aa.ptrace(opts(), p, o(%s), %s, o(%s)))' % (bstr(pname), perms_of(req, 4), bstr(peer)), 'ptr %s %d %s' % (pname, req, peer), exp))
        elif k == 7:
            op = r.randrange(3)
            opn = ['mount', 'remount', 'umount'][op]
            fs = r.pick(FSTYPES)
            qo = sorted(set(r.pick(MOUNTFLAGS) for _ in range(r.randrange(0, 3))))
            src = r.pick(['/dev/sda1', '/dev/sdb', '']) if op == 0 else ''
            tgt = r.pick(['/mnt/', '/mnt/x/', '/srv/a/', '/opt/'])
            exp = q_mount(prof, opn, fs, qo, src, tgt)
            ol = '[' + ', '.join('l(%s)' % bstr(x) for x in qo) + ']'
            out.append(('show.d(A.Aa.mount(opts(), p, o(%s), RM.AaMountQuery{mop(%dn), l(%s), %s, l(%s), l(%s)}))' % (bstr(pname), op, bstr(fs), ol, bstr(src), bstr(tgt)), 'mnt %s %s %s %s %s %s' % (pname, opn, fs, ','.join(qo), src, tgt), exp))
        elif k == 8:
            if r.random() < 0.5:
                req = r.pick([1, 2, 4, 8, 3])
                bus = r.pick(['session', 'system'])
                path, iface, member, name, plabel = r.pick(['/org/a', '/org/b', '']), r.pick(['org.a', 'org.b', '']), r.pick(['Get', 'SetX', '']), r.pick(['org.a', 'org.c', '']), r.pick(['p1', 'unconfined', 'q'])
                exp = q_dbus(prof, req, bus, path, iface, member, name, plabel)
                out.append(('show.d(A.Aa.dbus(opts(), p, o(%s), RD.AaDbusQuery{%s, l(%s), l(%s), l(%s), l(%s), l(%s), l(%s), l(%s)}))' % (bstr(pname), perms_of(req, 4), bstr(bus), bstr(path), bstr(iface), bstr(member), bstr(name), bstr(''), bstr(plabel)), 'dbus %s %d %s %s %s %s %s %s' % (pname, req, bus, path, iface, member, name, plabel), exp))
            else:
                exe = r.pick([None, '/bin/a', '/bin/b'])
                tgt = r.pick(['p1', 'p2', 'q', 'pz'])
                exp = q_change(prof, exe, tgt)
                ex = 'None{}' if exe is None else 'Some{o(%s)}' % bstr(exe)
                out.append(('show.d(A.Aa.change_profile(opts(), p, o(%s), %s, o(%s)))' % (bstr(pname), ex, bstr(tgt)), 'chg %s %s %s' % (pname, exe, tgt), exp))
        else:
            # execs: literal exec paths of the profile, attachments, and others
            cands = [t for x, t in file_rules(pol, prof) if x.xmode and glob_literal(t)]
            cands += ['/usr/bin/other', '/usr/bin/c1', '/usr/bin/cx', '/usr/bin/top2', '/usr/bin/t', '/usr/bin/main', '/bin/sh']
            path = r.pick(cands)
            owner = r.random() < 0.7
            exp = q_exec(pol, pname, path, owner)
            out.append(('TR.AaExecResult.show(A.Aa.exec(opts(), p, o(%s), o(%s), %s))' % (bstr(pname), bstr(path), 'True{}' if owner else 'False{}'), 'exec %s %s %s' % (pname, path, 'o' if owner else '-'), exp))
    return out

# Edge texts: (text, what the package says, what apparmor_parser said in the
# experiments). Each runs through both; KNOWN lists the disagreements.
EDGES = [
    ('profile e { /x r, }', True),
    ('profile e { /x wa, }', False),
    ('profile e { /x x, }', False),
    ('profile e { deny /x ix, }', False),
    ('profile e { /x ix px, }', False),
    ('profile e { /x ix, /x px, }', False),
    ('profile e { /x ix, owner /x px, }', False),
    ('profile e { /a/* ix, /a/b px, }', True),
    ('profile e { capability bogus, }', False),
    ('profile e { capability CAP_CHOWN, }', False),
    ('profile e { owner capability chown, }', False),
    ('profile e { network bogus, }', False),
    ('profile e { network inet stream tcp, }', False),
    ('profile e { signal set=(bogus), }', False),
    ('profile e { signal peer=a peer=b, }', False),
    ('profile e { ptrace (send), }', False),
    ('profile e { mount options=(bogus), }', False),
    ('profile e { umount -> /mnt/, }', False),
    ('profile e { dbus send name=x, }', False),
    ('profile e { dbus bind path=/x, }', False),
    ('profile e { dbus eavesdrop path=/x, }', False),
    ('profile e { change_profile safe -> foo, }', False),
    ('profile e { deny audit /x r, }', False),
    ('profile e { owner deny /x w, }', False),
    ('profile e { /x r }', False),
    ('profile e { /x/{a} r, }', False),
    ('profile e { /x/[a-] r, }', False),
    ('profile e { /x/[]] r, }', False),
    ('profile e { /x/{a,b r, }', False),
    ('profile e flags=(bogus) { }', False),
    ('profile e flags=(complain enforce) { }', False),
    ('profile e { } profile e { }', False),
    ('profile e { ^h { } ^h { } }', False),
    ('profile e { @{NOPE}/x r, }', False),
    ('@{A} = /x\n@{A} = /y\nprofile e { @{A} r, }', False),
    ('@{A} += /x\nprofile e { @{A} r, }', False),
    ('@{A} = /x,\nprofile e { @{A} r, }', False),
    ('profile e { /x r, }\n@{A} = /y\nprofile f { }', False),
    ('profile e { include <zzaa/nonexist> }', False),
    ('profile e { include if exists <zzaa/nonexist> }', True),
    ('profile e { audit { /x r, network, } deny { /y w, } }', True),
    ('profile e (complain) { /x r, }', True),
    ('profile e { /x rw -> b, }', False),
    ('profile e { foo r, }', False),
    ('profile e { /x uX, }', False),
    ('profile e { /x pix -> b, /y Cx -> c, profile c { } }', True),
    ('profile e { unix, }', False),
    ('profile e { pivot_root, }', False),
    ('profile e { set rlimit nproc <= 10, }', False),
    ('profile e { link /a -> /b, }', False),
    ('abi <abi/3.0>,\nprofile e { /x r, }', True),
    ('profile e { /x/a,b r, }', True),
    ('profile -e { }', False),
    ('profile e { network unix tcp, }', False),
    ('profile e { network inet6 icmp, }', False),
    ('profile e { network inet6 udp, }', True),
    ('profile e { mount options=(ro,rw), }', False),
    ('profile e { mount options in (ro,rw), }', True),
    ('profile e { lpx /x -> foo, }', False),
    ('profile e { /x lpx -> foo, }', True),
    ('profile e { change_profile /bin/a, change_profile unsafe /bin/*, }', False),
    ('profile e { change_profile safe /bin/a, change_profile unsafe /usr/b, }', False),
    ('profile e { change_profile unsafe /bin/a, change_profile unsafe /bin/*, }', True),
]
# what apparmor_parser 4.0.1 does differently (documented in the README):
# accepts a target without an exec mode, a relative path, uX, profile names
# starting with '-', and the rule kinds outside the model; and abi needs the
# system's abi files
KNOWN = {'profile e { /x rw -> b, }', 'profile e { foo r, }', 'profile e { /x uX, }', 'profile -e { }',
         'profile e { unix, }', 'profile e { pivot_root, }', 'profile e { set rlimit nproc <= 10, }',
         'profile e { link /a -> /b, }', 'abi <abi/3.0>,\nprofile e { /x r, }'}

# stricter than apparmor_parser, which refuses only overlapping exec conditions
KNOWN.add('profile e { change_profile safe /bin/a, change_profile unsafe /usr/b, }')

def parser_accepts(files, main, tmp):
    for name, text in files.items():
        path = os.path.join(tmp, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, 'w') as f:
            f.write(text)
    res = subprocess.run(['apparmor_parser', '-Q', '-K', '-q', '--base', tmp, '-I', tmp, os.path.join(tmp, main)],
                         stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    return res.returncode == 0, res.stderr.strip().split('\n')[-1] if res.stderr else ''

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    npol = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    r = Rng(seed)
    random.seed(seed)
    have_parser = shutil.which('apparmor_parser') is not None
    for old in os.listdir(HERE):
        if old.startswith('cases-') and old.endswith('.bend'):
            os.remove(os.path.join(HERE, old))
    expect = []
    files_out = []
    parser_bad = []
    tmp = tempfile.mkdtemp(prefix='aa-ref-')
    per_file = 10
    chunk = []
    nq = 0
    try:
        pols = []
        for i in range(npol):
            pol = gen_policy(r, i)
            files = render(pol)
            pnames = ['main', 'main//c1', 'other'] + (['main//h1'] if any(c.hat for c in pol['profiles'][0].children) else [])
            qs = gen_queries(r, pol, pnames)
            pols.append((i, files, qs))
            if have_parser:
                ok, msg = parser_accepts(files, 'main%d' % i, tmp)
                if not ok:
                    parser_bad.append((i, msg))
        for e, (text, ours) in enumerate(EDGES):
            pols.append(('e%d' % e, {'edge%d' % e: text + '\n'}, None))
        lines = []
        for item in pols:
            i, files, qs = item
            main = ('main%d' % i) if qs is not None else ('edge%s' % i[1:])
            fl = '[' + ', '.join('src(%s, %s)' % (bstr(n), bstr(t)) for n, t in sorted(files.items())) + ']'
            body = ['  +r = A.Aa.load(opts(), %s, o(%s))' % (fl, bstr(main)), '  +p = pol.of(r)', '  do IO<Unit>:']
            if qs is not None:
                body.append('    IO.print("%s load " ++ show.load(r))' % i)
                expect.append('%s load ok' % i)
                for expr, label, exp in qs:
                    body.append('    IO.print(%s ++ %s)' % (bstr('%s %s ' % (i, label)), expr))
                    expect.append('%s %s %s' % (i, label, exp))
                    nq += 1
            else:
                body.append('    IO.print("%s load " ++ show.ok(r))' % i)
            chunk.append((i, body))
        # write the case files: a few policies each, and the edge texts in one
        pchunks = [c for c in chunk if not str(c[0]).startswith('e')]
        echunks = [c for c in chunk if str(c[0]).startswith('e')]
        parts = [pchunks[k:k + per_file] for k in range(0, len(pchunks), per_file)] + [echunks]
        for k, part in enumerate(parts):
            with open(os.path.join(HERE, 'cases-%02d.bend' % k), 'w') as f:
                f.write(HEADER)
                for i, body in part:
                    f.write('\ndef t%s() -> IO(Unit):\n' % i)
                    f.write('\n'.join(body) + '\n')
                f.write('\ndef main() -> IO(Unit):\n  do IO<Unit>:\n')
                for i, body in part:
                    f.write('    t%s()\n' % i)
        # the edges: what the package must say; their apparmor_parser results go to edges.txt
        edge_lines = []
        for e, (text, ours) in enumerate(EDGES):
            expect.append('e%d load %s' % (e, 'ok' if ours else 'error'))
            if have_parser:
                ok, msg = parser_accepts({'edge%d' % e: text + '\n'}, 'edge%d' % e, tmp)
                same = ok == ours
                tag = 'agree' if same else ('known' if text in KNOWN else 'disagree')
                edge_lines.append('%s e%d package=%s parser=%s :: %s' % (tag, e, 'accept' if ours else 'reject', 'accept' if ok else 'reject', text.replace('\n', ' | ')))
        with open(os.path.join(HERE, 'expected.txt'), 'w') as f:
            f.write('\n'.join(expect) + '\n')
        with open(os.path.join(HERE, 'edges.txt'), 'w') as f:
            f.write('\n'.join(edge_lines) + ('\n' if edge_lines else ''))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    for i, msg in parser_bad:
        print('parser rejects generated policy %d: %s' % (i, msg))
    bad_edges = [x for x in edge_lines if x.startswith('disagree')]
    for x in bad_edges:
        print(x)
    print('%d policies, %d queries, %d edge texts%s' % (npol, nq, len(EDGES), (', apparmor_parser: %d policies accepted, edges %d agree, %d known disagreements, %d other' % (npol - len(parser_bad), sum(1 for x in edge_lines if x.startswith('agree')), sum(1 for x in edge_lines if x.startswith('known')), len(bad_edges))) if have_parser else ', apparmor_parser not installed'))
    if parser_bad or bad_edges:
        sys.exit(1)

main()
