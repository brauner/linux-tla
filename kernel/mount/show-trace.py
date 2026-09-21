#!/usr/bin/env python3
"""Print a TLC counterexample from a check.sh log compactly: one block per
state with the action, the live mounts (id sb:root parent@mp flags), the
namespaces, the processes and the lock covers.
    ./show-trace.py logs/<cfg>.log
"""
import re
import sys

log = open(sys.argv[1]).read()
if 'Error: The behavior up to this point is:' not in log:
    print(log[log.find('Error'):][:2000] if 'Error' in log else 'no error in log')
    sys.exit(0)
trace = log[log.index('Error: The behavior up to this point is:'):]
print(log[log.index('Error:'):log.index('Error: The behavior')].strip())
states = re.split(r'\nState (\d+): ', trace)


def field(rec, name):
    m = re.search(r'\b' + name + r' \|-> (<<[^>]*>>|\{[^}]*\}|\[[^\]]*\]|[^,\]\s]+)', rec)
    return m.group(1) if m else '?'


def records(text):
    """top-level [ ... ] records inside a << >> or { }"""
    out, depth, cur = [], 0, ''
    for ch in text:
        if ch == '[':
            depth += 1
        if depth:
            cur += ch
        if ch == ']':
            depth -= 1
            if depth == 0:
                out.append(cur)
                cur = ''
    return out


def var(body, name):
    m = re.search(r'/\\ ' + name + r' = (.*?)(?=\n/\\ |\Z)', body, re.S)
    return re.sub(r'\s+', ' ', m.group(1)).strip() if m else ''


for i in range(1, len(states), 2):
    num, body = states[i], states[i + 1]
    head = body.split('\n', 1)[0]
    h = var(body, 'hist')
    kind = field(h, 'kind')
    flags = [k for k in ('tucked', 'locktransfer', 'reparented', 'slaveofslave', 'skippedmaster',
                         'lockedkept', 'connected', 'syncbusy', 'putns', 'expired', 'trimmed')
             if field(h, k) == 'TRUE']
    print(f"\n=== State {num}: {head.strip()}  [{kind} {' '.join(flags)}]  ok={var(body, 'ok')} ops={var(body, 'ops')}")
    for idx, rec in enumerate(records(var(body, 'mt')), 1):
        if field(rec, 'alive') != 'TRUE':
            continue
        fl = ''.join(c for c, k in (('S', 'shared'), ('U', 'unbind'), ('L', 'locked'), ('X', 'umount'),
                                    ('H', 'hashed'), ('A', 'attached'), ('E', 'onexp'), ('e', 'expmark'),
                                    ('k', 'shrink'), ('M', 'marked'), ('C', 'cand')) if field(rec, k) == 'TRUE')
        print(f"  m{idx}: {field(rec, 'sb')}:{field(rec, 'root')} parent={field(rec, 'parent')}@{field(rec, 'mp')} "
              f"ns={field(rec, 'ns')} gid={field(rec, 'gid')} master={field(rec, 'master')} "
              f"npeer={field(rec, 'npeer')} slaves={field(rec, 'slaves')} over={field(rec, 'over')} "
              f"kids={field(rec, 'children')} [{fl}]")
    for idx, rec in enumerate(records(var(body, 'nst')), 1):
        if field(rec, 'alive') == 'TRUE':
            print(f"  ns{idx}: root={field(rec, 'root')} user={field(rec, 'user')} anon={field(rec, 'anon')} origin={field(rec, 'origin')}")
    prs = var(body, 'pr')
    for m in re.finditer(r'(\w+) :> \[(.*?)\](?= @@|\)|$)', prs):
        p, rec = m.group(1), m.group(2)
        print(f"  {p}: ns={field(rec, 'ns')} root={field(rec, 'root')} cwd={field(rec, 'cwd')} fds={field(rec, 'fds')} nsfds={field(rec, 'nsfds')}")
    cv = var(body, 'covers')
    if cv and cv != '{}':
        print(f"  covers: {cv}")
    dd = var(body, 'ddead')
    if dd and dd != '{}':
        print(f"  dead dentries: {dd}")
