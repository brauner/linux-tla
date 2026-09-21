#!/usr/bin/env python3
"""Print a TLC counterexample of the MountWalk model compactly.
    ./show-walk-trace.py logs/<cfg>.log
"""
import re
import sys

log = open(sys.argv[1]).read()
marks = ['Error: The behavior up to this point is:', 'Error: The following behavior constitutes a counter-example:']
mark = next((mk for mk in marks if mk in log), None)
if mark is None:
    print(log[log.find('Error'):][:1500] if 'Error' in log else 'no error in log')
    sys.exit(0)
print(log[log.index('Error:'):log.index(mark)].strip())
trace = log[log.index(mark):]
states = re.split(r'\nState (\d+): ', trace)


def var(body, name):
    m = re.search(r'/\\ ' + name + r' = (.*?)(?=\n/\\ |\Z)', body, re.S)
    return re.sub(r'\s+', ' ', m.group(1)).strip() if m else '?'


def recs(text):
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


def field(rec, name):
    m = re.search(r'\b' + name + r' \|-> (\{[^}]*\}|"[^"]*"|\[[^\]]*\]|[^,\]\s]+)', rec)
    return m.group(1) if m else '?'


for i in range(1, len(states), 2):
    num, body = states[i], states[i + 1]
    head = re.sub(r' line \d+, col \d+ to line \d+, col \d+ of module \w+', '', body.split('\n', 1)[0].strip())
    print(f"--- {num} {head}  seq={var(body, 'seqv')} pc={var(body, 'pc')}")
    print(f"    mode={var(body, 'mode')} path={var(body, 'path')} nxt={var(body, 'nxt')} ip={var(body, 'ip')} mseq={var(body, 'mseq')} restarts={var(body, 'restarts')}")
    print(f"    res={var(body, 'res')} held={var(body, 'held')} rcu={var(body, 'rcu')} gp={var(body, 'gp')} tgt={var(body, 'tgt')} ctgt={var(body, 'ctgt')} victim={var(body, 'victim')}")
    for idx, rec in enumerate(recs(var(body, 'mnt')), 1):
        if field(rec, 'alive') == 'TRUE' or field(rec, 'freed') == 'TRUE':
            fl = ''.join(c for c, k in (('H', 'hashed'), ('N', 'ns'), ('F', 'freed')) if field(rec, k) == 'TRUE')
            print(f"    m{idx}: parent={field(rec, 'parent')} mp={field(rec, 'mp')} root={field(rec, 'root')} count={field(rec, 'count')} [{fl}]")
    mounted = var(body, 'mounted')
    on = re.findall(r'(\w+) :> TRUE', mounted)
    if on:
        print(f"    mounted={on}")
